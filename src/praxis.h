#include <utility>
#include <vector>
#include <string>
#include <stdexcept>
#include <functional>
#include <optional>
#include <iostream>
#include <memory>
#include <variant>

namespace praxis {

template<size_t I, typename F>
decltype(auto) recursive(F f);

template<size_t I, size_t J, typename F>
struct Recursive
{
  F f;

  explicit Recursive(F f)
    : f(f)
  {}

  template<typename... Args>
  decltype(auto) operator()(Args&&... args) const
  {
    return std::get<J>(std::apply(this->f, recursive<I, F>(this->f)))(std::forward<Args>(args)...);
  }
};

template<size_t I, typename F, size_t... Is>
decltype(auto) recursive_helper(F f, std::index_sequence<Is...>)
{
  return std::tuple<Recursive<I, Is, F>...>(
    Recursive<I, Is, F>(f)...
  );
}

template<size_t I, typename F>
auto recursive(F f)
{
  return recursive_helper<I, F>(f, std::make_index_sequence<I>{});
}

using String = std::string;

template<typename T>
struct Copy
{
  static constexpr bool value = std::is_scalar_v<T>;
};

template<typename T>
inline constexpr bool can_copy = Copy<T>::value;

template<typename T>
struct Boxed : public std::unique_ptr<T>
{
  Boxed(std::unique_ptr<T>&& ptr)
    : std::unique_ptr<T>(std::move(ptr))
  {
  }

  template<size_t index>
  inline auto&& get()
  {
    return static_cast<std::unique_ptr<T>*>(this)->get()->template get<index>();
  }

  template<size_t index>
  inline const auto& get() const
  {
    return static_cast<const std::unique_ptr<T>*>(this)->get()->template get<index>();
  }

  inline auto index() const
  {
    return static_cast<const std::unique_ptr<T>*>(this)->get()->index();
  }
};

template<typename T, typename... Args>
auto mkBoxed(Args&&... args) -> Boxed<T>
{
  return Boxed<T>(std::make_unique<T>(std::forward<Args>(args)...));
}

template<typename T>
struct Ref;

enum class View
{
    VALUE,
    REF
};

template<View view, typename T>
struct Apply
{
};

template<typename T>
struct Apply<View::VALUE, T>
{
  using Type = T;
};

template<typename T>
struct Apply<View::REF, T>
{
  using Type = typename std::conditional<can_copy<T>, const T&, Ref<T>>::type;
};

template<>
struct Apply<View::REF, String>
{
  using Type = const char *;
};

template<View view, typename T>
using apply = typename Apply<view, T>::Type;

template<typename T>
auto ref(const T& obj) -> apply<View::REF, T>
{
  if constexpr (can_copy<T>)
    return obj;
  else if constexpr (std::is_same_v<T, String>)
    return Ref(obj.data());
  else
    return Ref(&obj);
}

template<typename T>
struct Ref
{
  explicit Ref(const T* data)
    : data(data)
  {}

  template<size_t index>
  inline auto get() const
  {
    return ref(data->template get<index>());
  }

  inline auto index() const
  {
    return data->index();
  }

  const T* data;
};

template<typename T1, typename T2>
inline auto first(const std::pair<T1, T2>& pair) -> const T1&
{
  return pair.first;
}

template<typename T1, typename T2>
inline auto first(std::pair<T1, T2>&& pair) -> T1&&
{
  return std::move(pair.first);
}

template<typename T1, typename T2>
inline auto first(Ref<std::pair<T1, T2>> pair) -> apply<View::REF, T1>
{
  return ref(pair.data->first);
}

template<typename T1, typename T2>
inline auto second(const std::pair<T1, T2>& pair) -> const T2&
{
  return pair.second;
}

template<typename T1, typename T2>
inline auto second(std::pair<T1, T2>&& pair) -> T2&&
{
  return std::move(pair.second);
}

template<typename T1, typename T2>
inline auto second(Ref<std::pair<T1, T2>> pair) -> apply<View::REF, T2>
{
  return ref(pair.data->second);
}

template<typename T>
struct Copy<Ref<T>>
{
  static constexpr bool value = true;
};

template<>
struct Copy<std::monostate>
{
  static constexpr bool value = true;
};

std::ostream& operator<<(std::ostream& ostream, const std::monostate&)
{
  ostream << "()";
  return ostream;
}

template<typename T1, typename T2>
struct Copy<std::pair<T1, T2>>
{
  static constexpr bool value = can_copy<T1> && can_copy<T2>;
};

template<typename T1, typename T2>
std::ostream& operator<<(std::ostream& ostream, const std::pair<T1, T2>& pair)
{
  ostream << "(" << pair.first << ", " << pair.second << ")";
  return ostream;
}

struct Exception : public std::runtime_error
{
  using std::runtime_error::runtime_error;
};

struct BindFail : public Exception
{
  using Exception::Exception;
};

struct CaseFail : public Exception
{
  using Exception::Exception;
};

struct SwitchFail : public Exception
{
  using Exception::Exception;
};

template<typename T>
using Array = std::vector<T>;

} // namespace praxis

namespace praxis::user {

#define ARITH_OP(name, op) auto name = []<typename T>() -> std::function<T(std::pair<T, T>)>\
{\
	return [](std::pair<T, T> arg)\
	{\
		return arg.first op arg.second;\
	};\
}

ARITH_OP(add, +);
ARITH_OP(subtract, -);
ARITH_OP(multiply, *);

#undef ARITH_OP

auto negate = []<typename T>() -> std::function<T(T)>
{
	return [](T arg)
	{
		return -arg;
	};
};

#define CMP_OP(name, op) auto name = []<typename T>() -> std::function<bool(std::pair<T, T>)>\
{\
	return [](std::pair<T, T> arg)\
	{\
		return arg.first op arg.second;\
	};\
}

CMP_OP(lt, <);
CMP_OP(gt, >);
CMP_OP(lte, <=);
CMP_OP(gte, >=);
CMP_OP(eq, ==);
CMP_OP(neq, !=);

#undef CMP_OP

using I8 = std::int8_t;
using I16 = std::int16_t;
using I32 = std::int32_t;
using I64 = std::int64_t;
using ISize = std::ptrdiff_t;

using U8 = std::uint8_t;
using U16 = std::uint16_t;
using U32 = std::uint32_t;
using U64 = std::uint64_t;
using USize = std::size_t;

/*
std::function<int()> get_int = []()
{
  int x;
  std::cin >> x;
  if (std::cin.fail())
    throw praxis::Exception("get_int: no parse");
  return x;
};

std::function<std::string()> get_str = []()
{
  std::string x;
  std::cin >> x;
  if (std::cin.fail())
    throw praxis::Exception("get_str: no parse");
  return x;
};

std::function<void(int)> put_int = [](auto x)
{
  std::cout << x;
};

std::function<void(const char*)> put_str = [](auto x)
{
  std::cout << x;
};

std::function<void(const char*)> put_str_ln = [](auto x)
{
  std::cout << x << std::endl;
};
*/

auto print = []<typename T>() -> std::function<std::monostate(praxis::apply<praxis::View::REF, T>)>
{
  return [=](T t) -> std::monostate
  {
    std::cout << t << std::endl;
    return std::monostate{};
  };
};

} // namespace praxis::user

/* prelude end */
