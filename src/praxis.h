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
  static constexpr bool value = false;
};

template<>
struct Copy<int>
{
  static constexpr bool value = true;
};

template<>
struct Copy<char>
{
  static constexpr bool value = true;
};

template<>
struct Copy<bool>
{
  static constexpr bool value = true;
};

template<>
struct Copy<const char *>
{
  static constexpr bool value = true;
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

#define BINARY_OP(name, ret_type, lhs_type, rhs_type, op) ret_type name(std::pair<lhs_type, rhs_type> args) { return args.first op args.second; }
#define UNARY_OP(name, ret_type, arg_type, op) ret_type name(arg_type arg) { return op arg; }

BINARY_OP(add_int, int, int, int, +);
BINARY_OP(subtract_int, int, int, int, -);
BINARY_OP(multiply_int, int, int, int, *);
UNARY_OP(negate_int, int, int, -);
UNARY_OP(unary_plus_int, int, int, +);
BINARY_OP(lt_int, bool, int, int, <);
BINARY_OP(gt_int, bool, int, int, >);
BINARY_OP(lte_int, bool, int, int, <);
BINARY_OP(gte_int, bool, int, int, >=);
BINARY_OP(eq_int, bool, int, int, ==);
BINARY_OP(neq_int, bool, int, int, !=);

#undef UNARY_OP
#undef BINARY_OP

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
