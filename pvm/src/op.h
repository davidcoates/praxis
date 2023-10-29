#pragma once

enum class OpCode : uint8_t
{
  Push8,
  Push16,
  Push32,
  Push64,
  PushN,

  Pop8,
  Pop16,
  Pop32,
  Pop64,
  PopN,

  Invoke,
  InvokeAt,
  Return,

  IAddr,
  ISub,
  IMul,
  IDiv,
  INeg,

  BNot,
  BOr,
  BAnd,
  BXor,

  ANew,
  ASet,
  AGet,
  ALen,

  VNew,
  VSet,
  VGet,
  VLen,

  BoxN,
  UnboxN,

  Load8,
  Load16,
  Load32,
  Load64,
  LoadN,

  Save8,
  Save16,
  Save32,
  Save64,
  SaveN,
};

struct Invokable
{
  uint64_t size;
};
