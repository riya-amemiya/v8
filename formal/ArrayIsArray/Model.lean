import Torque

namespace ArrayIsArray

open Torque

inductive Result where
  | value (b : Bool)
  | runtime
  deriving DecidableEq, Repr

def isArray : Val → Result
  | .arr _ => .value true
  | .proxy => .runtime
  | _ => .value false

def specIsArray (proxyTarget : Option Bool) : Val → Option Bool
  | .arr _ => some true
  | .proxy => proxyTarget
  | _ => some false

end ArrayIsArray
