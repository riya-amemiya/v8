import ArrayAt.Safety

namespace ArrayAt.Examples

open Torque ArrayAt

def exactAdd (x y : Int) : Int := x + y

def roundAway (x y : Int) : Int := if x + y < -(2 ^ 53) then x + y - 1 else x + y

#guard convertRelativeIndex exactAdd (.fin 1) 3 == some 1

#guard convertRelativeIndex exactAdd (.fin (-1)) 3 == some 2

#guard convertRelativeIndex exactAdd (.fin (-4)) 3 == none

#guard convertRelativeIndex exactAdd (.fin 3) 3 == none

#guard convertRelativeIndex exactAdd .posInf 3 == none

#guard convertRelativeIndex exactAdd .negInf 3 == none

#guard convertRelativeIndex roundAway (.fin (-(2 ^ 60))) 3 == specAt 3 (.fin (-(2 ^ 60)))

#guard specAt 0 (.fin 0) == none

end ArrayAt.Examples
