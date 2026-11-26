import ArrayIsArray.Safety

namespace ArrayIsArray.Examples

open Torque ArrayIsArray

#guard isArray (.arr 0) == .value true

#guard isArray .proxy == .runtime

#guard isArray (.smi 1) == .value false

#guard isArray .other == .value false

end ArrayIsArray.Examples
