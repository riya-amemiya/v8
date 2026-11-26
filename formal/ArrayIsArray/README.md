# Lean 4 model and proof for `Array.isArray`

This directory models `ArrayIsArray` in `src/builtins/array-isarray.tq`, a type
switch with no memory access of its own.

## Files

| File | Contents |
| --- | --- |
| `ArrayIsArray/Model.lean` | The type switch and the specification |
| `ArrayIsArray/Safety.lean` | Agreement with the specification |
| `ArrayIsArray/Examples.lean` | Executable `#guard` checks |

## Correspondence with `array-isarray.tq`

| Lean | Torque |
| --- | --- |
| `isArray` | `ArrayIsArray` |
| `Result.runtime` | the call of `runtime::ArrayIsArray` for a `JSProxy` |
| `specIsArray` | `IsArray`, where `proxyTarget` stands for the result for the proxy target, or a TypeError for a revoked proxy |

## Theorems

`isArray_spec`. For every value other than a proxy the builtin returns the
specification result, and it hands every proxy to the runtime.

## Not modeled

`Runtime_ArrayIsArray` and the proxy target chain are outside the model.
