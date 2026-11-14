import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeSuccessFinite

set_option autoImplicit false
namespace FlyCNS.C3NativePrecisionControls
open C3FiniteOccurrence C3NativeMinimum

example (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (C3NativePrecision.Successful boundary installed anchor) :=
  C3NativePrecision.finite_successful_carrier boundary installed anchor

end FlyCNS.C3NativePrecisionControls
