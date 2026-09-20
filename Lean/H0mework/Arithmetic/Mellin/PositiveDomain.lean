import Mathlib.Analysis.Complex.Basic

/-!
# Narrow positive Mellin base types

This module owns only the positive real domain and its complex-valued function
space.  Analytic convergence, dilation, q-rich, endpoint, and witness material
remain downstream.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

abbrev PositiveMellinReal := {t : ℝ // 0 < t}
abbrev ClozelPositiveMellinFunction := PositiveMellinReal → ℂ

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
