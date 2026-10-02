import H0mework.Versions.R2.Arithmetic.RiemannSource.NontrivialCompletedZero

/-!
# Narrow positive parameters from a nontrivial completed zero

The selected and reversed half-parameters lie in the positive half-plane.
This strip arithmetic is kept below Mellin-orbit, radial, separator, endpoint,
and fixedness consumers.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction

noncomputable section

theorem selectedPositiveParameter_re_pos
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    0 < (observation.coordinate / 2).re := by
  have strip :=
    observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  rw [div_ofNat_re]
  linarith

theorem reversalPositiveParameter_re_pos
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    0 < (coordinateReversal observation.coordinate / 2).re := by
  have strip :=
    observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  rw [div_ofNat_re]
  simp [coordinateReversal]
  linarith

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
