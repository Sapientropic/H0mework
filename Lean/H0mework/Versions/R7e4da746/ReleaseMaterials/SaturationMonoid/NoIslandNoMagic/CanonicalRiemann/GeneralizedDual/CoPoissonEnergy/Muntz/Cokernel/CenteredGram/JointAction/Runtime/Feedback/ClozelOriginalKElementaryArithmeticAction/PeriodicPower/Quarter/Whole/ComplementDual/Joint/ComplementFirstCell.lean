import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingFirstCell
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.ComplementFirstCell
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
open scoped Topology
local notation "q"=>(1/4:ℝ)

/-- The original complete integer source has exactly one true term on this collar. -/
theorem actual_complement_first_cell (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (lower:q/2<x) (upper:x≤q):
    fullFloorRaw c x=dualRaw c.value c.belowOne x:=by
  have positive:0<x:=by linarith
  have index:⌊q/x⌋₊=1:=by
    apply (Nat.floor_eq_iff (show 0≤q/x from by positivity)).mpr
    constructor
    · norm_num only [Nat.cast_one]
      exact (le_div_iff₀ positive).mpr (by simpa using upper)
    · norm_num only [Nat.cast_one]
      exact (div_lt_iff₀ positive).mpr (by linarith)
  rw [fullFloorRaw,floorRaw,DualSourceRaw.channels,abs_of_pos positive,index]
  norm_num

/-- The paid smooth correction and the true seed combine to that same unweighted counted field. -/
theorem actual_complete_first_cell (c:BurnolCompletedMellinCoordinate) (x:ℝ)
    (lower:q/2<x) (upper:x≤q):
    seedRaw c.value x+correctionRaw c.value c.belowOne x=fullFloorRaw c x:=by
  rw [actual_complement_first_cell c x lower upper]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.ComplementFirstCell
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
