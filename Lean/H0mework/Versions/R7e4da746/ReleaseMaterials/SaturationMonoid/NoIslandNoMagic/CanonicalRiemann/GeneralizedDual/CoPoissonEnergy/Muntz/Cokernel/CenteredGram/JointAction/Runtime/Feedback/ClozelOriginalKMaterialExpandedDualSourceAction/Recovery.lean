import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialExpandedDualSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalKExpandedInverseSourceAction
local instance recoveryComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "q" => (1/4:ℝ)

private theorem source_block_recovery (first second : BurnolQuarterMeanZeroCarrier) :
 burnolMeanZeroBlockFirst (first+T second,T first+second)=first ∧
 burnolMeanZeroBlockSecond (first+T second,T first+second)=second := by
 have left : burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare=1 :=
  Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
 have rhs : first+T second-T (T first+second)=burnolMeanZeroOneMinusSquare first := by
  simp only [map_add]
  change _=first-T (T first)
  module
 have actualFirst : burnolMeanZeroBlockFirst (first+T second,T first+second)=first := by
  unfold burnolMeanZeroBlockFirst
  rw [rhs]
  change (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) first=first
  rw [left]
  rfl
 refine ⟨actualFirst,?_⟩
 unfold burnolMeanZeroBlockSecond
 rw [actualFirst]
 module

/-- The source field itself regenerates both actual mean-zero RHS, with no physical qualifier or target price supplied. -/
theorem source_own_two_RHS (value : BurnolL2) (t : ℝ) :
 burnolAmbientMeanZeroPosition (sourceDualCompleteField t value) =
  sourceDualPlus t value + T (sourceDualMinus t value) ∧
 burnolAmbientMeanZeroFourier (sourceDualCompleteField t value) =
  T (sourceDualPlus t value) + sourceDualMinus t value := by
 have even := source_dual_complete_even value t
 have face : burnolAmbientEvenPart (sourceDualCompleteField t value)=sourceDualCompleteField t value := by
  unfold burnolAmbientEvenPart
  rw [even]
  module
 constructor
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (burnolAmbientEvenPart (sourceDualCompleteField t value)))=_
   rw [face,source_dual_complete_field,map_add,burnolQuarterRestriction_zeroExtension,map_add,
    burnolQuarterMeanZeroProjection_coe]
   change _+burnolQuarterMeanZeroProjection
    (burnolTruncatedFourier (sourceDualMinus t value : BurnolQuarterIntervalL2))=_
   rw [←burnolMeanZeroTruncatedFourier_coe]
   rfl
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (fourierL2 (burnolAmbientEvenPart (sourceDualCompleteField t value))))=_
   have reflected : reflectL2 (burnolQuarterZeroExtension
    (sourceDualMinus t value : BurnolQuarterIntervalL2)) =
     burnolQuarterZeroExtension (sourceDualMinus t value : BurnolQuarterIntervalL2) := by
    unfold burnolQuarterZeroExtension
    rw [burnolRadiusZeroExtension_reflect,(source_dual_own_qualifications value t).2.2.2]
   rw [face,source_dual_complete_field,map_add,fourierL2_fourierL2,reflected,
    map_add,burnolQuarterRestriction_zeroExtension,map_add,burnolQuarterMeanZeroProjection_coe]
   change burnolQuarterMeanZeroProjection
    (burnolTruncatedFourier (sourceDualPlus t value : BurnolQuarterIntervalL2))+_=_
   rw [←burnolMeanZeroTruncatedFourier_coe]
   rfl

/-- The already-paid inverse recovers the same two profiles from the complete source field, before independent fees are read. -/
theorem source_own_profiles_recovered (value : BurnolL2) (t : ℝ) :
 burnolAmbientMeanZeroFirstCorrection (sourceDualCompleteField t value)=sourceDualPlus t value ∧
 burnolAmbientMeanZeroSecondCorrection (sourceDualCompleteField t value)=sourceDualMinus t value := by
 have rhs := source_own_two_RHS value t
 unfold burnolAmbientMeanZeroFirstCorrection burnolAmbientMeanZeroSecondCorrection burnolAmbientMeanZeroBlockRhs
 rw [rhs.1,rhs.2]
 exact source_block_recovery _ _
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
