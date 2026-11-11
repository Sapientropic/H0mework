import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalKExpandedInverseSourceAction OriginalKMaterialExpandedDualSourceAction
local instance recoveryComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "q" => (1/4:ℝ)

theorem source_finite_complete_field (value : BurnolL2) (t : ℝ) (N : Nat) :
 sourceFiniteDualField t N value=
 burnolQuarterZeroExtension (sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2)+
 fourierL2 (burnolQuarterZeroExtension (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)) := rfl

theorem source_finite_own_qualifications (value : BurnolL2) (t : ℝ) (N : Nat) :
 burnolQuarterMeanCoefficient (sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2)=0 ∧
 burnolQuarterMeanCoefficient (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)=0 ∧
 reflectRestricted (1/4:ℝ) (sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2)=sourceFiniteDualPlus t N value ∧
 reflectRestricted (1/4:ℝ) (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)=sourceFiniteDualMinus t N value :=
 ⟨Constructor.mean_zero _,Constructor.mean_zero _,
  burnolAmbientMeanZeroPosition_reflection_fixed _,burnolAmbientMeanZeroPosition_reflection_fixed _⟩

theorem source_finite_complete_even (value : BurnolL2) (t : ℝ) (N : Nat) :
 reflectL2 (sourceFiniteDualField t N value)=sourceFiniteDualField t N value := by
 rw [source_finite_complete_field,map_add,←fourierL2_reflectL2_commute]
 rw [burnolQuarterZeroExtension,burnolRadiusZeroExtension_reflect,
  (source_finite_own_qualifications value t N).2.2.1,
  burnolRadiusZeroExtension_reflect,(source_finite_own_qualifications value t N).2.2.2]

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
theorem source_finite_two_RHS (value : BurnolL2) (t : ℝ) (N : Nat) :
 burnolAmbientMeanZeroPosition (sourceFiniteDualField t N value) =
  sourceFiniteDualPlus t N value + T (sourceFiniteDualMinus t N value) ∧
 burnolAmbientMeanZeroFourier (sourceFiniteDualField t N value) =
  T (sourceFiniteDualPlus t N value) + sourceFiniteDualMinus t N value := by
 have even := source_finite_complete_even value t N
 have face : burnolAmbientEvenPart (sourceFiniteDualField t N value)=sourceFiniteDualField t N value := by
  unfold burnolAmbientEvenPart
  rw [even]
  module
 constructor
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (burnolAmbientEvenPart (sourceFiniteDualField t N value)))=_
   rw [face,source_finite_complete_field,map_add,burnolQuarterRestriction_zeroExtension,map_add,
    burnolQuarterMeanZeroProjection_coe]
   change _+burnolQuarterMeanZeroProjection
    (burnolTruncatedFourier (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2))=_
   rw [←burnolMeanZeroTruncatedFourier_coe]
   rfl
 · apply Subtype.ext
   change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (fourierL2 (burnolAmbientEvenPart (sourceFiniteDualField t N value))))=_
   have reflected : reflectL2 (burnolQuarterZeroExtension
    (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)) =
     burnolQuarterZeroExtension (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2) := by
    unfold burnolQuarterZeroExtension
    rw [burnolRadiusZeroExtension_reflect,(source_finite_own_qualifications value t N).2.2.2]
   rw [face,source_finite_complete_field,map_add,fourierL2_fourierL2,reflected,
    map_add,burnolQuarterRestriction_zeroExtension,map_add,burnolQuarterMeanZeroProjection_coe]
   change burnolQuarterMeanZeroProjection
    (burnolTruncatedFourier (sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2))+_=_
   rw [←burnolMeanZeroTruncatedFourier_coe]
   rfl

/-- The already-paid inverse recovers the same two profiles from the complete source field, before independent fees are read. -/
theorem source_finite_profiles_recovered (value : BurnolL2) (t : ℝ) (N : Nat) :
 burnolAmbientMeanZeroFirstCorrection (sourceFiniteDualField t N value)=sourceFiniteDualPlus t N value ∧
 burnolAmbientMeanZeroSecondCorrection (sourceFiniteDualField t N value)=sourceFiniteDualMinus t N value := by
 have rhs := source_finite_two_RHS value t N
 unfold burnolAmbientMeanZeroFirstCorrection burnolAmbientMeanZeroSecondCorrection burnolAmbientMeanZeroBlockRhs
 rw [rhs.1,rhs.2]
 exact source_block_recovery _ _
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
