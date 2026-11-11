import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.EvenAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set Filter
open BurnolPhysicalState BurnolPhysicalState.OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "q" => (1/4:ℝ)
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The full source Volterra input is taken before the actual next state is read. -/
def sourceFourierInput (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  sourceVolterraResolvent coordinate (fourierL2 value)

def sourceFourierGap (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  burnolAmbientMeanZeroPosition (sourceFourierInput coordinate value)

/-- Both original mean-zero blocks are solved from the source Fourier gap and zero position gap. -/
def sourceOutsideColumn (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroBlockSecond (0,sourceFourierGap coordinate value)

def sourceOutsideField (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  fourierL2 (burnolQuarterZeroExtension (sourceOutsideColumn coordinate value : BurnolQuarterIntervalL2))-
    burnolQuarterZeroExtension (S (sourceOutsideColumn coordinate value) : BurnolQuarterIntervalL2)

private theorem rightQuarter (coordinate : BurnolCompletedMellinCoordinate) : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]

/-- Full L2 Fourier action uses the same parameter, without any Fourier-square substitution. -/
theorem source_fourier_input (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceFourierInput coordinate value=fourierL2 (burnolDirectRightResolvent (coordinate.value/2) value) := by
  change sourceVolterraResolvent coordinate (fourierL2 value)=_
  rw [FiniteMobiusResolventFlux.fourier_R _ (rightQuarter coordinate)]
  exact (FiniteMobiusResolventFlux.Rplus_tate _ (rightQuarter coordinate) _).symm

private theorem evenPart_fourier (value : BurnolL2) :
    burnolAmbientEvenPart (fourierL2 value)=fourierL2 (burnolAmbientEvenPart value) := by
  unfold burnolAmbientEvenPart
  rw [map_smul,map_add,fourierL2_reflectL2_commute]

theorem source_fourier_gap (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceFourierGap coordinate value=burnolAmbientMeanZeroFourier (burnolDirectRightResolvent (coordinate.value/2) value) := by
  unfold sourceFourierGap burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier
  rw [source_fourier_input,evenPart_fourier]

private theorem source_first_block (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    burnolMeanZeroBlockFirst (0,sourceFourierGap coordinate value)=-S (sourceOutsideColumn coordinate value) := by
  have actual := burnolMeanZeroBlock_first_equation (0,sourceFourierGap coordinate value)
  change burnolMeanZeroBlockFirst (0,sourceFourierGap coordinate value)+S (sourceOutsideColumn coordinate value)=0 at actual
  exact eq_neg_of_add_eq_zero_left actual

/-- The actual source column pays the complete original B equation. -/
theorem source_outside_B_action (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    burnolMeanZeroOneMinusSquare (sourceOutsideColumn coordinate value)=sourceFourierGap coordinate value := by
  have actual := burnolMeanZeroBlock_second_equation (0,sourceFourierGap coordinate value)
  rw [source_first_block,map_neg] at actual
  change -S (S (sourceOutsideColumn coordinate value))+sourceOutsideColumn coordinate value=sourceFourierGap coordinate value at actual
  change sourceOutsideColumn coordinate value-S (S (sourceOutsideColumn coordinate value))=_
  linear_combination (norm:=module) actual

private theorem source_gap_even (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectRestricted q (sourceFourierGap coordinate value : BurnolQuarterIntervalL2)=sourceFourierGap coordinate value :=
  burnolAmbientMeanZeroPosition_reflection_fixed _

private theorem source_column_even (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectRestricted q (sourceOutsideColumn coordinate value : BurnolQuarterIntervalL2)=sourceOutsideColumn coordinate value := by
  have reflected : burnolMeanZeroOneMinusSquare (sourceMeanZeroReflection (sourceOutsideColumn coordinate value))=sourceFourierGap coordinate value := by
    change sourceMeanZeroReflection (sourceOutsideColumn coordinate value)-S (S (sourceMeanZeroReflection (sourceOutsideColumn coordinate value)))=_
    rw [sourceMeanZeroFourier_reflect,sourceMeanZeroFourier_reflect]
    apply Subtype.ext
    change reflectRestricted q (sourceOutsideColumn coordinate value : BurnolQuarterIntervalL2)-
      reflectRestricted q (S (S (sourceOutsideColumn coordinate value)) : BurnolQuarterIntervalL2)=_
    rw [←map_sub]
    exact (congrArg (fun state:BurnolQuarterMeanZeroCarrier => reflectRestricted q (state:BurnolQuarterIntervalL2))
      (source_outside_B_action coordinate value)).trans (source_gap_even coordinate value)
  have same := congrArg burnolMeanZeroBlockInverse (reflected.trans (source_outside_B_action coordinate value).symm)
  have inverseLeft : burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare=1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  change (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) (sourceMeanZeroReflection (sourceOutsideColumn coordinate value))=
    (burnolMeanZeroBlockInverse*burnolMeanZeroOneMinusSquare) (sourceOutsideColumn coordinate value) at same
  rw [inverseLeft] at same
  exact congrArg (fun state:BurnolQuarterMeanZeroCarrier => (state:BurnolQuarterIntervalL2)) same

private theorem source_return_even (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectRestricted q (S (sourceOutsideColumn coordinate value) : BurnolQuarterIntervalL2)=S (sourceOutsideColumn coordinate value) := by
  have fixed : sourceMeanZeroReflection (sourceOutsideColumn coordinate value)=sourceOutsideColumn coordinate value :=
    Subtype.ext (source_column_even coordinate value)
  have actual := sourceMeanZeroFourier_reflect (sourceOutsideColumn coordinate value)
  rw [fixed] at actual
  exact congrArg (fun state:BurnolQuarterMeanZeroCarrier => (state:BurnolQuarterIntervalL2)) actual.symm

private theorem source_field_even (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectL2 (sourceOutsideField coordinate value)=sourceOutsideField coordinate value := by
  have column : reflectL2 (burnolQuarterZeroExtension (sourceOutsideColumn coordinate value : BurnolQuarterIntervalL2))=
      burnolQuarterZeroExtension (sourceOutsideColumn coordinate value : BurnolQuarterIntervalL2) := by
    change reflectL2 (burnolRadiusZeroExtension q _)=_
    rw [burnolRadiusZeroExtension_reflect,source_column_even]
    rfl
  have returned : reflectL2 (burnolQuarterZeroExtension (S (sourceOutsideColumn coordinate value) : BurnolQuarterIntervalL2))=
      burnolQuarterZeroExtension (S (sourceOutsideColumn coordinate value) : BurnolQuarterIntervalL2) := by
    change reflectL2 (burnolRadiusZeroExtension q _)=_
    rw [burnolRadiusZeroExtension_reflect,source_return_even]
    rfl
  unfold sourceOutsideField
  rw [map_sub,←fourierL2_reflectL2_commute,column,returned]

private theorem actual_R_reflect (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectL2 (burnolDirectRightResolvent (coordinate.value/2) value)=
      burnolDirectRightResolvent (coordinate.value/2) (reflectL2 value) := by
  apply fourierL2.injective
  rw [fourierL2_reflectL2_commute,←source_fourier_input]
  change reflectL2 (sourceVolterraResolvent coordinate (fourierL2 value))=_
  rw [sourceVolterraResolvent_reflect,←fourierL2_reflectL2_commute]
  exact source_fourier_input coordinate (reflectL2 value)

/-- The full outside-P vector is generated from the input Volterra gap and the original B blocks. -/
theorem full_R_outside_source (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (gap : value∈locallyConstantFace burnolUnscaledCommonGapRadius) (even : reflectL2 value=value) :
    OriginalKCombPhysicalAction.physicalRemainder (burnolDirectRightResolvent (coordinate.value/2) value)=sourceOutsideField coordinate value := by
  let target := burnolDirectRightResolvent (coordinate.value/2) value
  have targetEven : reflectL2 target=target := (actual_R_reflect coordinate value).trans (congrArg _ even)
  have part : burnolAmbientEvenPart target=target := by
    unfold burnolAmbientEvenPart
    rw [targetEven]
    module
  have zeroPosition : burnolAmbientMeanZeroPosition target=0 := by
    apply Subtype.ext
    change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolAmbientEvenPart target))=0
    rw [part]
    apply (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
    exact CombSource.Pricing.ambient_R_positionGap _ (rightQuarter coordinate) value gap
  have rhs : burnolAmbientMeanZeroBlockRhs target=(0,sourceFourierGap coordinate value) := by
    unfold burnolAmbientMeanZeroBlockRhs
    rw [zeroPosition,source_fourier_gap]
  have correction : burnolAmbientRawMeanZeroCorrection target=sourceOutsideField coordinate value := by
    unfold burnolAmbientRawMeanZeroCorrection burnolAmbientMeanZeroFirstCorrection burnolAmbientMeanZeroSecondCorrection
    rw [rhs,source_first_block]
    unfold sourceOutsideField sourceOutsideColumn
    rw [Submodule.coe_neg,map_neg]
    module
  have projected := burnolEvenOrthogonalProjection_eq_resolventFormula target
  unfold burnolAmbientExtendedSonineProjectionFormula burnolAmbientEvenMeanZeroCorrection at projected
  rw [part,correction] at projected
  have sourcePart : burnolAmbientEvenPart (sourceOutsideField coordinate value)=sourceOutsideField coordinate value := by
    unfold burnolAmbientEvenPart
    rw [source_field_even]
    module
  rw [sourcePart] at projected
  have split := (evenBurnolClosedFace q).toSubmodule.starProjection_add_starProjection_orthogonal target
  rw [projected] at split
  change (evenBurnolClosedFace q).toSubmodule.orthogonal.starProjection target=_
  linear_combination (norm:=module) split

namespace D
export OriginalKCombFirstFullSourceDynamics (raw input packet next_pair raw_successor raw_xi_source)
end D
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

private theorem actual_raw_even : reflectL2 (D.raw observation nontrivial half depth ordinal)=D.raw observation nontrivial half depth ordinal := by
  rw [D.raw_xi_source]
  generalize generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate+(ordinal+2)=steps
  induction steps with
  | zero => exact mem_evenL2ClosedFace_iff.mp (burnolPaCombApproximation 0).property.2
  | succ steps previous =>
    rw [pow_succ',Module.End.mul_apply]
    change reflectL2 (burnolDirectRightResolvent ((c).value/2) _)=burnolDirectRightResolvent ((c).value/2) _
    rw [actual_R_reflect,previous]

/-- The original next packet's entire second inventory slot is this source-generated vector. -/
theorem actual_born_outside_source :
    (D.input observation nontrivial half depth (ordinal+1)).2=
      sourceOutsideField c (D.raw observation nontrivial half depth ordinal) := by
  rw [D.next_pair,OriginalKCombCofinalRAction.original_R_direct]
  exact full_R_outside_source c _ (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal)
    (actual_raw_even observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
