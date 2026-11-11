import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HProjectionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource OriginalPaPhysicalGreen
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKForcingGapAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "K" => burnolCompletedMellinRieszVector
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "J" => sourceAdjointFK
local instance sharedOutsidePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance sharedOutsideQuarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

-- Exact checked private term from the independently paid HQuarterSource, with unchanged source bytes.
elab "paidConjugateVolterraQuarter" : term => do
  let head := ("_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HQuarterSource".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
  let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource.conjugate_volterra_quarter".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
  return Lean.mkConst full

private theorem generated_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (generatedK c)=generatedK c := by
  rw [generatedK_eq_original]
  exact mem_evenL2ClosedFace_iff.mp (K c).property.2
private theorem generated_fourier_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (fourierL2 (generatedK c))=fourierL2 (generatedK c) := by
  rw [←fourierL2_reflectL2_commute,generated_even]
private theorem generated_fourier_gap (c : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (fourierL2 (generatedK c))=jQuarterGap c • intervalConstant q := by
  have qualified : burnolQuarterRestriction (fourierL2 (generatedK c))∈intervalConstantLine q := by
    rw [generatedK_eq_original]
    exact (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c)).property.1.1
  have centered := (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr qualified
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  exact sub_eq_zero.mp centered

theorem j_adjoint_full_volterra (c : BurnolCompletedMellinCoordinate) :
    J c=sourceVolterraResolvent (OriginalPrimitiveRankBalance.conjugateCoordinate c)
      (fourierL2 (generatedK c)) := by
  rw [generatedK_eq_original]
  calc
    J c=FiniteMobiusResolventFlux.Rplus (star c.value/2) (fourierL2 (K c : BurnolL2)) := by
      simpa only [star_div₀,star_ofNat] using (original_R_adjoint_fields c).2.symm
    _ = _ := FiniteMobiusResolventFlux.Rplus_tate (star c.value/2)
      (by rw [Complex.div_re];norm_num;linarith [c.rightHalf]) _

theorem j_quarter_source (c : BurnolCompletedMellinCoordinate) :
    quarterCotest (J c)=jQuarterAmplitude c • SingularCounting.centeredPower c := by
  have source := paidConjugateVolterraQuarter c (fourierL2 (generatedK c)) (jQuarterGap c)
    (generated_fourier_gap c) (generated_fourier_even c)
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (J c))=_
  rw [j_adjoint_full_volterra,source,map_add,map_smul,map_smul]
  have constantZero : burnolQuarterMeanZeroProjection (intervalConstant q)=0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)
  rw [constantZero,smul_zero,zero_add]
  rfl

theorem j_source_even (c : BurnolCompletedMellinCoordinate) : reflectL2 (J c)=J c := by
  rw [j_adjoint_full_volterra,sourceVolterraResolvent_reflect,generated_fourier_even]

theorem j_inverseFourier_source (c : BurnolCompletedMellinCoordinate) :
    fourierL2.symm (J c)=burnolDirectRightResolvent (star c.value/2) (generatedK c) := by
  rw [sourceAdjointFK,fourierL2.symm_apply_apply,generatedK_eq_original,(source_conjugate_R_fields c).1]

theorem j_inverseFourier_quarter_zero (c : BurnolCompletedMellinCoordinate) :
    quarterCotest (fourierL2.symm (J c))=0 := by
  let gamma := burnolQuarterMeanCoefficient (burnolQuarterRestriction (generatedK c))
  have qualified : burnolQuarterRestriction (generatedK c)∈intervalConstantLine q := by
    rw [generatedK_eq_original]
    exact (K c).property.1.1
  have centered := (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr qualified
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  have gap : burnolQuarterRestriction (generatedK c)=gamma • intervalConstant q := sub_eq_zero.mp centered
  have acted := right_resolvent_quarter_constant (star c.value/2)
    (by rw [Complex.div_re];norm_num;linarith [c.rightHalf]) (generatedK c) gamma gap
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (fourierL2.symm (J c)))=0
  rw [j_inverseFourier_source,acted,map_smul]
  have constantZero : burnolQuarterMeanZeroProjection (intervalConstant q)=0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)
  rw [constantZero,smul_zero]

private theorem j_evenPart (c : BurnolCompletedMellinCoordinate) : burnolAmbientEvenPart (J c)=J c := by
  unfold burnolAmbientEvenPart
  rw [j_source_even]
  module
private theorem j_fourier_eq_inverse (c : BurnolCompletedMellinCoordinate) :
    fourierL2 (J c)=fourierL2.symm (J c) := by
  apply fourierL2.injective
  rw [fourierL2_fourierL2,j_source_even,fourierL2.apply_symm_apply]
private theorem j_position_source (c : BurnolCompletedMellinCoordinate) :
    burnolAmbientMeanZeroPosition (J c)=jQuarterAmplitude c • SingularCounting.centeredPower c := by
  change quarterCotest (burnolAmbientEvenPart (J c))=_
  rw [j_evenPart,j_quarter_source]
private theorem j_fourier_source (c : BurnolCompletedMellinCoordinate) :
    burnolAmbientMeanZeroFourier (J c)=0 := by
  change quarterCotest (fourierL2 (burnolAmbientEvenPart (J c)))=0
  rw [j_evenPart,j_fourier_eq_inverse,j_inverseFourier_quarter_zero]

/-- J uses the same already generated B power column as H. No B solve on J is a source input. -/
theorem j_complete_correction_source (c : BurnolCompletedMellinCoordinate) :
    burnolAmbientEvenMeanZeroCorrection (J c)=jQuarterAmplitude c • hPowerPhysicalCorrection c := by
  have first : burnolAmbientMeanZeroFirstCorrection (J c)=jQuarterAmplitude c • hPowerBColumn c := by
    change burnolMeanZeroBlockInverse
      (burnolAmbientMeanZeroPosition (J c)-S (burnolAmbientMeanZeroFourier (J c)))=_
    rw [j_position_source,j_fourier_source,map_zero,sub_zero,map_smul]
    rfl
  have second : burnolAmbientMeanZeroSecondCorrection (J c)=jQuarterAmplitude c • hPowerBSecond c := by
    change burnolAmbientMeanZeroFourier (J c)-S (burnolAmbientMeanZeroFirstCorrection (J c))=_
    rw [j_fourier_source,first,map_smul,zero_sub]
    simp only [hPowerBSecond,smul_neg]
  unfold burnolAmbientEvenMeanZeroCorrection burnolAmbientRawMeanZeroCorrection
  rw [first,second]
  simp only [SetLike.val_smul,map_smul]
  rw [←smul_add]
  change burnolAmbientEvenPart (jQuarterAmplitude c • _) = _
  unfold burnolAmbientEvenPart
  rw [map_smul]
  change _=jQuarterAmplitude c • ((1/2:ℂ) • (_+reflectL2 _))
  module

theorem j_projection_loss_source (c : BurnolCompletedMellinCoordinate) :
    J c-(burnolEvenAmbientProjection (J c) : BurnolL2)=
      jQuarterAmplitude c • hPowerPhysicalCorrection c := by
  have projected := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (J c)
  change (burnolEvenAmbientProjection (J c) : BurnolL2)=_ at projected
  rw [projected]
  unfold burnolAmbientExtendedSonineProjectionFormula
  rw [j_evenPart,j_complete_correction_source]
  module

/-- Both cotest and adjoint combination are constructed from actual generated source fields. -/
def sourceKernelCombo (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  jQuarterAmplitude c • generatedK c-hQuarterAmplitude c • fourierL2 (generatedK c)
def sourceL (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  jQuarterAmplitude c • sourceAdjointField c-hQuarterAmplitude c • J c

theorem sourceKernelCombo_actual (c : BurnolCompletedMellinCoordinate) :
    sourceKernelCombo c=jQuarterAmplitude c • (K c : BurnolL2)-
      hQuarterAmplitude c • fourierL2 (K c : BurnolL2) := by
  rw [sourceKernelCombo,generatedK_eq_original]

/-- The two complete outside vectors cancel, not merely their quarter restrictions. -/
theorem sourceL_physical (c : BurnolCompletedMellinCoordinate) :
    (burnolEvenAmbientProjection (sourceL c) : BurnolL2)=sourceL c := by
  change burnolEvenAmbientProjectionEndomorphism (sourceL c)=sourceL c
  unfold sourceL
  rw [map_sub,map_smul,map_smul]
  change jQuarterAmplitude c • (burnolEvenAmbientProjection (sourceAdjointField c) : BurnolL2)-
    hQuarterAmplitude c • (burnolEvenAmbientProjection (J c) : BurnolL2)=_
  have h := h_projection_loss_source c
  have j := j_projection_loss_source c
  linear_combination (norm := module) -(jQuarterAmplitude c) • h+(hQuarterAmplitude c) • j

theorem sourceL_mem (c : BurnolCompletedMellinCoordinate) :
    sourceL c∈evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  rw [←sourceL_physical]
  exact (burnolEvenAmbientProjection (sourceL c)).property

theorem original_R_sourceL_read (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (sourceKernelCombo c) (burnolDirectRightResolvent (c.value/2) value)=
      inner ℂ (sourceL c) value := by
  rw [sourceKernelCombo_actual,sourceL,inner_sub_left,inner_sub_left,inner_smul_left,inner_smul_left,
    inner_smul_left,inner_smul_left,original_R_full_input,(original_R_adjoint_reads c value).2]

theorem original_R_sourceL_physical_read (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (sourceKernelCombo c) (burnolDirectRightResolvent (c.value/2) value)=
      inner ℂ (sourceL c) (burnolEvenAmbientProjection value : BurnolL2) := by
  rw [original_R_sourceL_read]
  exact ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨sourceL c,sourceL_mem c⟩ value).symm

end OriginalKCrossParameterRAdjointSource.SharedOutsideSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
