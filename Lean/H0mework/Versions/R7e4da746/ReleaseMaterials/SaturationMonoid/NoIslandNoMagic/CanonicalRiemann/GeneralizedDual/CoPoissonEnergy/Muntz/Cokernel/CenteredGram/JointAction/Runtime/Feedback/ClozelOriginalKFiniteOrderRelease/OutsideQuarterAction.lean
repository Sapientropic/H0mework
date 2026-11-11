import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterCurrentSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.KernelGram
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.OutsideQuarterAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open UnitPowerJordanSource UnitPowerJordanAction QuarterSourceCommutator
open GenericSourceStepBAction QuarterCurrentSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "D" => burnolTruncatedFourier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "P" => Constructor.zeroMean
local notation "mu" => burnolQuarterMeanCoefficient
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local notation "Pi" => burnolEvenAmbientProjection
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

open private evenPart_of_even position_read fourier_read position_gap_zero block_unique
  first_B_even position_fourier fourier_fourier
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private fourier_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
open private extension_even inward_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private sourceTail_extension_zero
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource

/-- Both legs of the actual position-gap outside column, on its quarter carrier. -/
def outsideEmbedding : M →L[ℂ] BurnolL2 :=
  fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))-
  burnolQuarterZeroExtension.comp ((Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp S)

theorem outsideEmbedding_read (state : M) :
    outsideEmbedding state=fourierL2 (Eq (state:Hq))-Eq (S state:Hq) := rfl

/-- The two crossing terms are actual quarter projection pairings. -/
theorem outsideEmbedding_inner (left right : M) :
    inner ℂ (outsideEmbedding left) (outsideEmbedding right)=
      inner ℂ left right-inner ℂ (S left) (S right) := by
  have crossed : inner ℂ (fourierL2 (Eq (left:Hq))) (Eq (S right:Hq))=
      inner ℂ (S left) (S right) := by
    rw [←inner_conj_symm,OriginalRieszSourceGreen.extension_fourier_pairing,inner_conj_symm]
  rw [outsideEmbedding_read,outsideEmbedding_read,inner_sub_left,inner_sub_right,inner_sub_right,
    fourierL2.inner_map_map,OriginalRieszSourceGreen.quarter_extension_inner,crossed,
    OriginalRieszSourceGreen.extension_fourier_pairing,OriginalRieszSourceGreen.quarter_extension_inner]
  change (inner ℂ left right-inner ℂ (S left) (S right))-
    (inner ℂ (S left) (S right)-inner ℂ (S left) (S right))=_
  ring

theorem outsideGram (state : M) : ‖outsideEmbedding state‖^2=‖state‖^2-‖S state‖^2 := by
  have actual := outsideEmbedding_inner state state
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at actual
  exact_mod_cast actual

private theorem second_even (value : BurnolL2) : sourceMeanZeroReflection (d value)=d value := by
  apply Subtype.ext
  change reflectRestricted q ((Y value:Hq)-(S (b value):Hq))=(Y value:Hq)-(S (b value):Hq)
  have first := congrArg (fun state:M=>(state:Hq)) (fourier_even _ (first_B_even value))
  change reflectRestricted q (S (b value):Hq)=(S (b value):Hq) at first
  rw [map_sub,burnolAmbientMeanZeroFourier_reflection_fixed,first]

private theorem embedding_even (state : M) (even : sourceMeanZeroReflection state=state) :
    reflectL2 (outsideEmbedding state)=outsideEmbedding state := by
  rw [outsideEmbedding_read,map_sub,←fourierL2_reflectL2_commute,
    extension_even _ (congrArg (fun state:M=>(state:Hq)) even),
    extension_even _ (congrArg (fun state:M=>(state:Hq)) (fourier_even state even))]

private theorem gap_first (value : BurnolL2) (even : reflectL2 value=value)
    (gap : value∈locallyConstantFace q) : b value=-S (d value) := by
  have actual := burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs value)
  change b value+S (d value)=X value at actual
  rw [position_gap_zero value even gap] at actual
  exact eq_neg_of_add_eq_zero_left actual

private theorem outside_of_second (value : BurnolL2) (even : reflectL2 value=value)
    (first : b value=-S (d value)) : outside value=outsideEmbedding (d value) := by
  have projected := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula value
  change (Pi value:BurnolL2)=burnolAmbientEvenPart value-
    burnolAmbientEvenMeanZeroCorrection value at projected
  rw [evenPart_of_even value even] at projected
  have correction : burnolAmbientEvenMeanZeroCorrection value=outsideEmbedding (d value) := by
    unfold burnolAmbientEvenMeanZeroCorrection burnolAmbientRawMeanZeroCorrection
    rw [first]
    change burnolAmbientEvenPart (Eq (-(S (d value)):Hq)+fourierL2 (Eq (d value:Hq)))=_
    rw [map_neg]
    have body : -Eq (S (d value):Hq)+fourierL2 (Eq (d value:Hq))=outsideEmbedding (d value) := by
      rw [outsideEmbedding_read]
      module
    rw [body,evenPart_of_even _ (embedding_even _ (second_even value))]
  have whole := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal value
  change (Pi value:BurnolL2)+outside value=value at whole
  rw [projected,correction] at whole
  linear_combination (norm:=module) whole

theorem outside_of_gap (value : BurnolL2) (even : reflectL2 value=value)
    (gap : value∈locallyConstantFace q) : outside value=outsideEmbedding (d value) :=
  outside_of_second value even (gap_first value even gap)

private theorem embedding_position (state : M) (even : sourceMeanZeroReflection state=state) :
    X (outsideEmbedding state)=0 := by
  rw [position_read _ (embedding_even state even),outsideEmbedding_read,map_sub,map_sub,
    burnolQuarterRestriction_zeroExtension]
  change S state-P (S state:Hq)=0
  have fixed : P (S state:Hq)=S state := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [fixed,sub_self]

private theorem embedding_fourier (state : M) (even : sourceMeanZeroReflection state=state) :
    Y (outsideEmbedding state)=state-S (S state) := by
  rw [fourier_read _ (embedding_even state even),outsideEmbedding_read,map_sub,fourierL2_fourierL2,
    extension_even _ (congrArg (fun state:M=>(state:Hq)) even),map_sub,map_sub,
    burnolQuarterRestriction_zeroExtension]
  change P (state:Hq)-S (S state)=_
  have fixed : P (state:Hq)=state := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [fixed]

theorem embedding_B (state : M) (even : sourceMeanZeroReflection state=state) :
    b (outsideEmbedding state)=-S state ∧ d (outsideEmbedding state)=state := by
  have source := block_unique (X (outsideEmbedding state)) (Y (outsideEmbedding state)) (-S state) state
    (by rw [embedding_position state even];module)
    (by rw [embedding_fourier state even,map_neg];module)
  exact ⟨source.1.symm,source.2.symm⟩

/-- The complete outside return reads its actual exterior tail and the unremoved Fourier mean. -/
def outsideAmplitude (c : BurnolCompletedMellinCoordinate) : M →L[ℂ] ℂ :=
  (2:ℂ) • (((sourceTail (barC c)).comp
    (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (burnolQuarterZeroExtension.comp ((Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp S))))+
    ((q:ℂ)^(1-c.value)/(1-c.value)) •
      ((quarterMean.comp D).comp ((Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp S)))

def quarterReturn (c : BurnolCompletedMellinCoordinate) : M →L[ℂ] M :=
  centeredQuarterStep (barC c)+(outsideAmplitude c).smulRight (logBFirst (barC c) 0)-
    burnolMeanZeroBlockInverse.comp ((currentContactMap (barC c)).comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

private theorem embedding_amplitude (c : BurnolCompletedMellinCoordinate) (state : M)
    (even : sourceMeanZeroReflection state=state) :
    currentAmplitude (barC c) (fourierL2 (outsideEmbedding state))=outsideAmplitude c state := by
  unfold currentAmplitude
  rw [outsideEmbedding_read,map_sub,fourierL2_fourierL2,
    extension_even _ (congrArg (fun state:M=>(state:Hq)) even),map_sub,
    sourceTail_extension_zero,zero_sub,map_sub,burnolQuarterRestriction_zeroExtension]
  change -2*(-sourceTail (barC c) (fourierL2 (Eq (S state:Hq)))+
    mu ((state:Hq)-D (S state:Hq))*(q:ℂ)^(1-star (barC c).value)/(1-star (barC c).value))=_
  rw [←quarterMean_read ((state:Hq)-D (S state:Hq)),map_sub,
    quarterMean_read,quarterMean_read,Constructor.mean_zero]
  simp only [star_star,OriginalPrimitiveRankBalance.conjugateCoordinate]
  simp [outsideAmplitude,quarterMean_read,OriginalPrimitiveRankBalance.conjugateCoordinate]; ring

private theorem embedding_gap (state : M) (even : sourceMeanZeroReflection state=state) :
    outsideEmbedding state∈locallyConstantFace q := by
  change Rq (outsideEmbedding state)∈intervalConstantLine q
  apply (burnolQuarterMeanZeroProjection_eq_zero_iff _).mp
  have actual := embedding_position state even
  rw [position_read _ (embedding_even state even)] at actual
  exact congrArg (fun value:M=>(value:Hq)) actual

theorem quarterReturn_native (c : BurnolCompletedMellinCoordinate) (state : M)
    (even : sourceMeanZeroReflection state=state) :
    gapSecondNext c (outsideEmbedding state)=quarterReturn c state := by
  unfold gapSecondNext
  rw [(embedding_B state even).2,embedding_amplitude c state even]
  change _=centeredQuarterStep (barC c) state+outsideAmplitude c state • logBFirst (barC c) 0-
    BI (currentContactMap (barC c) (state:Hq))
  rw [currentContactMap_read]

theorem outside_R_outside (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) (gap : value∈locallyConstantFace q) :
    outside (burnolDirectRightResolventCLM c (outside value))=
      outsideEmbedding (quarterReturn c (d value)) := by
  rw [outside_of_gap value even gap]
  have stateEven := second_even value
  have actual := actual_forward_R_gap_B c (outsideEmbedding (d value))
    (embedding_even _ stateEven) (embedding_gap _ stateEven)
  have outputEven : reflectL2 (burnolDirectRightResolventCLM c (outsideEmbedding (d value)))=
      burnolDirectRightResolventCLM c (outsideEmbedding (d value)) :=
    inward_even c _ (embedding_even _ stateEven)
  rw [outside_of_second _ outputEven (by rw [actual.1,actual.2]),actual.2,
    quarterReturn_native c _ stateEven]

/-- The original exterior embedding is faithful on the whole mean-zero carrier. -/
theorem outsideEmbedding_injective : Function.Injective outsideEmbedding := by
  intro left right same
  have balance := outsideGram (left-right)
  rw [map_sub,same,sub_self,norm_zero,zero_pow (by decide : (2:Nat)≠0)] at balance
  have bound := burnolMeanZeroTruncatedFourier_norm_le (left-right)
  have square : ‖S (left-right)‖^2≤((1/2:ℝ)*‖left-right‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mpr bound
  have zero : ‖left-right‖=0 := by nlinarith [norm_nonneg (left-right)]
  exact sub_eq_zero.mp (norm_eq_zero.mp zero)

/-- The actual outside rank-one response has the same quarter column and original parameter. -/
theorem physicalOutsideColumn_embedding (c : BurnolCompletedMellinCoordinate) :
    OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c=
      outsideEmbedding (OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (barC c)) := by
  let h := OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (barC c)
  have hEven : sourceMeanZeroReflection h=h := log_B_even (barC c) 0
  have sEven := fourier_even h hEven
  have rawEven : reflectL2 (Eq (h:Hq)-fourierL2 (Eq (S h:Hq)))=
      Eq (h:Hq)-fourierL2 (Eq (S h:Hq)) := by
    rw [map_sub,extension_even _ (congrArg (fun state:M=>(state:Hq)) hEven),
      ←fourierL2_reflectL2_commute,extension_even _ (congrArg (fun state:M=>(state:Hq)) sEven)]
  have correction : OriginalKDirectRCofinalOutsideVolterraSource.hPowerPhysicalCorrection (barC c)=
      Eq (h:Hq)-fourierL2 (Eq (S h:Hq)) := by
    change burnolAmbientEvenPart (Eq (h:Hq)+fourierL2 (Eq (-(S h):Hq)))=_
    rw [map_neg,map_neg,←sub_eq_add_neg,evenPart_of_even _ rawEven]
  apply fourierL2.injective
  rw [OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn,
    fourierL2.apply_symm_apply,correction,outsideEmbedding_read,map_sub,fourierL2_fourierL2,
    extension_even _ (congrArg (fun state:M=>(state:Hq)) hEven)]

/-- The physical incoming price is an actual linear read of the complete current outside column. -/
def incomingAmplitude (c : BurnolCompletedMellinCoordinate) : M →L[ℂ] ℂ :=
  (-2:ℂ) • ((innerSL ℂ (OriginalKDirectRCofinalOutsideVolterraSource.hPowerPhysicalCorrection c)).comp outsideEmbedding)

def fullOutsideReturn (c : BurnolCompletedMellinCoordinate) : M →L[ℂ] BurnolL2 :=
  (incomingAmplitude c).smulRight (OriginalKSourceResolventReconstruction.generatedK (barC c))+
    outsideEmbedding.comp (quarterReturn c)

/-- The complete original R action, including the physical rank-one field and the full outside return. -/
theorem actual_R_outside (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) (gap : value∈locallyConstantFace q) :
    burnolDirectRightResolventCLM c (outside value)=fullOutsideReturn c (d value) := by
  have whole := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolDirectRightResolventCLM c (outside value))
  change (Pi (burnolDirectRightResolventCLM c (outside value)):BurnolL2)+
    outside (burnolDirectRightResolventCLM c (outside value))=burnolDirectRightResolventCLM c (outside value) at whole
  have physical := OriginalKCrossParameterRAdjointSource.PhysicalDefectSource.original_R_outside_physical_generatedK c value
  change (Pi (burnolDirectRightResolventCLM c (outside value)):BurnolL2)=_ at physical
  rw [physical,outside_R_outside c value even gap,outside_of_gap value even gap] at whole
  rw [outside_of_gap value even gap]
  exact whole.symm

/-- The complete current input produces the next B foot by the exterior CLM and the original physical cotest. -/
theorem nativeNext_decomposition (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) (gap : value∈locallyConstantFace q) :
    gapSecondNext c value=quarterReturn c (d value)+
      (-2*inner ℂ (fourierL2 (OriginalKSourceResolventReconstruction.generatedK c)) (Pi value:BurnolL2)) •
        OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (barC c) := by
  have actual := actual_forward_R_gap_B c value even gap
  have output : outside (burnolDirectRightResolventCLM c value)=outsideEmbedding (gapSecondNext c value) := by
    rw [outside_of_second _ (inward_even c value even) (by rw [actual.1,actual.2]),actual.2]
  have whole := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal value
  change (Pi value:BurnolL2)+outside value=value at whole
  have acted := congrArg (fun state=>outside (burnolDirectRightResolventCLM c state)) whole
  have physical := OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.original_R_physical_outside_source c (Pi value)
  change outside (burnolDirectRightResolventCLM c (Pi value:BurnolL2))=_ at physical
  rw [map_add,map_add,physical,outside_R_outside c value even gap,
    physicalOutsideColumn_embedding,output] at acted
  apply outsideEmbedding_injective
  rw [map_add,map_smul]
  linear_combination (norm:=module) -acted

end OriginalKFiniteOrderRelease.OutsideQuarterAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
