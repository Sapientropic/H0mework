import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.SharedOutsideSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PaFeedbackSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open scoped InnerProductSpace
local notation "K" => burnolCompletedMellinRieszVector
local notation "Paphys" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
namespace PA
export OriginalKCombCofinalPaAction (E Q wholePa_normal_read)
end PA
local instance paFeedbackPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The two actual whole-unit prices, with their true complex first-slot convention. -/
def fourierWholeUnitSourcePrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (fourierL2 (generatedK c)) (burnolUnitTailResponse c 4)
def sourcePaCoefficient (c : BurnolCompletedMellinCoordinate) : ℂ :=
  jQuarterAmplitude c*star (wholeUnitSourcePrice c)-hQuarterAmplitude c*star (fourierWholeUnitSourcePrice c)
def sourcePaField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  sourcePaCoefficient c • paCoefficientSource c
def sourceQ (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  sourceL c-(sourcePaField c : BurnolL2)

theorem sourcePaCoefficient_price (c : BurnolCompletedMellinCoordinate) :
    star (sourcePaCoefficient c)=inner ℂ (sourceKernelCombo c) (burnolUnitTailResponse c 4) := by
  simp only [sourcePaCoefficient,star_sub,star_mul,star_star,sourceKernelCombo,
    inner_sub_left,inner_smul_left,starRingEnd_apply,wholeUnitSourcePrice,fourierWholeUnitSourcePrice]
  ring

private theorem sourceKernel_mem (c : BurnolCompletedMellinCoordinate) :
    sourceKernelCombo c∈evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  rw [sourceKernelCombo_actual]
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.sub_mem
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.smul_mem _ (K c).property)
    ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.smul_mem _ (Paphys (K c)).property)

private theorem sourceKernel_orthogonal (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    (⟨sourceKernelCombo c,sourceKernel_mem c⟩ : BurnolPaAmbientCarrier)∈
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := by
  have original := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  have Fourier : Paphys (K c)∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := by
    intro g inside
    have FgPa := burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside
    have killed := original (Paphys g) FgPa
    have paired := (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).inner_map_map (Paphys g) (K c)
    have invol : Paphys (Paphys g)=g := evenFaceFourier_involutive burnolUnscaledCommonGapRadius g
    rw [invol] at paired
    exact paired.trans killed
  have both := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.sub_mem
    (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.smul_mem (jQuarterAmplitude c) original)
    (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.smul_mem (hQuarterAmplitude c) Fourier)
  convert both using 1
  apply Subtype.ext
  exact sourceKernelCombo_actual c

private theorem sourcePaField_mem (c : BurnolCompletedMellinCoordinate) :
    sourcePaField c∈burnolCompactCoPoissonClosedRange := by
  apply burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
  exact burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
    (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector
      (OriginalPrimitiveRankBalance.conjugateCoordinate c)).property

/-- The original full-Pa Division correction is consumed before the actual unit covector is read. -/
theorem sourceL_Pa_tests (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (g : BurnolPaAmbientCarrier) (inside : g∈burnolCompactCoPoissonClosedRange) :
    inner ℂ (sourceL c) (g : BurnolL2)=inner ℂ (sourcePaField c) g := by
  let corrected := burnolPaSourceCorrection c ⟨g,inside⟩
  have correctedPa := burnolPaSourceCorrection_mem c ⟨g,inside⟩
  have killed : inner ℂ (sourceKernelCombo c) (corrected : BurnolL2)=0 :=
    inner_eq_zero_symm.mp (sourceKernel_orthogonal c zero corrected correctedPa)
  have split : burnolDirectRightResolvent (c.value/2) (g : BurnolL2)=
      (corrected : BurnolL2)+burnolPaResolventSourceCoefficient c g • burnolUnitTailResponse c 4 := by
    change burnolDirectRightResolvent (c.value/2) (g : BurnolL2)=
      (burnolDirectRightResolvent (c.value/2) (g : BurnolL2)-
        burnolPaResolventSourceCoefficient c g • burnolUnitTailResponse c 4)+_
    abel
  have action := original_R_sourceL_read c (g : BurnolL2)
  rw [split,inner_add_right,inner_smul_right,killed,zero_add] at action
  rw [sourcePaField,inner_smul_left]
  change _=star (sourcePaCoefficient c)*inner ℂ (paCoefficientSource c) g
  rw [paCoefficientSource_read c g inside,sourcePaCoefficient_price]
  exact action.symm.trans (mul_comm _ _)

theorem sourceL_E_actual (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    PA.E (sourceL c)=sourcePaField c := by
  have normal (g : BurnolPaAmbientCarrier) (inside : g∈burnolCompactCoPoissonClosedRange) :
      inner ℂ g (PA.E (sourceL c))=inner ℂ g (sourcePaField c) := by
    rw [PA.wholePa_normal_read _ g inside]
    calc
      inner ℂ (g : BurnolL2) (sourceL c)=star (inner ℂ (sourceL c) (g : BurnolL2)) :=
        (inner_conj_symm (𝕜:=ℂ) (g : BurnolL2) (sourceL c)).symm
      _ = star (inner ℂ (sourcePaField c) g) := congrArg star (sourceL_Pa_tests c zero g inside)
      _ = inner ℂ g (sourcePaField c) := inner_conj_symm (𝕜:=ℂ) g (sourcePaField c)
  have belongs : PA.E (sourceL c)-sourcePaField c∈burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem (Submodule.starProjection_apply_mem _ _)
      (sourcePaField_mem c)
  have killed : inner ℂ (PA.E (sourceL c)-sourcePaField c) (PA.E (sourceL c)-sourcePaField c)=0 := by
    rw [inner_sub_right,normal _ belongs,sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp killed)

theorem sourceL_Q_actual (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    (PA.Q (sourceL c) : BurnolL2)=sourceQ c := by
  have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (sourceL c))
  have inventory := congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) split
  change (PA.E (sourceL c) : BurnolL2)+(PA.Q (sourceL c) : BurnolL2)=
    (burnolEvenAmbientProjection (sourceL c) : BurnolL2) at inventory
  rw [sourceL_E_actual c zero,sourceL_physical] at inventory
  unfold sourceQ
  linear_combination (norm := module) inventory

private theorem sourceKernel_Q_normal (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (value : BurnolL2) :
    inner ℂ (sourceKernelCombo c) (PA.Q value : BurnolL2)=inner ℂ (sourceKernelCombo c) value := by
  have pa := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨⟨sourceKernelCombo c,sourceKernel_mem c⟩,sourceKernel_orthogonal c zero⟩ (burnolEvenAmbientProjection value)
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨sourceKernelCombo c,sourceKernel_mem c⟩ value
  exact pa.trans physical

/-- Full physical loss is already zero; the remaining Pa and Q source prices are both retained. -/
theorem original_R_sourceL_Q_feedback (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (value : BurnolL2) :
    inner ℂ (sourceKernelCombo c) (PA.Q (burnolDirectRightResolvent (c.value/2) value) : BurnolL2)=
      star (sourcePaCoefficient c)*burnolPaResolventSourceCoefficient c (PA.E value)+
        inner ℂ (sourceQ c) (PA.Q value : BurnolL2) := by
  rw [sourceKernel_Q_normal c zero,original_R_sourceL_physical_read]
  have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection value)
  have inventory := congrArg (fun field : BurnolPaAmbientCarrier => (field : BurnolL2)) split
  change (PA.E value : BurnolL2)+(PA.Q value : BurnolL2)=
    (burnolEvenAmbientProjection value : BurnolL2) at inventory
  rw [←inventory,inner_add_right,sourceL_Pa_tests c zero (PA.E value) (Submodule.starProjection_apply_mem _ _)]
  have paPrice : inner ℂ (sourcePaField c) (PA.E value)=
      star (sourcePaCoefficient c)*burnolPaResolventSourceCoefficient c (PA.E value) := by
    rw [sourcePaField,inner_smul_left]
    change star (sourcePaCoefficient c)*inner ℂ (paCoefficientSource c) (PA.E value)=_
    rw [paCoefficientSource_read c (PA.E value) (Submodule.starProjection_apply_mem _ _)]
  rw [paPrice]
  congr 1
  have qMember : PA.Q value∈burnolCompactCoPoissonClosedRange.toSubmoduleᗮ := Submodule.starProjection_apply_mem _ _
  have killed : inner ℂ (sourcePaField c) (PA.Q value)=0 := qMember _ (sourcePaField_mem c)
  rw [sourceQ,inner_sub_left]
  change _=inner ℂ (sourceL c) (PA.Q value : BurnolL2)-inner ℂ (sourcePaField c) (PA.Q value)
  rw [killed,sub_zero]

/-- Removing the Pa source deletes this exact unit vector, even though the outside channel has vanished. -/
theorem deleted_Pa_source_defect (c : BurnolCompletedMellinCoordinate) :
    sourceL c-sourceQ c=(sourcePaField c : BurnolL2) := by
  unfold sourceQ
  abel

theorem zero_sourcePaCoefficient_override (c : BurnolCompletedMellinCoordinate)
    (coefficientZero : sourcePaCoefficient c=0) : sourcePaField c=0 ∧ sourceQ c=sourceL c := by
  have actual : sourcePaField c=0 := by rw [sourcePaField,coefficientZero,zero_smul]
  exact ⟨actual,by rw [sourceQ,actual];simp only [ZeroMemClass.coe_zero,sub_zero]⟩

end OriginalKCrossParameterRAdjointSource.PaFeedbackSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
