import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullOriginalRUnitSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource
open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalKSourceResolventReconstruction
open scoped InnerProductSpace
local notation "K" => burnolCompletedMellinRieszVector
local notation "Rop" => burnolDirectRightResolventCLM
local notation "seed" => OriginalKSectorEulerMixedSource.NativeK.seed
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
namespace Base
export OriginalKElementaryArithmeticAction.FullOriginalRUnitSource (sourcePlusCorrected sourceMinusCorrected)
end Base

def sourcePlusUnit (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (Kernel.A c-Kernel.beta c) • (seed+fourierL2 seed)
def sourceMinusUnit (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (Kernel.A c+Kernel.beta c) • (seed-fourierL2 seed)
def sourcePlusForcing (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  OriginalKSectorEulerMixedSource.actualPlusForcing c+(c.value-d.value) • sourcePlusUnit c
def sourceMinusForcing (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  OriginalKSectorEulerMixedSource.actualMinusForcing c+(c.value-d.value) • sourceMinusUnit c
def sourcePlusDrive (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Rop d (sourcePlusForcing c d)+(2 : ℂ) • Base.sourcePlusCorrected c
def sourceMinusDrive (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Rop d (sourceMinusForcing c d)+(2 : ℂ) • Base.sourceMinusCorrected c
def sourceFKResponse (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (2*(star c.value+d.value-1))⁻¹ • (sourceMinusDrive c d-sourcePlusDrive c d)

private theorem corrected_actual (c : BurnolCompletedMellinCoordinate) :
    Base.sourcePlusCorrected c=OriginalKSectorEulerMixedSource.actualPlusCorrected c ∧
    Base.sourceMinusCorrected c=OriginalKSectorEulerMixedSource.actualMinusCorrected c := by
  have actual := OriginalKSectorEulerMixedSource.actual_source_two_corrected_fields c
  change OriginalKSectorEulerMixedSource.actualPlusCorrected c=
      (K c : BurnolL2)+fourierL2 (K c : BurnolL2)-sourcePlusUnit c ∧
    OriginalKSectorEulerMixedSource.actualMinusCorrected c=
      (K c : BurnolL2)-fourierL2 (K c : BurnolL2)-sourceMinusUnit c at actual
  simp only [Base.sourcePlusCorrected, Base.sourceMinusCorrected, generatedK_eq_original]
  exact ⟨actual.1.symm, actual.2.symm⟩

/-- Only the inverse parameter changes; both velocities still come from the original c source. -/
theorem cross_parameter_forcing (c d : BurnolCompletedMellinCoordinate) :
    OriginalKSectorEulerMixedSource.actualPlusVelocity c+(d.value-1/2) •
        OriginalKSectorEulerMixedSource.actualPlusCorrected c=
      -(star c.value-1/2) • ((K c : BurnolL2)-fourierL2 (K c : BurnolL2))+
        (d.value-1/2) • ((K c : BurnolL2)+fourierL2 (K c : BurnolL2))+sourcePlusForcing c d ∧
    OriginalKSectorEulerMixedSource.actualMinusVelocity c+(d.value-1/2) •
        OriginalKSectorEulerMixedSource.actualMinusCorrected c=
      -(star c.value-1/2) • ((K c : BurnolL2)+fourierL2 (K c : BurnolL2))+
        (d.value-1/2) • ((K c : BurnolL2)-fourierL2 (K c : BurnolL2))+sourceMinusForcing c d := by
  have old := OriginalKSectorEulerMixedSource.actual_source_coupled_forcing c
  have correction := OriginalKSectorEulerMixedSource.actual_source_two_corrected_fields c
  change OriginalKSectorEulerMixedSource.actualPlusCorrected c=
      (K c : BurnolL2)+fourierL2 (K c : BurnolL2)-sourcePlusUnit c ∧
    OriginalKSectorEulerMixedSource.actualMinusCorrected c=
      (K c : BurnolL2)-fourierL2 (K c : BurnolL2)-sourceMinusUnit c at correction
  change OriginalKSectorEulerMixedSource.actualPlusVelocity c+(c.value-1/2) •
      OriginalKSectorEulerMixedSource.actualPlusCorrected c=
    -(star c.value-1/2) • ((K c : BurnolL2)-fourierL2 (K c : BurnolL2))+
      (c.value-1/2) • ((K c : BurnolL2)+fourierL2 (K c : BurnolL2))+
        OriginalKSectorEulerMixedSource.actualPlusForcing c ∧
    OriginalKSectorEulerMixedSource.actualMinusVelocity c+(c.value-1/2) •
      OriginalKSectorEulerMixedSource.actualMinusCorrected c=
    -(star c.value-1/2) • ((K c : BurnolL2)+fourierL2 (K c : BurnolL2))+
      (c.value-1/2) • ((K c : BurnolL2)-fourierL2 (K c : BurnolL2))+
        OriginalKSectorEulerMixedSource.actualMinusForcing c at old
  unfold sourcePlusForcing sourceMinusForcing
  constructor
  · linear_combination (norm := module) old.1+(d.value-c.value) • correction.1
  · linear_combination (norm := module) old.2+(d.value-c.value) • correction.2

/-- Full source inverse action is retained at resonance, without dividing either weighted equation. -/
theorem cross_parameter_weighted_fields (c d : BurnolCompletedMellinCoordinate) :
    (2*(star c.value-d.value)) • burnolDirectRightResolvent (d.value/2) (K c : BurnolL2)=
      sourcePlusDrive c d+sourceMinusDrive c d ∧
    (2*(star c.value+d.value-1)) • burnolDirectRightResolvent (d.value/2)
        (fourierL2 (K c : BurnolL2))=sourceMinusDrive c d-sourcePlusDrive c d := by
  have strong := OriginalKSectorEulerMixedSource.actual_source_two_strong_fields c
  have forcing := cross_parameter_forcing c d
  have plus := paid189ActualRInverse d _ _ strong.1
  have minus := paid189ActualRInverse d _ _ strong.2
  rw [forcing.1, burnolDirectRightResolvent_smul] at plus
  rw [forcing.2, burnolDirectRightResolvent_smul] at minus
  change OriginalKSectorEulerMixedSource.actualPlusCorrected c=(-1/2 : ℂ) • Rop d _ at plus
  change OriginalKSectorEulerMixedSource.actualMinusCorrected c=(-1/2 : ℂ) • Rop d _ at minus
  rw [map_add, map_add, map_smul, map_smul, map_sub, map_add] at plus
  rw [map_add, map_add, map_smul, map_smul, map_add, map_sub] at minus
  unfold sourcePlusDrive sourceMinusDrive
  rw [(corrected_actual c).1, (corrected_actual c).2]
  change (2*(star c.value-d.value)) • Rop d (K c : BurnolL2)=_ ∧
    (2*(star c.value+d.value-1)) • Rop d (fourierL2 (K c : BurnolL2))=_
  constructor
  · linear_combination (norm := module) (-2 : ℂ) • plus+(-2 : ℂ) • minus
  · linear_combination (norm := module) (2 : ℂ) • plus+(-2 : ℂ) • minus

theorem source_FK_response (c d : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (d.value/2) (fourierL2 (K c : BurnolL2))=sourceFKResponse c d := by
  have unit : 2*(star c.value+d.value-1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    simpa only [add_comm] using source_cross_parameter_ne_zero d c
  rw [sourceFKResponse, ←(cross_parameter_weighted_fields c d).2,
    smul_smul, inv_mul_cancel₀ unit, one_smul]

def sourceSeedCombo (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Kernel.A c • seed-Kernel.beta c • fourierL2 seed
def sourceResonantKernel (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  sourceSeedCombo c-(1/4 : ℂ) • Rop (barC c)
    (sourcePlusForcing c (barC c)+sourceMinusForcing c (barC c))

/-- The zero weighted coefficient yields a whole source identity, rather than an inverse of zero. -/
theorem resonant_kernel_source (c : BurnolCompletedMellinCoordinate) :
    sourceResonantKernel c=(K c : BurnolL2) := by
  have resonance := (cross_parameter_weighted_fields c (barC c)).1
  change (2*(star c.value-star c.value)) • Rop (barC c) (K c : BurnolL2)=
    sourcePlusDrive c (barC c)+sourceMinusDrive c (barC c) at resonance
  simp only [sub_self, mul_zero, zero_smul] at resonance
  have sum : sourcePlusDrive c (barC c)+sourceMinusDrive c (barC c)=
      Rop (barC c) (sourcePlusForcing c (barC c)+sourceMinusForcing c (barC c))+
        (4 : ℂ) • (generatedK c-sourceSeedCombo c) := by
    unfold sourcePlusDrive sourceMinusDrive Base.sourcePlusCorrected Base.sourceMinusCorrected sourceSeedCombo
    rw [map_add]
    module
  rw [sum] at resonance
  have generated : sourceResonantKernel c=generatedK c := by
    unfold sourceResonantKernel
    linear_combination (norm := module) (1/4 : ℂ) • resonance
  exact generated.trans (generatedK_eq_original c)

/-- This source uses one more original inverse action on the generated resonance identity. -/
def sourceConjugateKResponse (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Rop (barC c) (sourceSeedCombo c)-(1/4 : ℂ) • Rop (barC c)
    (Rop (barC c) (sourcePlusForcing c (barC c)+sourceMinusForcing c (barC c)))

theorem source_conjugate_R_fields (c : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (star c.value/2) (K c : BurnolL2)=sourceConjugateKResponse c ∧
    burnolDirectRightResolvent (star c.value/2) (fourierL2 (K c : BurnolL2))=
      sourceFKResponse c (barC c) := by
  constructor
  · rw [←resonant_kernel_source c]
    change Rop (barC c) (sourceResonantKernel c)=_
    unfold sourceResonantKernel sourceConjugateKResponse
    rw [map_sub, map_smul]
  · exact source_FK_response c (barC c)

def sourceAdjointK (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (sourceFKResponse c (barC c))
def sourceAdjointFK (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (sourceConjugateKResponse c)

/-- Both true Rc adjoint fields are generated from the fixed c source and its conjugate inverse parameter. -/
theorem original_R_adjoint_fields (c : BurnolCompletedMellinCoordinate) :
    FiniteMobiusResolventFlux.Rplus (star (c.value/2)) (K c : BurnolL2)=sourceAdjointK c ∧
    FiniteMobiusResolventFlux.Rplus (star (c.value/2)) (fourierL2 (K c : BurnolL2))=sourceAdjointFK c := by
  have right : 1/4 < (star c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have evenK : reflectL2 (K c : BurnolL2)=(K c : BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp (K c).property.2
  have Kfield := FiniteMobiusResolventFlux.fourier_R (star c.value/2) right (fourierL2 (K c : BurnolL2))
  rw [(source_conjugate_R_fields c).2, fourierL2_fourierL2, evenK] at Kfield
  have FKfield := FiniteMobiusResolventFlux.fourier_R (star c.value/2) right (K c : BurnolL2)
  rw [(source_conjugate_R_fields c).1] at FKfield
  constructor
  · simpa only [sourceAdjointK, star_div₀, star_ofNat] using Kfield.symm
  · simpa only [sourceAdjointFK, star_div₀, star_ofNat] using FKfield.symm

theorem original_R_adjoint_reads (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (K c : BurnolL2) (burnolDirectRightResolvent (c.value/2) value)=
        inner ℂ (sourceAdjointK c) value ∧
    inner ℂ (fourierL2 (K c : BurnolL2)) (burnolDirectRightResolvent (c.value/2) value)=
        inner ℂ (sourceAdjointFK c) value := by
  have first := sourceResolvent_actual_adjoint_read c (fourierL2 (K c : BurnolL2)) value
  have second := sourceResolvent_actual_adjoint_read c (K c : BurnolL2) value
  change inner ℂ (fourierL2 (burnolDirectRightResolvent (star c.value/2) (fourierL2 (K c : BurnolL2)))) value=
    inner ℂ (fourierL2 (fourierL2 (K c : BurnolL2))) (burnolDirectRightResolvent (c.value/2) value) at first
  change inner ℂ (fourierL2 (burnolDirectRightResolvent (star c.value/2) (K c : BurnolL2))) value=
    inner ℂ (fourierL2 (K c : BurnolL2)) (burnolDirectRightResolvent (c.value/2) value) at second
  have evenK : reflectL2 (K c : BurnolL2)=(K c : BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp (K c).property.2
  rw [(source_conjugate_R_fields c).2, fourierL2_fourierL2, evenK] at first
  rw [(source_conjugate_R_fields c).1] at second
  exact ⟨first.symm, second.symm⟩

theorem diagonal_source_override (c : BurnolCompletedMellinCoordinate) :
    sourcePlusForcing c c=OriginalKSectorEulerMixedSource.actualPlusForcing c ∧
    sourceMinusForcing c c=OriginalKSectorEulerMixedSource.actualMinusForcing c ∧
    sourcePlusDrive c c=OriginalKElementaryArithmeticAction.FullOriginalRUnitSource.sourcePlusDrive c ∧
    sourceMinusDrive c c=OriginalKElementaryArithmeticAction.FullOriginalRUnitSource.sourceMinusDrive c := by
  unfold sourcePlusDrive sourceMinusDrive sourcePlusForcing sourceMinusForcing
  simp only [sub_self, zero_smul, add_zero]
  exact ⟨trivial, trivial, rfl, rfl⟩

/-- Omitting the parameter correction changes both whole vector equations by these actual source actions. -/
theorem deleted_correction_residual (c d : BurnolCompletedMellinCoordinate) :
    (2*(star c.value-d.value)) • Rop d (K c : BurnolL2)-
        ((Rop d (OriginalKSectorEulerMixedSource.actualPlusForcing c)+(2 : ℂ) • Base.sourcePlusCorrected c)+
          (Rop d (OriginalKSectorEulerMixedSource.actualMinusForcing c)+(2 : ℂ) • Base.sourceMinusCorrected c))=
      (c.value-d.value) • Rop d (sourcePlusUnit c+sourceMinusUnit c) ∧
    (2*(star c.value+d.value-1)) • Rop d (fourierL2 (K c : BurnolL2))-
        ((Rop d (OriginalKSectorEulerMixedSource.actualMinusForcing c)+(2 : ℂ) • Base.sourceMinusCorrected c)-
          (Rop d (OriginalKSectorEulerMixedSource.actualPlusForcing c)+(2 : ℂ) • Base.sourcePlusCorrected c))=
      (c.value-d.value) • Rop d (sourceMinusUnit c-sourcePlusUnit c) := by
  have paid := cross_parameter_weighted_fields c d
  change (2*(star c.value-d.value)) • Rop d (K c : BurnolL2)=_ ∧
    (2*(star c.value+d.value-1)) • Rop d (fourierL2 (K c : BurnolL2))=_ at paid
  rw [paid.1, paid.2]
  unfold sourcePlusDrive sourceMinusDrive sourcePlusForcing sourceMinusForcing
  simp only [map_add, map_sub, map_smul]
  constructor <;> module

theorem real_coordinate_weighted_override (c : BurnolCompletedMellinCoordinate)
    (realCoordinate : star c.value=c.value) : sourcePlusDrive c c+sourceMinusDrive c c=0 := by
  have paid := (cross_parameter_weighted_fields c c).1
  simpa only [realCoordinate, sub_self, mul_zero, zero_smul] using paid.symm

end OriginalKCrossParameterRAdjointSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
