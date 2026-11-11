import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResolventReconstruction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FullOriginalRUnitSource
open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalKSourceResolventReconstruction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

local notation "K" => burnolCompletedMellinRieszVector
local notation "Rop" => burnolDirectRightResolventCLM
local notation "seed" => OriginalKSectorEulerMixedSource.NativeK.seed

def sourcePlusCorrected (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  generatedK c + fourierL2 (generatedK c) -
    (Kernel.A c - Kernel.beta c) • (seed + fourierL2 seed)

def sourceMinusCorrected (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  generatedK c - fourierL2 (generatedK c) -
    (Kernel.A c + Kernel.beta c) • (seed - fourierL2 seed)

def sourcePlusDrive (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Rop c (OriginalKSectorEulerMixedSource.actualPlusForcing c) +
    (2 : ℂ) • sourcePlusCorrected c

def sourceMinusDrive (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Rop c (OriginalKSectorEulerMixedSource.actualMinusForcing c) +
    (2 : ℂ) • sourceMinusCorrected c

def sourceWeightedK (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  sourcePlusDrive c + sourceMinusDrive c

def sourceFK (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (2 * (star c.value + c.value - 1))⁻¹ • (sourceMinusDrive c - sourcePlusDrive c)

private theorem corrected_source (c : BurnolCompletedMellinCoordinate) :
    sourcePlusCorrected c = OriginalKSectorEulerMixedSource.actualPlusCorrected c ∧
    sourceMinusCorrected c = OriginalKSectorEulerMixedSource.actualMinusCorrected c := by
  have paid := OriginalKSectorEulerMixedSource.actual_source_two_corrected_fields c
  change OriginalKSectorEulerMixedSource.actualPlusCorrected c =
      (K c : BurnolL2) + fourierL2 (K c : BurnolL2) -
        (Kernel.A c - Kernel.beta c) • (seed + fourierL2 seed) ∧
    OriginalKSectorEulerMixedSource.actualMinusCorrected c =
      (K c : BurnolL2) - fourierL2 (K c : BurnolL2) -
        (Kernel.A c + Kernel.beta c) • (seed - fourierL2 seed) at paid
  simp only [sourcePlusCorrected, sourceMinusCorrected, generatedK_eq_original]
  exact ⟨paid.1.symm, paid.2.symm⟩

/-- The full source equations are solved before any physical projection is read. -/
theorem full_original_R_fields (c : BurnolCompletedMellinCoordinate) :
    (2 * (star c.value - c.value)) •
        burnolDirectRightResolvent (c.value/2) (K c : BurnolL2) = sourceWeightedK c ∧
    burnolDirectRightResolvent (c.value/2) (fourierL2 (K c : BurnolL2)) = sourceFK c := by
  have plus := (OriginalKSectorEulerMixedSource.actual_source_coupled_R_fields c).1
  have minus := (OriginalKSectorEulerMixedSource.actual_source_coupled_R_fields c).2
  change (star c.value-1/2) • Rop c ((K c : BurnolL2)-fourierL2 (K c : BurnolL2)) =
    (c.value-1/2) • Rop c ((K c : BurnolL2)+fourierL2 (K c : BurnolL2)) +
      Rop c (OriginalKSectorEulerMixedSource.actualPlusForcing c) +
        (2 : ℂ) • OriginalKSectorEulerMixedSource.actualPlusCorrected c at plus
  change (star c.value-1/2) • Rop c ((K c : BurnolL2)+fourierL2 (K c : BurnolL2)) =
    (c.value-1/2) • Rop c ((K c : BurnolL2)-fourierL2 (K c : BurnolL2)) +
      Rop c (OriginalKSectorEulerMixedSource.actualMinusForcing c) +
        (2 : ℂ) • OriginalKSectorEulerMixedSource.actualMinusCorrected c at minus
  simp only [map_add, map_sub] at plus minus
  have weightedFK : (2 * (star c.value+c.value-1)) • Rop c (fourierL2 (K c : BurnolL2)) =
      sourceMinusDrive c-sourcePlusDrive c := by
    unfold sourceMinusDrive sourcePlusDrive
    rw [(corrected_source c).1, (corrected_source c).2]
    linear_combination (norm := module) minus-plus
  have unit : 2 * (star c.value+c.value-1) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    simpa only [add_comm] using source_cross_parameter_ne_zero c c
  constructor
  · change (2 * (star c.value-c.value)) • Rop c (K c : BurnolL2) = _
    unfold sourceWeightedK sourcePlusDrive sourceMinusDrive
    rw [(corrected_source c).1, (corrected_source c).2]
    linear_combination (norm := module) plus+minus
  · change Rop c (fourierL2 (K c : BurnolL2)) = _
    rw [sourceFK, ←weightedFK, smul_smul, inv_mul_cancel₀ unit, one_smul]

/-- A real parameter does not authorize division of the independent weighted K equation. -/
theorem real_coordinate_weighted_override (c : BurnolCompletedMellinCoordinate)
    (realCoordinate : star c.value = c.value) : sourceWeightedK c = 0 := by
  have paid := (full_original_R_fields c).1
  simpa only [realCoordinate, sub_self, mul_zero, zero_smul] using paid.symm

private theorem sourceRbar_adjoint (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (K c : BurnolL2) (sourceResolvent c value) =
      inner ℂ (fourierL2 (sourceFK c)) value := by
  have right : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have starRight : 1/4 < (star c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have evenK : reflectL2 (K c : BurnolL2) = (K c : BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp (K c).property.2
  have transformed := FiniteMobiusResolventFlux.fourier_R (c.value/2) right
    (fourierL2 (K c : BurnolL2))
  rw [(full_original_R_fields c).2, fourierL2_fourierL2, evenK] at transformed
  have adjoint := OriginalKCompactAdjointRSource.actual_original_R_adjoint
    (star c.value/2) starRight (K c : BurnolL2) value
  simpa only [sourceResolvent, star_div₀, star_ofNat, star_star, ←transformed] using adjoint

def unitAdjointSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  star (star c.value * GapEuler.gapMean (1/4) c) •
    (generatedK c - star ((1-star c.value)/2) • fourierL2 (sourceFK c))

/-- The true adjoint field is generated from the original full R response of the Fourier source. -/
theorem unit_adjoint_source (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (K c : BurnolL2) (unitResolventSource c value) =
      inner ℂ (unitAdjointSource c) value := by
  simp only [unitResolventSource, unitAdjointSource, inner_smul_right, inner_sub_right,
    sourceRbar_adjoint, inner_smul_left, inner_sub_left, starRingEnd_apply, star_star,
    generatedK_eq_original]

private theorem unit_dilation (c : BurnolCompletedMellinCoordinate) (shift : ℝ) (value : BurnolL2) :
    burnolMultiplicativeDilation shift (unitResolventSource c value) =
      unitResolventSource c (burnolMultiplicativeDilation shift value) := by
  simp only [unitResolventSource, sourceResolvent, map_smul, map_sub,
    burnolDirectRightResolvent_dilation]

/-- The shifted original cotest consumes the same complete unit-R field. -/
theorem shifted_forward_unit_source (c : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    inner ℂ (burnolMultiplicativeDilation shift (K c : BurnolL2))
        (unitResolventSource c ConstantForward.value) =
      inner ℂ (burnolMultiplicativeDilation shift (unitAdjointSource c)) ConstantForward.value := by
  have flip (left right : BurnolL2) :
      inner ℂ (burnolMultiplicativeDilation shift left) right =
        inner ℂ left (burnolMultiplicativeDilation (-shift) right) := by
    have actual := (burnolMultiplicativeDilation shift).inner_map_eq_flip left right
    rwa [←burnolMultiplicativeDilation_neg_eq_symm] at actual
  rw [flip, unit_dilation, unit_adjoint_source]
  exact (flip _ _).symm

end OriginalKElementaryArithmeticAction.FullOriginalRUnitSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
