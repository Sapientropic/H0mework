import H0mework.Versions.V2.Arithmetic.RieszFiniteSource.FourierEdge
import H0mework.Versions.V2.Arithmetic.RieszColumns.EdgeSupport
import H0mework.Versions.V2.Arithmetic.RieszColumns.Support

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform Topology
open OriginalRieszFiniteSource OriginalPaPhysicalGreen
noncomputable section

local notation "q" => (1 / 4 : ℝ)

def reverseEdgeRadius (endpoint : ℝ) : ℝ := q * Real.exp |endpoint|

def reverseEdgeIntegrand (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint time : ℝ) : BurnolL2 :=
  Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) •
    edgeIntegral coordinate (-time)

/-- Reverse time is applied to the finite edge source itself, so the tail cancels before integration. -/
def reverseEdgeIntegral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) : BurnolL2 :=
  (2 * (star coordinate.value - 1 / 2)) •
      (∫ time : ℝ in (0 : ℝ)..endpoint, reverseEdgeIntegrand coordinate endpoint time) -
    edgeIntegral coordinate (-endpoint)

theorem edgeIntegral_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (edgeIntegral coordinate) := by
  have character : Continuous (fullMellinTranslationCharacter (star coordinate.value)) :=
    (continuous_const.mul Complex.continuous_ofReal).cexp
  exact (burnolMultiplicativeDilation_stronglyContinuous (edgePrimitive coordinate)).sub
    (character.smul continuous_const)

theorem reverseEdgeIntegrand_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) : Continuous (reverseEdgeIntegrand coordinate endpoint) := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact weight.smul ((edgeIntegral_continuous coordinate).comp continuous_neg)

private theorem negative_character (coordinate : BurnolCompletedMellinCoordinate) (time : ℝ) :
    fullMellinTranslationCharacter (star coordinate.value) (-time) =
      Complex.exp ((star coordinate.value - 1 / 2) * (time : ℂ)) := by
  unfold fullMellinTranslationCharacter
  congr 1
  push_cast
  ring

private theorem positive_character (coordinate : BurnolCompletedMellinCoordinate) (time : ℝ) :
    fullMellinTranslationCharacter (star coordinate.value) time =
      Complex.exp (-(star coordinate.value - 1 / 2) * (time : ℂ)) := by
  unfold fullMellinTranslationCharacter
  congr 1
  ring

private theorem character_integral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    (2 * (star coordinate.value - 1 / 2)) *
      (∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-(star coordinate.value - 1 / 2) * ((endpoint : ℂ) - (time : ℂ))) *
          fullMellinTranslationCharacter (star coordinate.value) (-time)) =
    fullMellinTranslationCharacter (star coordinate.value) (-endpoint) -
      fullMellinTranslationCharacter (star coordinate.value) endpoint := by
  let lambda := star coordinate.value - 1 / 2
  let value := fun time : ℝ => Complex.exp (lambda * (time : ℂ))
  have derivative (time : ℝ) :
      HasDerivAt value (2 * lambda * value time - lambda * value time) time := by
    have source := ((Complex.ofRealCLM.hasDerivAt (x := time)).const_mul lambda).cexp
    convert! source using 1
    simp only [value, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    ring
  have continuous : Continuous value := (continuous_const.mul Complex.continuous_ofReal).cexp
  have generated := _root_.OriginalRieszFiniteResponse.Integration.finite_response value
    (fun time : ℝ => 2 * lambda * value time) lambda derivative
    (continuous_const.mul continuous) endpoint
  have rearrange (time : ℝ) :
      Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) * (2 * lambda * value time) =
      2 * lambda * (Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) * value time) := by ring
  simp only [rearrange] at generated
  rw [intervalIntegral.integral_const_mul] at generated
  have base : value 0 = 1 := by simp [value]
  rw [base, mul_one] at generated
  simp only [negative_character]
  rw [positive_character]
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans generated.symm))

private theorem fourier_negative_edge (coordinate : BurnolCompletedMellinCoordinate) (time : ℝ) :
    fourierL2 (edgeIntegral coordinate (-time)) =
      burnolMultiplicativeDilation time (fourierPrimitive coordinate) -
        fullMellinTranslationCharacter (star coordinate.value) (-time) • fourierPrimitive coordinate := by
  rw [edgeIntegral, map_sub, map_smul, fourierL2_burnolMultiplicativeDilation, neg_neg]
  rfl

theorem fourier_reverseEdgeIntegral (coordinate : BurnolCompletedMellinCoordinate) (endpoint : ℝ) :
    fourierL2 (reverseEdgeIntegral coordinate endpoint) =
      fourierEdgeIntegral coordinate endpoint := by
  let lambda := star coordinate.value - 1 / 2
  let scalar := fun time : ℝ =>
    Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) *
      fullMellinTranslationCharacter (star coordinate.value) (-time)
  have scalarContinuous : Continuous scalar := by
    have first : Continuous (fun time : ℝ =>
        Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ)))) :=
      (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
    have second : Continuous (fun time : ℝ =>
        fullMellinTranslationCharacter (star coordinate.value) (-time)) :=
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_neg)).cexp
    exact first.mul second
  have same (time : ℝ) :
      fourierL2 (reverseEdgeIntegrand coordinate endpoint time) =
        nativeIntegrand lambda (fourierPrimitive coordinate) endpoint time -
          scalar time • fourierPrimitive coordinate := by
    rw [reverseEdgeIntegrand, map_smul, fourier_negative_edge, smul_sub, smul_smul]
    rfl
  have integral : fourierL2
      (∫ time : ℝ in (0 : ℝ)..endpoint, reverseEdgeIntegrand coordinate endpoint time) =
      nativeIntegral lambda (fourierPrimitive coordinate) endpoint -
        (∫ time : ℝ in (0 : ℝ)..endpoint, scalar time) • fourierPrimitive coordinate := by
    have scalarIntegrable : IntervalIntegrable
        (fun time : ℝ => scalar time • fourierPrimitive coordinate) volume 0 endpoint :=
      (scalarContinuous.smul continuous_const).intervalIntegrable 0 endpoint
    have mapped := fourierL2.toLinearIsometry.intervalIntegral_comp_comm
      (μ := volume) (a := (0 : ℝ)) (b := endpoint) (reverseEdgeIntegrand coordinate endpoint)
    change (∫ time : ℝ in (0 : ℝ)..endpoint,
      fourierL2 (reverseEdgeIntegrand coordinate endpoint time)) =
      fourierL2 (∫ time : ℝ in (0 : ℝ)..endpoint, reverseEdgeIntegrand coordinate endpoint time) at mapped
    rw [← mapped]
    simp only [same]
    rw [intervalIntegral.integral_sub
      (nativeIntegrand_integrable lambda (fourierPrimitive coordinate) endpoint)
      scalarIntegrable,
      intervalIntegral.integral_smul_const]
    rfl
  rw [reverseEdgeIntegral, map_sub, map_smul, integral, fourier_negative_edge]
  change (2 * lambda) •
      (nativeIntegral lambda (fourierPrimitive coordinate) endpoint -
        (∫ time : ℝ in (0 : ℝ)..endpoint, scalar time) • fourierPrimitive coordinate) -
      (burnolMultiplicativeDilation endpoint (fourierPrimitive coordinate) -
        fullMellinTranslationCharacter (star coordinate.value) (-endpoint) • fourierPrimitive coordinate) = _
  rw [smul_sub, smul_smul]
  have scalarRead : (2 * lambda) * (∫ time : ℝ in (0 : ℝ)..endpoint, scalar time) =
      fullMellinTranslationCharacter (star coordinate.value) (-endpoint) -
        fullMellinTranslationCharacter (star coordinate.value) endpoint :=
    character_integral coordinate endpoint
  rw [scalarRead, fourierEdgeIntegral]
  dsimp only [lambda]
  module

theorem reverseEdgeIntegral_cutoff_self (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) :
    originalPhysicalCutoff (reverseEdgeRadius endpoint) (reverseEdgeIntegral coordinate endpoint) =
      reverseEdgeIntegral coordinate endpoint := by
  let radius := reverseEdgeRadius endpoint
  have baseBound : q ≤ radius := by
    change q ≤ q * Real.exp |endpoint|
    nlinarith [Real.one_le_exp_iff.mpr (abs_nonneg endpoint)]
  have timeBound {time : ℝ} (bounded : time ≤ |endpoint|) : q * Real.exp time ≤ radius :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr bounded) (by norm_num)
  have edgeSupport (time : ℝ) (bounded : time ≤ |endpoint|) :
      originalPhysicalCutoff radius (edgeIntegral coordinate (-time)) = edgeIntegral coordinate (-time) :=
    cutoff_eq_self_of_ae_zero radius _ (edgeIntegral_ae_zero coordinate (-time) radius baseBound
      (by simpa only [neg_neg] using timeBound bounded))
  have integrandSupport (time : ℝ) (inside : time ∈ Set.uIcc (0 : ℝ) endpoint) :
      originalPhysicalCutoff radius (reverseEdgeIntegrand coordinate endpoint time) =
        reverseEdgeIntegrand coordinate endpoint time := by
    have bounded : |time| ≤ |endpoint| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc inside
    exact cutoff_smul_self radius (edgeIntegral coordinate (-time)) _
      (edgeSupport time ((le_abs_self time).trans bounded))
  have integralSupport := intervalIntegral_cutoff_self radius
    (reverseEdgeIntegrand coordinate endpoint) 0 endpoint
    ((reverseEdgeIntegrand_continuous coordinate endpoint).intervalIntegrable 0 endpoint) integrandSupport
  have finalSupport := edgeSupport endpoint (le_abs_self endpoint)
  change (burnolRadiusZeroExtension radius).comp (burnolRadiusRestriction radius)
      ((2 * (star coordinate.value - 1 / 2)) •
          (∫ time : ℝ in (0 : ℝ)..endpoint, reverseEdgeIntegrand coordinate endpoint time) -
        edgeIntegral coordinate (-endpoint)) = _
  rw [map_sub, map_smul]
  change (2 * (star coordinate.value - 1 / 2)) •
      originalPhysicalCutoff radius
        (∫ time : ℝ in (0 : ℝ)..endpoint, reverseEdgeIntegrand coordinate endpoint time) -
      originalPhysicalCutoff radius (edgeIntegral coordinate (-endpoint)) = _
  rw [integralSupport, finalSupport]
  rfl

theorem reverseEdgeIntegral_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) : Integrable (reverseEdgeIntegral coordinate endpoint) :=
  integrable_of_cutoff_eq_self (reverseEdgeRadius endpoint) _
    (reverseEdgeIntegral_cutoff_self coordinate endpoint)

theorem reverseEdgeIntegral_firstMoment (coordinate : BurnolCompletedMellinCoordinate)
    (endpoint : ℝ) :
    MemLp (fun x : ℝ => (x : ℂ) * reverseEdgeIntegral coordinate endpoint x) 2 volume :=
  firstMoment_of_cutoff_eq_self (reverseEdgeRadius endpoint) _
    (reverseEdgeIntegral_cutoff_self coordinate endpoint)

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
