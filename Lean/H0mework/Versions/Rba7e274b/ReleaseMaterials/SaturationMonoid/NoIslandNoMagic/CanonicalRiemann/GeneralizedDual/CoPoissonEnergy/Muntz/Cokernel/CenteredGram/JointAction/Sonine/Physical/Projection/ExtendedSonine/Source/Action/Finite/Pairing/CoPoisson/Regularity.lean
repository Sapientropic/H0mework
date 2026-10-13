import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.Band
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing

noncomputable section

def reciprocalWeight (shift : ℝ) (profile : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(Real.exp (-shift / 2) : ℂ) * (t : ℂ)⁻¹ * profile (Real.exp (-shift) / t)

private def reciprocalSlope (shift : ℝ) (profile slope : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(Real.exp (-shift / 2) : ℂ) *
    ((-1 / (t : ℂ) ^ 2) * profile (Real.exp (-shift) / t) +
      (t : ℂ)⁻¹ * ((-Real.exp (-shift) / t ^ 2) • slope (Real.exp (-shift) / t)))

private theorem reciprocalWeight_hasDerivAt (shift : ℝ) (profile slope : ℝ → ℂ)
    {t : ℝ} (positive : 0 < t)
    (source : HasDerivAt profile (slope (Real.exp (-shift) / t)) (Real.exp (-shift) / t)) :
    HasDerivAt (reciprocalWeight shift profile) (reciprocalSlope shift profile slope t) t := by
  have moved : HasDerivAt (fun u : ℝ => Real.exp (-shift) / u)
      (-Real.exp (-shift) / t ^ 2) t := by
    convert! (hasDerivAt_const t (Real.exp (-shift))).div (hasDerivAt_id t) positive.ne' using 1
    simp
  have inverted : HasDerivAt (fun u : ℝ => (u : ℂ)⁻¹) (-1 / (t : ℂ) ^ 2) t :=
    (Complex.ofRealCLM.hasDerivAt).inv (Complex.ofReal_ne_zero.mpr positive.ne')
  convert! (inverted.mul (source.scomp t moved)).const_mul (-(Real.exp (-shift / 2) : ℂ)) using 1
  funext u
  simp only [reciprocalWeight, Function.comp_def, Pi.mul_apply, mul_assoc]

private theorem reciprocalWeight_deriv_continuousOn (shift : ℝ) (profile slope : ℝ → ℂ)
    (source : ∀ t, 0 < t → HasDerivAt profile (slope t) t)
    (regular : ∀ t, 0 < t → ContinuousAt slope t) :
    ContinuousOn (deriv (reciprocalWeight shift profile)) (Ioi 0) := by
  have actual (t : ℝ) (positive : 0 < t) :
      deriv (reciprocalWeight shift profile) t = reciprocalSlope shift profile slope t :=
    (reciprocalWeight_hasDerivAt shift profile slope positive
      (source _ (div_pos (Real.exp_pos _) positive))).deriv
  have continuousSlope : ContinuousOn (reciprocalSlope shift profile slope) (Ioi 0) := by
    intro t positive
    have moved : ContinuousAt (fun u : ℝ => Real.exp (-shift) / u) t :=
      continuousAt_const.div continuousAt_id positive.ne'
    have movedPositive : 0 < Real.exp (-shift) / t := div_pos (Real.exp_pos _) positive
    have profileContinuous := (source _ movedPositive).continuousAt.comp moved
    have slopeContinuous := (regular _ movedPositive).comp moved
    have castNonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
    exact (continuousAt_const.mul
      (((continuousAt_const.div (Complex.continuous_ofReal.continuousAt.pow 2)
        (pow_ne_zero _ castNonzero)).mul profileContinuous).add
          ((Complex.continuous_ofReal.continuousAt.inv₀ castNonzero).mul
            ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero _ positive.ne')).smul
              slopeContinuous)))).continuousWithinAt
  exact continuousSlope.congr (fun t positive => actual t positive)

private theorem positionSource_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    HasDerivAt (positionSource coordinate) (positionExteriorDerivative coordinate x) x := by
  exact (((burnolMellinTailPower_hasDerivAt (star coordinate.value) positive).const_mul
    (1 / 2 : ℂ)).sub_const (GapEuler.gapMean (1 / 4 : ℝ) coordinate)).sub
      (burnolRieszReturnRaw_hasDerivAt coordinate x)

private theorem positionSlope_continuousAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) : ContinuousAt (positionExteriorDerivative coordinate) x := by
  exact (continuousAt_const.mul
    (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const x
      (-(star coordinate.value + 1)) (Or.inr positive.ne')))).sub
        (burnolRieszReturnRawDerivative_continuous coordinate).continuousAt

private theorem sourceSlope_continuousAt (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) : ContinuousAt (sourceRawDerivative coordinate) x := by
  exact (((continuousAt_const.mul (Translator.ForcingWhole.raw_continuousAt coordinate positive.ne')).add
    (continuousAt_const.mul (Edge.raw_continuous (1 / 4 : ℝ)).continuousAt)).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr positive.ne')).add
        (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous coordinate)).continuousAt

def positionWeight (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℝ → ℂ :=
  reciprocalWeight shift (positionSource coordinate)

def fourierWeight (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℝ → ℂ :=
  reciprocalWeight shift (burnolRieszSingleFourierSourceRaw coordinate)

theorem positionWeight_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (shift t : ℝ)
    (positive : 0 < t) :
    HasDerivAt (positionWeight coordinate shift) (deriv (positionWeight coordinate shift) t) t :=
  (reciprocalWeight_hasDerivAt shift _ _ positive
    (positionSource_hasDerivAt coordinate _ (div_pos (Real.exp_pos _) positive))).differentiableAt.hasDerivAt

theorem fourierWeight_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (shift t : ℝ)
    (positive : 0 < t) :
    HasDerivAt (fourierWeight coordinate shift) (deriv (fourierWeight coordinate shift) t) t :=
  (reciprocalWeight_hasDerivAt shift _ _ positive
    (sourceRaw_hasDerivAt coordinate _ (div_pos (Real.exp_pos _) positive).ne')).differentiableAt.hasDerivAt

theorem positionWeight_deriv_continuousOn (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    ContinuousOn (deriv (positionWeight coordinate shift)) (Ioi 0) :=
  reciprocalWeight_deriv_continuousOn shift _ _
    (positionSource_hasDerivAt coordinate) (positionSlope_continuousAt coordinate)

theorem fourierWeight_deriv_continuousOn (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    ContinuousOn (deriv (fourierWeight coordinate shift)) (Ioi 0) :=
  reciprocalWeight_deriv_continuousOn shift _ _
    (fun x positive => sourceRaw_hasDerivAt coordinate x positive.ne') (sourceSlope_continuousAt coordinate)

end
end OriginalRieszFinitePairing.CoPoisson
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
