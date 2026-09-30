import H0mework.Versions.X.NavierStokes.UnheatedWriterOne.Write
import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.ViscousCancellation
import H0mework.NavierStokes.UnheatedWriterPair.IntegralBilinear

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairGlobalEvolution

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing
open NativeNegativeOneMomentum NativeEndpointVelocityCarrier NativeUnheatedSourceGradient
open NativeUnheatedPairNegativeKernel NativeUnheatedPairInverseFlux
open NativeUnheatedGlobalNegativeOne NativeUnheatedIntegralBilinear

noncomputable section
variable {nu : Viscosity}

def sourcePair (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  coefficient nu order (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave output input

def sourceTriple (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ := by
  classical
  exact if nonnegative : 0 ≤ time then
    if regular : H1 (physical seed time nonnegative) then
      bilinear nu order wave output input (negativeAction (physical seed time nonnegative) (physical seed time nonnegative) regular regular)
        (state seed time) +
      bilinear nu order wave output input (state seed time)
        (negativeAction (physical seed time nonnegative) (physical seed time nonnegative) regular regular)
    else 0
  else 0

theorem sourcePair_represented (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    sourcePair seed (order+1) time wave output input =
      bilinear nu order wave output input (state seed time) (state seed time) :=
  (bilinear_original order wave output input _ _).symm

theorem derivative_value_ae (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ∀ᵐ time : ℝ, 0 ≤ time →
      bilinear nu order wave output input (rate seed time) (state seed time) +
        bilinear nu order wave output input (state seed time) (rate seed time) =
      sourceTriple seed order time wave output input - sourcePair seed order time wave output input := by
  filter_upwards [physical_H1_ae seed] with time generated
  intro nonnegative
  have regular := generated nonnegative
  have cancelled := viscous_pair (nu := nu) order (physical seed time nonnegative) regular wave output input
  change nu.coeff • (bilinear nu order wave output input (gradientValue (physical seed time nonnegative) regular) (state seed time) +
    bilinear nu order wave output input (state seed time) (gradientValue (physical seed time nonnegative) regular)) =
      sourcePair seed order time wave output input at cancelled
  rw [rate, dif_pos nonnegative, dif_pos regular, NativeNegativeOneMomentum.momentum,
    sourceTriple, dif_pos nonnegative, dif_pos regular]
  simp only [map_sub, map_smul, sub_apply, smul_apply]
  rw [← cancelled, smul_add]
  abel

theorem sourcePair_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (fun t => sourcePair seed (order+1) t wave output input)
      (sourceTriple seed order time wave output input - sourcePair seed order time wave output input) time := by
  filter_upwards [source_hasDerivAt_ae seed, derivative_value_ae seed order wave output input] with time actual value
  intro positive
  have pair := ((bilinear nu order wave output input).hasFDerivAt.comp_hasDerivAt time (actual positive)).clm_apply (actual positive)
  simp only [Function.comp_def] at pair
  rw [value positive.le] at pair
  simpa only [sourcePair_represented, Function.comp_def] using! pair

theorem state_ac (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    AbsolutelyContinuousOnInterval (state seed) a b :=
  written_ac (state seed) (rate seed) (rate_intervalIntegrable seed a b a0 b0)
    (fun _ hx _ hy => source_integral seed _ _ ((le_min a0 b0).trans hx.1) ((le_min a0 b0).trans hy.1))

theorem sourcePair_ac (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b)
    (wave : IntegerWavevector) (output input : Coordinate) :
    AbsolutelyContinuousOnInterval (fun t => sourcePair seed (order+1) t wave output input) a b := by
  simpa only [sourcePair_represented] using diagonal_ac (bilinear nu order wave output input) (state_ac seed a b a0 b0)

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairGlobalEvolution
