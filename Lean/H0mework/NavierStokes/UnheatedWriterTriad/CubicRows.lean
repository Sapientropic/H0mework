import H0mework.NavierStokes.UnheatedWriterTail.QuadraticCubic

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedCubicRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeTimeJetCarrier NativeHigherTimeJets NativeWholeH1Mixed NativeWholeH1Pairing
open NativeEndpointVelocityCarrier NativeResolventCompactness NativeWholeResolvent
open NativeUnheatedPairNegativeKernel NativeUnheatedPairInverseFlux NativeUnheatedStressPairEvolution
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedSourceGradient NativeUnheatedGlobalNegativeOne NativeUnheatedPairGlobalEvolution
noncomputable section

def dyad (left right : ComplexCoordinateVector) : NativeFluidStressCoefficient :=
  fun output input => -(left input*right output)

theorem dyad_summable (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    Summable (fun a => dyad (left a) (right (wave-a))) := by
  apply Pi.summable.mpr
  intro output
  apply Pi.summable.mpr
  intro input
  exact (mixed_pair_summable left right wave output input).neg

theorem dyad_sum (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    (∑' a, dyad (left a) (right (wave-a))) = mixedFlux left right wave := by
  funext output input
  rw [tsum_apply (dyad_summable left right wave),
    tsum_apply (Pi.summable.mp (dyad_summable left right wave) output)]
  simp only [dyad, mixedFlux, tsum_neg]

def rowTerm (left right : ComplexVorticityHilbertState) (wave a : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (dyad (left a) (right (wave-a)))

theorem rowTerm_summable (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    Summable (rowTerm left right wave) :=
  (projectedDivergenceCLM wave).hasSum (dyad_summable left right wave).hasSum |>.summable

theorem rowTerm_sum (left right : wholePhysical) (wave : IntegerWavevector) :
    (∑' a, rowTerm (wholeVelocity left.1) (wholeVelocity right.1) wave a) = row left right wave := by
  unfold rowTerm
  rw [← (projectedDivergenceCLM wave).map_tsum (dyad_summable _ _ wave), dyad_sum]
  rfl

theorem negative_row (left right : wholePhysical) (leftH1 : H1 left) (rightH1 : H1 right)
    (wave : IntegerWavevector) :
    wholeVelocity (negativeAction left right leftH1 rightH1) wave = (root wave)⁻¹ • row left right wave := by
  by_cases zero : wave = 0
  · subst wave
    simp [wholeVelocity_zero, root, integerWaveViscousMultiplier, integerWaveNormSq]
  · funext coordinate
    simp only [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave,zero⟩, negativeAction, negativeRow]
    rfl

theorem row_zero (left right : wholePhysical) : row left right 0 = 0 := by
  simp only [NativeWholeH1Mixed.row, projectedDivergenceCLM_apply]
  simp [transverseProjection]

theorem bilinear_raw (nu : Viscosity) (left right outer : wholePhysical)
    (leftH1 : H1 left) (rightH1 : H1 right) (wave : IntegerWavevector) (output input : Coordinate) :
    bilinear nu 0 wave output input (inverseGradient outer.1) (negativeAction left right leftH1 rightH1) =
      -∑' c, ((decay nu c (wave-c))⁻¹) • (wholeVelocity outer.1 c input * row left right (wave-c) output) := by
  rw [bilinear_apply]
  congr 1
  apply tsum_congr
  intro c
  by_cases cZero : c = 0
  · subst c
    simp [wholeVelocity_zero, inverse_row]
  by_cases otherZero : wave-c = 0
  · simp [otherZero, negative_row, row_zero]
  rw [inverse_row, negative_row]
  simp only [gradedKernel, pow_zero, mul_one, NativeUnheatedPairNegativeKernel.kernel,
    Pi.smul_apply, Complex.real_smul]
  push_cast
  field_simp [(root_positive c cZero).ne', (root_positive (wave-c) otherZero).ne']

theorem bilinear_swap (nu : Viscosity) (left right : State) (wave : IntegerWavevector) (output input : Coordinate) :
    bilinear nu 0 wave output input left right = bilinear nu 0 wave input output right left := by
  rw [bilinear_apply, bilinear_apply]
  congr 1
  rw [← (Equiv.subLeft wave).tsum_eq (fun c => gradedKernel nu 0 c (wave-c) •
    (wholeVelocity right c output*wholeVelocity left (wave-c) input))]
  apply tsum_congr
  intro c
  simp only [Equiv.subLeft_apply, sub_sub_cancel, gradedKernel, pow_zero, mul_one,
    NativeUnheatedPairNegativeKernel.kernel, decay, Complex.real_smul]
  push_cast
  ring

def value (nu : Viscosity) (left right outer : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (response outside : Coordinate) : ℂ :=
  ∑' c, ((decay nu c (wave-c))⁻¹) •
    ((∑' a, rowTerm left right (wave-c) a response)*outer c outside)

theorem bilinear_value (nu : Viscosity) (left right outer : wholePhysical)
    (leftH1 : H1 left) (rightH1 : H1 right) (wave : IntegerWavevector) (output input : Coordinate) :
    bilinear nu 0 wave output input (inverseGradient outer.1) (negativeAction left right leftH1 rightH1) =
      -value nu (wholeVelocity left.1) (wholeVelocity right.1) (wholeVelocity outer.1) wave output input := by
  rw [bilinear_raw nu left right outer leftH1 rightH1 wave output input, value]
  congr 1
  apply tsum_congr
  intro c
  have rowRead := congrFun (rowTerm_sum left right (wave-c)) output
  rw [tsum_apply (rowTerm_summable _ _ (wave-c))] at rowRead
  rw [rowRead, mul_comm]

def sourceValue {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (response outside : Coordinate) : ℂ :=
  let U := wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
  value nu U U U wave response outside

theorem source_identity {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave output input,
      sourceTriple seed 0 time wave output input =
        -sourceValue seed time wave input output-sourceValue seed time wave output input := by
  filter_upwards [physical_H1_ae seed] with time generated nonnegative wave output input
  have regular := generated nonnegative
  rw [sourceTriple, dif_pos nonnegative, dif_pos regular]
  change bilinear nu 0 wave output input _ (inverseGradient (physical seed time nonnegative).1) +
    bilinear nu 0 wave output input (inverseGradient (physical seed time nonnegative).1) _ = _
  rw [bilinear_swap nu _ _ wave output input, bilinear_value, bilinear_value]
  rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedCubicRows
