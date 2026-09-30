import H0mework.NavierStokes.UnheatedWriterTriad.Time
import H0mework.NavierStokes.UnheatedWriterTriad.CubicCarrier

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedCubicRaw
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing
open NativeUnheatedStressPairEvolution NativeUnheatedPairNegativeKernel NativeUnheatedTriadChannels NativeUnheatedSourceGradient
open NativeUnheatedPairGlobalEvolution NativeUnheatedCubicRows NativeUnheatedCubicIdentity
noncomputable section
variable {nu : Viscosity}

def rawRow (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (indices : IntegerWavevector × IntegerWavevector) (time : ℝ) : ℂ :=
  let c := indices.1
  let a := indices.2
  let b := wave-c-a
  (decay nu (a+b) c)⁻¹ • (pressure (a+b) i j response*
    NativeUnheatedTriadTime.product seed (a,i) (b,j) (c,outside) time)

theorem row_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (indices : IntegerWavevector × IntegerWavevector) :
    rawRow seed wave i j response outside indices time =
      NativeUnheatedTriadSum.term (NativeUnheatedCubicKernel.kernel nu i j response) wave i j outside
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (gradientValue (physical seed time nonnegative) regular)) indices := by
  by_cases zero : indices.1 = 0
  · simp only [rawRow, NativeUnheatedTriadTime.product, NativeUnheatedTriadRows.velocity_original,
      NativeUnheatedTriadSum.term, zero, wholeVelocity_zero, Pi.zero_apply, mul_zero, smul_zero]
  · simp only [rawRow, NativeUnheatedTriadTime.product, NativeUnheatedTriadRows.velocity_original,
      NativeUnheatedTriadSum.term, NativeUnheatedTriadSum.innerTerm, NativeUnheatedCubicKernel.kernel,
      NativeUnheatedCubicKernel.gradient_row, Pi.smul_apply, Complex.real_smul]
    change _ = _ * (↑(root indices.1)*wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst indices.1 outside)
    push_cast
    field_simp [(root_positive indices.1 zero).ne']

theorem row_sum_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector) (i j response outside : Coordinate) :
    (∑' indices, rawRow seed wave i j response outside indices time) =
      NativeUnheatedCubicKernel.value nu wave i j response outside
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
        (wholeVelocity (gradientValue (physical seed time nonnegative) regular)) := by
  simp_rw [row_original seed time nonnegative regular]
  exact (NativeUnheatedTriadSum.value_eq_tsum _ (NativeUnheatedCubicKernel.cap nu)
    (NativeUnheatedCubicKernel.kernel_bound nu i j response) _ _ _ _ _ _ _).symm

theorem source_identity (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave output input,
      sourceTriple seed 0 time wave output input =
        -(∑ i : Coordinate, ∑ j : Coordinate, ∑' indices, rawRow seed wave i j input output indices time) -
          (∑ i : Coordinate, ∑ j : Coordinate, ∑' indices, rawRow seed wave i j output input indices time) := by
  filter_upwards [NativeUnheatedCubicRows.source_identity seed, physical_H1_ae seed] with time actual generated nonnegative wave output input
  have regular := generated nonnegative
  rw [actual nonnegative]
  simp_rw [row_sum_original seed time nonnegative regular]
  congr 1
  · congr 1
    exact value_channels nu _ _ (physical seed time nonnegative) regular wave input output
  · exact value_channels nu _ _ (physical seed time nonnegative) regular wave output input

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector) (i j response outside : Coordinate) :
    Summable (fun indices => ‖rawRow seed wave i j response outside indices time‖) := by
  simp_rw [row_original seed time nonnegative regular]
  exact NativeUnheatedCubicKernel.value_absolute nu wave i j response outside _ _ _

def coefficient (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  (3*NativeUnheatedCubicKernel.cap nu*‖NativeUnheatedTriadSum.weights‖)*NativeUnifiedCompleteSource.budget seed^2*(2*Real.pi)

theorem coefficient_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ coefficient seed := by
  unfold coefficient NativeUnheatedCubicKernel.cap
  positivity [nu.coeff_pos]

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (wave : IntegerWavevector) (i j response outside : Coordinate) :
    (∑' indices, ‖rawRow seed wave i j response outside indices time‖) ≤ coefficient seed*Real.sqrt (mass seed time) := by
  simp_rw [row_original seed time nonnegative regular]
  have actual := NativeUnheatedTriadSum.absolute_bound _ (NativeUnheatedCubicKernel.cap nu)
    (NativeUnheatedCubicKernel.kernel_bound nu i j response) wave i j outside
    (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
    (wholeVelocity (gradientValue (physical seed time nonnegative) regular))
  have velocity : ‖wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst‖ ≤ NativeUnifiedCompleteSource.budget seed :=
    (wholeVelocity_norm_le _).trans ((WithLp.norm_fst_le _ _).trans (NativeUnifiedCompleteSource.source_bound seed time))
  have gradient : ‖wholeVelocity (gradientValue (physical seed time nonnegative) regular)‖ ≤ (2*Real.pi)*Real.sqrt (mass seed time) := by
    apply (wholeVelocity_norm_le _).trans
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [gradientValue_norm_sq, physical_mass]
    simp only [mul_pow, Real.sq_sqrt (mass_nonnegative seed time), le_refl]
  have square := mul_le_mul velocity velocity (norm_nonneg _) ((norm_nonneg _).trans velocity)
  have constant0 : 0 ≤ 3*NativeUnheatedCubicKernel.cap nu*‖NativeUnheatedTriadSum.weights‖ := by
    unfold NativeUnheatedCubicKernel.cap
    positivity [nu.coeff_pos]
  have estimated := mul_le_mul (mul_le_mul_of_nonneg_left square constant0) gradient (norm_nonneg _)
    (mul_nonneg constant0 (mul_nonneg ((norm_nonneg _).trans velocity) ((norm_nonneg _).trans velocity)))
  apply actual.trans
  convert! estimated using 1
  · ring
  · unfold coefficient
    ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedCubicRaw
