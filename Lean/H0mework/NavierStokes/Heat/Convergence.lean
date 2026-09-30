import H0mework.NavierStokes.Heat.Primitive
import H0mework.NavierStokes.SourceEstimates.ReferenceKineticMixedPair
import H0mework.NavierStokes.Fourier.IntegerLatticeCriticalKernel

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.HeatWholeWork

open scoped BigOperators
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalIntegerLatticeCriticalKernel

noncomputable section

private theorem transport_work_sq (x : ComplexVorticityHilbertState)
    (p q : IntegerWavevector) (pNe : p ≠ 0) :
    complexCoordinateRealInner (x (p + q)) (ReferencePair.transport (x p) (x q) p q) ^ 2 ≤
      integerWaveNormSq q * (vorticityRowAmplitude x (p + q) *
        vorticityRowAmplitude x p * vorticityRowAmplitude x q) ^ 2 / integerWaveNormSq p := by
  have bound := ReferenceKineticMixed.derivativeWork_abs_le x x q p
  have rhsNonneg : 0 ≤ (2 * Real.pi * Real.sqrt (integerWaveNormSq q) * vorticityRowAmplitude x q) *
      ReferenceKineticMixed.kineticProduct x q p := by
    unfold ReferenceKineticMixed.kineticProduct vorticityRowAmplitude
    positivity
  have squared := (sq_le_sq₀ (abs_nonneg _) rhsNonneg).2 bound
  have denPos : 0 < integerWaveViscousMultiplier p := by
    unfold integerWaveViscousMultiplier
    exact mul_pos (sq_pos_of_pos (by positivity)) (integerWaveNormSq_pos pNe)
  have densityNonneg := div_nonneg (complexCoordinateAmplitudeSq_nonneg (x p)) denPos.le
  simp only [ReferenceWork.derivativeWork, ReferenceKineticMixed.kineticProduct,
    sq_abs, mul_pow, Real.sq_sqrt (integerWaveNormSq_nonneg q), Real.sq_sqrt densityNonneg,
    vorticityRowAmplitude_sq] at squared ⊢
  convert squared using 1 <;> try rfl
  · rw [add_comm p q]
  · unfold integerWaveViscousMultiplier
    rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, add_comm q p]
    field_simp [(integerWaveNormSq_pos pNe).ne', Real.pi_ne_zero]

/-- Three-leg heat inversion pays both placements using only the original L² rows. -/
theorem row_abs_le (nu : Viscosity) (x : ComplexVorticityHilbertState) (zeroRow : x 0 = 0)
    (p q : IntegerWavevector) :
    |HeatPrimitive.row nu p q x| ≤
      (2 / (nu.coeff * (2 * Real.pi) ^ 2)) *
        (vorticityRowAmplitude x p / integerWaveNormSq p) *
        (vorticityRowAmplitude x (p + q) * vorticityRowAmplitude x q) := by
  by_cases pNe : p ≠ 0
  · let P := integerWaveNormSq p
    let Q := integerWaveNormSq q
    let H := P + Q + integerWaveNormSq (p + q)
    let A := vorticityRowAmplitude x (p + q) * vorticityRowAmplitude x p * vorticityRowAmplitude x q
    let S := complexCoordinateRealInner (x (p + q)) (ReferencePair.stretching (x p) (x q) q)
    let T := complexCoordinateRealInner (x (p + q)) (ReferencePair.transport (x p) (x q) p q)
    have Ppos : 0 < P := integerWaveNormSq_pos pNe
    have Qnonneg : 0 ≤ Q := integerWaveNormSq_nonneg q
    have Hge : P + Q ≤ H := le_add_of_nonneg_right (integerWaveNormSq_nonneg _)
    have Hpos : 0 < H := Ppos.trans_le ((le_add_of_nonneg_right Qnonneg).trans Hge)
    have Anonneg : 0 ≤ A := by dsimp [A, vorticityRowAmplitude]; positivity
    have stretch : S ^ 2 ≤ A ^ 2 := by
      have bound := ReferencePair.stretchingWork_abs_le (x (p + q)) (x p) (x q) q
      simpa only [sq_abs, S, A, vorticityRowAmplitude] using
        (sq_le_sq₀ (abs_nonneg _) Anonneg).2 bound
    have transport : T ^ 2 * P ≤ Q * A ^ 2 :=
      (le_div_iff₀ Ppos).mp (transport_work_sq x p q pNe)
    have workSq : (S - T) ^ 2 * P ≤ 2 * (P + Q) * A ^ 2 := by
      nlinarith [mul_nonneg Ppos.le (sq_nonneg (S + T)),
        mul_le_mul_of_nonneg_right stretch Ppos.le]
    have PH : (P + Q) * P ≤ H * H :=
      mul_le_mul Hge ((le_add_of_nonneg_right Qnonneg).trans Hge) Ppos.le Hpos.le
    have absolute : |S - T| * P ≤ 2 * H * A := by
      apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) Ppos.le)
        (mul_nonneg (mul_nonneg (by norm_num) Hpos.le) Anonneg)).mp
      rw [mul_pow, sq_abs]
      nlinarith [mul_le_mul_of_nonneg_right workSq Ppos.le,
        mul_le_mul_of_nonneg_right PH (sq_nonneg A), sq_nonneg (H * A)]
    have ratePos : 0 < nu.coeff * (2 * Real.pi) ^ 2 :=
      mul_pos nu.coeff_pos (sq_pos_of_pos (by positivity))
    have divided : |S - T| / ((nu.coeff * (2 * Real.pi) ^ 2) * H) ≤
        (2 * A) / ((nu.coeff * (2 * Real.pi) ^ 2) * P) := by
      apply (div_le_div_iff₀ (mul_pos ratePos Hpos) (mul_pos ratePos Ppos)).2
      nlinarith [mul_le_mul_of_nonneg_left absolute ratePos.le]
    have heat : HeatWork.heatWeight nu p q = (nu.coeff * (2 * Real.pi) ^ 2) * H := by
      unfold HeatWork.heatWeight integerWaveViscousMultiplier H P Q
      ring
    rw [HeatPrimitive.row, HeatWork.work, HeatWork.pair, complexCoordinateRealInner_sub_right,
      abs_div, heat, abs_of_pos (mul_pos ratePos Hpos)]
    convert divided using 1
    dsimp [S, T, A, P]
    ring
  · have pZero : p = 0 := not_ne_iff.mp pNe
    subst p
    simp [HeatPrimitive.row, HeatWork.work, HeatWork.pair, ReferencePair.stretching,
      ReferencePair.transport, zeroRow, complexCoordinateRealInner, vorticityRowAmplitude]

theorem inverse_amplitude_budget (x : ComplexVorticityHilbertState) :
    (Summable fun p : IntegerWavevector => vorticityRowAmplitude x p / integerWaveNormSq p) ∧
      (∑' p, vorticityRowAmplitude x p / integerWaveNormSq p) ≤
        Real.sqrt (wholeVorticityEuclideanMass x) * Real.sqrt (∑' p, integerWaveCriticalKernel p) := by
  have kernel : Summable fun p : IntegerWavevector => (integerWaveNormSq p)⁻¹ ^ 2 :=
    summable_integerWaveCriticalKernel
  have weighted := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (vorticityRowAmplitude_nonneg x) (fun p => inv_nonneg.mpr (integerWaveNormSq_nonneg p))
    (by simpa only [Real.rpow_two] using summable_vorticityRowAmplitude_sq x)
    (by simpa only [Real.rpow_two] using kernel)
  refine ⟨by simpa only [div_eq_mul_inv] using weighted.1, ?_⟩
  simpa [div_eq_mul_inv, Real.rpow_two, wholeVorticityEuclideanMass,
    integerWaveCriticalKernel, Real.sqrt_eq_rpow] using weighted.2

theorem product_budget (output right : ComplexVorticityHilbertState) (p : IntegerWavevector) :
    (Summable fun q => vorticityRowAmplitude output (p + q) * vorticityRowAmplitude right q) ∧
      (∑' q, vorticityRowAmplitude output (p + q) * vorticityRowAmplitude right q) ≤
        Real.sqrt (wholeVorticityEuclideanMass output) * Real.sqrt (wholeVorticityEuclideanMass right) := by
  have shifted : Summable fun q : IntegerWavevector => vorticityRowAmplitude output (p + q) ^ 2 :=
    (Equiv.addLeft p).summable_iff.mpr (summable_vorticityRowAmplitude_sq output)
  have cauchy := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun q => vorticityRowAmplitude_nonneg output (p + q)) (vorticityRowAmplitude_nonneg right)
    (by simpa only [Real.rpow_two] using shifted)
    (by simpa only [Real.rpow_two] using summable_vorticityRowAmplitude_sq right)
  have shiftedMass : (∑' q, vorticityRowAmplitude output (p + q) ^ 2) = wholeVorticityEuclideanMass output :=
    (Equiv.addLeft p).tsum_eq (fun q => vorticityRowAmplitude output q ^ 2)
  refine ⟨cauchy.1, ?_⟩
  simpa [Real.rpow_two, one_div, shiftedMass, wholeVorticityEuclideanMass,
    Real.sqrt_eq_rpow] using cauchy.2

def kernel (left output right : ComplexVorticityHilbertState) (p q : IntegerWavevector) : Real :=
  (vorticityRowAmplitude left p / integerWaveNormSq p) *
    (vorticityRowAmplitude output (p + q) * vorticityRowAmplitude right q)

/-- The three fields may differ; this is the common spatial payment for all differentiated slots. -/
theorem kernel_budget (left output right : ComplexVorticityHilbertState) :
    (Summable fun pair : IntegerWavevector × IntegerWavevector => kernel left output right pair.1 pair.2) ∧
      (∑' pair : IntegerWavevector × IntegerWavevector, kernel left output right pair.1 pair.2) ≤
        (Real.sqrt (wholeVorticityEuclideanMass left) * Real.sqrt (∑' p, integerWaveCriticalKernel p)) *
          (Real.sqrt (wholeVorticityEuclideanMass output) * Real.sqrt (wholeVorticityEuclideanMass right)) := by
  let coefficient := fun p => vorticityRowAmplitude left p / integerWaveNormSq p
  let bound := Real.sqrt (wholeVorticityEuclideanMass output) * Real.sqrt (wholeVorticityEuclideanMass right)
  have coefficientNonneg (p) : 0 ≤ coefficient p :=
    div_nonneg (vorticityRowAmplitude_nonneg _ _) (integerWaveNormSq_nonneg _)
  have productNonneg (p q) : 0 ≤ vorticityRowAmplitude output (p + q) * vorticityRowAmplitude right q :=
    mul_nonneg (vorticityRowAmplitude_nonneg _ _) (vorticityRowAmplitude_nonneg _ _)
  have coefficientSummable : Summable coefficient := (inverse_amplitude_budget left).1
  have outer : Summable fun p => ∑' q, kernel left output right p q := by
    simp only [kernel, tsum_mul_left]
    exact (coefficientSummable.mul_right bound).of_nonneg_of_le
      (fun p => mul_nonneg (coefficientNonneg p) (tsum_nonneg (productNonneg p)))
      (fun p => mul_le_mul_of_nonneg_left (product_budget output right p).2 (coefficientNonneg p))
  have total : Summable fun pair : IntegerWavevector × IntegerWavevector => kernel left output right pair.1 pair.2 :=
    (summable_prod_of_nonneg (fun pair => mul_nonneg (coefficientNonneg _) (productNonneg _ _))).2
      ⟨fun p => (product_budget output right p).1.mul_left (coefficient p), outer⟩
  refine ⟨total, ?_⟩
  rw [total.tsum_prod]
  calc
    _ ≤ ∑' p, coefficient p * bound := outer.tsum_le_tsum (fun p => by
      simp only [kernel, tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (product_budget output right p).2 (coefficientNonneg p))
        (coefficientSummable.mul_right bound)
    _ = (∑' p, coefficient p) * bound := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right (inverse_amplitude_budget left).2
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Absolute convergence over the complete ordered-pair inventory, including all outputs. -/
theorem row_abs_summable (nu : Viscosity) (x : ComplexVorticityHilbertState) (zeroRow : x 0 = 0) :
    Summable fun pair : IntegerWavevector × IntegerWavevector =>
      |HeatPrimitive.row nu pair.1 pair.2 x| := by
  have majorantSummable := (kernel_budget x x x).1.mul_left (2 / (nu.coeff * (2 * Real.pi) ^ 2))
  exact majorantSummable.of_nonneg_of_le (fun pair => abs_nonneg _)
    (fun pair => by simpa only [kernel, mul_assoc] using row_abs_le nu x zeroRow pair.1 pair.2)

theorem row_summable (nu : Viscosity) (x : ComplexVorticityHilbertState) (zeroRow : x 0 = 0) :
    Summable fun pair : IntegerWavevector × IntegerWavevector => HeatPrimitive.row nu pair.1 pair.2 x :=
  summable_abs_iff.mp (row_abs_summable nu x zeroRow)

def value (nu : Viscosity) (x : ComplexVorticityHilbertState) : Real :=
  ∑' pair : IntegerWavevector × IntegerWavevector, HeatPrimitive.row nu pair.1 pair.2 x

theorem value_eq_iterated (nu : Viscosity) (x : ComplexVorticityHilbertState) (zeroRow : x 0 = 0) :
    value nu x = ∑' p, ∑' q, HeatPrimitive.row nu p q x :=
  (row_summable nu x zeroRow).tsum_prod

end
end SaturationMonoid.NavierStokes.HeatWholeWork
