import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussCoframeKinetic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.PreparationActualFactor
open GaussNativeEnergy GaussHistoryHilbert GaussLiveMomentum
open GaussCoreDifferential GaussNativeForm GaussCoframeCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open scoped BigOperators ContDiff

abbrev Cotangent := SourceCoordinateSlice →L[ℝ] ℝ

def coframeMomentum (p : Cotangent) (i : Fin 6) : ℝ := p (coframeDirection i)

def scalarMomentum (z : SourceCoordinateSlice) (p : Cotangent) (a : ScalarIndex) : ℝ :=
  p (direction (scalarDirection a) z)

def electricMomentum (z : SourceCoordinateSlice) (p : Cotangent)
    (i : Fin 3) (a : LieIndex) : ℝ := p (direction (gaugeDirection i a) z)

def scalarNormSquare (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  ∑ a : ScalarIndex, scalarMomentum z p a ^ 2

def electricGram (z : SourceCoordinateSlice) (p : Cotangent) (i j : Fin 3) : ℝ :=
  ∑ a : LieIndex, electricMomentum z p i a * electricMomentum z p j a

def coframeQuadratic (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6,
    GaussCoframeKinetic.coefficient i j z * coframeMomentum p i * coframeMomentum p j

def scalarQuadratic (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  scalarWeight z * scalarNormSquare z p / 2

def gaugeQuadratic (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, gaugeWeight z i j * electricGram z p i j) / 2

def nativePrincipal (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  coframeQuadratic z p + scalarQuadratic z p + gaugeQuadratic z p

-- The scalar Gram is the original full 70-direction contraction. The gauge
-- Gram uses the basis already present in the native quadratic action.
def A (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  coframeQuadratic z p / sourceTime 0 - scalarNormSquare z p / (2 * volume z)

def S (z : SourceCoordinateSlice) (p : Cotangent) (k l : Fin 3) : ℝ :=
  sourceSigma * volume z *
    ∑ i : Fin 3, ∑ j : Fin 3,
      triadInverse z.1 i k * electricGram z p i j * triadInverse z.1 j l

def T (z : SourceCoordinateSlice) (p : Cotangent) : ℝ := ∑ k : Fin 3, S z p k k

theorem electricGram_symmetric (z : SourceCoordinateSlice) (p : Cotangent) (i j : Fin 3) :
    electricGram z p i j = electricGram z p j i := by
  unfold electricGram
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem S_symmetric (z : SourceCoordinateSlice) (p : Cotangent) (k l : Fin 3) :
    S z p k l = S z p l k := by
  unfold S
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [electricGram_symmetric z p j i]
  ring

theorem T_trace_native (z : SourceCoordinateSlice) (p : Cotangent) :
    T z p = sourceSigma * volume z *
      ∑ i : Fin 3, ∑ j : Fin 3, inverseSpatial z i j * electricGram z p i j := by
  unfold T S inverseSpatial
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gaugeQuadratic_trace (z : SourceCoordinateSlice) (p : Cotangent) :
    gaugeQuadratic z p = T z p / (2 * sourceTime 0) := by
  rw [T_trace_native]
  unfold gaugeQuadratic gaugeWeight
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem nativePrincipal_original_coefficients (z : physicalChart) (p : Cotangent) :
    nativePrincipal z.val p = sourceTime 0 * A z.val p + T z.val p / (2 * sourceTime 0) := by
  rw [nativePrincipal, gaugeQuadratic_trace]
  unfold A scalarQuadratic scalarWeight
  have n := source_time_nonzero
  have v := (volume_pos z).ne'
  field_simp
  ring

def positiveCone : Set (SourceCoordinateSlice × Cotangent) :=
  {zp | zp.1 ∈ physicalChart ∧ 0 < A zp.1 zp.2 ∧ 0 < T zp.1 zp.2}

def C (z : SourceCoordinateSlice) (p : Cotangent) : ℝ := Real.sqrt (T z p / (2 * A z p))

def h2 (z : SourceCoordinateSlice) (p : Cotangent) : ℝ := T z p / C z p

def principalFactor (z : SourceCoordinateSlice) (p : Cotangent) : ℝ := Real.sqrt (h2 z p)

theorem C_positive {zp : SourceCoordinateSlice × Cotangent} (cone : zp ∈ positiveCone) :
    0 < C zp.1 zp.2 :=
  Real.sqrt_pos.mpr (div_pos cone.2.2 (mul_pos (by norm_num) cone.2.1))

theorem C_equation {zp : SourceCoordinateSlice × Cotangent} (cone : zp ∈ positiveCone) :
    2 * A zp.1 zp.2 * C zp.1 zp.2 ^ 2 = T zp.1 zp.2 := by
  rw [C, Real.sq_sqrt (div_pos cone.2.2 (mul_pos (by norm_num) cone.2.1)).le]
  field_simp [(ne_of_gt cone.2.1)]

def timelikePrincipal (z : SourceCoordinateSlice) (p : Cotangent) (n : ℝ)
    (b : Fin 3 → ℝ) : ℝ :=
  n * A z p +
    (n^2 * T z p - ∑ i : Fin 3, ∑ j : Fin 3, b i * S z p i j * b j) /
      (2 * n * (n^2 - ∑ i : Fin 3, b i^2))

theorem zero_shift_principal (z : SourceCoordinateSlice) (p : Cotangent)
    (n : ℝ) (nonzero : n ≠ 0) :
    timelikePrincipal z p n 0 = n * A z p + T z p / (2*n) := by
  simp only [timelikePrincipal, Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  congr 1
  field_simp

theorem principal_clock_energy {zp : SourceCoordinateSlice × Cotangent}
    (cone : zp ∈ positiveCone) : timelikePrincipal zp.1 zp.2 (C zp.1 zp.2) 0 = h2 zp.1 zp.2 := by
  have c := (C_positive cone).ne'
  have relation := C_equation cone
  rw [zero_shift_principal _ _ _ c, h2]
  field_simp
  nlinarith

theorem principal_clock_force {zp : SourceCoordinateSlice × Cotangent}
    (cone : zp ∈ positiveCone) :
    HasDerivAt (fun n => timelikePrincipal zp.1 zp.2 n 0) 0 (C zp.1 zp.2) := by
  have c := (C_positive cone).ne'
  have relation := C_equation cone
  have derivative := ((hasDerivAt_id (C zp.1 zp.2)).mul_const (A zp.1 zp.2)).add
    ((hasDerivAt_const (C zp.1 zp.2) (T zp.1 zp.2)).div
      ((hasDerivAt_const (C zp.1 zp.2) (2 : ℝ)).mul (hasDerivAt_id (C zp.1 zp.2)))
        (mul_ne_zero (by norm_num) c))
  have zero : A zp.1 zp.2 +
      (0 * (2 * C zp.1 zp.2) - T zp.1 zp.2 * (0 * C zp.1 zp.2 + 2 * 1)) /
        (2 * C zp.1 zp.2)^2 = 0 := by
    field_simp
    nlinarith
  have normalized : HasDerivAt (fun n => n * A zp.1 zp.2 + T zp.1 zp.2/(2*n))
      0 (C zp.1 zp.2) := by
    simpa only [Pi.mul_apply,id_eq,one_mul,zero] using! derivative
  apply normalized.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds c] with n hn
  exact zero_shift_principal _ _ _ hn

theorem h2_positive {zp : SourceCoordinateSlice × Cotangent} (cone : zp ∈ positiveCone) :
    0 < h2 zp.1 zp.2 := div_pos cone.2.2 (C_positive cone)

theorem principalFactor_square {zp : SourceCoordinateSlice × Cotangent}
    (cone : zp ∈ positiveCone) : principalFactor zp.1 zp.2 ^ 2 = h2 zp.1 zp.2 :=
  Real.sq_sqrt (h2_positive cone).le

-- This native operator consumer reads the actual lower principal before any
-- clock substitution. Connection and weighted density terms remain in the
-- original operators; vanishing value only isolates their first-order symbol.
theorem original_momentum_principal (v : Ambient) (f : QuantumTest)
    (z : SourceCoordinateSlice) (zeroValue : f z = 0) :
    covariantMomentum v f z = (-Complex.I) • fderiv ℝ f z (direction v z) := by
  rw [covariantMomentum_apply, zeroValue, map_zero, add_zero]
  rfl

end LowEnergy.PreparationActualFactor
