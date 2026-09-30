import H0mework.Versions.X.NavierStokes.HigherTreeOctic.TemporalResponse
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticThetaGram
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTreeTime NativeUnheatedTreeRateChange
noncomputable section
variable {nu : Viscosity} {n : ℕ}

def rate (nu : Viscosity) (wave : IntegerWavevector) : ℝ := nu.coeff*integerWaveViscousMultiplier wave
def damping (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) : ℝ :=
  ∑ position : Fin n, rate nu (nodes (leaf.succAbove position)).1

theorem rate_nonnegative (wave : IntegerWavevector) : 0 ≤ rate nu wave :=
  mul_nonneg nu.coeff_pos.le (NativeUnheatedTriadKernel.multiplier_nonnegative wave)

theorem damping_nonnegative (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) : 0 ≤ damping (nu := nu) nodes leaf :=
  Finset.sum_nonneg fun _ _ => rate_nonnegative _

theorem splitRate_original (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) :
    NativeUnheatedOcticTemporalResponse.splitRate (nu := nu) nodes leaf p q inside =
      damping (nu := nu) nodes leaf+rate nu inside+rate nu ((nodes leaf).1-inside) := by
  unfold NativeUnheatedOcticTemporalResponse.splitRate sumRate NativeUnheatedTreeLeaf.slots damping rate
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
  ring

def kernel (nu : Viscosity) (rest : ℝ) (first last : IntegerWavevector) : ℝ :=
  crossRate nu first last*(rest+rate nu first+rate nu last)⁻¹

theorem ratio_original (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) :
    NativeUnheatedTreeRateTransfer.ratio (nu := nu) nodes leaf p q inside =
      kernel nu (damping (nu := nu) nodes leaf) inside ((nodes leaf).1-inside) := by
  unfold NativeUnheatedTreeRateTransfer.ratio kernel
  rw [← splitRate_original nodes leaf p q inside]
  rfl

private theorem cross_le_rate (first last : IntegerWavevector) :
    |crossRate nu first last| ≤ rate nu first+rate nu last := by
  simpa only [NativeUnheatedStressPairEvolution.decay, mul_add, rate] using
    NativeUnheatedTreeRateTransfer.cross_bound (nu := nu) first last

private theorem zero_cross (rest : ℝ) (nonnegative : 0 ≤ rest) (first last : IntegerWavevector)
    (zero : rest+rate nu first+rate nu last=0) : crossRate nu first last=0 := by
  have paid := cross_le_rate (nu := nu) first last
  exact abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg _))

theorem kernel_bound (rest : ℝ) (nonnegative : 0 ≤ rest) (first last : IntegerWavevector) :
    |kernel nu rest first last| ≤ 1 := by
  have total0 : 0 ≤ rest+rate nu first+rate nu last :=
    add_nonneg (add_nonneg nonnegative (rate_nonnegative first)) (rate_nonnegative last)
  unfold kernel
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr total0)]
  by_cases zero : rest+rate nu first+rate nu last=0
  · simp only [zero, inv_zero, mul_zero, zero_le_one]
  · exact (mul_le_mul_of_nonneg_right ((cross_le_rate (nu := nu) first last).trans (by linarith))
      (inv_nonneg.mpr total0)).trans_eq (mul_inv_cancel₀ zero)

def feature (nu : Viscosity) (rest : ℝ) (wave : IntegerWavevector) (direction : Coordinate) (auxiliary : ℝ) : ℝ :=
  Real.sqrt (2*nu.coeff*(2*Real.pi)^2)*(wave direction : ℝ)*Real.exp (-(rest/2+rate nu wave)*auxiliary)

theorem feature_product (rest : ℝ) (first last : IntegerWavevector) (auxiliary : ℝ) :
    (∑ direction : Coordinate, feature nu rest first direction auxiliary*feature nu rest last direction auxiliary) =
      crossRate nu first last*Real.exp (-(rest+rate nu first+rate nu last)*auxiliary) := by
  have pair (direction : Coordinate) : feature nu rest first direction auxiliary*feature nu rest last direction auxiliary =
      (2*nu.coeff*(2*Real.pi)^2)*((first direction : ℝ)*(last direction : ℝ))*
        Real.exp (-(rest+rate nu first+rate nu last)*auxiliary) := by
    unfold feature
    calc
      _ = Real.sqrt (2*nu.coeff*(2*Real.pi)^2)^2*((first direction : ℝ)*(last direction : ℝ))*
          (Real.exp (-(rest/2+rate nu first)*auxiliary)*Real.exp (-(rest/2+rate nu last)*auxiliary)) := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity [nu.coeff_pos]), ← Real.exp_add]; congr 2; ring
  simp only [pair, ← Finset.sum_mul, ← Finset.mul_sum, crossRate]

theorem gram_integrable (rest : ℝ) (nonnegative : 0 ≤ rest) (first last : IntegerWavevector) :
    Integrable (fun auxiliary => ∑ direction : Coordinate,
      feature nu rest first direction auxiliary*feature nu rest last direction auxiliary) (volume.restrict (Ioi 0)) := by
  simp only [feature_product]
  by_cases zero : rest+rate nu first+rate nu last=0
  · simp [zero_cross rest nonnegative first last zero]
  · have positive : 0 < rest+rate nu first+rate nu last := lt_of_le_of_ne
      (add_nonneg (add_nonneg nonnegative (rate_nonnegative first)) (rate_nonnegative last)) (Ne.symm zero)
    exact (integrableOn_exp_mul_Ioi (by linarith : -(rest+rate nu first+rate nu last)<0) 0).const_mul _

theorem laplace_gram (rest : ℝ) (nonnegative : 0 ≤ rest) (first last : IntegerWavevector) :
    (∫ auxiliary in Ioi (0 : ℝ), ∑ direction : Coordinate,
      feature nu rest first direction auxiliary*feature nu rest last direction auxiliary) = kernel nu rest first last := by
  simp only [feature_product, kernel]
  by_cases zero : rest+rate nu first+rate nu last=0
  · simp only [zero_cross rest nonnegative first last zero, zero_mul, integral_zero]
  · have positive : 0 < rest+rate nu first+rate nu last := lt_of_le_of_ne
      (add_nonneg (add_nonneg nonnegative (rate_nonnegative first)) (rate_nonnegative last)) (Ne.symm zero)
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(rest+rate nu first+rate nu last)<0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp

theorem ratio_gram (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) :
    NativeUnheatedTreeRateTransfer.ratio (nu := nu) nodes leaf p q inside =
      ∫ auxiliary in Ioi (0 : ℝ), ∑ direction : Coordinate,
        feature nu (damping (nu := nu) nodes leaf) inside direction auxiliary*
          feature nu (damping (nu := nu) nodes leaf) ((nodes leaf).1-inside) direction auxiliary := by
  rw [ratio_original, laplace_gram _ (damping_nonnegative nodes leaf)]

theorem diagonal_nonnegative (rest : ℝ) (nonnegative : 0 ≤ rest) (wave : IntegerWavevector) :
    0 ≤ kernel nu rest wave wave := by
  rw [← laplace_gram rest nonnegative wave wave]
  exact integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem diagonal_formula (rest : ℝ) (wave : IntegerWavevector) :
    kernel nu rest wave wave = 2*rate nu wave/(rest+2*rate nu wave) := by
  have cross : crossRate nu wave wave = 2*rate nu wave := by
    unfold crossRate rate integerWaveViscousMultiplier integerWaveNormSq
    simp only [pow_two]
    ring
  unfold kernel
  rw [cross, show rest+rate nu wave+rate nu wave=rest+2*rate nu wave by ring]
  rfl

theorem finite_gram (rest : ℝ) (nonnegative : 0 ≤ rest) (observed : Finset IntegerWavevector) (coefficient : IntegerWavevector → ℝ) :
    (∑ first ∈ observed, ∑ last ∈ observed, coefficient first*kernel nu rest first last*coefficient last) =
      ∫ auxiliary in Ioi (0 : ℝ), ∑ direction : Coordinate,
        (∑ wave ∈ observed, coefficient wave*feature nu rest wave direction auxiliary)^2 := by
  have paid (first last : IntegerWavevector) :=
    ((gram_integrable (nu := nu) rest nonnegative first last).const_mul (coefficient first)).mul_const (coefficient last)
  calc
    _ = ∫ auxiliary in Ioi (0 : ℝ), ∑ first ∈ observed, ∑ last ∈ observed,
        coefficient first*(∑ direction : Coordinate,
          feature nu rest first direction auxiliary*feature nu rest last direction auxiliary)*coefficient last := by
      rw [integral_finsetSum observed (fun first _ => integrable_finsetSum observed (fun last _ => paid first last))]
      apply Finset.sum_congr rfl
      intro first _
      rw [integral_finsetSum observed (fun last _ => paid first last)]
      apply Finset.sum_congr rfl
      intro last _
      rw [integral_mul_const, integral_const_mul, laplace_gram rest nonnegative first last]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun auxiliary => by
        symm
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro first _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro last _
        exact Finset.sum_congr rfl fun direction _ => by ring

theorem finite_positive (rest : ℝ) (nonnegative : 0 ≤ rest) (observed : Finset IntegerWavevector) (coefficient : IntegerWavevector → ℝ) :
    0 ≤ ∑ first ∈ observed, ∑ last ∈ observed, coefficient first*kernel nu rest first last*coefficient last := by
  rw [finite_gram rest nonnegative observed coefficient]
  exact integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem primitive_gram (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (z : ℂ) (p q : Coordinate) (inside : IntegerWavevector) (time : ℝ) :
    NativeUnheatedTreeNormalForm.primitive seed (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)
      (NativeUnheatedTreeLeaf.kernel z nodes leaf p q) time =
    (1+∫ auxiliary in Ioi (0 : ℝ), ∑ direction : Coordinate,
      feature nu (damping (nu := nu) nodes leaf) inside direction auxiliary*
        feature nu (damping (nu := nu) nodes leaf) ((nodes leaf).1-inside) direction auxiliary) •
      NativeUnheatedTreeLeaf.term seed nodes (NativeUnheatedTreeNormalForm.normalizer nu nodes z) leaf p q inside time := by
  rw [NativeUnheatedTreeRateTransfer.primitive_transfer, ratio_gram nodes leaf p q inside]

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticThetaGram
