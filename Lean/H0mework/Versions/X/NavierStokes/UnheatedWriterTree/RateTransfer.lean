import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RateChange

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeRateTransfer
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTreeTime NativeUnheatedTreeRateChange NativeUnheatedTriadKernel
noncomputable section
variable {nu : Viscosity} {n : ℕ}

theorem cross_bound (first last : IntegerWavevector) :
    |crossRate nu first last| ≤ NativeUnheatedStressPairEvolution.decay nu first last := by
  have row (coordinate : Coordinate) : |(first coordinate : ℝ)*(last coordinate : ℝ)| ≤
      ((first coordinate : ℝ)^2+(last coordinate : ℝ)^2)/2 := by
    apply (abs_le).mpr
    constructor <;> nlinarith [sq_nonneg ((first coordinate : ℝ)+(last coordinate : ℝ)),
      sq_nonneg ((first coordinate : ℝ)-(last coordinate : ℝ))]
  have sumBound : |∑ coordinate : Coordinate, (first coordinate : ℝ)*(last coordinate : ℝ)| ≤
      ((∑ coordinate : Coordinate, (first coordinate : ℝ)^2)+
        ∑ coordinate : Coordinate, (last coordinate : ℝ)^2)/2 := by
    calc
      _ ≤ ∑ coordinate : Coordinate, |(first coordinate : ℝ)*(last coordinate : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ coordinate : Coordinate, ((first coordinate : ℝ)^2+(last coordinate : ℝ)^2)/2 :=
        Finset.sum_le_sum fun coordinate _ => row coordinate
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [crossRate, abs_mul, abs_of_pos (show 0 < 2*nu.coeff*(2*Real.pi)^2 by positivity [nu.coeff_pos])]
  exact (mul_le_mul_of_nonneg_left sumBound (by positivity [nu.coeff_pos])).trans_eq (by
    unfold NativeUnheatedStressPairEvolution.decay integerWaveViscousMultiplier integerWaveNormSq
    ring)

def ratio (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) : ℝ :=
  crossRate nu inside ((nodes leaf).1-inside)*
    (sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf p q inside))⁻¹

theorem ratio_bound (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) :
    |ratio (nu := nu) nodes leaf p q inside| ≤ 1 := by
  have lower : NativeUnheatedStressPairEvolution.decay nu inside ((nodes leaf).1-inside) ≤
      sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf p q inside) := by
    have other : 0 ≤ ∑ number : Fin n, integerWaveViscousMultiplier (nodes (leaf.succAbove number)).1 :=
      Finset.sum_nonneg fun number _ => multiplier_nonnegative _
    unfold sumRate NativeUnheatedTreeLeaf.slots NativeUnheatedStressPairEvolution.decay
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    nlinarith only [mul_nonneg nu.coeff_pos.le other]
  have nonnegative := NativeUnheatedTreeOutput.rate_nonnegative (nu := nu) (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)
  rw [ratio, abs_mul, abs_of_nonneg (inv_nonneg.mpr nonnegative)]
  by_cases zero : sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf p q inside) = 0
  · rw [zero, inv_zero, mul_zero]
    norm_num
  · exact ((mul_le_mul_of_nonneg_right ((cross_bound (nu := nu) inside ((nodes leaf).1-inside)).trans lower)
      (inv_nonneg.mpr nonnegative)).trans_eq (mul_inv_cancel₀ zero)).trans le_rfl

theorem normalizer_transfer (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (z : ℂ)
    (p q : Coordinate) (inside : IntegerWavevector) :
    NativeUnheatedTreeNormalForm.normalizer nu (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)
      (NativeUnheatedTreeLeaf.kernel z nodes leaf p q) =
    (1+ratio (nu := nu) nodes leaf p q inside) •
      NativeUnheatedTreeLeaf.kernel (NativeUnheatedTreeNormalForm.normalizer nu nodes z) nodes leaf p q := by
  by_cases oldZero : sumRate nu nodes = 0
  · have parent := NativeUnheatedTreeOutput.rate_zero_wave nodes oldZero leaf
    simp only [NativeUnheatedTreeLeaf.kernel, parent, pressure_zero, mul_zero,
      NativeUnheatedTreeNormalForm.normalizer, smul_zero]
  have difference := normalizer_commutator (nu := nu) nodes leaf z p q inside
  have rearranged : (-(crossRate nu inside ((nodes leaf).1-inside))*
      (sumRate nu nodes*sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf p q inside))⁻¹) •
        NativeUnheatedTreeLeaf.kernel z nodes leaf p q =
      -(ratio (nu := nu) nodes leaf p q inside) •
        NativeUnheatedTreeLeaf.kernel (NativeUnheatedTreeNormalForm.normalizer nu nodes z) nodes leaf p q := by
    simp only [NativeUnheatedTreeLeaf.kernel, NativeUnheatedTreeNormalForm.normalizer,
      smul_mul_assoc, smul_smul, ratio, mul_inv_rev]
    congr 1
    ring
  rw [rearranged] at difference
  rw [neg_smul] at difference
  rw [add_smul, one_smul]
  linear_combination -difference

theorem transfer_nonnegative (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) :
    0 ≤ 1+ratio (nu := nu) nodes leaf p q inside ∧ 1+ratio (nu := nu) nodes leaf p q inside ≤ 2 := by
  have paid := (abs_le.mp (ratio_bound (nu := nu) nodes leaf p q inside))
  constructor <;> linarith

theorem primitive_transfer (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (z : ℂ) (p q : Coordinate) (inside : IntegerWavevector) (time : ℝ) :
    NativeUnheatedTreeNormalForm.primitive seed (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)
      (NativeUnheatedTreeLeaf.kernel z nodes leaf p q) time =
    (1+ratio (nu := nu) nodes leaf p q inside) •
      NativeUnheatedTreeLeaf.term seed nodes (NativeUnheatedTreeNormalForm.normalizer nu nodes z) leaf p q inside time := by
  rw [NativeUnheatedTreeLeaf.term_product]
  unfold NativeUnheatedTreeNormalForm.primitive
  rw [normalizer_transfer, smul_mul_assoc]

theorem window_transfer (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (z : ℂ) (p q : Coordinate) (inside : IntegerWavevector) (order : ℕ) (observation : ℝ) :
    (∫ sample in Set.Icc (0 : ℝ) (observation+2), NativeUnheatedStressPairEvolution.kernelWeight order observation 0 sample •
      NativeUnheatedTreeNormalForm.primitive seed (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)
        (NativeUnheatedTreeLeaf.kernel z nodes leaf p q) sample) =
    (1+ratio (nu := nu) nodes leaf p q inside) •
      ∫ sample in Set.Icc (0 : ℝ) (observation+2), NativeUnheatedStressPairEvolution.kernelWeight order observation 0 sample •
        NativeUnheatedTreeLeaf.term seed nodes (NativeUnheatedTreeNormalForm.normalizer nu nodes z) leaf p q inside sample := by
  simp_rw [primitive_transfer, smul_comm (NativeUnheatedStressPairEvolution.kernelWeight order observation 0 _)]
  exact MeasureTheory.integral_smul _ _

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeRateTransfer
