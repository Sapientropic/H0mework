import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.GlobalIntegral
import H0mework.Versions.X.NavierStokes.StressEvolutionUnfiltered.Interpolation
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RateTransfer

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticTemporalResponse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeWholeH1Pairing
open NativeUnheatedTreeTime NativeUnheatedPairNegativeKernel NativeUnheatedGlobalNegativeOne
noncomputable section
variable {nu : Viscosity} {n : ℕ}

def splitRate (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate)
    (inside : IntegerWavevector) : ℝ :=
  sumRate nu (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)

theorem split_lower (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate)
    (inside : IntegerWavevector) :
    NativeUnheatedStressPairEvolution.decay nu inside ((nodes leaf).1-inside) ≤
      splitRate (nu := nu) nodes leaf p q inside := by
  have other : 0 ≤ ∑ number : Fin n, integerWaveViscousMultiplier (nodes (leaf.succAbove number)).1 :=
    Finset.sum_nonneg fun number _ => NativeUnheatedTriadKernel.multiplier_nonnegative _
  unfold splitRate sumRate NativeUnheatedTreeLeaf.slots NativeUnheatedStressPairEvolution.decay
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  nlinarith only [mul_nonneg nu.coeff_pos.le other]

def kernel (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate)
    (first last : IntegerWavevector) : ℝ :=
  root first * root last * (splitRate (nu := nu) nodes leaf p q first)⁻¹

theorem kernel_bound (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate)
    (inside : IntegerWavevector) :
    ‖kernel (nu := nu) nodes leaf p q inside ((nodes leaf).1-inside)‖ ≤ (2*nu.coeff)⁻¹ := by
  have nonnegative := NativeUnheatedTreeOutput.rate_nonnegative (nu := nu)
    (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)
  change 0 ≤ splitRate (nu := nu) nodes leaf p q inside at nonnegative
  have roots : 2*root inside*root ((nodes leaf).1-inside) ≤
      integerWaveViscousMultiplier inside+integerWaveViscousMultiplier ((nodes leaf).1-inside) := by
    nlinarith [sq_nonneg (root inside-root ((nodes leaf).1-inside)), root_sq inside, root_sq ((nodes leaf).1-inside)]
  have paid := split_lower (nu := nu) nodes leaf p q inside
  unfold NativeUnheatedStressPairEvolution.decay at paid
  have product : (2*nu.coeff)*(root inside*root ((nodes leaf).1-inside)) ≤
      splitRate (nu := nu) nodes leaf p q inside := by
    nlinarith [mul_le_mul_of_nonneg_left roots nu.coeff_pos.le]
  rw [kernel, Real.norm_of_nonneg (by positivity [root_nonnegative inside, root_nonnegative ((nodes leaf).1-inside)])]
  by_cases zero : splitRate (nu := nu) nodes leaf p q inside = 0
  · rw [zero, inv_zero, mul_zero]; positivity [nu.coeff_pos]
  · rw [mul_inv_le_iff₀ (lt_of_le_of_ne nonnegative (Ne.symm zero))]
    have divided : root inside*root ((nodes leaf).1-inside) ≤
        splitRate (nu := nu) nodes leaf p q inside/(2*nu.coeff) :=
      (le_div_iff₀ (show 0 < 2*nu.coeff by positivity [nu.coeff_pos])).mpr (by nlinarith only [product])
    exact divided.trans_eq (by ring)

def bilinear (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate) :
    State →L[ℝ] State →L[ℝ] ℂ :=
  -((NativeUnheatedPairKernelBilinear.bilinear (kernel (nu := nu) nodes leaf p q)
    (nodes leaf).1 q p (2*nu.coeff)⁻¹ (kernel_bound nodes leaf p q)).bilinearComp
      wholeVelocityCLM wholeVelocityCLM)

theorem bilinear_apply (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate)
    (left right : State) :
    bilinear (nu := nu) nodes leaf p q left right = ∑' inside,
      kernel (nu := nu) nodes leaf p q inside ((nodes leaf).1-inside) •
        (wholeVelocity left inside p*wholeVelocity right ((nodes leaf).1-inside) q) := by
  change -(-∑' inside, _) = _
  rw [neg_neg]
  rfl

theorem bilinear_bound (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate)
    (left right : State) :
    ‖bilinear (nu := nu) nodes leaf p q left right‖ ≤ (3*(2*nu.coeff)⁻¹)*‖left‖*‖right‖ := by
  change ‖-NativeUnheatedPairKernelBilinear.value _ _ _ _ _ _‖ ≤ _
  rw [norm_neg]
  apply (NativeUnheatedPairKernelBilinear.norm_bound _ _ _ _ _ (kernel_bound nodes leaf p q) _ _).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (wholeVelocity_norm_le left) (by positivity [nu.coeff_pos]))
    (wholeVelocity_norm_le right) (norm_nonneg _) (by positivity [nu.coeff_pos])

theorem restored_row (nodes : Fin (n+1) → Slot) (leaf : Fin (n+1)) (p q : Coordinate)
    (left right : State) (inside : IntegerWavevector) :
    kernel (nu := nu) nodes leaf p q inside ((nodes leaf).1-inside) •
      (wholeVelocity (inverseGradient left) inside p*wholeVelocity (inverseGradient right) ((nodes leaf).1-inside) q) =
    (splitRate (nu := nu) nodes leaf p q inside)⁻¹ •
      (wholeVelocity left inside p*wholeVelocity right ((nodes leaf).1-inside) q) := by
  by_cases firstZero : inside = 0
  · subst inside; simp [wholeVelocity_zero]
  by_cases lastZero : (nodes leaf).1-inside = 0
  · simp [lastZero, wholeVelocity_zero]
  rw [inverse_row, inverse_row]
  simp only [kernel, Pi.smul_apply, Complex.real_smul]
  push_cast
  field_simp [(root_positive inside firstZero).ne', (root_positive ((nodes leaf).1-inside) lastZero).ne']

def response (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (time : ℝ) : ℂ :=
  bilinear (nu := nu) nodes leaf p q (state seed time) (state seed time)

theorem response_original (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (time : ℝ) :
    response seed nodes leaf p q time = ∑' inside,
      (splitRate (nu := nu) nodes leaf p q inside)⁻¹ •
        (NativeUnheatedTriadRows.velocity seed time inside p*
          NativeUnheatedTriadRows.velocity seed time ((nodes leaf).1-inside) q) := by
  simp only [response, bilinear_apply, state, restored_row, NativeUnheatedTriadRows.velocity_original]

theorem response_summable (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (p q : Coordinate) (time : ℝ) :
    Summable (fun inside => (splitRate (nu := nu) nodes leaf p q inside)⁻¹ •
      (NativeUnheatedTriadRows.velocity seed time inside p*
        NativeUnheatedTriadRows.velocity seed time ((nodes leaf).1-inside) q)) := by
  have paid := NativeUnheatedPairKernelBilinear.summable_pair (kernel (nu := nu) nodes leaf p q)
    (nodes leaf).1 q p (2*nu.coeff)⁻¹ (kernel_bound nodes leaf p q)
    (wholeVelocity (state seed time)) (wholeVelocity (state seed time))
  simpa only [state, restored_row, NativeUnheatedTriadRows.velocity_original] using paid

theorem primitive_fiber (seed : GeneratedWholeRestartCurrent nu) (nodes : Fin (n+1) → Slot)
    (leaf : Fin (n+1)) (z : ℂ) (p q : Coordinate) (time : ℝ) :
    (∑' inside, NativeUnheatedTreeNormalForm.primitive seed (NativeUnheatedTreeLeaf.slots nodes leaf p q inside)
      (NativeUnheatedTreeLeaf.kernel z nodes leaf p q) time) =
    NativeUnheatedTreeLeaf.kernel z nodes leaf p q*response seed nodes leaf p q time*
      NativeUnheatedTreeLeaf.remaining (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) nodes leaf := by
  rw [response_original, ← tsum_mul_left, ← tsum_mul_right]
  apply tsum_congr
  intro inside
  rw [NativeUnheatedTreeNormalForm.primitive_original, ← NativeUnheatedTreeLeaf.term_product]
  simp only [NativeUnheatedTreeLeaf.term, NativeUnheatedTreeLeaf.raw, splitRate,
    NativeUnheatedTriadRows.velocity_original, Complex.real_smul]
  ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticTemporalResponse
