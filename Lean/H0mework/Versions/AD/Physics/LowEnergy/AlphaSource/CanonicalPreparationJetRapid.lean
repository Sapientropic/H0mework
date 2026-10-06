import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMomentumIntegralBudgets

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumJetDecay
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumMomentumFirst CanonicalPreparationSquareCutoff
open MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap FourierTransform BigOperators

def sourceJetWeight : ℕ → PhysicalMomentum → ℝ
  | 0,p => 1+‖p‖
  | n+1,p => ((1+‖p‖)^n)⁻¹

def sourceJetIntegralBudget (j : ℕ) : ℕ → ℝ
  | 0 => sourceTargetIntegralBound j 0
  | n+1 => 4^n*sourceTargetIntegralBound j (n+1)

theorem sourceJetWeight_nonnegative (n : ℕ) (p : PhysicalMomentum) : 0 ≤ sourceJetWeight n p := by
  cases n <;> simp only [sourceJetWeight] <;> positivity

theorem sourceJetIntegralBudget_nonnegative (j n : ℕ) : 0 ≤ sourceJetIntegralBudget j n := by
  cases n with
  | zero => exact sourceTargetIntegralBound_nonnegative j 0
  | succ n => exact mul_nonneg (by positivity) (sourceTargetIntegralBound_nonnegative j (n+1))

theorem sourceJet_derivative_integral_bound (j n : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ j (sourceMomentumJetSchwartz n p) x‖) ≤
      sourceJetIntegralBudget j n*sourceJetWeight n p := by
  cases n with
  | zero => exact sourceFourierJet_derivative_integral_order_zero j p
  | succ n => simpa only [sourceJetIntegralBudget,sourceJetWeight,div_eq_mul_inv] using
      sourceFourierJet_derivative_integral_order_succ j n p

def sourceRapidJetBound (n : ℕ) : ℝ :=
  2^103*(sourceJetIntegralBudget 0 n+2^104*∑ j∈Finset.range 105,sourceJetIntegralBudget j n)

theorem sourceRapidJetBound_nonnegative (n : ℕ) : 0 ≤ sourceRapidJetBound n := by
  unfold sourceRapidJetBound
  exact mul_nonneg (by positivity) (add_nonneg (sourceJetIntegralBudget_nonnegative 0 n)
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sourceJetIntegralBudget_nonnegative j n)))

theorem partialFourierJet_rapid_bound (n : ℕ) (p k : PhysicalMomentum) :
    (1+‖k‖)^104*‖partialFourierJet n p k‖ ≤ sourceRapidJetBound n*sourceJetWeight n p := by
  have zero : ‖partialFourierJet n p k‖ ≤ sourceJetIntegralBudget 0 n*sourceJetWeight n p := by
    have normBound := VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ PhysicalMomentum) (sourceMomentumJetSchwartz n p) k
    apply normBound.trans
    simpa only [norm_iteratedFDeriv_zero] using sourceJet_derivative_integral_bound 0 n p
  have high : ‖k‖^104*‖partialFourierJet n p k‖ ≤
      2^104*(∑ j∈Finset.range 105,sourceJetIntegralBudget j n)*sourceJetWeight n p := by
    have transformed := Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞)) ((sourceMomentumJetSchwartz n p).smooth ⊤)
      (fun a j _ _ => (sourceMomentumJetSchwartz n p).integrable_pow_mul_iteratedFDeriv volume a j)
      (k := 0) (n := 104) (by simp) (by simp) k
    simp at transformed
    change ‖k‖^104*‖partialFourierJet n p k‖ ≤ _ at transformed
    apply transformed.trans
    have sum := Finset.sum_le_sum (s := Finset.range 105)
      (fun j _ => sourceJet_derivative_integral_bound j n p)
    rw [←Finset.sum_mul] at sum
    exact (mul_le_mul_of_nonneg_left sum (by positivity)).trans_eq (by ring)
  have binomial := add_pow_le (by norm_num : (0 : ℝ)≤1) (norm_nonneg k) 104
  simp only [one_pow] at binomial
  calc
    _ ≤ (2^103*(1+‖k‖^104))*‖partialFourierJet n p k‖ :=
      mul_le_mul_of_nonneg_right binomial (norm_nonneg (partialFourierJet n p k))
    _ = 2^103*(‖partialFourierJet n p k‖+‖k‖^104*‖partialFourierJet n p k‖) := by ring
    _ ≤ 2^103*(sourceJetIntegralBudget 0 n*sourceJetWeight n p+
      2^104*(∑ j∈Finset.range 105,sourceJetIntegralBudget j n)*sourceJetWeight n p) :=
      mul_le_mul_of_nonneg_left (add_le_add zero high) (by positivity)
    _ = _ := by rw [sourceRapidJetBound]; ring

theorem partialFourierJet_decay (n : ℕ) (p k : PhysicalMomentum) :
    ‖partialFourierJet n p k‖ ≤ (sourceRapidJetBound n*sourceJetWeight n p)/(1+‖k‖)^104 := by
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using partialFourierJet_rapid_bound n p k

theorem partialFourierJet_norm_zero (p k : PhysicalMomentum) : ‖partialFourierJet 0 p k‖=‖partialFourier p k‖ := by
  have actual := (continuousMultilinearCurryFin0 ℝ PhysicalMomentum ℂ).norm_map (partialFourierJet 0 p k)
  rw [continuousMultilinearCurryFin0_apply,partialFourierJet_zero_readback] at actual
  exact actual.symm

theorem actual_partialFourier_104_bound (p k : PhysicalMomentum) :
    ‖partialFourier p k‖ ≤ sourceRapidJetBound 0*(1+‖p‖)/(1+‖k‖)^104 := by
  simpa only [partialFourierJet_norm_zero,sourceJetWeight] using partialFourierJet_decay 0 p k

end LowEnergy.PreparationVacuumJetDecay
