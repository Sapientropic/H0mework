import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Scalar

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Power

def errorBound (epsilon : ℝ) (cap : ℕ → ℝ) : ℕ → ℝ
  | 0 => epsilon
  | n+1 => 2*cap n*errorBound epsilon cap n+epsilon

theorem square_error (z w : ℂ) : ‖z^2-w^2‖ ≤ (‖z‖+‖w‖)*‖z-w‖ := by
  rw [show z^2-w^2=(z+w)*(z-w) by ring,norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le z w) (norm_nonneg (z-w))

theorem power_twice (z : ℂ) (k : ℕ) : z^(2^(k+1))=(z^(2^k))^2 := by
  rw [pow_succ,pow_mul]

theorem squared_history_error (N : ℕ) (z : ℂ) (rows : Fin (N+1) → ℂ) (epsilon : ℝ) (cap : ℕ → ℝ)
    (seed : ‖z-rows 0‖ ≤ epsilon)
    (step : ∀ k : Fin N, ‖(rows k.castSucc)^2-rows k.succ‖ ≤ epsilon)
    (actualSize : ∀ k : Fin N, ‖z^(2^k.val)‖ ≤ cap k.val)
    (rowSize : ∀ k : Fin N, ‖rows k.castSucc‖ ≤ cap k.val) :
    ∀ k : Fin (N+1), ‖z^(2^k.val)-rows k‖ ≤ errorBound epsilon cap k.val := by
  have induction : ∀ n (hn : n ≤ N), ‖z^(2^n)-rows ⟨n,Nat.lt_succ_of_le hn⟩‖ ≤ errorBound epsilon cap n := by
    intro n
    induction n with
    | zero =>
      intro hn
      have index : (⟨0,Nat.lt_succ_of_le hn⟩ : Fin (N+1))=0 := by apply Fin.ext; simp
      rw [index]
      simpa only [pow_zero,pow_one,errorBound] using seed
    | succ n ih =>
      intro hn
      have small : n < N := Nat.lt_of_succ_le hn
      have previous := ih (Nat.le_of_lt small)
      let k : Fin N := ⟨n,small⟩
      have actual := actualSize k
      have rounded := rowSize k
      have nonnegative : 0 ≤ cap n := (norm_nonneg (z^(2^n))).trans actual
      have square := square_error (z^(2^n)) (rows k.castSucc)
      have budget := mul_le_mul (add_le_add actual rounded) previous (norm_nonneg (z^(2^n)-rows k.castSucc))
        (by linarith : 0 ≤ cap n+cap n)
      have triangle := norm_sub_le_norm_sub_add_norm_sub ((z^(2^n))^2) ((rows k.castSucc)^2) (rows k.succ)
      rw [power_twice]
      calc
        _ ≤ (cap n+cap n)*errorBound epsilon cap n+epsilon := triangle.trans (add_le_add (square.trans budget) (step k))
        _ = errorBound epsilon cap (n+1) := by rw [errorBound]; ring
  intro k
  exact induction k.val (Nat.le_of_lt_succ k.isLt)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Power
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
