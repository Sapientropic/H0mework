import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Certificate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Propagation.Interface

private theorem distance_checked (z w : Scalar.QComplex) (paid : Scalar.distance z w ≤ (1/10^24 : ℚ)) :
    ‖Scalar.value z-Scalar.value w‖ ≤ (1/10^24 : ℝ) := by
  have checked := rational_order paid
  norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at checked
  exact (Scalar.value_distance z w).trans (checked.trans (by norm_num))

private theorem square_checked (z w : Scalar.QComplex)
    (paid : Scalar.distance (Scalar.multiply z z) w ≤ (1/10^24 : ℚ)) :
    ‖(Scalar.value z)^2-Scalar.value w‖ ≤ (1/10^24 : ℝ) := by
  rw [pow_two,← Scalar.value_multiply]
  exact distance_checked _ _ paid

set_option exponentiation.threshold 1024 in
private theorem active_power_cap (k : Fin 10) : (1+(2/10^18 : ℝ))^(2^k.val) ≤ 2 := by
  fin_cases k <;> norm_num

private theorem active_error_budget : Power.errorBound (1/10^24 : ℝ) (fun _ => 2) 10 ≤ (2/10^18 : ℝ) := by
  norm_num [Power.errorBound]

private theorem gibbs_error_budget : Power.errorBound (1/10^24 : ℝ) (fun n => (6/5 : ℝ)^(2^n)) 7 ≤ (3/10^12 : ℝ) := by
  norm_num [Power.errorBound]

theorem active_final_error (i : Basis) (M : ActiveMaterial i) :
    ‖(activeInitial i)^1024-Scalar.value (M.rows 10)‖ ≤ (2/10^18 : ℝ) := by
  have sourceSize (k : Fin 10) : ‖(activeInitial i)^(2^k.val)‖ ≤ 2 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (active_initial_norm i M) _).trans (active_power_cap k)
  have rowSize (k : Fin 10) : ‖Scalar.value (M.rows k.castSucc)‖ ≤ 2 := by
    have paid := rational_norm_from_square (M.rows k.castSucc) 2 (by norm_num) (M.stageNorm k.castSucc)
    norm_num at paid
    exact paid
  have bound := Power.squared_history_error 10 (activeInitial i) (fun k => Scalar.value (M.rows k)) (1/10^24) (fun _ => 2)
    (distance_checked _ _ M.seed) (fun k => square_checked _ _ (M.steps k)) sourceSize rowSize
  have final := bound (10 : Fin 11)
  exact final.trans active_error_budget

theorem gibbs_final_error (i : Basis) (M : GibbsMaterial i) :
    ‖(gibbsInitial i)^128-Scalar.value (M.rows 7)‖ ≤ (3/10^12 : ℝ) := by
  have sourceSize (k : Fin 7) : ‖(gibbsInitial i)^(2^k.val)‖ ≤ (6/5 : ℝ)^(2^k.val) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (gibbs_initial_norm i M) _
  have rowSize (k : Fin 7) : ‖Scalar.value (M.rows k.castSucc)‖ ≤ (6/5 : ℝ)^(2^k.val) := by
    have paid := rational_norm_from_l1 (M.rows k.castSucc) ((6/5 : ℚ)^(2^k.val)) (M.stageNorm k.castSucc)
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using paid
  have bound := Power.squared_history_error 7 (gibbsInitial i) (fun k => Scalar.value (M.rows k)) (1/10^24) (fun n => (6/5 : ℝ)^(2^n))
    (distance_checked _ _ M.seed) (fun k => square_checked _ _ (M.steps k)) sourceSize rowSize
  have final := bound (7 : Fin 8)
  exact final.trans gibbs_error_budget

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
