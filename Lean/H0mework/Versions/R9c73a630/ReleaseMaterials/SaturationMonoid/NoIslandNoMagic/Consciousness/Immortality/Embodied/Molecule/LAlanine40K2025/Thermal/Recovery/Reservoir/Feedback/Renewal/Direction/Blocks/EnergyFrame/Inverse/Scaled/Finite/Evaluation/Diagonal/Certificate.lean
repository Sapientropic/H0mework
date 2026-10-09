import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Power

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Propagation.Interface

structure ActiveMaterial (i : Basis) where
  rows : Fin 11 → Scalar.QComplex
  seed : Scalar.distance (Scalar.polynomial (activeSeed i) 14) (rows 0) ≤ (1/10^24 : ℚ)
  steps : ∀ k : Fin 10, Scalar.distance (Scalar.multiply (rows k.castSucc) (rows k.castSucc)) (rows k.succ) ≤ (1/10^24 : ℚ)
  initialNorm : (rows 0).1^2+(rows 0).2^2 ≤ (1+(1/10^18 : ℚ))^2
  stageNorm : ∀ k : Fin 11, (rows k).1^2+(rows k).2^2 ≤ 4

structure GibbsMaterial (i : Basis) where
  rows : Fin 8 → Scalar.QComplex
  seed : Scalar.distance (Scalar.polynomial (gibbsSeed i) 14) (rows 0) ≤ (1/10^24 : ℚ)
  steps : ∀ k : Fin 7, Scalar.distance (Scalar.multiply (rows k.castSucc) (rows k.castSucc)) (rows k.succ) ≤ (1/10^24 : ℚ)
  initialNorm : |(rows 0).1|+|(rows 0).2| ≤ (119/100 : ℚ)
  stageNorm : ∀ k : Fin 8, |(rows k).1|+|(rows k).2| ≤ (6/5 : ℚ)^(2^k.val)

theorem rational_norm_from_square (z : Scalar.QComplex) (r : ℚ) (positive : 0 ≤ r)
    (square : z.1^2+z.2^2 ≤ r^2) : ‖Scalar.value z‖ ≤ (r : ℝ) := by
  have bound : ((z.1^2+z.2^2 : ℚ) : ℝ) ≤ (r : ℝ)^2 := by exact_mod_cast square
  have pos : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast positive
  rw [← Scalar.value_norm_squared] at bound
  nlinarith [norm_nonneg (Scalar.value z)]

theorem rational_norm_from_l1 (z : Scalar.QComplex) (r : ℚ) (paid : |z.1|+|z.2| ≤ r) :
    ‖Scalar.value z‖ ≤ (r : ℝ) := by
  have bound := Scalar.value_distance z (0,0)
  have read : Scalar.value (0,0)=0 := by simp [Scalar.value]
  rw [read,sub_zero] at bound
  apply bound.trans
  change ((|z.1-0|+|z.2-0| : ℚ) : ℝ) ≤ _
  simp only [sub_zero]
  exact_mod_cast paid

noncomputable def activeInitial (i : Basis) : ℂ := Scalar.value (Scalar.polynomial (activeSeed i) 14)
noncomputable def gibbsInitial (i : Basis) : ℂ := Scalar.value (Scalar.polynomial (gibbsSeed i) 14)

theorem rational_order {a b : ℚ} (paid : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast paid

theorem active_initial_norm (i : Basis) (M : ActiveMaterial i) : ‖activeInitial i‖ ≤ 1+(2/10^18 : ℝ) := by
  have initial := rational_norm_from_square (M.rows 0) (1+1/10^18) (by norm_num) M.initialNorm
  have checked := rational_order M.seed
  norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at checked
  have distance := (Scalar.value_distance (Scalar.polynomial (activeSeed i) 14) (M.rows 0)).trans checked
  have triangle := norm_sub_le_norm_sub_add_norm_sub (activeInitial i) (Scalar.value (M.rows 0)) 0
  simp only [sub_zero] at triangle
  norm_num only [Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at initial
  change ‖activeInitial i-Scalar.value (M.rows 0)‖ ≤ _ at distance
  linarith

theorem gibbs_initial_norm (i : Basis) (M : GibbsMaterial i) : ‖gibbsInitial i‖ ≤ (6/5 : ℝ) := by
  have initial := rational_norm_from_l1 (M.rows 0) (119/100) M.initialNorm
  have checked := rational_order M.seed
  norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at checked
  have distance := (Scalar.value_distance (Scalar.polynomial (gibbsSeed i) 14) (M.rows 0)).trans checked
  have triangle := norm_sub_le_norm_sub_add_norm_sub (gibbsInitial i) (Scalar.value (M.rows 0)) 0
  simp only [sub_zero] at triangle
  norm_num at initial
  change ‖gibbsInitial i-Scalar.value (M.rows 0)‖ ≤ _ at distance
  linarith

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
