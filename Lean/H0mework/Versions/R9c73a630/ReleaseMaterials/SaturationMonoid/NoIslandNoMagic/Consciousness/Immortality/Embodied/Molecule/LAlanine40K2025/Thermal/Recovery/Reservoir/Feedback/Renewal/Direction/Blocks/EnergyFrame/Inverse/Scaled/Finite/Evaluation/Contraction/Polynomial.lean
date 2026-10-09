import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Algebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open scoped Matrix BigOperators
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

theorem power_preserves {label : ι → κ} {A : Matrix ι ι ℂ} (kept : Preserves label A) (n : Nat) :
    Preserves label (A^n) := by
  induction n with
  | zero => simpa only [pow_zero] using preserves_one label
  | succ n ih => rw [pow_succ]; exact preserves_mul ih kept

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem sum_preserves {τ : Type*} (s : Finset τ) (label : ι → κ) (family : τ → Matrix ι ι ℂ)
    (kept : ∀ x ∈ s, Preserves label (family x)) : Preserves label (∑ x ∈ s, family x) := by
  intro i j separated
  simp only [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun x hx => kept x hx i j separated)

theorem polynomial_preserves {label : ι → κ} {A : Matrix ι ι ℂ} (kept : Preserves label A) (N : Nat) :
    Preserves label (Phase.polynomial A N) :=
  sum_preserves (Finset.range N) label _ (fun n _ => preserves_smul (power_preserves kept n) _)

theorem flow_polynomial_preserves {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (time : ℝ) : Preserves label (Phase.flowPolynomial A time) :=
  polynomial_preserves (preserves_smul (preserves_smul kept (-Complex.I)) time) 14

omit [DecidableEq ι] in
theorem sandwich_preserves {label : ι → κ} {A O : Matrix ι ι ℂ}
    (action : Preserves label A) (observable : Preserves label O) : Preserves label (star A*O*A) :=
  preserves_mul (preserves_mul (preserves_star action) observable) action

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
