import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
open scoped Matrix BigOperators
noncomputable section
variable {ι κ : Type*}

theorem restriction_one [DecidableEq ι] (label : ι → κ) (k : κ) :
    restrict label k (1 : Matrix ι ι ℂ)=1 := by
  ext i j
  simp only [restrict,Matrix.submatrix_apply,Matrix.one_apply,Subtype.val_inj]

theorem restriction_sub (label : ι → κ) (k : κ) (A B : Matrix ι ι ℂ) :
    restrict label k (A-B)=restrict label k A-restrict label k B := rfl

theorem restriction_smul (label : ι → κ) (k : κ) (A : Matrix ι ι ℂ) (c : ℂ) :
    restrict label k (c • A)=c • restrict label k A := rfl

theorem restriction_sum {τ : Type*} (label : ι → κ) (k : κ) (s : Finset τ) (family : τ → Matrix ι ι ℂ) :
    restrict label k (∑ x ∈ s, family x)=∑ x ∈ s, restrict label k (family x) := by
  ext i j
  simp only [restrict,Matrix.submatrix_apply,Matrix.sum_apply]

theorem restriction_pullback [Fintype ι] [DecidableEq κ] {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (O : Matrix ι ι ℂ) (k : κ) :
    restrict label k (star A*O*A)=star (restrict label k A)*restrict label k O*restrict label k A := by
  rw [Matrix.star_eq_conjTranspose,restrict_mul_right kept,restrict_mul (preserves_star kept),restrict_star,Matrix.star_eq_conjTranspose]

theorem restriction_pow [Fintype ι] [DecidableEq ι] [DecidableEq κ] {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (k : κ) (n : Nat) :
    restrict label k (A^n)=(restrict label k A)^n := by
  induction n with
  | zero => rw [pow_zero,pow_zero,restriction_one]
  | succ n ih => rw [pow_succ,pow_succ,restrict_mul (power_preserves kept n),ih]

theorem restriction_polynomial [Fintype ι] [DecidableEq ι] [DecidableEq κ] {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (k : κ) (N : Nat) :
    restrict label k (Phase.polynomial A N)=Phase.polynomial (restrict label k A) N := by
  rw [Phase.polynomial,restriction_sum,Phase.polynomial]
  apply Finset.sum_congr rfl
  intro n _
  rw [restriction_smul,restriction_pow kept]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Contraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
