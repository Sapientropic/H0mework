import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Exchange
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.BinaryPointerDilation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks

open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

def Preserves (label : ι → κ) (A : Matrix ι ι ℂ) : Prop :=
  ∀ i j, label i ≠ label j → A i j = 0

def restrict (label : ι → κ) (k : κ) (A : Matrix ι ι ℂ) :
    Matrix {i // label i = k} {i // label i = k} ℂ := A.submatrix Subtype.val Subtype.val

def mask (label : ι → κ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if label i = label j then A i j else 0

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem preserves_zero (label : ι → κ) : Preserves label (0 : Matrix ι ι ℂ) := by
  intro i j _
  rfl

omit [Fintype ι] [DecidableEq κ] in
theorem preserves_diagonal (label : ι → κ) (d : ι → ℂ) :
    Preserves label (Matrix.diagonal d) := by
  intro i j separated
  have distinct : i ≠ j := fun same => separated (congrArg label same)
  simp [Matrix.diagonal, distinct]

omit [Fintype ι] [DecidableEq κ] in
theorem preserves_one (label : ι → κ) : Preserves label (1 : Matrix ι ι ℂ) :=
  preserves_diagonal label (fun _ => 1)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem preserves_add {label : ι → κ} {A B : Matrix ι ι ℂ}
    (left : Preserves label A) (right : Preserves label B) : Preserves label (A+B) := by
  intro i j separated
  simp only [Matrix.add_apply, left i j separated, right i j separated, add_zero]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem preserves_sub {label : ι → κ} {A B : Matrix ι ι ℂ}
    (left : Preserves label A) (right : Preserves label B) : Preserves label (A-B) := by
  intro i j separated
  simp only [Matrix.sub_apply, left i j separated, right i j separated, sub_self]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem preserves_neg {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) : Preserves label (-A) := by
  intro i j separated
  simp only [Matrix.neg_apply, kept i j separated, neg_zero]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem preserves_smul {R : Type*} [SMulZeroClass R ℂ] {label : ι → κ}
    {A : Matrix ι ι ℂ} (kept : Preserves label A) (c : R) : Preserves label (c • A) := by
  intro i j separated
  simp only [Matrix.smul_apply, kept i j separated, smul_zero]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem preserves_star {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) : Preserves label Aᴴ := by
  intro i j separated
  simp only [Matrix.conjTranspose_apply, kept j i (Ne.symm separated), star_zero]

omit [DecidableEq ι] in
theorem preserves_mul {label : ι → κ} {A B : Matrix ι ι ℂ}
    (left : Preserves label A) (right : Preserves label B) : Preserves label (A*B) := by
  intro i j separated
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases same : label i = label k
  · rw [right k j (fun equality => separated (same.trans equality)), mul_zero]
  · rw [left i k same, zero_mul]

def projector (label : ι → κ) (k : κ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if label i = k then 1 else 0)

theorem preserves_iff_commute (label : ι → κ) (A : Matrix ι ι ℂ) :
    Preserves label A ↔ ∀ k, Commute (projector label k) A := by
  constructor
  · intro kept k
    change projector label k * A = A * projector label k
    ext i j
    simp only [projector, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases same : label i = label j
    · rw [same]
      split_ifs <;> simp
    · rw [kept i j same]
      simp
  · intro commute i j separated
    have entry := congrArg (fun M : Matrix ι ι ℂ => M i j) (commute (label i)).eq
    simpa [projector, Matrix.diagonal_mul, Matrix.mul_diagonal, Ne.symm separated] using entry

theorem preserves_exp {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) : Preserves label (NormedSpace.exp A) := by
  apply (preserves_iff_commute label _).mpr
  intro k
  exact ((preserves_iff_commute label A).mp kept k).exp_right

theorem preserves_sqrt {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) : Preserves label (CFC.sqrt A) := by
  apply (preserves_iff_commute label _).mpr
  intro k
  rw [CFC.sqrt_eq_cfc]
  exact (((preserves_iff_commute label A).mp kept k).symm.cfc_nnreal NNReal.sqrt).symm

omit [DecidableEq ι] in
theorem energy_ignores_cross {label : ι → κ} {O : Matrix ι ι ℂ}
    (kept : Preserves label O) (rho : Matrix ι ι ℂ) :
    energy O rho = energy O (mask label rho) := by
  unfold energy
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases same : label i = label j
  · simp only [mask, if_pos same.symm]
  · rw [kept i j same]
    simp

omit [DecidableEq ι] in
theorem sum_on_fiber (label : ι → κ) (k : κ) (f : ι → ℂ)
    (support : ∀ i, label i ≠ k → f i = 0) :
    ∑ i, f i = ∑ i : {i // label i = k}, f i := by
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => label i = k), f i := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ outside
      apply support i
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using outside
    _ = _ := Finset.sum_subtype _ (by simp) _

omit [DecidableEq ι] in
theorem restrict_mul {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (B : Matrix ι ι ℂ) (k : κ) :
    restrict label k (A*B) = restrict label k A * restrict label k B := by
  ext i j
  change (∑ x, A i x * B x j) = ∑ x : {x // label x = k}, A i x * B x j
  apply sum_on_fiber
  intro x outside
  rw [kept i x (fun same => outside (same.symm.trans i.property)), zero_mul]

omit [DecidableEq ι] in
theorem restrict_mul_right {label : ι → κ} {B : Matrix ι ι ℂ}
    (kept : Preserves label B) (A : Matrix ι ι ℂ) (k : κ) :
    restrict label k (A*B) = restrict label k A * restrict label k B := by
  ext i j
  change (∑ x, A i x * B x j) = ∑ x : {x // label x = k}, A i x * B x j
  apply sum_on_fiber
  intro x outside
  rw [kept x j (fun same => outside (same.trans j.property)), mul_zero]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem restrict_star (label : ι → κ) (A : Matrix ι ι ℂ) (k : κ) :
    restrict label k Aᴴ = (restrict label k A)ᴴ := rfl

theorem restrict_conjugation {label : ι → κ} (U : Matrix.unitaryGroup ι ℂ)
    (kept : Preserves label (U : Matrix ι ι ℂ)) (rho : Matrix ι ι ℂ) (k : κ) :
    restrict label k (Quantum.conjugation U rho) =
      restrict label k (U : Matrix ι ι ℂ) * restrict label k rho *
        (restrict label k (U : Matrix ι ι ℂ))ᴴ := by
  rw [Quantum.conjugation_apply, Matrix.star_eq_conjTranspose,
    restrict_mul_right (preserves_star kept), restrict_mul kept, restrict_star]

theorem restrict_sqrt {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (positive : A.PosSemidef) (k : κ) :
    restrict label k (CFC.sqrt A) = CFC.sqrt (restrict label k A) := by
  have rootPositive : (restrict label k (CFC.sqrt A)).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).submatrix Subtype.val
  have square : restrict label k (CFC.sqrt A) * restrict label k (CFC.sqrt A) =
      restrict label k A := by
    rw [← restrict_mul (preserves_sqrt kept), CFC.sqrt_mul_sqrt_self A positive.nonneg]
  exact (CFC.sqrt_unique square rootPositive.nonneg).symm

omit [Fintype ι] [DecidableEq ι] in
theorem regroup_eq_blocks {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) :
    Matrix.reindex (Equiv.sigmaFiberEquiv label).symm (Equiv.sigmaFiberEquiv label).symm A =
      Matrix.blockDiagonal' (fun k => restrict label k A) := by
  ext ⟨k,i⟩ ⟨l,j⟩
  change A i j = Matrix.blockDiagonal' (fun k => restrict label k A) ⟨k,i⟩ ⟨l,j⟩
  by_cases same : k = l
  · subst l
    rw [Matrix.blockDiagonal'_apply_eq]
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ same]
    apply kept
    intro equal
    exact same (i.property.symm.trans (equal.trans j.property))

theorem restrict_exp [Fintype κ] {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (k : κ) :
    restrict label k (NormedSpace.exp A) = NormedSpace.exp (restrict label k A) := by
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (Matrix (Σ k, {i // label i = k}) (Σ k, {i // label i = k}) ℂ) :=
    .restrictScalars ℚ ℂ _
  let : ∀ k, NormedAlgebra ℚ (Matrix {i // label i = k} {i // label i = k} ℂ) :=
    fun _ => .restrictScalars ℚ ℂ _
  let equivalence := Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv label).symm
  have mapped := NormedSpace.map_exp equivalence
    equivalence.toLinearEquiv.toContinuousLinearEquiv.continuous A
  change Matrix.reindex (Equiv.sigmaFiberEquiv label).symm
    (Equiv.sigmaFiberEquiv label).symm (NormedSpace.exp A) =
    NormedSpace.exp (Matrix.reindex (Equiv.sigmaFiberEquiv label).symm
      (Equiv.sigmaFiberEquiv label).symm A) at mapped
  rw [regroup_eq_blocks kept, Matrix.exp_blockDiagonal', Pi.exp_def] at mapped
  ext i j
  have entry := congrArg (fun M => M ⟨k,i⟩ ⟨k,j⟩) mapped
  simp only [Matrix.blockDiagonal'_apply_eq] at entry
  change (NormedSpace.exp A) i.val j.val = NormedSpace.exp (restrict label k A) i j at entry
  exact entry

omit [DecidableEq ι] in
theorem energy_eq_sum_restrict [Fintype κ] {label : ι → κ} {O : Matrix ι ι ℂ}
    (kept : Preserves label O) (rho : Matrix ι ι ℂ) :
    energy O rho = ∑ k, energy (restrict label k O) (restrict label k rho) := by
  have trace : (O*rho).trace =
      ∑ k, (restrict label k O * restrict label k rho).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Fintype.sum_fiberwise label (fun i => ∑ j, O i j * rho j i)]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j, O i j * rho j i) = ∑ j : {j // label j = k}, O i j * rho j i
    apply sum_on_fiber
    intro j outside
    rw [kept i j (fun same => outside (same.symm.trans i.property)), zero_mul]
  unfold energy
  rw [trace, Complex.re_sum]

omit [DecidableEq ι] in
theorem trace_eq_sum_restrict [Fintype κ] (label : ι → κ) (rho : Matrix ι ι ℂ) :
    rho.trace = ∑ k, (restrict label k rho).trace := by
  simpa only [Matrix.trace, Matrix.diag, restrict, Matrix.submatrix_apply] using
    (Fintype.sum_fiberwise label (fun i => rho i i)).symm

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem preserves_relabel {δ : Type*} {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (map : κ → δ) : Preserves (map ∘ label) A := by
  intro i j separated
  exact kept i j (fun same => separated (congrArg map same))

section Tensor
variable {α β γ δ : Type*}

theorem preserves_tensor {leftLabel : α → γ} {rightLabel : β → δ}
    {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (left : Preserves leftLabel A) (right : Preserves rightLabel B) :
    Preserves (fun i => (leftLabel i.1, rightLabel i.2)) (Matrix.kronecker A B) := by
  classical
  intro i j separated
  change A i.1 j.1 * B i.2 j.2 = 0
  by_cases same : leftLabel i.1 = leftLabel j.1
  · rw [right i.2 j.2 (fun equal => separated (Prod.ext same equal)), mul_zero]
  · rw [left i.1 j.1 same, zero_mul]

theorem preserves_tensor_left {label : α → γ} {A : Matrix α α ℂ}
    (kept : Preserves label A) (B : Matrix β β ℂ) :
    Preserves (fun i => label i.1) (Matrix.kronecker A B) := by
  intro i j separated
  change A i.1 j.1 * B i.2 j.2 = 0
  rw [kept i.1 j.1 separated, zero_mul]
end Tensor


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
