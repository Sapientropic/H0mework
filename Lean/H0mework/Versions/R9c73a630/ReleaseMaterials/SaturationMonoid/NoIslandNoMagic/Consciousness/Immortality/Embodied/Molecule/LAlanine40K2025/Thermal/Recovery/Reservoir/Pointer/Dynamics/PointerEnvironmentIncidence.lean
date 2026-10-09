import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PurePointerPreparation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerFreeContinuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Quantum.GibbsEntropyDisposition

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Environment

open scoped Matrix ComplexOrder
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def incidence : ((ι ⊕ ι) × κ) ≃ ((ι × κ) ⊕ (ι × κ)) where
  toFun x := x.1.elim (fun i => Sum.inl (i, x.2)) (fun i => Sum.inr (i, x.2))
  invFun := Sum.elim (fun x => (Sum.inl x.1, x.2)) (fun x => (Sum.inr x.1, x.2))
  left_inv x := by rcases x with ⟨i, a⟩; cases i <;> rfl
  right_inv x := by cases x <;> rfl

def reframe (M : Matrix ((ι × κ) ⊕ (ι × κ)) ((ι × κ) ⊕ (ι × κ)) ℂ) :
    Matrix ((ι ⊕ ι) × κ) ((ι ⊕ ι) × κ) ℂ := M.submatrix incidence incidence

def reframeUnitary (U : Matrix.unitaryGroup ((ι × κ) ⊕ (ι × κ)) ℂ) :
    Matrix.unitaryGroup ((ι ⊕ ι) × κ) ℂ :=
  ⟨reframe U, by
    rw [Unitary.mem_iff]
    change _ᴴ * _ = 1 ∧ _ * _ᴴ = 1
    simp only [reframe, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self,
      Unitary.mul_star_self_of_mem U.property, Matrix.submatrix_one_equiv, and_self]⟩

theorem reframe_conjugation (U : Matrix.unitaryGroup ((ι × κ) ⊕ (ι × κ)) ℂ)
    (M : Matrix ((ι × κ) ⊕ (ι × κ)) ((ι × κ) ⊕ (ι × κ)) ℂ) :
    reframe (Quantum.conjugation U M) = Quantum.conjugation (reframeUnitary U) (reframe M) := by
  simp only [Quantum.conjugation_apply, reframeUnitary, reframe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem prepared_tensor (rho : Matrix ι ι ℂ) (tau : Matrix κ κ ℂ) :
    reframe (prepared (Matrix.kronecker rho tau)) = Matrix.kronecker (prepared rho) tau := by
  ext ⟨i, a⟩ ⟨j, b⟩
  cases i <;> cases j <;>
    simp [reframe, incidence, prepared, Matrix.fromBlocks, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.submatrix]

theorem prepared_conjugation (U : Matrix.unitaryGroup ι ℂ) (rho : Matrix ι ι ℂ) :
    prepared (Quantum.conjugation U rho) =
      Quantum.conjugation (blockUnitary U U) (prepared rho) := by
  simp only [Quantum.conjugation_apply]
  rw [blockUnitary_conjugation_blocks]
  simp [prepared]

theorem conjugation_comp (U V : Matrix.unitaryGroup ι ℂ) (rho : Matrix ι ι ℂ) :
    Quantum.conjugation U (Quantum.conjugation V rho) = Quantum.conjugation (U * V) rho := by
  change (U : Matrix ι ι ℂ) * ((V : Matrix ι ι ℂ) * rho * star (V : Matrix ι ι ℂ)) *
    star (U : Matrix ι ι ℂ) =
    ((U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) * rho *
      star ((U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ))
  simp only [star_mul, Matrix.mul_assoc]

variable [Nonempty κ]

/-- Preparing a pointer retains the old actual action and the same single Gibbs environment. -/
theorem actual_joint_gibbs (rho : Matrix ι ι ℂ) (energies : κ → ℝ) (beta : ℝ)
    (Uold : Matrix.unitaryGroup (ι × κ) ℂ)
    (Unew : Matrix.unitaryGroup ((ι × κ) ⊕ (ι × κ)) ℂ) :
    reframe (Quantum.conjugation Unew
      (prepared (Load.Quantum.unitaryGibbsJoint rho energies beta Uold))) =
    Load.Quantum.unitaryGibbsJoint (prepared rho) energies beta
      (reframeUnitary (Unew * blockUnitary Uold Uold)) := by
  unfold Load.Quantum.unitaryGibbsJoint
  rw [prepared_conjugation, conjugation_comp, reframe_conjugation, prepared_tensor]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Environment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
