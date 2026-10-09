import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.LiftResponse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def twoBlockEmbedding : (Matrix ι ι ℂ × Matrix ι ι ℂ) →⋆ₐ[ℂ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := Matrix.fromBlocks_one
  map_add' A B := by ext i j; cases i <;> cases j <;> simp
  map_mul' A B := by rw [Matrix.fromBlocks_multiply]; simp
  commutes' c := by ext i j; cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one,Matrix.one_apply]
  map_star' A := by simp only [Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]; rfl

theorem two_block_norm (A B : Matrix ι ι ℂ) : ‖Matrix.fromBlocks A 0 0 B‖ ≤ max ‖A‖ ‖B‖ :=
  NonUnitalStarAlgHom.norm_apply_le twoBlockEmbedding (A,B)

theorem block_unitary_star (U V : Matrix.unitaryGroup ι ℂ) :
    star (blockUnitary U V)=blockUnitary (star U) (star V) := by
  apply Subtype.ext
  simp only [blockUnitary,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]

theorem block_observable_response (U V : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    ‖Quantum.conjugation (star (blockUnitary U V)) (pointerDiagonal O)-pointerDiagonal O‖ ≤
      max ‖Quantum.conjugation (star U) O-O‖ ‖Quantum.conjugation (star V) O-O‖ := by
  rw [block_unitary_star]
  have same : Quantum.conjugation (blockUnitary (star U) (star V)) (pointerDiagonal O)-pointerDiagonal O=
      Matrix.fromBlocks (Quantum.conjugation (star U) O-O) 0 0 (Quantum.conjugation (star V) O-O) := by
    change (blockUnitary (star U) (star V) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*Matrix.fromBlocks O 0 0 O*
      star (blockUnitary (star U) (star V) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)-Matrix.fromBlocks O 0 0 O = _
    rw [blockUnitary_conjugation_blocks]
    ext i j
    cases i <;> cases j <;> simp [Quantum.conjugation_apply]
  rw [same]
  exact two_block_norm _ _

attribute [local irreducible] Sectors.pcObservable numericLoadPC loadInteraction Current.loadPulse

theorem original_pointer_load_response (time : ℝ) :
    ‖Quantum.conjugation (star (loadPulse time)) Sectors.pointerPCObservable-Sectors.pointerPCObservable‖ ≤
    |time| * (‖loadInteraction*numericLoadPC-numericLoadPC*loadInteraction‖+(252/10^12 : ℝ)) := by
  have paid := block_observable_response (Current.loadPulse time) (freePhase time • Current.loadPulse time) Sectors.pcObservable
  rw [star_smul,Resource.unitPhase_conjugation,max_self] at paid
  have source := paid.trans (original_body_load_response time)
  unfold loadPulse Sectors.pointerPCObservable
  unfold pointerDiagonal at source
  exact source

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
