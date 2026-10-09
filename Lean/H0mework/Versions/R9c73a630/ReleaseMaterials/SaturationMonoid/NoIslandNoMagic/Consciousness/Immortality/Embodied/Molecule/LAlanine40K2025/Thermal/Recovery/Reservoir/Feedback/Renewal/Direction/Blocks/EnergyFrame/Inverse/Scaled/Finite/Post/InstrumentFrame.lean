import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Pointer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem body_conjugation {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ) (A : Matrix (ι × κ) (ι × κ) ℂ) :
    Quantum.conjugation (Incidence.localLift U V) (Incidence.bodyObservable A)=
      Incidence.bodyObservable (Quantum.conjugation U A) := by
  change Quantum.conjugation (Incidence.regroupUnitary (Load.Quantum.localUnitary U V))
    ((Matrix.kronecker A (1 : Matrix ι ι ℂ)).submatrix Incidence.bodyReservoir Incidence.bodyReservoir)=_
  rw [Incidence.regroup_conjugation]
  change (Load.Quantum.localConjugation U V (Matrix.kronecker A (1 : Matrix ι ι ℂ))).submatrix
    Incidence.bodyReservoir Incidence.bodyReservoir=_
  rw [Load.Quantum.localConjugation_tensor]
  have one : Quantum.conjugation V (1 : Matrix ι ι ℂ)=1 := map_one (Unitary.conjStarAlgAut ℂ _ V)
  rw [one]
  rfl

theorem restored_root_calculated (R : LoadedJoint) :
    Quantum.conjugation Supply.installedFullFrame (SquareRoot.bodyRoot R)=
      Incidence.bodyObservable (Quantum.conjugation numericFree R) := by
  rw [Supply.installed_full_frame_local,SquareRoot.bodyRoot,body_conjugation,SquareRoot.restoreRoot,Supply.conjugation_undo]

theorem raw_dilation_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) :
    Quantum.conjugation (blockUnitary U U) (SquareRoot.rawDilation A B)=
      SquareRoot.rawDilation (Quantum.conjugation U A) (Quantum.conjugation U B) := by
  simp only [SquareRoot.raw_dilation_read]
  change (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)*Matrix.fromBlocks A (-B) B A*
    star (blockUnitary U U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)=_
  rw [blockUnitary_conjugation_blocks]
  ext i j
  cases i <;> cases j <;> simp [Quantum.conjugation_apply]

def calculatedSourcePointer : PointerJoint := Quantum.conjugation pointerFrame SquareRoot.Full.sourcePointer

attribute [local irreducible] SquareRoot.Full.sourceRoot SquareRoot.Full.sourceComplement

theorem original_source_pointer_coordinates : calculatedSourcePointer=
    SquareRoot.rawDilation (Incidence.bodyObservable (Quantum.conjugation numericFree SquareRoot.Full.sourceRoot))
      (Incidence.bodyObservable (Quantum.conjugation numericFree SquareRoot.Full.sourceComplement)) := by
  change Quantum.conjugation (blockUnitary Supply.installedFullFrame Supply.installedFullFrame)
    (SquareRoot.rawDilation (SquareRoot.bodyRoot SquareRoot.Full.sourceRoot) (SquareRoot.bodyRoot SquareRoot.Full.sourceComplement))=_
  rw [raw_dilation_conjugation,restored_root_calculated,restored_root_calculated]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
