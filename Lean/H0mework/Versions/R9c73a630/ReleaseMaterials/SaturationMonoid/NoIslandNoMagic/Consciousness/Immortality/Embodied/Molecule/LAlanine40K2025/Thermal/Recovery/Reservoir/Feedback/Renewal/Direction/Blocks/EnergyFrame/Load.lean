import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Tensor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Powered.Dynamics Load.Source
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem reindexed_commute {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (A B : Matrix κ κ ℂ) (commute : Commute A B) :
    Commute (A.submatrix e e) (B.submatrix e e) := by
  show _*_ = _*_
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,commute.eq]

theorem controller_environment_invariant (U : Matrix.unitaryGroup Basis ℂ) :
    Quantum.conjugation (spectatorFrame (κ := Fin 2) (controllerFrame U)) loadInteraction = loadInteraction := by
  let paired := (Quantum.localUnitary U U : JointMatrix Basis)
  let e := Equiv.prodAssoc (Basis × Basis) (Fin 2) (Fin 2)
  have frameValue : (spectatorFrame (κ := Fin 2) (controllerFrame U) : LoadedJoint) =
      (Matrix.kronecker paired (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).submatrix e e := by
    ext i j
    rcases i with ⟨⟨a,c⟩,v⟩
    rcases j with ⟨⟨b,d⟩,w⟩
    simp only [spectatorFrame,controllerFrame,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply,Matrix.one_apply,Equiv.prodAssoc_apply,Prod.mk.injEq,paired,e]
    split_ifs <;> simp_all
  have commute : Commute (spectatorFrame (κ := Fin 2) (controllerFrame U) : LoadedJoint) loadInteraction := by
    rw [frameValue]
    exact reindexed_commute e _ _ (one_tensor_commutes paired controllerEnvironmentExchange)
  rw [Quantum.conjugation_apply,commute.eq,Matrix.mul_assoc,
    Unitary.mul_star_self_of_mem (spectatorFrame (κ := Fin 2) (controllerFrame U)).property,Matrix.mul_one]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
