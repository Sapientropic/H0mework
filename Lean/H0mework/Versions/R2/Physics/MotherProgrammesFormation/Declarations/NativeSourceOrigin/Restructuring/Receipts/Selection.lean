import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory
open scoped Classical
noncomputable section

def subtypeAddress {I : Type} (index : I ↪ B) (P : I → Prop) : {i // P i} ↪ B :=
  (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : {i // P i} ↪ I).trans index

theorem every_selection {I : Type} (index : I ↪ B) (P : I → Prop) :
    ∃ material : M, ∀ i, bit material 0 (index i) ↔ P i := by
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective
    (fun code _ => if ∃ i, index i = code ∧ P i then 0 else 1)
  refine ⟨material, fun i => ?_⟩
  simp only [bit, hm, ite_eq_left_iff, one_ne_zero, imp_false, not_not]
  constructor
  · rintro ⟨j, same, member⟩
    exact index.injective same ▸ member
  · exact fun member => ⟨i, rfl, member⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
