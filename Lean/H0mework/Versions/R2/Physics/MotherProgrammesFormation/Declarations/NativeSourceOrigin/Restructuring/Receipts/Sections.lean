import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts.NativeSection
open MotherNetworkFactory
open scoped Classical
noncomputable section

variable {I : Type} {F : I → Type} (index : I ↪ B) (member : ∀ i, F i ↪ B)

def Check (material : M) : Prop := ∀ i, ∃! value : F i, r2 material 0 (index i) (member i value)

def form (material : M) : Option ((i : I) → F i) :=
  if checked : Check index member material then some (fun i => Classical.choose (checked i)) else none

theorem every_section (original : (i : I) → F i) :
    ∃ material : M, form index member material = some original := by
  obtain ⟨material, hm⟩ := every_binary_graph 0 (fun input output => ∃ i, index i = input ∧ member i (original i) = output)
  have at_graph (i : I) (value : F i) : r2 material 0 (index i) (member i value) ↔ value = original i := by
    rw [hm]
    constructor
    · rintro ⟨j, indexEq, valueEq⟩
      have same := index.injective indexEq
      cases same
      exact (member i).injective valueEq.symm
    · intro same
      cases same
      exact ⟨i, rfl, rfl⟩
  have checked : Check index member material := fun i =>
    ⟨original i, (at_graph i _).mpr rfl, fun value selected => (at_graph i value).mp selected⟩
  refine ⟨material, ?_⟩
  simp only [form, dif_pos checked]
  congr 1
  funext i
  exact (at_graph i _).mp (Classical.choose_spec (checked i)).1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts.NativeSection
