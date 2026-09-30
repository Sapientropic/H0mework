import H0mework.Physics.MotherProgrammesFormation.Declarations.Subquotient.Formation

/-! Complete dependent members use the existing higher-law family producer.
No target section, relation compatibility, or new type family enters these
factories. The index and member carriers are the original formed Law. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotient

open scoped Classical

noncomputable section

def Total (material : Material) : Type := Σ index : Base, Fiber material index

def formTotal (material : Material) (index input : Base) : Option (Total material) :=
  (formMember material index input).map (Sigma.mk index)

theorem every_total (material : Material) (target : Total material) :
    ∃ index input : Base, formTotal material index input = some target := by
  rcases target with ⟨index, value⟩
  obtain ⟨input, formed⟩ := every_member material index value
  exact ⟨index, input, congrArg (Option.map (Sigma.mk index)) formed⟩

def pointwiseMember (material operation : Material) (index : Base) :
    Option (Fiber material index) :=
  formMember material index
    (MotherHigherLawValue.readBase (MotherHigherLawFamily.family operation index))

def formSection (material operation : Material) : Option ((index : Base) → Fiber material index) :=
  if total : ∀ index, ∃ value, pointwiseMember material operation index = some value then
    some (fun index => (total index).choose)
  else none

theorem section_sound (material operation : Material)
    (result : (index : Base) → Fiber material index)
    (formed : formSection material operation = some result) :
    ∀ index, pointwiseMember material operation index = some (result index) := by
  unfold formSection at formed
  split at formed
  · rename_i total
    have same := Option.some.inj formed
    intro index
    exact (total index).choose_spec.trans (congrArg some (congrFun same index))
  · cases formed

theorem every_section (material : Material) (target : (index : Base) → Fiber material index) :
    ∃ operation : Material,
      (∀ index, pointwiseMember material operation index = some (target index)) ∧
      formSection material operation = some target := by
  have available (index : Base) : ∃ value : Material,
      formMember material index (MotherHigherLawValue.readBase value) = some (target index) := by
    obtain ⟨input, formed⟩ := every_member material index (target index)
    obtain ⟨value, readValue⟩ := MotherHigherLawValue.readBase_surjective input
    exact ⟨value, (congrArg (formMember material index) readValue).trans formed⟩
  choose values valuesExact using available
  obtain ⟨operation, allValues⟩ := MotherHigherLawFamily.every_family values
  have exactAt (index : Base) : pointwiseMember material operation index = some (target index) := by
    exact (congrArg (fun value => formMember material index (MotherHigherLawValue.readBase value))
      (congrFun allValues index)).trans (valuesExact index)
  have total : ∀ index, ∃ value, pointwiseMember material operation index = some value :=
    fun index => ⟨target index, exactAt index⟩
  refine ⟨operation, exactAt, ?_⟩
  unfold formSection
  rw [dif_pos total]
  apply congrArg some
  funext index
  exact Option.some.inj ((total index).choose_spec.symm.trans (exactAt index))

theorem empty_fibre_rejects (material operation : Material) (index : Base)
    (empty : IsEmpty (Fiber material index)) : formSection material operation = none := by
  unfold formSection
  split
  · rename_i total
    exact (empty.false (total index).choose).elim
  · rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotient
