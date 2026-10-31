import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

universe u v

/-- Restrict a finite receipt encoding through its stored metadata. This
inverts no world-ledger evolution and makes no choice of a source child. -/
def recoverAttached {Old : Type u} {New : Type v} (entries : List Old)
    (image : {old // old ∈ entries} → New) (read : New → Option Old)
    (readImage : ∀ old, read (image old) = some old.val)
    (value : New) (member : value ∈ entries.attach.map image) :
    {old : {old // old ∈ entries} // image old = value} := by
  have present : (read value).isSome := by
    obtain ⟨old,_,same⟩ := List.mem_map.mp member
    rw [← same,readImage]
    rfl
  let old := (read value).get present
  have belongs : old ∈ entries := by
    obtain ⟨actual,_,same⟩ := List.mem_map.mp member
    have actualRead := readImage actual
    rw [same] at actualRead
    have equal : old = actual.val := Option.some.inj ((Option.some_get present).trans actualRead)
    exact equal ▸ actual.property
  refine ⟨⟨old,belongs⟩,?_⟩
  obtain ⟨actual,_,same⟩ := List.mem_map.mp member
  have actualRead := readImage actual
  rw [same] at actualRead
  have equal : old = actual.val := Option.some.inj ((Option.some_get present).trans actualRead)
  have indices : (⟨old,belongs⟩ : {old // old ∈ entries}) = actual := Subtype.ext equal
  exact (congrArg image indices).trans same

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
