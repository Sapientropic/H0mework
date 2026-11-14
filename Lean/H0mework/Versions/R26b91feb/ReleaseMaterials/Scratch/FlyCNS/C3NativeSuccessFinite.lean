import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativePrecision

set_option autoImplicit false
namespace FlyCNS.C3NativePrecision
open C3FiniteOccurrence C3NativeMinimum

abbrev Successful (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :=
  {state : Carrier boundary installed anchor // ∃ current,state.val=.ok current}

def successfulAddress {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Successful boundary installed anchor) : Option (Fin (stateBound boundary anchor)) :=
  (encode state.val).getLeft?

private theorem has_success_address {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (state : Successful boundary installed anchor) : ∃ address,encode state.val=.inl address := by
  rcases state.property with ⟨current,success⟩
  cases encoded:encode state.val with
  | inl address => exact ⟨address,rfl⟩
  | inr why =>
    have retained:=forget_encode state.val
    rw [encoded] at retained
    change Sum.inr why=key state.val.val at retained
    rw [success] at retained
    contradiction

theorem successfulAddress_injective {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary} :
    Function.Injective (successfulAddress (boundary:=boundary) (installed:=installed) (anchor:=anchor)) := by
  intro left right same
  rcases has_success_address left with ⟨first,firstIs⟩
  rcases has_success_address right with ⟨second,secondIs⟩
  have addresses:first=second := by
    simpa only [successfulAddress,firstIs,secondIs,Sum.getLeft?_inl,Option.some.injEq] using same
  apply Subtype.ext
  apply finite_key_injective
  rw [firstIs,secondIs,addresses]

theorem finite_successful_carrier (boundary : Boundary) (installed : Installed boundary) (anchor : Anchor boundary) :
    Finite (Successful boundary installed anchor) :=
  Finite.of_injective successfulAddress successfulAddress_injective

end FlyCNS.C3NativePrecision
