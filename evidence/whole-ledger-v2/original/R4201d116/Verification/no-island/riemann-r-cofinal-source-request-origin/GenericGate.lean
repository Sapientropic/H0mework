import SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Origin

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalSourceRequestOriginCertificate

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement

namespace F
export SourceInventoryExecutionFeed
  (Event Inventory Request eventItems requestsFrom requests readRequestOrigin relation_support_request)
end F

private abbrev Values : Unit → Type := fun _ => ℤ
private abbrev Vars : Unit → Type := fun _ => Unit
private abbrev Term := Expr Values Vars ()
private abbrev Word := Formal ℤ Values Vars ()
private abbrev Event := F.Event (V := Values) (X := Vars) (s := ())
private abbrev Request := F.Request (V := Values) (X := Vars) (s := ())
private def firstTerm : Term := .var ()
private def secondTerm : Term := .const 0

private theorem terms_distinct : firstTerm ≠ secondTerm := by
  intro same
  change ((.var ()) : Term) = .const 0 at same
  cases same

private def singleWord : Word := Finsupp.single firstTerm 2
private def repeatedEvents : List Event := [.relation singleWord, .relation singleWord]
private def repeatedRequests : List Request := F.requestsFrom 7 repeatedEvents

private theorem singleton_item : F.eventItems (.relation singleWord) = [(firstTerm,2)] := by
  classical
  simp only [F.eventItems, Coefficients.sourceItems, singleWord,
    Finsupp.support_single firstTerm (by decide : (2 : ℤ) ≠ 0), Finset.toList_singleton,
    List.map_cons, Finsupp.single_eq_same, List.map_nil]

private theorem repeated_layout :
    repeatedRequests =
      [⟨7, .relation singleWord, firstTerm, 2⟩, ⟨8, .relation singleWord, firstTerm, 2⟩] := by
  simp only [repeatedRequests, repeatedEvents, F.requestsFrom, singleton_item,
    List.map_cons, List.map_nil, List.singleton_append, List.append_nil]

private def firstOrdinal : Fin repeatedRequests.length := ⟨0, by rw [repeated_layout]; decide⟩
private def secondOrdinal : Fin repeatedRequests.length := ⟨1, by rw [repeated_layout]; decide⟩

private theorem repeated_first_position : (repeatedRequests.get firstOrdinal).position = 7 := by
  have first : repeatedRequests[0]? = some (⟨7,.relation singleWord,firstTerm,2⟩ : Request) :=
    (congrArg (fun entries : List Request => entries[0]?) repeated_layout).trans rfl
  exact congrArg (fun request : Request => request.position)
    (Option.some.inj ((List.getElem?_eq_getElem firstOrdinal.isLt).symm.trans first))

private theorem repeated_second_position : (repeatedRequests.get secondOrdinal).position = 8 := by
  have second : repeatedRequests[1]? = some (⟨8,.relation singleWord,firstTerm,2⟩ : Request) :=
    (congrArg (fun entries : List Request => entries[1]?) repeated_layout).trans rfl
  exact congrArg (fun request : Request => request.position)
    (Option.some.inj ((List.getElem?_eq_getElem secondOrdinal.isLt).symm.trans second))

run_cmd IO.eprintln "CP530_CONTROL - equal_source_events_keep_distinct_ordinals"
theorem equal_source_events_keep_distinct_ordinals :
    let first := F.readRequestOrigin 7 repeatedEvents firstOrdinal
    let second := F.readRequestOrigin 7 repeatedEvents secondOrdinal
    first.eventIndex.val = 0 ∧ second.eventIndex.val = 1 ∧
    first.eventIndex ≠ second.eventIndex := by
  let first := F.readRequestOrigin 7 repeatedEvents firstOrdinal
  let second := F.readRequestOrigin 7 repeatedEvents secondOrdinal
  have left : 7 = 7 + first.eventIndex.val :=
    repeated_first_position.symm.trans (congrArg (fun request : Request => request.position) first.request_eq)
  have right : 8 = 7 + second.eventIndex.val :=
    repeated_second_position.symm.trans (congrArg (fun request : Request => request.position) second.request_eq)
  have leftIndex : first.eventIndex.val = 0 :=
    Nat.add_left_cancel (left.symm.trans (Nat.add_zero 7).symm)
  have rightIndex : second.eventIndex.val = 1 :=
    Nat.add_left_cancel (right.symm.trans (show 7+1 = 8 from rfl).symm)
  exact ⟨leftIndex, rightIndex, fun equal =>
    Nat.zero_ne_one (leftIndex.symm.trans ((congrArg Fin.val equal).trans rightIndex))⟩

private def dualWord : Word := Finsupp.single firstTerm 2 + Finsupp.single secondTerm (-3)
private def dualStock : F.Inventory (V := Values) (X := Vars) (s := ()) := .zero (.relation dualWord)
private def dualRequests : List Request := F.requests dualStock

private theorem first_coefficient : dualWord firstTerm = 2 := by
  simp only [dualWord, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne terms_distinct, add_zero]

private theorem second_coefficient : dualWord secondTerm = -3 := by
  simp only [dualWord, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne terms_distinct.symm, zero_add]

private theorem actual_item (term : Term) (present : dualWord term ≠ 0) :
    ∃ ordinal : Fin dualRequests.length,
      (dualRequests.get ordinal).expression = term ∧
      (dualRequests.get ordinal).coefficient = dualWord term := by
  have source : (.relation dualWord : Event) ∈ dualStock.trace := List.mem_cons_self
  obtain ⟨request,member,expr,coefficient⟩ :=
    F.relation_support_request dualStock dualWord source term (Finsupp.mem_support_iff.mpr present)
  obtain ⟨ordinal,found⟩ := List.mem_iff_get.mp member
  exact ⟨ordinal, (congrArg (fun r : Request => r.expression) found).trans expr,
    (congrArg (fun r : Request => r.coefficient) found).trans coefficient⟩

private def originItem (ordinal : Fin dualRequests.length) : Term × ℤ :=
  let found := F.readRequestOrigin 0 dualStock.trace ordinal
  (F.eventItems (dualStock.trace.get found.eventIndex)).get found.itemIndex

private theorem originItem_exact (ordinal : Fin dualRequests.length) :
    originItem ordinal = ((dualRequests.get ordinal).expression, (dualRequests.get ordinal).coefficient) :=
  (congrArg (fun request : Request => (request.expression,request.coefficient))
    (F.readRequestOrigin 0 dualStock.trace ordinal).request_eq).symm

run_cmd IO.eprintln "CP530_CONTROL - swapped_support_coefficients_rejected"
theorem swapped_support_coefficients_rejected :
    ∃ first second : Fin dualRequests.length,
      originItem first = (firstTerm,2) ∧ originItem second = (secondTerm,-3) ∧
      (originItem first).1 ≠ (originItem second).1 ∧
      (dualRequests.get first).coefficient ≠ (originItem second).2 := by
  obtain ⟨i, iTerm, iCoeff⟩ := actual_item firstTerm (by rw [first_coefficient]; decide)
  obtain ⟨j, jTerm, jCoeff⟩ := actual_item secondTerm (by rw [second_coefficient]; decide)
  have iValue := iCoeff.trans first_coefficient
  have jValue := jCoeff.trans second_coefficient
  have iItem : originItem i = (firstTerm,2) := (originItem_exact i).trans (Prod.ext iTerm iValue)
  have jItem : originItem j = (secondTerm,-3) := (originItem_exact j).trans (Prod.ext jTerm jValue)
  refine ⟨i,j,iItem,jItem,?_,?_⟩
  · rw [iItem,jItem]
    exact terms_distinct
  · rw [iValue,jItem]
    decide

end CofinalSourceRequestOriginCertificate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
