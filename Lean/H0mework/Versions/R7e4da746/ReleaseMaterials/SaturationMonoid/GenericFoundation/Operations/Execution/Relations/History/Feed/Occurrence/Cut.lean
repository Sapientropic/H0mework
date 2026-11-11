import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Step

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement

universe u
variable {Sorts : Type u} {Value Var : Sorts → Type u}
variable [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {raw last : Expr Value Var sort}

/-- A cut of one paid Trace preserves the typed Step and both surrounding executions. -/
structure AtStep (trace : Trace environment raw last) (position : Nat) where
  entry : Expr Value Var sort
  exit : Expr Value Var sort
  past : Trace environment raw entry
  step : Step environment entry exit
  future : Trace environment exit last
  trace_eq : past.append (.cons step future) = trace
  position_eq : past.length = position

def atStep : {raw last : Expr Value Var sort} → (trace : Trace environment raw last) →
    (position : Nat) → position < trace.length → AtStep trace position
  | _, _, .nil _, position, bound => False.elim (Nat.not_lt_zero position bound)
  | _, _, .cons step future, 0, _ => ⟨_, _, .nil _, step, future, rfl, rfl⟩
  | _, _, .cons step future, position + 1, bound =>
    let later := atStep future position (by
      simp only [Trace.length] at bound
      omega)
    ⟨later.entry, later.exit, .cons step later.past, later.step, later.future,
      congrArg (Trace.cons step) later.trace_eq, by
        simp only [Trace.length, later.position_eq]
        omega⟩

/-- Recover the original typed cut from the existing paid relation address. -/
def paidCut (trace : Trace environment raw last) (index : Fin (words trace).length) :
    AtStep trace index.val :=
  atStep trace index.val (complete_steps trace ▸ index.isLt)

theorem paidCut_word (trace : Trace environment raw last) (index : Fin (words trace).length) :
    let cut := paidCut trace index
    (stepOccurrence trace index).word =
      relation (R := ℤ) environment (.inl ⟨cut.entry, cut.exit, cut.step.toDerivation⟩) := by
  let cut := paidCut trace index
  let current := relation (R := ℤ) environment (.inl ⟨cut.entry, cut.exit, cut.step.toDerivation⟩)
  have complete := congrArg (fun trace : Trace environment raw last => words trace) cut.trace_eq
  have written : words cut.past ++ current :: words cut.future = words trace := by
    rw [words_append, words] at complete
    exact complete
  have position : (words cut.past).length = index.val := (complete_steps cut.past).trans cut.position_eq
  have atAddress : (words trace)[index.val]? = some current := by
    have zero : index.val - (words cut.past).length = 0 := Nat.sub_eq_zero_of_le position.ge
    calc
      _ = (words cut.past ++ current :: words cut.future)[index.val]? :=
        congrArg (fun sequence : List (Formal ℤ Value Var sort) => sequence[index.val]?) written.symm
      _ = _ := by rw [List.getElem?_append_right position.le, zero, List.getElem?_cons_zero]
  rw [List.getElem?_eq_getElem index.isLt] at atAddress
  exact (stepOccurrence_word trace index).trans (Option.some.inj atAddress)

/-- An actual relation slot of a paid exposure resolves to the original Step address. -/
structure ReadStep (trace : Trace environment raw last) (position : Nat)
    (word : Formal ℤ Value Var sort) where
  index : Fin (words trace).length
  position_eq : position = 1 + index.val
  word_eq : (stepOccurrence trace index).word = word

def readStep (trace : Trace environment raw last) (position : Nat)
    (word : Formal ℤ Value Var sort)
    (actual : (exposure trace).trace[position]? = some (.relation word)) :
    ReadStep trace position word := by
  have read :
      (PresentedRelationEventAt.generator raw :: (words trace).map PresentedRelationEventAt.relation)[position]? =
        some (.relation word) := by
    change (PresentedRelationEventAt.generator raw ::
      RootedAccountedUnfolding.traceBranches (events trace))[position]? = some (.relation word) at actual
    rw [events_trace] at actual
    exact actual
  cases position with
  | zero =>
    have impossible : PresentedRelationEventAt.generator raw = .relation word := Option.some.inj read
    cases impossible
  | succ position =>
    change ((words trace).map PresentedRelationEventAt.relation)[position]? = some (.relation word) at read
    rw [List.getElem?_map] at read
    cases present : (words trace)[position]? with
    | none => simp only [present, Option.map_none, reduceCtorEq] at read
    | some current =>
      have inside : position < (words trace).length :=
        (List.getElem?_eq_some_iff.mp present).elim (fun bound _ => bound)
      have address : (words trace).get ⟨position, inside⟩ = current :=
        Option.some.inj ((List.getElem?_eq_getElem inside).symm.trans present)
      have actualWord : PresentedRelationEventAt.relation current = .relation word :=
        Option.some.inj (by simpa only [present, Option.map_some] using read)
      exact ⟨⟨position, inside⟩, Nat.add_comm position 1,
        (stepOccurrence_word trace ⟨position, inside⟩).trans
          (address.trans (PresentedRelationEventAt.relation.inj actualWord))⟩

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
