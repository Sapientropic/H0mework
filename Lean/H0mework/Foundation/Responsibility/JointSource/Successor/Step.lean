import H0mework.Foundation.Responsibility.JointSource.Successor.Source
import H0mework.Foundation.Responsibility.JointSource.Compiler

/-! The actual mathematical action joins any continuing original whole write.
The target owner and complete ledger are generated from that same source receipt. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor
open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure N V} {origin current : V.Current}
variable {registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin}
variable (packet : Packet lower current) (event : EventAt registered current)

abbrev JoinedLaw := Idle.law registered.input.environment registered.input.expression
abbrev sourceSupport := lower.source.source.toRootSource.account.supportOf (lower.emitted current)
abbrev targetSupport := lower.source.source.toRootSource.account.supportOf (lower.emitted packet.targetCurrent)

private def castOwner {source target : N.Support} (same : source = target)
    (owner : OpenResponsibilityAt N source) : OpenResponsibilityAt N target := same ▸ owner

def nextOwner : OpenResponsibilityAt N (targetSupport packet) :=
  castOwner (congrArg (lower.source.source.toRootSource.account.supportOf) packet.target_emitted)
    (packet.ledgerEvolution.destination event.owner).1

private def untransportedWhole :
    LedgerWriteEvolutionAt (ExtendedNetwork N (JoinedLaw (registered := registered)))
      (activeLedger (sourceSupport (lower := lower) (current := current)) event.state)
      (activeLedger (lower.source.source.toRootSource.account.supportOf packet.targetOccurrence) (mathTarget event)) := by
  cases action : mathAction event with
  | inl settled =>
      simpa only [mathTarget, action, JoinedLaw, sourceSupport, Packet.ledgerEvolution, Packet.targetOccurrence] using
        Idle.wholeEvolution packet.ledgerEvolution event.owner event.state settled
  | inr paid =>
      simpa only [mathTarget, action, JoinedLaw, sourceSupport, Packet.ledgerEvolution, Packet.targetOccurrence] using
        jointStepLedgerEvolution (law := JoinedLaw (registered := registered)) packet.ledgerEvolution event.owner paid.2

private def castEvolution {W : WorldRelationNetwork.{u}} {source target actual : W.Support}
    (same : target = actual) (rows : LedgerWriteEvolutionAt W ⟨source⟩ ⟨target⟩) :
    LedgerWriteEvolutionAt W ⟨source⟩ ⟨actual⟩ := same ▸ rows

private def transportedWhole :
    LedgerWriteEvolutionAt (ExtendedNetwork N (JoinedLaw (registered := registered)))
      (activeLedger (sourceSupport (lower := lower) (current := current)) event.state)
      (activeLedger (targetSupport packet) (mathTarget event)) :=
  castEvolution (congrArg (fun occurrence =>
    (lower.source.source.toRootSource.account.supportOf occurrence, some (mathTarget event))) packet.target_emitted)
    (untransportedWhole packet event)

structure JoinedAt : Type u where
  private mk ::
  nextState : SourceOperationExecutionDebt.State registered.input.environment registered.input.expression
  next_state : nextState = mathTarget event
  nextOwner : OpenResponsibilityAt N (targetSupport packet)
  wholeEvolution : LedgerWriteEvolutionAt (ExtendedNetwork N (JoinedLaw (registered := registered)))
    (activeLedger (sourceSupport (lower := lower) (current := current)) event.state)
    (activeLedger (targetSupport packet) nextState)

def join : JoinedAt packet event :=
  ⟨mathTarget event, rfl, nextOwner packet event, transportedWhole packet event⟩

theorem join_next_state : (join packet event).nextState = mathTarget event := rfl
theorem join_next_owner : (join packet event).nextOwner = nextOwner packet event := rfl


/-- The same old whole write at its canonical emitted target. -/
def originalFold : LedgerWriteEvolutionAt N
    ⟨sourceSupport (lower := lower) (current := current)⟩ ⟨targetSupport packet⟩ :=
  castEvolution (congrArg (lower.source.source.toRootSource.account.supportOf) packet.target_emitted)
    packet.ledgerEvolution

private theorem cast_destination_old {scope : DebtActivationLaw.{u}}
    {before after : scope.DebtState} {source target actual : N.Support}
    (same : target = actual)
    (base : LedgerWriteEvolutionAt N ⟨source⟩ ⟨target⟩)
    (whole : LedgerWriteEvolutionAt (ExtendedNetwork N scope)
      (activeLedger source before) (activeLedger target after))
    (square : (entry : OpenResponsibilityAt N source) →
      (whole.destination (oldEntry (law := scope) (state? := some before) entry)).1 =
        oldEntry (law := scope) (state? := some after) (base.destination entry).1)
    (entry : OpenResponsibilityAt N source) :
    ((castEvolution (congrArg (fun support => (support, some after)) same) whole).destination
      (oldEntry (law := scope) (state? := some before) entry)).1 =
        oldEntry (law := scope) (state? := some after) ((castEvolution same base).destination entry).1 := by
  cases same
  exact square entry

private theorem cast_origin_old {scope : DebtActivationLaw.{u}}
    {before after : scope.DebtState} {source target actual : N.Support}
    (same : target = actual)
    (base : LedgerWriteEvolutionAt N ⟨source⟩ ⟨target⟩)
    (whole : LedgerWriteEvolutionAt (ExtendedNetwork N scope)
      (activeLedger source before) (activeLedger target after))
    (square : (entry : OpenResponsibilityAt N target) →
      (whole.origin (oldEntry (law := scope) (state? := some after) entry)).1 =
        oldEntry (law := scope) (state? := some before) (base.origin entry).1)
    (entry : OpenResponsibilityAt N actual) :
    ((castEvolution (congrArg (fun support => (support, some after)) same) whole).origin
      (oldEntry (law := scope) (state? := some after) entry)).1 =
        oldEntry (law := scope) (state? := some before) ((castEvolution same base).origin entry).1 := by
  cases same
  exact square entry

private theorem select_left {L R C : Type u} (selected : L ⊕ R)
    (left : (value : L) → selected = .inl value → C)
    (right : (value : R) → selected = .inr value → C)
    (value : L) (same : selected = .inl value) :
    Sum.rec (motive := fun output => selected = output → C) left right selected rfl = left value same := by
  cases same
  rfl

private theorem select_right {L R C : Type u} (selected : L ⊕ R)
    (left : (value : L) → selected = .inl value → C)
    (right : (value : R) → selected = .inr value → C)
    (value : R) (same : selected = .inr value) :
    Sum.rec (motive := fun output => selected = output → C) left right selected rfl = right value same := by
  cases same
  rfl

private theorem rec_apply_heq {A C : Sort (u + 1)} {selected first second : A}
    (body : selected = first → C) (same : first = second) (actual : selected = second) :
    HEq ((Eq.rec (motive := fun value _ => selected = value → C) body same) actual)
      (body (actual.trans same.symm)) := by
  cases same
  rfl

private theorem mpr_heq {A B : Sort (u + 1)} (same : A = B) (value : B) :
    HEq (Eq.mpr same value) value := by
  cases same
  rfl

private theorem untransported_settled
    (settled : SourceOperationExecutionDebt.Settlement event.state)
    (action : mathAction event = .inl settled) :
    HEq (untransportedWhole packet event)
      (Idle.wholeEvolution packet.ledgerEvolution event.owner event.state settled) := by
  unfold untransportedWhole
  refine (heq_of_eq (select_left _ _ _ settled action)).trans ?_
  dsimp only
  refine (rec_apply_heq _ _ _).trans ?_
  exact mpr_heq _ _

private theorem untransported_paid
    (paid : GeneratedStepAt (JoinedLaw (registered := registered)) event.state)
    (action : mathAction event = .inr paid) :
    HEq (untransportedWhole packet event)
      (jointStepLedgerEvolution (law := JoinedLaw (registered := registered)) packet.ledgerEvolution event.owner paid.2) := by
  unfold untransportedWhole
  refine (heq_of_eq (select_right _ _ _ paid action)).trans ?_
  dsimp only
  refine (rec_apply_heq _ _ _).trans ?_
  exact mpr_heq _ _

private theorem destination_old_of_heq {scope : DebtActivationLaw.{u}}
    {before after actual : scope.DebtState} {source target : N.Support}
    (same : after = actual)
    (base : LedgerWriteEvolutionAt N ⟨source⟩ ⟨target⟩)
    {first : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target after)}
    {second : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target actual)}
    (rows : HEq first second)
    (square : (entry : OpenResponsibilityAt N source) →
      (second.destination (oldEntry (law := scope) (state? := some before) entry)).1 =
        oldEntry (law := scope) (state? := some actual) (base.destination entry).1)
    (entry : OpenResponsibilityAt N source) :
    (first.destination (oldEntry (law := scope) (state? := some before) entry)).1 =
      oldEntry (law := scope) (state? := some after) (base.destination entry).1 := by
  cases same
  rw [eq_of_heq rows]
  exact square entry

private theorem origin_old_of_heq {scope : DebtActivationLaw.{u}}
    {before after actual : scope.DebtState} {source target : N.Support}
    (same : after = actual)
    (base : LedgerWriteEvolutionAt N ⟨source⟩ ⟨target⟩)
    {first : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target after)}
    {second : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target actual)}
    (rows : HEq first second)
    (square : (entry : OpenResponsibilityAt N target) →
      (second.origin (oldEntry (law := scope) (state? := some actual) entry)).1 =
        oldEntry (law := scope) (state? := some before) (base.origin entry).1)
    (entry : OpenResponsibilityAt N target) :
    (first.origin (oldEntry (law := scope) (state? := some after) entry)).1 =
      oldEntry (law := scope) (state? := some before) (base.origin entry).1 := by
  cases same
  rw [eq_of_heq rows]
  exact square entry

private theorem untransported_destination_old
    (entry : OpenResponsibilityAt N (sourceSupport (lower := lower) (current := current))) :
    ((untransportedWhole packet event).destination
      (oldEntry (law := JoinedLaw (registered := registered)) (state? := some event.state) entry)).1 =
        oldEntry (law := JoinedLaw (registered := registered)) (state? := some (mathTarget event))
          (packet.ledgerEvolution.destination entry).1 := by
  cases action : mathAction event with
  | inl settled =>
      exact destination_old_of_heq (by simp only [mathTarget, action]; rfl) packet.ledgerEvolution
        (untransported_settled packet event settled action) (fun _ => rfl) entry
  | inr paid =>
      exact destination_old_of_heq (by simp only [mathTarget, action]; rfl) packet.ledgerEvolution
        (untransported_paid packet event paid action) (fun _ => rfl) entry

private theorem untransported_origin_old
    (entry : OpenResponsibilityAt N
      (lower.source.source.toRootSource.account.supportOf packet.targetOccurrence)) :
    ((untransportedWhole packet event).origin
      (oldEntry (law := JoinedLaw (registered := registered)) (state? := some (mathTarget event)) entry)).1 =
        oldEntry (law := JoinedLaw (registered := registered)) (state? := some event.state)
          (packet.ledgerEvolution.origin entry).1 := by
  cases action : mathAction event with
  | inl settled =>
      exact origin_old_of_heq (by simp only [mathTarget, action]; rfl) packet.ledgerEvolution
        (untransported_settled packet event settled action) (fun _ => rfl) entry
  | inr paid =>
      exact origin_old_of_heq (by simp only [mathTarget, action]; rfl) packet.ledgerEvolution
        (untransported_paid packet event paid action) (fun _ => rfl) entry

theorem join_destination_old
    (entry : OpenResponsibilityAt N (sourceSupport (lower := lower) (current := current))) :
    ((join packet event).wholeEvolution.destination
      (oldEntry (law := JoinedLaw (registered := registered)) (state? := some event.state) entry)).1 =
        oldEntry (law := JoinedLaw (registered := registered)) (state? := some (mathTarget event))
          ((originalFold packet).destination entry).1 :=
  cast_destination_old (congrArg (lower.source.source.toRootSource.account.supportOf) packet.target_emitted)
    packet.ledgerEvolution (untransportedWhole packet event)
    (untransported_destination_old packet event) entry

theorem join_origin_old
    (entry : OpenResponsibilityAt N (targetSupport packet)) :
    ((join packet event).wholeEvolution.origin
      (oldEntry (law := JoinedLaw (registered := registered)) (state? := some (mathTarget event)) entry)).1 =
        oldEntry (law := JoinedLaw (registered := registered)) (state? := some event.state)
          ((originalFold packet).origin entry).1 :=
  cast_origin_old (congrArg (lower.source.source.toRootSource.account.supportOf) packet.target_emitted)
    packet.ledgerEvolution (untransportedWhole packet event)
    (untransported_origin_old packet event) entry


private theorem cast_action_paid {scope : DebtActivationLaw.{u}}
    {before after actualState : scope.DebtState} {source target actual : N.Support}
    (same : target = actual) (states : after = actualState)
    (base : LedgerWriteEvolutionAt N ⟨source⟩ ⟨target⟩)
    (owner : OpenResponsibilityAt N source) (step : scope.StepAt before actualState)
    {rows : LedgerWriteEvolutionAt (ExtendedNetwork N scope)
      (activeLedger source before) (activeLedger target after)}
    (receipt : HEq rows (jointStepLedgerEvolution base owner step)) :
    HEq (castEvolution (congrArg (fun support => (support, some after)) same) rows)
      (jointStepLedgerEvolution (castEvolution same base) owner step) := by
  cases same
  cases states
  exact receipt

private theorem cast_action_settled {scope : DebtActivationLaw.{u}}
    {before after : scope.DebtState} {source target actual : N.Support}
    (same : target = actual) (states : after = before)
    {rows : LedgerWriteEvolutionAt (ExtendedNetwork N scope)
      (activeLedger source before) (activeLedger target after)}
    {actualRows : LedgerWriteEvolutionAt (ExtendedNetwork N scope)
      (activeLedger source before) (activeLedger target before)}
    (receipt : HEq rows actualRows) :
    HEq (castEvolution (congrArg (fun support => (support, some after)) same) rows)
      (castEvolution (congrArg (fun support => (support, some before)) same) actualRows) := by
  cases same
  cases states
  exact receipt

/-- All original receipt data, including the full mathematical payer, survive
canonical target transport. -/
theorem join_whole_paid
    (paid : GeneratedStepAt (JoinedLaw (registered := registered)) event.state)
    (action : mathAction event = .inr paid) :
    HEq (join packet event).wholeEvolution
      (jointStepLedgerEvolution (law := JoinedLaw (registered := registered))
        (originalFold packet) event.owner paid.2) :=
  cast_action_paid
    (congrArg (lower.source.source.toRootSource.account.supportOf) packet.target_emitted)
    (by simp only [mathTarget, action]) packet.ledgerEvolution event.owner paid.2
    (untransported_paid packet event paid action)

private theorem destination_math_of_heq {scope : DebtActivationLaw.{u}}
    {before after actual : scope.DebtState} {source target : N.Support}
    (same : after = actual)
    {first : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target after)}
    {second : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target actual)}
    (rows : HEq first second)
    (square : (second.destination (debtEntry (N := N) (law := scope) source before)).1 =
      debtEntry (N := N) (law := scope) target actual) :
    (first.destination (debtEntry (N := N) (law := scope) source before)).1 =
      debtEntry (N := N) (law := scope) target after := by
  cases same
  rw [eq_of_heq rows]
  exact square

private theorem origin_math_of_heq {scope : DebtActivationLaw.{u}}
    {before after actual : scope.DebtState} {source target : N.Support}
    (same : after = actual)
    {first : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target after)}
    {second : LedgerWriteEvolutionAt (ExtendedNetwork N scope) (activeLedger source before) (activeLedger target actual)}
    (rows : HEq first second)
    (square : (second.origin (debtEntry (N := N) (law := scope) target actual)).1 =
      debtEntry (N := N) (law := scope) source before) :
    (first.origin (debtEntry (N := N) (law := scope) target after)).1 =
      debtEntry (N := N) (law := scope) source before := by
  cases same
  rw [eq_of_heq rows]
  exact square

private theorem cast_destination_math {scope : DebtActivationLaw.{u}}
    {before after : scope.DebtState} {source target actual : N.Support}
    (same : target = actual)
    (whole : LedgerWriteEvolutionAt (ExtendedNetwork N scope)
      (activeLedger source before) (activeLedger target after))
    (square : (whole.destination (debtEntry (N := N) (law := scope) source before)).1 =
      debtEntry (N := N) (law := scope) target after) :
    ((castEvolution (congrArg (fun support => (support, some after)) same) whole).destination
      (debtEntry (N := N) (law := scope) source before)).1 =
        debtEntry (N := N) (law := scope) actual after := by
  cases same
  exact square

private theorem cast_origin_math {scope : DebtActivationLaw.{u}}
    {before after : scope.DebtState} {source target actual : N.Support}
    (same : target = actual)
    (whole : LedgerWriteEvolutionAt (ExtendedNetwork N scope)
      (activeLedger source before) (activeLedger target after))
    (square : (whole.origin (debtEntry (N := N) (law := scope) target after)).1 =
      debtEntry (N := N) (law := scope) source before) :
    ((castEvolution (congrArg (fun support => (support, some after)) same) whole).origin
      (debtEntry (N := N) (law := scope) actual after)).1 =
        debtEntry (N := N) (law := scope) source before := by
  cases same
  exact square

private theorem untransported_destination_math :
    ((untransportedWhole packet event).destination
      (debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (sourceSupport (lower := lower) (current := current)) event.state)).1 =
      debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (lower.source.source.toRootSource.account.supportOf packet.targetOccurrence) (mathTarget event) := by
  cases action : mathAction event with
  | inl settled =>
      exact destination_math_of_heq (by simp only [mathTarget, action]; rfl)
        (untransported_settled packet event settled action) rfl
  | inr paid =>
      exact destination_math_of_heq (by simp only [mathTarget, action]; rfl)
        (untransported_paid packet event paid action) rfl

private theorem untransported_origin_math :
    ((untransportedWhole packet event).origin
      (debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (lower.source.source.toRootSource.account.supportOf packet.targetOccurrence) (mathTarget event))).1 =
      debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (sourceSupport (lower := lower) (current := current)) event.state := by
  cases action : mathAction event with
  | inl settled =>
      exact origin_math_of_heq (by simp only [mathTarget, action]; rfl)
        (untransported_settled packet event settled action) rfl
  | inr paid =>
      exact origin_math_of_heq (by simp only [mathTarget, action]; rfl)
        (untransported_paid packet event paid action) rfl

theorem join_destination_math :
    ((join packet event).wholeEvolution.destination
      (debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (sourceSupport (lower := lower) (current := current)) event.state)).1 =
      debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (targetSupport packet) (mathTarget event) :=
  cast_destination_math
    (congrArg (lower.source.source.toRootSource.account.supportOf) packet.target_emitted)
    (untransportedWhole packet event) (untransported_destination_math packet event)

theorem join_origin_math :
    ((join packet event).wholeEvolution.origin
      (debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (targetSupport packet) (mathTarget event))).1 =
      debtEntry (N := N) (law := JoinedLaw (registered := registered))
        (sourceSupport (lower := lower) (current := current)) event.state :=
  cast_origin_math
    (congrArg (lower.source.source.toRootSource.account.supportOf) packet.target_emitted)
    (untransportedWhole packet event) (untransported_origin_math packet event)

end RootGeneratedDebtActivationJointSource.Successor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
