import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Offers
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} (all : Candidates source catalogue)
abbrev Entry := Common.Entry all

def owned (owner : Ready all) (cached : List (Owned owner)) : List (Offer all) := cached.map (offer owner)
def outerOffers (remaining : List (Entry all)) : List (Offer all) :=
  (remaining.filterMap (readyOf all)).flatMap fun owner => owned all owner (policies owner)

inductive Cursor where
  | outer (remaining : List (Entry all))
  | owner (who : Ready all) (current : Enumeration.State who) (valid : SourceOnly who current) (tail : List (Entry all))
  | emitting (who : Ready all) (cached : List (Owned who)) (tail : List (Entry all))
def start : Cursor all := .outer all.entries.attach

def Cursor.denote : Cursor all → List (Offer all)
  | .outer remaining => outerOffers all remaining
  | .owner who _ _ tail => owned all who (policies who)++outerOffers all tail
  | .emitting who cached tail => owned all who cached++outerOffers all tail

inductive Event where
  | outer (entry : Entry all)
  | localStep (who : Ready all) (action : Enumeration.Action who)
  | handoff (who : Ready all)
  | emit (who : Ready all) (policy : Owned who)
  | close

private theorem source_open_has_next (who : Ready all) (current : Enumeration.State who) (unstarted : SourceOpen who current) :
    Enumeration.move who current ≠ none := by
  intro stopped
  have impossible := (Enumeration.move_none_iff_finished who current).mp stopped
  cases current <;> simp_all [SourceOpen,Enumeration.State.finished]

private def advanceOwner (who : Ready all) (current : Enumeration.State who) (unstarted : SourceOpen who current)
    (tail : List (Entry all)) : Option (Cursor all × Option (Offer all) × Event all) :=
  match observed : Enumeration.move who current with
  | none => False.elim (by
      have impossible := (Enumeration.move_none_iff_finished who current).mp observed
      cases current <;> simp_all [SourceOpen,Enumeration.State.finished])
  | some (after,action) => some
      (.owner who after (source_steps_preserve_the_complete_catalogue who unstarted observed) tail,none,.localStep who action)

def step : Cursor all → Option (Cursor all × Option (Offer all) × Event all)
  | .outer [] => none
  | .outer (entry::tail) => match readyOf all entry with
    | none => some (.outer tail,none,.outer entry)
    | some who => some (.owner who (Enumeration.start who) (by trivial) tail,none,.outer entry)
  | .owner who current@(.constructing ..) _ tail => advanceOwner all who current (by simp_all [SourceOpen]) tail
  | .owner who current@(.loading ..) _ tail => advanceOwner all who current (by simp_all [SourceOpen]) tail
  | .owner who current@(.admitting ..) _ tail => advanceOwner all who current (by simp_all [SourceOpen]) tail
  | .owner who current@(.nativeChecking ..) _ tail => advanceOwner all who current (by simp_all [SourceOpen]) tail
  | .owner who (.searching (.candidates cached _)) _ tail => some (.emitting who cached tail,none,.handoff who)
  | .owner _ (.searching (.checking ..)) invalid _ => False.elim invalid
  | .owner _ (.searching (.released ..)) invalid _ => False.elim invalid
  | .owner _ (.searching (.excluded ..)) invalid _ => False.elim invalid
  | .emitting _ [] tail => some (.outer tail,none,.close)
  | .emitting who (head::tailPolicies) tail => some (.emitting who tailPolicies tail,some (offer who head),.emit who head)

theorem initial_denote : (start all).denote all = offers all := rfl

private theorem advanceOwner_conserves (who : Ready all) (current : Enumeration.State who) (unstarted : SourceOpen who current)
    (tail : List (Entry all)) {after : Cursor all} {yielded : Option (Offer all)} {event : Event all}
    (observed : advanceOwner all who current unstarted tail = some (after,yielded,event)) :
    owned all who (policies who)++outerOffers all tail = yielded.toList++after.denote all := by
  dsimp only [advanceOwner] at observed;split at observed
  · rename_i stopped;exact False.elim (source_open_has_next all who current unstarted stopped)
  · cases Option.some.inj observed;rfl

theorem one_step_conserves {before after : Cursor all} {yielded : Option (Offer all)} {event : Event all}
    (observed : step all before = some (after,yielded,event)) :
    before.denote all = yielded.toList++after.denote all := by
  cases before with
  | outer remaining =>
    cases remaining with
    | nil => cases observed
    | cons entry tail =>
      dsimp only [step] at observed;split at observed
      all_goals cases Option.some.inj observed
      all_goals simp_all [Cursor.denote,outerOffers]
  | owner who current valid tail =>
    cases current with
    | constructing | loading | admitting | nativeChecking =>
      dsimp only [step] at observed
      exact advanceOwner_conserves all who _ (by trivial) tail observed
    | searching search =>
      cases search with
      | candidates cached safe =>
        cases Option.some.inj observed
        change cached = policies who at valid
        simp only [Cursor.denote,Option.toList_none,List.nil_append,valid]
      | checking | released | excluded => exact False.elim valid
  | emitting who cached tail =>
    cases cached <;> cases Option.some.inj observed
    all_goals simp [Cursor.denote,owned]

def outerRank (remaining : List (Entry all)) : Nat := (remaining.map fun entry => match readyOf all entry with
  | none => 1
  | some who => (Enumeration.start who).rank who+3).sum

def Cursor.rank : Cursor all → Nat
  | .outer remaining => outerRank all remaining
  | .owner who current _ tail => current.rank who+2+outerRank all tail
  | .emitting _ cached tail => cached.length+1+outerRank all tail

private theorem advanceOwner_progresses (who : Ready all) (current : Enumeration.State who) (unstarted : SourceOpen who current)
    (tail : List (Entry all)) {after : Cursor all} {yielded : Option (Offer all)} {event : Event all}
    (observed : advanceOwner all who current unstarted tail = some (after,yielded,event)) :
    after.rank all < current.rank who+2+outerRank all tail := by
  dsimp only [advanceOwner] at observed;split at observed
  · rename_i stopped;exact False.elim (source_open_has_next all who current unstarted stopped)
  · rename_i next action actual
    cases Option.some.inj observed
    have reduced := each_paid_constructor_or_review_step_progresses who actual
    simp only [Cursor.rank];omega

theorem step_progresses {before after : Cursor all} {yielded : Option (Offer all)} {event : Event all}
    (observed : step all before = some (after,yielded,event)) : after.rank all < before.rank all := by
  cases before with
  | outer remaining =>
    cases remaining with
    | nil => cases observed
    | cons entry tail =>
      dsimp only [step] at observed;split at observed
      all_goals cases Option.some.inj observed
      all_goals simp_all [Cursor.rank,outerRank]
  | owner who current valid tail =>
    cases current with
    | constructing | loading | admitting | nativeChecking =>
      dsimp only [step] at observed
      exact advanceOwner_progresses all who _ (by trivial) tail observed
    | searching search =>
      cases search with
      | candidates cached safe =>
        cases Option.some.inj observed
        simp only [Cursor.rank,Enumeration.State.rank,Search.rank]
        have positive : 0 ≤ innerBound (all := all) := Nat.zero_le _
        nlinarith
      | checking | released | excluded => exact False.elim valid
  | emitting who cached tail =>
    cases cached <;> cases Option.some.inj observed
    all_goals simp only [Cursor.rank,List.length_nil,List.length_cons];omega

private theorem advanceOwner_ne_none (who : Ready all) (current : Enumeration.State who) (unstarted : SourceOpen who current)
    (tail : List (Entry all)) : advanceOwner all who current unstarted tail ≠ none := by
  dsimp only [advanceOwner];split
  · rename_i stopped;exact False.elim (source_open_has_next all who current unstarted stopped)
  · simp

theorem stopped_iff_empty (before : Cursor all) : step all before = none ↔ before = .outer [] := by
  cases before with
  | outer remaining =>
    cases remaining with
    | nil => simp [step]
    | cons entry tail => dsimp only [step];split <;> simp
  | owner who current valid tail =>
    cases current with
    | constructing | loading | admitting | nativeChecking =>
      constructor
      · intro stopped
        apply False.elim
        dsimp only [step] at stopped
        refine advanceOwner_ne_none all who _ ?_ tail stopped
        trivial
      · intro impossible;cases impossible
    | searching search =>
      cases search with
      | candidates => simp [step]
      | checking | released | excluded => exact False.elim valid
  | emitting who cached tail => cases cached <;> simp [step]

theorem stopped_has_no_residual (before : Cursor all) (stopped : step all before = none) : before.denote all = [] := by
  rw [(stopped_iff_empty all before).mp stopped];rfl

def Cursor.creditMark : Cursor all → Admission.Credit.Mark all
  | .owner who current _ _ => current.creditMark who
  | _ => .idle
def Event.creditLog : Event all → Admission.Credit.Log all
  | .localStep who action => action.creditLog who
  | _ => .silent

private theorem advanceOwner_credit_rule (who : Ready all) (current : Enumeration.State who) (unstarted : SourceOpen who current)
    (tail : List (Entry all)) {after : Cursor all} {yielded : Option (Offer all)} {event : Event all}
    (observed : advanceOwner all who current unstarted tail = some (after,yielded,event)) :
    Admission.Credit.Rule (current.creditMark who) (event.creditLog all) (after.creditMark all) := by
  dsimp only [advanceOwner] at observed;split at observed
  · rename_i stopped;exact False.elim (source_open_has_next all who current unstarted stopped)
  · rename_i next action actual
    cases Option.some.inj observed
    exact Enumeration.move_credit_rule who actual

theorem step_credit_rule {before after : Cursor all} {yielded : Option (Offer all)} {event : Event all}
    (observed : step all before = some (after,yielded,event)) :
    Admission.Credit.Rule (before.creditMark all) (event.creditLog all) (after.creditMark all) := by
  cases before with
  | outer remaining =>
    cases remaining with
    | nil => cases observed
    | cons entry tail =>
      dsimp only [step] at observed;split at observed
      all_goals cases Option.some.inj observed
      all_goals exact .fresh _ _ rfl
  | owner who current valid tail =>
    cases current with
    | constructing | loading | admitting | nativeChecking =>
      dsimp only [step] at observed
      exact advanceOwner_credit_rule all who _ (by trivial) tail observed
    | searching search =>
      cases search with
      | candidates => cases Option.some.inj observed;exact .fresh _ _ rfl
      | checking | released | excluded => exact False.elim valid
  | emitting who cached tail =>
    cases cached <;> cases Option.some.inj observed
    all_goals exact .fresh _ _ rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Offers
