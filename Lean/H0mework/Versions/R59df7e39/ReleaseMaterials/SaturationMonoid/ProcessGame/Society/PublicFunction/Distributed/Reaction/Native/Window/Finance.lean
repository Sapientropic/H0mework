import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)
abbrev Ledger := (Financial.process bound.source.input).GeneratedState
structure Completed where
  private mk ::
  atStart : Ledger bound
  atEnd : Ledger bound
  start_exact : atStart = Window.first bound start
  end_exact : atEnd = Window.last bound start span
structure Cursor where
  private mk ::
  ordinal : Nat
  ledger : Ledger bound
  saved : Option (Ledger bound)
  bounded : ordinal ≤ Window.finish start span
  known : ledger = Financial.accountAt bound.source.input ordinal
  checkpoint : if ordinal < start+1 then saved = none else saved = some (Window.first bound start)
def initial : Cursor bound start span :=
  ⟨0,.initial (Financial.process bound.source.input),none,Nat.zero_le _,rfl,by simp⟩
def capacity (start span : Nat) := Window.finish start span
variable {bound start span}
def Cursor.rank (cursor : Cursor bound start span) := Window.finish start span-cursor.ordinal

def Cursor.move (cursor : Cursor bound start span) : Option (Nat × Cursor bound start span) :=
  if active : cursor.ordinal < Window.finish start span then
    let next := Financial.oneVisit bound.source.input (ProgrammeHistory.visitAt bound.source.input cursor.ordinal) cursor.ledger
    have next_exact : next = Financial.accountAt bound.source.input (cursor.ordinal+1) := by
      dsimp only [next];rw [Financial.accountAt,cursor.known]
    some (cursor.ordinal,⟨cursor.ordinal+1,next,if cursor.ordinal+1 = start+1 then some next else cursor.saved,by omega,next_exact,by
      by_cases hit : cursor.ordinal+1 = start+1
      · rw [if_pos hit]
        have late : ¬cursor.ordinal+1 < start+1 := by omega
        rw [if_neg late]
        exact congrArg some (by rw [next_exact,hit])
      · rw [if_neg hit]
        by_cases early : cursor.ordinal+1 < start+1
        · have before : cursor.ordinal < start+1 := by omega
          simpa only [if_pos early,if_pos before] using cursor.checkpoint
        · have before : ¬cursor.ordinal < start+1 := by omega
          simpa only [if_neg early,if_neg before] using cursor.checkpoint⟩)
  else none

def Cursor.finish (cursor : Cursor bound start span) (ending : cursor.ordinal = Window.finish start span) : Completed bound start span :=
  have late : ¬cursor.ordinal < start+1 := by unfold Window.finish at ending;omega
  have saved := cursor.checkpoint
  have exact_saved : cursor.saved = some (Window.first bound start) := by simpa only [if_neg late] using saved
  match actual : cursor.saved with
  | none => False.elim (by rw [actual] at exact_saved;cases exact_saved)
  | some previous => ⟨previous,cursor.ledger,by rw [actual] at exact_saved;exact Option.some.inj exact_saved,by rw [cursor.known,ending]⟩
def Cursor.completed (cursor : Cursor bound start span) : Option (Completed bound start span) :=
  if ending : cursor.ordinal = Window.finish start span then some (cursor.finish ending) else none

theorem initial_rank : (initial bound start span).rank = capacity start span := by
  simp only [initial,Cursor.rank,Nat.sub_zero,capacity]
theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Nat}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Cursor.move] at actual
  split at actual
  · rename_i active;cases actual;dsimp only [Cursor.rank];omega
  · cases actual

theorem Cursor.completed_iff_stopped (cursor : Cursor bound start span) :
    cursor.completed.isSome = true ↔ cursor.move = none := by
  have bounded := cursor.bounded
  by_cases ending : cursor.ordinal = Window.finish start span
  · simp [Cursor.completed,Cursor.move,ending]
  · have active : cursor.ordinal < Window.finish start span := by omega
    simp [Cursor.completed,Cursor.move,ending,active]
theorem Cursor.stopped_iff_zero (cursor : Cursor bound start span) :
    cursor.move = none ↔ cursor.rank = 0 := by
  have bounded := cursor.bounded
  have finished : cursor.completed.isSome = true ↔ cursor.ordinal = Window.finish start span := by
    by_cases ending : cursor.ordinal = Window.finish start span <;> simp [Cursor.completed,ending]
  rw [←Cursor.completed_iff_stopped cursor,finished]
  dsimp only [Cursor.rank];omega

inductive History : Cursor bound start span → Cursor bound start span → List Nat → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor bound start span) (capacity : Nat) where
  private mk ::
  endpoint : Cursor bound start span
  work : List Nat
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor bound start span) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩
theorem run_sufficient (before : Cursor bound start span) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

theorem run_work_exact (before : Cursor bound start span) (available : Nat) :
    (run available before).work.length = min available before.rank := by
  have covered := (run available before).covered
  have conserved := (run available before).conservation
  rcases (run available before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped
    rw [zero] at conserved
    have same : (run available before).work.length = before.rank := by omega
    rw [same,Nat.min_eq_right (by omega)]
  · rw [full,Nat.min_eq_left (by omega)]

def Completed.originalDebts (cache : Completed bound start span) :=
  Identity.financeImage bound.source.code bound.source.input cache.atStart
def Completed.admittedDebts (cache : Completed bound start span) :=
  (Identity.financeImage bound.source.code bound.source.input cache.atEnd).drop cache.atStart.current.slots.length
def Completed.unmatchedClaims (cache : Completed bound start span) :=
  bound.source.code.instruments.flatMap fun instrument => bound.source.code.parties.flatMap fun debtor =>
    bound.source.code.parties.map fun creditor => (Window.terminal bound start span).claims instrument debtor creditor -
      Financial.BalanceConservation.ledgerClaims bound.source.input cache.atEnd.current instrument debtor creditor

theorem Completed.originalDebts_exact (cache : Completed bound start span) : cache.originalDebts =
    Identity.financeImage bound.source.code bound.source.input (Window.first bound start) := by
  unfold Completed.originalDebts;rw [cache.start_exact]
theorem Completed.admittedDebts_exact (cache : Completed bound start span) : cache.admittedDebts =
    (Identity.financeImage bound.source.code bound.source.input (Window.last bound start span)).drop (Window.first bound start).current.slots.length := by
  unfold Completed.admittedDebts;rw [cache.start_exact,cache.end_exact]
theorem Completed.unmatchedClaims_exact (cache : Completed bound start span) : cache.unmatchedClaims =
    bound.source.code.instruments.flatMap fun instrument => bound.source.code.parties.flatMap fun debtor =>
      bound.source.code.parties.map fun creditor => (Window.terminal bound start span).claims instrument debtor creditor -
        Financial.BalanceConservation.ledgerClaims bound.source.input (Window.last bound start span).current instrument debtor creditor := by
  unfold Completed.unmatchedClaims;rw [cache.end_exact]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance
