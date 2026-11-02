import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Action
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Origin
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)
abbrev inventory (ordinal : Nat) := Financial.inventoryAt bound.source.input (ProgrammeHistory.visitAt bound.source.input ordinal)
-- Logical termination potential. Execution uses only its supplied ticket and current inventory.
noncomputable def laterWork : Nat → Nat → Nat
  | _,0 => 0
  | ordinal,count+1 => (inventory bound ordinal).length+2+laterWork (ordinal+1) count
noncomputable def capacity := laterWork bound 0 (Window.finish start span)
structure Batch (ordinal : Nat) (ledger : Ledger bound) where
  private mk ::
  remaining : List (Financial.InstructionOrigin bound.source.input)
  ordered : ∃ processed,processed++remaining = inventory bound ordinal
  meaning : Financial.consumeOrigins bound.source.input remaining ledger = Financial.accountAt bound.source.input (ordinal+1)
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
  pending : Option (Batch bound ordinal ledger)
  bounded : ordinal ≤ Window.finish start span
  known : match pending with | none => ledger = Financial.accountAt bound.source.input ordinal | some _ => True
  active : pending.isSome = true → ordinal < Window.finish start span
  checkpoint : if ordinal < start+1 then saved = none else saved = some (Window.first bound start)
def initial : Cursor bound start span :=
  ⟨0,.initial (Financial.process bound.source.input),none,none,Nat.zero_le _,rfl,by simp,by simp⟩
variable {bound start span}
noncomputable def Cursor.rank (cursor : Cursor bound start span) := match cursor.pending with
  | none => laterWork bound cursor.ordinal (Window.finish start span-cursor.ordinal)
  | some batch => batch.remaining.length+1+laterWork bound (cursor.ordinal+1) (Window.finish start span-(cursor.ordinal+1))
inductive Event (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) where
  | beginVisit (ordinal : Nat)
  | origin (ordinal : Nat) (original : Financial.InstructionOrigin bound.source.input)
  | finishVisit (ordinal : Nat)

def Cursor.move (cursor : Cursor bound start span) : Option (Event bound × Cursor bound start span) :=
  match loaded : cursor.pending with
  | none => if active : cursor.ordinal < Window.finish start span then
      have known : cursor.ledger = Financial.accountAt bound.source.input cursor.ordinal := by simpa only [loaded] using cursor.known
      let batch : Batch bound cursor.ordinal cursor.ledger := ⟨inventory bound cursor.ordinal,⟨[],rfl⟩,by
        rw [known,Financial.accountAt];rfl⟩
      some (.beginVisit cursor.ordinal,⟨cursor.ordinal,cursor.ledger,cursor.saved,some batch,cursor.bounded,True.intro,fun _ => active,cursor.checkpoint⟩)
    else none
  | some batch => match contents : batch.remaining with
    | [] =>
        have active := cursor.active (by rw [loaded];rfl)
        have next_exact : cursor.ledger = Financial.accountAt bound.source.input (cursor.ordinal+1) := by
          simpa only [contents,Financial.consumeOrigins] using batch.meaning
        some (.finishVisit cursor.ordinal,⟨cursor.ordinal+1,cursor.ledger,
          if cursor.ordinal+1 = start+1 then some cursor.ledger else cursor.saved,none,by omega,next_exact,by simp,by
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
    | origin::rest =>
        let next := (Financial.Installation.sourceAction bound.source.input origin).next bound.source.input cursor.ledger
        let remaining : Batch bound cursor.ordinal next := ⟨rest,by
          obtain ⟨processed,ordered⟩ := batch.ordered
          refine ⟨processed++[origin],?_⟩
          rw [contents] at ordered
          simpa only [List.append_assoc,List.singleton_append] using ordered,by
          dsimp only [next]
          rw [Financial.Installation.sourceAction_is_actual_consumer]
          have known := batch.meaning
          rw [contents] at known
          exact known⟩
        some (.origin cursor.ordinal origin,⟨cursor.ordinal,next,cursor.saved,some remaining,cursor.bounded,True.intro,
          fun _ => cursor.active (by rw [loaded];rfl),cursor.checkpoint⟩)

def Cursor.finish (cursor : Cursor bound start span) (ending : cursor.ordinal = Window.finish start span) : Completed bound start span :=
  have notLoaded : cursor.pending = none := by
    cases actual : cursor.pending with
    | none => rfl
    | some batch => have active := cursor.active (by rw [actual];rfl);omega
  have known : cursor.ledger = Window.last bound start span := by
    have exact_ledger := cursor.known
    simpa only [notLoaded,ending] using exact_ledger
  have late : ¬cursor.ordinal < start+1 := by unfold Window.finish at ending;omega
  have exact_saved : cursor.saved = some (Window.first bound start) := by simpa only [if_neg late] using cursor.checkpoint
  match actual : cursor.saved with
  | none => False.elim (by rw [actual] at exact_saved;cases exact_saved)
  | some previous => ⟨previous,cursor.ledger,by rw [actual] at exact_saved;exact Option.some.inj exact_saved,known⟩
def Cursor.completed (cursor : Cursor bound start span) : Option (Completed bound start span) :=
  if ending : cursor.ordinal = Window.finish start span then some (cursor.finish ending) else none

theorem initial_rank : (initial bound start span).rank = capacity bound start span := rfl

theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Event bound}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Cursor.move] at actual
  split at actual
  · rename_i loaded
    split at actual
    · rename_i active
      cases actual
      have count : Window.finish start span-before.ordinal = (Window.finish start span-(before.ordinal+1))+1 := by omega
      simp only [Cursor.rank,loaded,count,laterWork]
      omega
    · cases actual
  · rename_i batch loaded
    split at actual
    · rename_i contents
      cases actual
      simp only [Cursor.rank,loaded,contents,List.length_nil,Nat.zero_add];omega
    · rename_i origin rest contents
      cases actual
      simp only [Cursor.rank,loaded,contents,List.length_cons]
      omega

theorem Cursor.completed_iff_stopped (cursor : Cursor bound start span) : cursor.completed.isSome = true ↔ cursor.move = none := by
  rcases cursor with ⟨ordinal,ledger,saved,pending,bounded,known,active,checkpoint⟩
  cases pending with
  | none =>
    by_cases ending : ordinal = Window.finish start span
    · simp [Cursor.completed,Cursor.move,ending]
    · have enabled : ordinal < Window.finish start span := by omega
      simp [Cursor.completed,Cursor.move,ending,enabled]
  | some batch =>
    have enabled : ordinal < Window.finish start span := active rfl
    have ending : ordinal ≠ Window.finish start span := by omega
    simp only [Cursor.completed,dif_neg ending,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move]
    split <;> simp

theorem Cursor.stopped_iff_zero (cursor : Cursor bound start span) : cursor.move = none ↔ cursor.rank = 0 := by
  have finished : cursor.move = none ↔ cursor.ordinal = Window.finish start span := by
    rw [←Cursor.completed_iff_stopped]
    by_cases ending : cursor.ordinal = Window.finish start span <;> simp [Cursor.completed,ending]
  rw [finished]
  cases loaded : cursor.pending with
  | none =>
    dsimp only [Cursor.rank];rw [loaded]
    by_cases ending : cursor.ordinal = Window.finish start span
    · simp [ending,laterWork]
    · have active : cursor.ordinal < Window.finish start span := by have := cursor.bounded;omega
      have count : Window.finish start span-cursor.ordinal = (Window.finish start span-(cursor.ordinal+1))+1 := by omega
      simp only [ending,false_iff]
      rw [count,laterWork]
      omega
  | some batch =>
    have active := cursor.active (by rw [loaded];rfl)
    simp only [Cursor.rank,loaded]
    omega

inductive History : Cursor bound start span → Cursor bound start span → List (Event bound) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor bound start span) (capacity : Nat) where
  private mk ::
  endpoint : Cursor bound start span
  work : List (Event bound)
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
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Origin
