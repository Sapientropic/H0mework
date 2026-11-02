import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Accounting
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Fields
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Fields
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)
structure Completed where
  private mk ::
  base : Accounting.Completed bound start span
  financial : Finance.Fields.Completed base.finance
inductive Cursor where
  | source (state : Accounting.Cursor bound start span)
  | financial (base : Accounting.Completed bound start span) (state : Finance.Fields.Cursor base.finance)
def initial : Cursor bound start span := .source (Accounting.initial bound start span)
noncomputable def capacity := Accounting.capacity bound start span+Finance.Fields.capacity bound start span+1
variable {bound start span}
noncomputable def Cursor.rank : Cursor bound start span → Nat
  | .source state => state.rank+Finance.Fields.capacity bound start span+1
  | .financial _ state => state.rank
inductive Event (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) where
  | source (event : Accounting.Event bound)
  | beginFields
  | financial (native : Finance.Origin.Completed bound start span) (event : Finance.Fields.Event native)
def Cursor.move : Cursor bound start span → Option (Event bound start span × Cursor bound start span)
  | .source state => match done : state.completed with
    | some collected => some (.beginFields,.financial collected (Finance.Fields.initial (native := collected.finance)))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Accounting.Cursor.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (event,next) => some (.source event,.source next)
  | .financial collected state => state.move.map fun (event,next) => (.financial collected.finance event,.financial collected next)
def Cursor.completed : Cursor bound start span → Option (Completed bound start span)
  | .source _ => none
  | .financial collected state => state.completed.map fun fields => ⟨collected,fields⟩
theorem initial_rank : (initial bound start span).rank = capacity bound start span := by
  simp only [initial,Cursor.rank,Accounting.initial_rank,capacity]

theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Event bound start span}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | source state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i collected done;cases actual
      have zero := (Accounting.Cursor.stopped_iff_zero state).mp ((Accounting.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,Finance.Fields.initial_rank,zero];omega
    · rename_i pending;split at actual
      · rename_i stopped
        have complete := (Accounting.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved;cases actual
        have decrease := Accounting.Cursor.move_decreases moved;dsimp only [Cursor.rank];omega
  | financial collected state =>
    dsimp only [Cursor.move] at actual
    cases moved : state.move with
    | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
    | some pair =>
      rcases pair with ⟨native,next⟩;rw [moved] at actual;cases actual
      exact Finance.Fields.Cursor.move_decreases moved

theorem Cursor.completed_iff_stopped (cursor : Cursor bound start span) : cursor.completed.isSome = true ↔ cursor.move = none := by
  cases cursor with
  | source state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move];split
    · simp
    · rename_i pending;split
      · rename_i stopped
        have complete := (Accounting.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | financial collected state =>
    have same := Finance.Fields.Cursor.completed_iff_stopped state
    cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
theorem Cursor.stopped_iff_zero (cursor : Cursor bound start span) : cursor.move = none ↔ cursor.rank = 0 := by
  cases cursor with
  | source state =>
    have active : (Cursor.source state).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped (Cursor.source state)).mpr stopped;cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | financial collected state =>
    have same : (Cursor.financial collected state).move = none ↔ state.move = none := by cases moved : state.move <;> simp [Cursor.move,moved]
    rw [same];exact Finance.Fields.Cursor.stopped_iff_zero state

inductive History : Cursor bound start span → Cursor bound start span → List (Event bound start span) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor bound start span) (capacity : Nat) where
  private mk ::
  endpoint : Cursor bound start span
  work : List (Event bound start span)
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

def Completed.profile (cache : Completed bound start span) : Settlement.Profile P G O (Mandate.State P T) I :=
  ⟨cache.financial.originalDebts,cache.financial.admittedDebts,cache.financial.rights,cache.financial.unmatchedClaims,
    cache.base.services.startValues,
    ⟨(Window.terminal bound start span).technology,(Window.terminal bound start span).clock,(Window.terminal bound start span).round⟩⟩
theorem Completed.profile_exact (cache : Completed bound start span) : cache.profile = Window.profile bound start span := by
  unfold Completed.profile Window.profile
  rw [cache.financial.originalDebts_exact,cache.financial.admittedDebts_exact,cache.financial.rights_exact,
    cache.financial.unmatchedClaims_exact,cache.base.services.startValues_exact]

def Completed.evaluation (cache : Completed bound start span) : Evaluation bound.source.code where
  legal := cache.base.material.legal
  complete := cache.base.services.complete
  profile := cache.profile
  native := Window.manifest bound start span
  value := fun axis => match axis with
    | .material metric => cache.base.material.material metric
    | .unpaid index holder => cache.financial.unpaid index holder
    | .service index => (((cache.base.services.at index).atEnd).getD (Window.finish start span) : ℚ)
theorem Completed.evaluation_exact (cache : Completed bound start span) : cache.evaluation = Window.evaluate bound start span := by
  have legal : cache.base.material.legal = Window.legal bound start span := (cache.base.material.at .admissibility).exact_lawful rfl
  have complete : cache.base.services.complete = (Window.evaluate bound start span).complete := by
    simpa only [Window.evaluate,Window.finish,Nat.add_sub_cancel] using cache.base.services.complete_exact
  have values : cache.evaluation.value = (Window.evaluate bound start span).value := by
    funext axis;cases axis with
    | material metric => exact (cache.base.material.at metric).exact_value
    | unpaid index holder => exact cache.financial.unpaid_exact index holder
    | service index =>
        dsimp only [Completed.evaluation,Window.evaluate,Window.value]
        rw [(cache.base.services.at index).end_exact]
        simp only [Window.finish,Nat.add_sub_cancel]
  unfold Completed.evaluation Window.evaluate
  simp only [Evaluation.mk.injEq]
  exact ⟨legal,complete,cache.profile_exact,by trivial,values⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Fields
