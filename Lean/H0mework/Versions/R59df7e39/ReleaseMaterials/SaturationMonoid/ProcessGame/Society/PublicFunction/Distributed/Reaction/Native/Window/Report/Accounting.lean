import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Finance.Origin
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Accounting
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)
structure Completed where
  private mk ::
  material : Fold.Completed bound start span
  services : Service.Completed bound start span
  finance : Finance.Origin.Completed bound start span
inductive Cursor where
  | material (state : Fold.Cursor bound start span)
  | services (material : Fold.Completed bound start span) (state : Service.Cursor bound start span)
  | finance (material : Fold.Completed bound start span) (services : Service.Completed bound start span) (state : Finance.Origin.Cursor bound start span)
def initial : Cursor bound start span := .material (Fold.initial bound start span)
noncomputable def capacity (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) := Fold.capacity bound.source.code span+Service.capacity bound.source.code start span+1+Finance.Origin.capacity bound start span+1
variable {bound start span}
noncomputable def Cursor.rank : Cursor bound start span → Nat
  | .material state => state.rank+Service.capacity bound.source.code start span+1+Finance.Origin.capacity bound start span+1
  | .services _ state => state.rank+Finance.Origin.capacity bound start span+1
  | .finance _ _ state => state.rank
inductive Event (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) where
  | material (event : Fold.Event bound)
  | beginServices
  | service (event : Service.Event bound)
  | beginFinance
  | finance (event : Finance.Origin.Event bound)
def Cursor.move : Cursor bound start span → Option (Event bound × Cursor bound start span)
  | .material state => match done : state.completed with
    | some collected => some (.beginServices,.services collected (Service.initial bound start span))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Fold.Cursor.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (event,next) => some (.material event,.material next)
  | .services collected state => match done : state.completed with
    | some delivered => some (.beginFinance,.finance collected delivered (Finance.Origin.initial bound start span))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Service.Cursor.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (event,next) => some (.service event,.services collected next)
  | .finance collected delivered state => state.move.map fun (event,next) => (.finance event,.finance collected delivered next)
def Cursor.completed : Cursor bound start span → Option (Completed bound start span)
  | .material _ => none
  | .services _ _ => none
  | .finance collected delivered state => state.completed.map fun finance => ⟨collected,delivered,finance⟩
theorem initial_rank : (initial bound start span).rank = capacity bound start span := by
  simp only [initial,Cursor.rank,Fold.initial_rank,capacity]

theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Event bound}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | material state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i collected done
      cases actual
      have zero := (Fold.Cursor.stopped_iff_zero state).mp ((Fold.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,Service.initial_rank,zero];omega
    · rename_i pending
      split at actual
      · rename_i stopped
        have complete := (Fold.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved
        cases actual
        have decrease := Fold.Cursor.move_decreases moved
        dsimp only [Cursor.rank];omega
  | services collected state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i delivered done
      cases actual
      have zero := (Service.Cursor.stopped_iff_zero state).mp ((Service.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,Finance.Origin.initial_rank,zero];omega
    · rename_i pending
      split at actual
      · rename_i stopped
        have complete := (Service.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved
        cases actual
        have decrease := Service.Cursor.move_decreases moved
        dsimp only [Cursor.rank];omega
  | finance collected delivered state =>
    dsimp only [Cursor.move] at actual
    cases moved : state.move with
    | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
    | some pair =>
      rcases pair with ⟨native,next⟩
      rw [moved] at actual
      cases actual
      exact Finance.Origin.Cursor.move_decreases moved

theorem Cursor.completed_iff_stopped (cursor : Cursor bound start span) : cursor.completed.isSome = true ↔ cursor.move = none := by
  cases cursor with
  | material state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move]
    split
    · simp
    · rename_i pending
      split
      · rename_i stopped
        have complete := (Fold.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | services collected state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move]
    split
    · simp
    · rename_i pending
      split
      · rename_i stopped
        have complete := (Service.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | finance collected delivered state =>
    have same := Finance.Origin.Cursor.completed_iff_stopped state
    cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
theorem Cursor.stopped_iff_zero (cursor : Cursor bound start span) : cursor.move = none ↔ cursor.rank = 0 := by
  cases cursor with
  | material state =>
    have active : (Cursor.material state).move ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped (Cursor.material state)).mpr stopped
      cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | services collected state =>
    have active : (Cursor.services collected state).move ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped (Cursor.services collected state)).mpr stopped
      cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | finance collected delivered state =>
    have same : (Cursor.finance collected delivered state).move = none ↔ state.move = none := by
      cases moved : state.move <;> simp [Cursor.move,moved]
    rw [same]
    exact Finance.Origin.Cursor.stopped_iff_zero state
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

def Completed.profile (cache : Completed bound start span) : Settlement.Profile P G O (Mandate.State P T) I :=
  ⟨cache.finance.originalDebts,
    cache.finance.admittedDebts,
    Settlement.rights (Window.holdings bound start span),
    cache.finance.unmatchedClaims,
    cache.services.startValues,
    ⟨(Window.terminal bound start span).technology,(Window.terminal bound start span).clock,(Window.terminal bound start span).round⟩⟩
theorem Completed.profile_exact (cache : Completed bound start span) : cache.profile = Window.profile bound start span := by
  unfold Completed.profile Window.profile
  rw [cache.services.startValues_exact,cache.finance.originalDebts_exact,cache.finance.admittedDebts_exact,cache.finance.unmatchedClaims_exact]

def Completed.evaluation (cache : Completed bound start span) : Evaluation bound.source.code where
  legal := cache.material.legal
  complete := cache.services.complete
  profile := cache.profile
  native := Window.manifest bound start span
  value := fun axis => match axis with
    | .material metric => cache.material.material metric
    | .unpaid index holder => Window.value bound start span (.unpaid index holder)
    | .service index => (((cache.services.at index).atEnd).getD (Window.finish start span) : ℚ)
theorem Completed.evaluation_exact (cache : Completed bound start span) : cache.evaluation = Window.evaluate bound start span := by
  have legal : cache.material.legal = Window.legal bound start span := (cache.material.at .admissibility).exact_lawful rfl
  have complete : cache.services.complete = (Window.evaluate bound start span).complete := by
    simpa only [Window.evaluate,Window.finish,Nat.add_sub_cancel] using cache.services.complete_exact
  have values : cache.evaluation.value = (Window.evaluate bound start span).value := by
    funext axis
    cases axis with
    | material metric => exact (cache.material.at metric).exact_value
    | unpaid index holder => rfl
    | service index =>
        dsimp only [Completed.evaluation,Window.evaluate,Window.value]
        rw [(cache.services.at index).end_exact]
        simp only [Window.finish,Nat.add_sub_cancel]
  unfold Completed.evaluation Window.evaluate
  simp only [Evaluation.mk.injEq]
  exact ⟨legal,complete,cache.profile_exact,by trivial,values⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Accounting
