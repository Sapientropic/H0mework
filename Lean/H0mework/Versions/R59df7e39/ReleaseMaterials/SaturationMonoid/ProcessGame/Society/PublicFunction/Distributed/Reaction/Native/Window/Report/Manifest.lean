import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Fields
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Manifest
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Manifest
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)
structure Completed where
  private mk ::
  base : Fields.Completed bound start span
  native : Window.Manifest.Completed bound start span
inductive Cursor where
  | source (state : Fields.Cursor bound start span)
  | native (base : Fields.Completed bound start span) (state : Window.Manifest.Cursor bound start span)
def initial : Cursor bound start span := .source (Fields.initial bound start span)
noncomputable def capacity := Fields.capacity bound start span+Window.Manifest.capacity bound start span+1
variable {bound start span}
noncomputable def Cursor.rank : Cursor bound start span → Nat
  | .source state => state.rank+Window.Manifest.capacity bound start span+1
  | .native _ state => state.rank
inductive Event (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat) where
  | source (event : Fields.Event bound start span)
  | beginManifest
  | native (event : Window.Manifest.Event bound start span)
def Cursor.move : Cursor bound start span → Option (Event bound start span × Cursor bound start span)
  | .source state => match done : state.completed with
    | some collected => some (.beginManifest,.native collected (Window.Manifest.initial bound start span))
    | none => match moved : state.move with
      | none => False.elim (by have complete := (Fields.Cursor.completed_iff_stopped state).mpr moved;rw [done] at complete;cases complete)
      | some (event,next) => some (.source event,.source next)
  | .native collected state => state.move.map fun (event,next) => (.native event,.native collected next)
def Cursor.completed : Cursor bound start span → Option (Completed bound start span)
  | .source _ => none
  | .native collected state => state.completed.map fun fields => ⟨collected,fields⟩
theorem initial_rank : (initial bound start span).rank = capacity bound start span := by
  simp only [initial,Cursor.rank,Fields.initial_rank,capacity]

theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Event bound start span}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | source state =>
    dsimp only [Cursor.move] at actual;split at actual
    · rename_i collected done;cases actual
      have zero := (Fields.Cursor.stopped_iff_zero state).mp ((Fields.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,Window.Manifest.initial_rank,zero];omega
    · rename_i pending;split at actual
      · rename_i stopped
        have complete := (Fields.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · rename_i native next moved;cases actual
        have decrease := Fields.Cursor.move_decreases moved;dsimp only [Cursor.rank];omega
  | native collected state =>
    dsimp only [Cursor.move] at actual
    cases moved : state.move with
    | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
    | some pair =>
      rcases pair with ⟨native,next⟩;rw [moved] at actual;cases actual
      exact Window.Manifest.Cursor.move_decreases moved

theorem Cursor.completed_iff_stopped (cursor : Cursor bound start span) : cursor.completed.isSome = true ↔ cursor.move = none := by
  cases cursor with
  | source state =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move];split
    · simp
    · rename_i pending;split
      · rename_i stopped
        have complete := (Fields.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
      · simp
  | native collected state =>
    have same := Window.Manifest.Cursor.completed_iff_stopped state
    cases done : state.completed <;> cases moved : state.move <;> simp [Cursor.completed,Cursor.move,done,moved] at *
theorem Cursor.stopped_iff_zero (cursor : Cursor bound start span) : cursor.move = none ↔ cursor.rank = 0 := by
  cases cursor with
  | source state =>
    have active : (Cursor.source state).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped (Cursor.source state)).mpr stopped;cases complete
    simp only [active,false_iff,Cursor.rank];omega
  | native collected state =>
    have same : (Cursor.native collected state).move = none ↔ state.move = none := by cases moved : state.move <;> simp [Cursor.move,moved]
    rw [same];exact Window.Manifest.Cursor.stopped_iff_zero state

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
  ⟨cache.base.financial.originalDebts,cache.base.financial.admittedDebts,cache.base.financial.rights,cache.base.financial.unmatchedClaims,
    cache.base.base.services.startValues,cache.native.control⟩
theorem Completed.profile_exact (cache : Completed bound start span) : cache.profile = Window.profile bound start span := by
  have control : cache.native.control = ⟨(Window.terminal bound start span).technology,(Window.terminal bound start span).clock,(Window.terminal bound start span).round⟩ := cache.native.control_exact
  unfold Completed.profile Window.profile
  rw [cache.base.financial.originalDebts_exact,cache.base.financial.admittedDebts_exact,cache.base.financial.rights_exact,
    cache.base.financial.unmatchedClaims_exact,cache.base.base.services.startValues_exact,control]
def Completed.evaluation (cache : Completed bound start span) : Evaluation bound.source.code where
  legal := cache.base.base.material.legal
  complete := cache.base.base.services.complete
  profile := cache.profile
  native := cache.native.manifest
  value := fun axis => match axis with
    | .material metric => cache.base.base.material.material metric
    | .unpaid index holder => cache.base.financial.unpaid index holder
    | .service index => (((cache.base.base.services.at index).atEnd).getD (Window.finish start span) : ℚ)
theorem Completed.evaluation_exact (cache : Completed bound start span) : cache.evaluation = Window.evaluate bound start span := by
  have legal : cache.base.base.material.legal = Window.legal bound start span := (cache.base.base.material.at .admissibility).exact_lawful rfl
  have complete : cache.base.base.services.complete = (Window.evaluate bound start span).complete := by
    simpa only [Window.evaluate,Window.finish,Nat.add_sub_cancel] using cache.base.base.services.complete_exact
  have values : cache.evaluation.value = (Window.evaluate bound start span).value := by
    funext axis;cases axis with
    | material metric => exact (cache.base.base.material.at metric).exact_value
    | unpaid index holder => exact cache.base.financial.unpaid_exact index holder
    | service index =>
        dsimp only [Completed.evaluation,Window.evaluate,Window.value]
        rw [(cache.base.base.services.at index).end_exact]
        simp only [Window.finish,Nat.add_sub_cancel]
  unfold Completed.evaluation Window.evaluate
  simp only [Evaluation.mk.injEq]
  exact ⟨legal,complete,cache.profile_exact,cache.native.manifest_exact,values⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Manifest
