import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Decision

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock
open PublicFunction PublicFunction.Mandate

abbrev Party := Fin 3

inductive Port where
  | service | challenge | resource
  deriving DecidableEq

abbrev Raw := RawCurrent Party Unit (State Party Unit) Unit
abbrev Req := Request Party Unit Port (State Party Unit) Unit
abbrev Word := List Req

def task : PublicTaskSpec Party Unit :=
  ⟨[⟨0, [((), 1)], .maintenance⟩, ⟨1, [((), 1)], .maintenance⟩],
    0, 4, ⟨_, List.mem_cons_self, _, List.mem_cons_self, by decide⟩⟩

def base : RawLaw Party Unit Port Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ _ => 2
  allowed := fun _ port _ => decide (port = .resource)
  stockPort := fun _ _ _ => .resource
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [((), 1)]
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => .resource
  necessities := fun _ _ => []
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

def scope : Scope (Party := Party) (Good := Unit) (Port := Port) :=
  ⟨task, .service, .challenge, by decide, [((), 1)]⟩

abbrev active := law base scope

def initial : Raw :=
  ⟨fun _ _ => 5, fun _ _ _ => 0, ⟨(), 0, none, none, none⟩, 0, 0⟩

def refusedRequest : Req := ⟨2, [], .service, [.service], .present⟩

def issue : Req := ⟨0, [], .resource, [], .issue () 0 1 2⟩

def originalWord : Word :=
  let before := active.next initial []
  let proposal := request scope before 0 (.propose 2)
  let offered := active.step before proposal
  [refusedRequest, proposal, request scope offered 2 .accept, issue]

def source : OutstandingSource Party Unit Port (State Party Unit) Unit where
  seed := {
    law := active
    initial := initial
    task := task
    actionsAt := fun _ => []
    budget := 0
    original := originalWord
    refused := by decide +kernel }
  positive := by
    intro slot member
    simp only [task, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨((), 1), List.mem_cons_self, by decide⟩

def bound : BoundSource base scope := ⟨source, rfl⟩

def past : List Word := [[], [], []]

abbrev cut := OutstandingSource.History.currentAt source past 5

def reviews : Word := reviewPair base scope cut 0 1

def submitted : List Word := past ++ [reviews]

abbrev actual := OutstandingSource.History.actualExecution source submitted 4

theorem the_review_word_is_the_actual_source_submission : actual.submitted = reviews := by
  exact OutstandingSource.History.scheduled_input_is_actual source submitted 3 (by decide)

theorem the_review_current_is_the_unreset_original_expired_cut : actual.before = cut := by
  change OutstandingSource.History.currentAt source (past ++ [reviews]) 5 =
    OutstandingSource.History.currentAt source past 5
  rw [(OutstandingSource.History.actual_frame source (past ++ [reviews]) 5).1,
    (OutstandingSource.History.actual_frame source past 5).1,
    OutstandingSource.History.extending_inputs_preserves_its_executed_prefix source past [reviews] 5 (by decide)]

theorem the_scope_deadline_is_crossed_at_five_for_every_actual_history
    (inputs : List Word) (ordinal : Nat) :
    scope.task.deadline < Mandate.clockAt bound inputs ordinal ↔ 5 ≤ ordinal := by
  have original := Mandate.exact_expiry_for_owned_constant_duration bound inputs 1
    (by decide) (fun _ => rfl) ordinal
  have exactOrdinal : Mandate.expiryOrdinal bound.source.seed.initial.clock scope.task.deadline 1 = 5 := by
    decide +kernel
  simpa only [exactOrdinal] using original

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Consumers
