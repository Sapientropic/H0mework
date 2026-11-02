import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Regression

/-! An information obstruction is repaired by a real local reading and a
paid message. The two hidden stocks remain different actual histories.
The message's material debit is included in the same source word and vector.
Removing its resource prevents the packet from being generated. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Learning

open Institutions.Capitalism.Universal.Source.Program

abbrev Current := RawCurrent Bool Bool Unit Unit
abbrev Request := Institutions.Capitalism.Universal.Source.Program.Request Bool Bool Unit Unit Unit

def law : RawLaw Bool Bool Unit Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ _ => false
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => false
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ _ => [(false, 1)]
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

def initial (communication : ℚ) : Current where
  stock := fun p g => if g then communication else if p then 2 else 0
  claims := fun _ _ _ => 7
  technology := ()
  clock := 0
  round := 0

def relocate : Request := ⟨true, [], (), [], .transfer true false [(false, 2)]⟩
def route : Request := ⟨true, [], (), [], .transfer true false [(false, 1)]⟩
def serve : Request := ⟨true, [], (), [], .use false [(false, 1)] .necessity⟩
def communicationFee : Request := ⟨true, [], (), [], .use true [(true, 1)] .contribution⟩

def eventTag : Event Bool Bool Unit Unit Unit 1 → Nat
  | .send .. => 0 | .deliver _ => 1 | .activate _ => 2 | .adversary _ => 3

abbrev code : Code Bool Bool Unit Unit Unit where
  law := law
  initial := initial 1
  task := ⟨[⟨false, [(false, 1)], .necessity⟩], 0, 10, by decide +kernel⟩
  actions := [route, serve]
  actionLimit := 2
  sites := 1
  signals := 2
  initialSignal := 0
  siteParty := fun _ => true
  readLocal := fun _ snapshot => if 0 < snapshot.stock false then 1 else 0
  sendCost := fun _ _ => [communicationFee]
  historyAlphabet := [[relocate]]
  historyLimit := 1
  eventAlphabet := [.send 0 0, .deliver 0, .activate 0]
  eventLimit := 3
  eligible := fun events => events.map eventTag == [0, 1, 2]
  parties := [false, true]
  goods := [false, true]
  instruments := [()]
  parties_cover := by intro p; cases p <;> simp
  goods_cover := by intro g; cases g <;> simp
  instruments_cover := by simp

def reference : code.Policy := fun key _ => if key.2 = 1 then [route, serve] else [serve]

def events : List (Event Bool Bool Unit Unit Unit 1) := [.send 0 0, .deliver 0, .activate 0]

def source (relocated : Bool) : Source Bool Bool Unit Unit Unit :=
  ⟨code, reference, if relocated then [[relocate]] else [], events, by
    cases relocated <;>
      apply code.every_legal_history_and_eligible_deviation_is_replayed <;>
      simp [code, events, eventTag, Code.historyLegal]
    decide +kernel⟩

theorem the_same_local_program_solves_both_histories_after_paid_observation :
    reference ∈ code.policies ∧ code.feasible reference := by
  constructor
  · apply code.every_local_policy_is_enumerated
    intro key _
    apply (mem_words_iff _ _ _).mpr
    by_cases signal : key.2 = 1 <;> simp [reference, signal, code]
  · decide +kernel

def isSelected : code.Outcome reference → Bool
  | .selected _ => true | .blocked _ => false

theorem paid_observation_generates_a_feasible_selection : isSelected (code.compile reference) = true := by
  cases generated : code.compile reference with
  | selected choice => rfl
  | blocked rejected => exact False.elim (code.feasible_reference_cannot_be_blocked reference
      the_same_local_program_solves_both_histories_after_paid_observation.1
      the_same_local_program_solves_both_histories_after_paid_observation.2 rejected)

theorem both_actual_sources_pay_for_the_observation_and_the_task :
    ((source false).actualExecution 0).after.stock true true = 0 ∧
    ((source false).actualExecution 0).after.stock true false = 1 ∧
    ((source false).actualExecution 0).after.claims () true false = 7 ∧
    ((source true).actualExecution 1).after.stock true true = 0 ∧
    ((source true).actualExecution 1).after.stock false false = 1 ∧
    ((source true).actualExecution 1).after.claims () true false = 7 := by decide +kernel

abbrev unpaid := { code with initial := initial 0 }
def unpaidReference : unpaid.Policy := fun key _ => if key.2 = 1 then [route, serve] else [serve]

theorem missing_communication_resource_generates_no_packet :
    (unpaid.replay unpaidReference (initial 0) events).sent = [] ∧
      (unpaid.replay unpaidReference (initial 0) events).inbox 0 = 0 ∧
      (unpaid.replay unpaidReference (initial 0) events).localLegal = false := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  with_unfolding_all rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Learning
