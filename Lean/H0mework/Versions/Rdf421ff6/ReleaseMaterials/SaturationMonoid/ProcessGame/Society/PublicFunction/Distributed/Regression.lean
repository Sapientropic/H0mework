import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Regression

open Institutions.Capitalism.Universal.Source.Program

def transfer : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .transfer true false [((), 1)]⟩
def use : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .use false [((), 1)] .necessity⟩
def waste : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .use true [((), 1)] .contribution⟩

abbrev code : Code Bool Unit Unit Unit Unit where
  law := PublicFunction.Regression.law false
  initial := PublicFunction.Regression.initial 2
  task := ⟨[⟨false, [((), 1)], .necessity⟩], 0, 10, by decide +kernel⟩
  actions := [waste, transfer, use]
  actionLimit := 3
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => true
  readLocal := fun _ _ => 0
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0]
  eventLimit := 1
  eligible := fun events => events.length == 1
  parties := [false, true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro p; cases p <;> simp
  goods_cover := by simp
  instruments_cover := by simp

def reference : code.Policy := fun _ _ => [waste, transfer, use]
def efficient : code.Policy := fun _ _ => [transfer, use]

def source : Source Bool Unit Unit Unit Unit := ⟨code, reference, [], [.activate 0], by
  apply code.every_legal_history_and_eligible_deviation_is_replayed <;>
    simp [code, Code.historyLegal]⟩

def isSelected {c : Code Bool Unit Unit Unit Unit} {r : c.Policy} : c.Outcome r → Bool
  | .selected _ => true
  | .blocked _ => false

theorem efficient_policy_passes_independent_replay : code.verify reference efficient = true := by decide +kernel

theorem actual_strict_improvement_is_generated : isSelected source.answer = true ∧
    (source.actualExecution 0).submitted = [transfer, transfer, use] ∧
    (source.actualExecution 0).after.stock false () = 1 ∧
    (source.actualExecution 0).after.claims () true false = 7 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  with_unfolding_all rfl

theorem strict_coordinate_is_actual_material : code.StrictlyImproves reference efficient := by decide +kernel

theorem a_dominated_reference_is_rejected_by_the_independent_verifier :
    code.verify reference reference = false := by decide +kernel

def obscured : Code Bool Unit Unit Unit Unit :=
  { code with
    initial := PublicFunction.Regression.initial 1
    historyAlphabet := [[transfer]]
    historyLimit := 1
    actions := [transfer, use]
    actionLimit := 2 }

def obscuredReference : obscured.Policy := fun _ _ => [transfer, use]

theorem each_hidden_world_is_individually_feasible :
    ServiceAdequate obscured.law (obscured.historyCurrent []) obscured.task [transfer, use] ∧
    ServiceAdequate obscured.law (obscured.historyCurrent [[transfer]]) obscured.task [use] := by decide +kernel

theorem no_uniform_local_policy_solves_both_hidden_worlds :
    (∀ policy ∈ obscured.policies, ¬ obscured.feasible policy) ∧
    isSelected (obscured.compile obscuredReference) = false := by decide +kernel

abbrev stale : Code Bool Unit Unit Unit Unit :=
  { code with
    signals := 2
    memoryReady := fun _ => true
    afterSend := fun _ _ old _ => old
    afterDelivery := fun _ _ _ reading => reading
    afterAction := fun _ old _ => old
    initialSignal := 0
    readLocal := fun _ snapshot => if 0 < snapshot.stock () then 1 else 0 }

def stalePolicy : stale.Policy := fun key _ => if key.2 = 1 then [waste] else []

def staleEvents : List (Event Bool Unit Unit Unit Unit 1) :=
  [.send 0 0, .adversary waste, .adversary waste, .deliver 0, .activate 0]

theorem delayed_reading_does_not_become_current_global_knowledge :
    (stale.replay stalePolicy (PublicFunction.Regression.initial 2) staleEvents).inbox 0 = 1 ∧
    (stale.rawAt (PublicFunction.Regression.initial 2)
      (stale.replay stalePolicy (PublicFunction.Regression.initial 2) staleEvents)).stock true () = 0 ∧
    (stale.replay stalePolicy (PublicFunction.Regression.initial 2) staleEvents).localLegal = false := by decide +kernel

abbrev deviationCode : Code Bool Unit Unit Unit Unit :=
  { code with
    eventAlphabet := [.activate 0, .adversary waste, .send 0 0, .deliver 0]
    eventLimit := 4
    eligible := fun _ => true }

theorem opponents_and_delayed_repeated_delivery_are_covered :
    ([], [.send 0 0, .adversary waste, .deliver 0, .activate 0]) ∈ deviationCode.scenarios ∧
    ([], [.send 0 0, .deliver 0, .deliver 0, .activate 0]) ∈ deviationCode.scenarios := by
  constructor <;>
    apply deviationCode.every_legal_history_and_eligible_deviation_is_replayed <;>
    simp [deviationCode, code, Code.historyLegal]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Regression
