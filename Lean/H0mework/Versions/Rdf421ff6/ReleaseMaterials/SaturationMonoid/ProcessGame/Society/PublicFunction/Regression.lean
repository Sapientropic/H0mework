import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.CapturedSource

/-! Actual compilation of a captured request, independent paid service,
complete control blockage and exhausted inventory. The original seven units
of debt survive service replacement; it is never labelled settlement. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Regression

open Institutions.Capitalism.Universal.Source.Program

abbrev Current := RawCurrent Bool Unit Unit Unit
abbrev Action := Request Bool Unit Unit Unit Unit

def law (captured : Bool) : RawLaw Bool Unit Unit Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ _ => false
  allowed := fun _ _ signer => !captured && signer
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ _ => [((), 1)]
  mandatoryMaintenance := fun _ _ => [((), 1)]
  duration := fun _ => 1

def initial (stock : ℚ) : Current where
  stock := fun party _ => if party then stock else 0
  claims := fun _ _ _ => 7
  technology := ()
  clock := 0
  round := 0

def transfer (signer : Bool) : Action :=
  ⟨signer, [], (), [], .transfer true false [((), 2)]⟩

def necessity : Action := ⟨true, [], (), [], .use false [((), 1)] .necessity⟩
def maintenance : Action := ⟨true, [], (), [], .use false [((), 1)] .maintenance⟩

def alphabet : List Action := [transfer false, transfer true, necessity, maintenance]

def taskAt (current : Current) : PublicTaskSpec Bool Unit :=
  ⟨[⟨false, [((), 1)], .necessity⟩, ⟨false, [((), 1)], .maintenance⟩],
    current.clock, current.clock + 1, by decide +kernel⟩

def code (captured : Bool) (stock : ℚ) : SourceCode Bool Unit Unit Unit Unit :=
  ⟨law captured, initial stock, taskAt, fun _ => alphabet, 3⟩

def isPaid {law : RawLaw Bool Unit Unit Unit Unit} {current task alphabet budget}
    (outcome : PlanningOutcome law current task alphabet budget) : Bool :=
  match outcome with | .paid _ => true | _ => false

def isCapture {law : RawLaw Bool Unit Unit Unit Unit} {current task alphabet budget}
    (outcome : PlanningOutcome law current task alphabet budget) : Bool :=
  match outcome with | .capture _ => true | _ => false

def isPhysical {law : RawLaw Bool Unit Unit Unit Unit} {current task alphabet budget}
    (outcome : PlanningOutcome law current task alphabet budget) : Bool :=
  match outcome with | .physical _ => true | _ => false

theorem captured_original_cannot_start :
    ¬ (law false).Valid (initial 2) (transfer false) := by decide +kernel

theorem original_exit_is_zero :
    ((law false).next (initial 2) [transfer false]).stock false () = 0 := by decide +kernel

theorem replacement_is_generated :
    isPaid ((code false 2).compileAt (initial 2)) = true := by decide +kernel

theorem generated_word_is_different :
    (code false 2).body (initial 2) = [transfer true, necessity, maintenance] := by with_unfolding_all rfl

theorem full_capture_is_control_blockage :
    isCapture ((code true 2).compileAt (initial 2)) = true := by decide +kernel

theorem no_inventory_is_physical_obstruction :
    isPhysical ((code false 0).compileAt (initial 0)) = true := by decide +kernel

theorem insufficient_execution_budget_is_visible :
    isPhysical (compile (law false) (initial 2) (taskAt (initial 2)) alphabet 2) = true := by decide +kernel

theorem real_root_executes_replacement :
    ((code false 2).actualExecution 0).submitted = [transfer true, necessity, maintenance] ∧
    ((code false 2).actualExecution 0).after.stock true () = 0 ∧
    ((code false 2).actualExecution 0).after.stock false () = 0 ∧
    ((code false 2).actualExecution 0).after.claims () true false = 7 ∧
    (code false 2).currentAt 2 = ((code false 2).actualExecution 0).after := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [(code false 2).actual_execution_word]
    with_unfolding_all rfl
  · change ((law false).next _ _).stock true () = 0
    rw [(code false 2).source_word_exact]
    decide +kernel
  · change ((law false).next _ _).stock false () = 0
    rw [(code false 2).source_word_exact]
    decide +kernel
  · change ((law false).next _ _).claims () true false = 7
    rw [(code false 2).source_word_exact]
    decide +kernel
  · exact ((code false 2).actualExecution 0).root_next_exact.symm

theorem exhausted_successor_does_not_fabricate_renewal :
    isPhysical ((code false 2).outcomeAt 2) = true := by decide +kernel

theorem captured_root_preserves_stock_and_original_debt :
    ((code true 2).actualExecution 0).submitted = [] ∧
    ((code true 2).actualExecution 0).after.stock true () = 2 ∧
    ((code true 2).actualExecution 0).after.claims () true false = 7 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(code true 2).actual_execution_word]; decide +kernel
  · change ((law true).next _ _).stock true () = 2
    rw [(code true 2).source_word_exact]; decide +kernel
  · change ((law true).next _ _).claims () true false = 7
    rw [(code true 2).source_word_exact]; decide +kernel

def capturedSource : CapturedSource Bool Unit Unit Unit Unit :=
  ⟨code false 2, [transfer false], by decide +kernel⟩

def fullyCapturedSource : CapturedSource Bool Unit Unit Unit Unit :=
  ⟨code true 2, [transfer false], by decide +kernel⟩

theorem full_capture_blockage_is_rooted :
    isCapture (fullyCapturedSource.code.compileAt (fullyCapturedSource.currentAt 2)) = true ∧
    (fullyCapturedSource.actualExecution 1).submitted = [] ∧
    (fullyCapturedSource.actualExecution 1).after.stock true () = 2 ∧
    (fullyCapturedSource.actualExecution 1).after.claims () true false = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · rw [fullyCapturedSource.planning_is_actually_executed]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem actual_capture_then_replacement :
    (capturedSource.actualExecution 0).submitted = [transfer false] ∧
    (capturedSource.actualExecution 0).after.stock false () = 0 ∧
    (capturedSource.actualExecution 1).submitted = [transfer true, necessity, maintenance] ∧
    (capturedSource.actualExecution 1).after.stock true () = 0 ∧
    (capturedSource.actualExecution 1).after.claims () true false = 7 ∧
    capturedSource.currentAt 3 = (capturedSource.actualExecution 1).after := by
  refine ⟨capturedSource.original_is_actually_executed, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · rw [capturedSource.planning_is_actually_executed]
    with_unfolding_all rfl
  · decide +kernel
  · decide +kernel
  · exact (capturedSource.actualExecution 1).root_next_exact.symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Regression
