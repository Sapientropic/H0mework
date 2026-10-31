import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Effects

/-! The last actual input closes directly into a new scope or its original
obstruction. No further review or repayment is inserted into this source. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} {inventory : Inventory epoch}

def lastAttempt (execution : Execution inventory) : Sigma fun _ : Inventory epoch => Intent :=
  Execution.rec (motive := fun _ _ => Sigma fun _ : Inventory epoch => Intent)
    (fun saved intent _ => ⟨cut saved intent,intent⟩)
    (fun saved _ _ => ⟨cut saved .revision,.revision⟩)
    (fun _ _ _ _ _ final => final) execution

theorem last_attempt_has_the_complete_final_inventory (execution : Execution inventory) :
    Input.advance (lastAttempt execution).1 (lastAttempt execution).2 = execution.finalInventory := by
  induction execution
  next saved intent reason => rfl
  next saved payment selected => rfl
  next saved intent payment selected next ih => exact ih

def I (inventory : Inventory epoch) := Input.I (lastAttempt (Programme.produce inventory)).1 (lastAttempt (Programme.produce inventory)).2

theorem source_inputs_are_exactly_the_executed_programme (inventory : Inventory epoch) :
    (Input.advance (lastAttempt (Programme.produce inventory)).1 (lastAttempt (Programme.produce inventory)).2).inputs =
      (Programme.produce inventory).finalInventory.inputs :=
  congrArg Inventory.inputs (last_attempt_has_the_complete_final_inventory (Programme.produce inventory))

structure PaidNext (execution : Execution inventory) where
  private mk ::
  fresh : Handoff.Ready epoch.bound execution.finalInventory.inputs
  chosen : Handoff.choose epoch.bound execution.finalInventory.inputs = some fresh
  payment : Handoff.Paid fresh (Handoff.start fresh)
  selected : Handoff.select fresh (Handoff.start fresh) = some payment
  opening : Handoff.PaidOpening fresh (Handoff.actual fresh 1).before (Handoff.actual fresh 1).submitted
  origin : (World.handoff execution.finalInventory fresh).originOpening.paidOpening? fresh = some opening

def PaidNext.packet {execution : Execution inventory} (next : PaidNext execution) : Packet :=
  ⟨Epoch.ofFresh next.fresh,World.handoff execution.finalInventory next.fresh⟩

inductive Decision (execution : Execution inventory) where
  | private paid (next : PaidNext execution)
  | private reviewBlocked (absent : Handoff.choose epoch.bound execution.finalInventory.inputs = none)
      (reason : Handoff.Blocked epoch.bound execution.finalInventory.inputs)
  | private replacementBlocked (fresh : Handoff.Ready epoch.bound execution.finalInventory.inputs)
      (chosen : Handoff.choose epoch.bound execution.finalInventory.inputs = some fresh)
      (absent : Handoff.select fresh (Handoff.start fresh) = none)
      (actual : Handoff.Failure fresh (Handoff.actual fresh 1).before (Handoff.actual fresh 1).submitted)
      (methods : (method : Handoff.Method) → method ∈ Handoff.methods →
        Handoff.Failure fresh (Handoff.start fresh) (Handoff.candidate fresh (Handoff.start fresh) method))

def generate (execution : Execution inventory) : Decision execution :=
  match chosen : Handoff.choose epoch.bound execution.finalInventory.inputs with
  | some fresh => match selected : Handoff.select fresh (Handoff.start fresh) with
    | some payment =>
      .paid ⟨fresh,chosen,payment,selected,Handoff.actualPaidOpening fresh payment selected,
        Handoff.selected_actual_opening_is_in_the_generated_outcome fresh payment selected⟩
    | none => .replacementBlocked fresh chosen selected (Handoff.actualFailure fresh selected)
        (fun method listed => Handoff.failedMethod fresh selected method listed)
  | none => .reviewBlocked chosen (Handoff.every_failed_handoff_has_an_actual_reason _ _ chosen)

def Decision.kind {execution : Execution inventory} : Decision execution → World.ContinuationKind
  | .paid .. => .paid
  | .reviewBlocked .. => .reviewBlocked
  | .replacementBlocked .. => .replacementBlocked

theorem selected_payment_generates_a_paid_new_scope (execution : Execution inventory)
    (fresh : Handoff.Ready epoch.bound execution.finalInventory.inputs)
    (chosen : Handoff.choose epoch.bound execution.finalInventory.inputs = some fresh)
    (payment : Handoff.Paid fresh (Handoff.start fresh))
    (selected : Handoff.select fresh (Handoff.start fresh) = some payment) :
    (generate execution).kind = .paid := by
  unfold generate
  split
  next other actualChoice =>
    have same := Option.some.inj (actualChoice.symm.trans chosen)
    subst other
    split
    next paid actualPayment => rfl
    next absent => cases absent.symm.trans selected
  next absent => cases absent.symm.trans chosen

theorem an_actual_review_cannot_be_reported_as_review_blocked (execution : Execution inventory)
    (present : (Handoff.choose epoch.bound execution.finalInventory.inputs).isSome = true) :
    (generate execution).kind ≠ .reviewBlocked := by
  unfold generate
  split
  next fresh chosen =>
    split
    next payment selected => intro impossible; cases impossible
    next absent => intro impossible; cases impossible
  next absent => simp only [absent,Option.isSome_none,Bool.false_eq_true] at present

def Decision.packet {execution : Execution inventory} : Decision execution → Packet
  | .paid next => next.packet
  | .reviewBlocked .. => ⟨epoch,execution.finalInventory⟩
  | .replacementBlocked fresh .. => ⟨Epoch.ofFresh fresh,World.handoff execution.finalInventory fresh⟩

theorem Decision.packet_is_the_actual_direct_handoff {execution : Execution inventory} (decision : Decision execution) :
    decision.packet = (World.generate execution.finalInventory).packet _ := by
  cases decision
  next next => exact (World.generated_packet_of_selected _ next.fresh next.chosen).symm
  next absent reason =>
    unfold World.generate
    split
    next fresh chosen => cases absent.symm.trans chosen
    next none => rfl
  next fresh chosen absent actual methods => exact (World.generated_packet_of_selected _ fresh chosen).symm

def Decision.financialRun {execution : Execution inventory} (decision : Decision execution) :
    (Financial.Family.process sources).Run inventory.finance.current decision.packet.2.finance.current := by
  rw [decision.packet_is_the_actual_direct_handoff]
  exact execution.finalFinancialRun.concatRuns _ (World.Result.financialRun _ (World.generate execution.finalInventory))

theorem Decision.every_past_cohort_continues {execution : Execution inventory} (decision : Decision execution) :
    inventory.pastGrants.map GrantCohort.origin <+: decision.packet.2.pastGrants.map GrantCohort.origin ∧
    inventory.pastChallenges.map ChallengeCohort.origin <+: decision.packet.2.pastChallenges.map ChallengeCohort.origin ∧
    inventory.pastServices.map ServiceCohort.origin <+: decision.packet.2.pastServices.map ServiceCohort.origin := by
  rw [decision.packet_is_the_actual_direct_handoff]
  have before := execution.all_past_cohorts_continue inventory
  have after := World.Result.all_original_cohorts_are_prefixes _ (World.generate execution.finalInventory)
  rw [before.1,before.2.1,before.2.2] at after
  exact after

theorem PaidNext.all_original_service_slots_are_paid {execution : Execution inventory} (next : PaidNext execution) (index : epoch.source.Slot) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (Handoff.law next.fresh)
      (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted
      (epoch.source.seed.slot index).bearer (epoch.source.seed.slot index).goods (epoch.source.seed.slot index).purpose := by
  have payment := (Handoff.selected_word_really_pays next.fresh next.payment next.selected).2.2.2
    ((Handoff.source next.fresh).seed.slot (Handoff.homologous next.fresh index))
    (List.getElem_mem (Handoff.homologous next.fresh index).isLt)
  rw [Handoff.original_slot_content_is_preserved next.fresh index] at payment
  exact payment

theorem terminal_input_is_the_actual_last_attempt (execution : Execution inventory) :
    Handoff.reported epoch.bound execution.finalInventory.inputs = Input.emit (lastAttempt execution).1 (lastAttempt execution).2 ∧
    Handoff.before epoch.bound execution.finalInventory.inputs = current epoch (lastAttempt execution).1.inputs := by
  have same := last_attempt_has_the_complete_final_inventory execution
  have actual := Input.actual_word_and_cut (lastAttempt execution).1 (lastAttempt execution).2
  rw [← same]
  have length : (Input.advance (lastAttempt execution).1 (lastAttempt execution).2).inputs.length = (lastAttempt execution).1.inputs.length + 2 := by
    rw [Input.inputs_exact]
    simp
  constructor
  · change ProgrammeSource.rawEvent (Input.I (lastAttempt execution).1 (lastAttempt execution).2)
      (ProgrammeHistory.visitAt (Input.I (lastAttempt execution).1 (lastAttempt execution).2)
        (Input.advance (lastAttempt execution).1 (lastAttempt execution).2).inputs.length).current = _
    rw [length]
    exact actual.1
  · change OutstandingSource.History.currentAt epoch.source
      (Input.advance (lastAttempt execution).1 (lastAttempt execution).2).inputs
      (Input.advance (lastAttempt execution).1 (lastAttempt execution).2).inputs.length = _
    rw [length]
    exact actual.2

theorem the_new_scope_review_belongs_to_the_same_last_execution (execution : Execution inventory)
    (fresh : Handoff.Ready epoch.bound execution.finalInventory.inputs) :
    fresh.actual.item.val ∈ (Input.execution (lastAttempt execution).1 (lastAttempt execution).2).interpreted.items ∧
    (Mandate.law base epoch.scope).Valid fresh.actual.item.val.before fresh.actual.item.val.request := by
  refine ⟨?_,fresh.actual.accepted⟩
  rw [(Input.execution (lastAttempt execution).1 (lastAttempt execution).2).interpreted_exact]
  have law : (Input.I (lastAttempt execution).1 (lastAttempt execution).2).law = Mandate.law base epoch.scope := epoch.bound.law_exact
  rw [law,(Input.actual_word_and_cut (lastAttempt execution).1 (lastAttempt execution).2).1,
    (Input.actual_word_and_cut (lastAttempt execution).1 (lastAttempt execution).2).2]
  rw [← (terminal_input_is_the_actual_last_attempt execution).1,← (terminal_input_is_the_actual_last_attempt execution).2]
  exact fresh.actual.item.property

theorem no_additional_review_or_repayment_is_emitted (execution : Execution inventory) :
    (Input.advance (lastAttempt execution).1 (lastAttempt execution).2).inputs.length + 2 =
      (World.reviewed execution.finalInventory).inputs.length := by
  rw [last_attempt_has_the_complete_final_inventory,World.review_inputs_exact]
  simp

theorem PaidNext.initial_is_the_actual_complete_after {execution : Execution inventory} (next : PaidNext execution) :
    (Handoff.I next.fresh).initial = current epoch execution.finalInventory.inputs := rfl

variable (execution : Execution inventory) (stage : PaidStage (epoch := epoch)) (member : stage ∈ execution.paidStages)
def actual := OutstandingSource.History.actualExecution epoch.source execution.finalInventory.inputs (stage.inventory.inputs.length + 1)

include member
theorem paid_stage_frames_are_the_same_actual_prefix :
    (actual execution stage).before = (stage.actual execution).before ∧
    (actual execution stage).submitted = (stage.actual execution).submitted ∧
    (actual execution stage).after = (stage.actual execution).after := by
  have past :=  execution.every_record_is_an_actual_prefix inventory ⟨stage.inventory,stage.intent⟩
    (execution.every_paid_stage_is_an_actual_record stage member)
  have length := past.length_le
  rw [Input.inputs_exact,List.length_append] at length
  simp only [List.length_cons,List.length_nil] at length
  let final := execution.finalInventory
  let first := World.reviewWord final
  let second := World.repaymentWord final
  have shape : (World.reviewed final).inputs = (final.inputs ++ [first]) ++ [second] := rfl
  have oldWord : (stage.actual execution).submitted = (actual execution stage).submitted := by
    change (OutstandingSource.History.actualExecution epoch.source (World.reviewed final).inputs (stage.inventory.inputs.length+1)).submitted = _
    rw [shape]
    have later := Mandate.Challenge.Cross.common_word epoch.bound (final.inputs ++ [first]) second
      (stage.inventory.inputs.length+1) (by dsimp only [final]; simp only [List.length_append,List.length_singleton]; omega)
    have earlier := Mandate.Challenge.Cross.common_word epoch.bound final.inputs first
      (stage.inventory.inputs.length+1) (by dsimp only [final]; omega)
    exact later.trans earlier
  have oldBefore : (stage.actual execution).before = (actual execution stage).before := by
    change OutstandingSource.History.currentAt epoch.source (World.reviewed final).inputs (stage.inventory.inputs.length+2) = _
    rw [shape]
    have later := Mandate.Challenge.Cross.common_current epoch.bound (final.inputs ++ [first]) second
      (stage.inventory.inputs.length+2) (by dsimp only [final]; simp only [List.length_append,List.length_singleton]; omega)
    have earlier := Mandate.Challenge.Cross.common_current epoch.bound final.inputs first
      (stage.inventory.inputs.length+2) (by dsimp only [final]; omega)
    exact later.trans earlier
  refine ⟨oldBefore.symm,oldWord.symm,?_⟩
  rw [(actual execution stage).after_exact,(stage.actual execution).after_exact]
  change epoch.source.seed.law.next (actual execution stage).before (actual execution stage).submitted =
    epoch.source.seed.law.next (stage.actual execution).before (stage.actual execution).submitted
  rw [oldBefore,oldWord]

theorem every_paid_stage_has_its_effect_in_the_direct_source :
    stage.EffectAt (actual execution stage).after (actual execution stage).submitted := by
  have effect := Programme.every_paid_phase_has_its_actual_native_effect execution stage member
  change stage.EffectAt (stage.actual execution).after (stage.actual execution).submitted at effect
  have same := paid_stage_frames_are_the_same_actual_prefix execution stage member
  rw [same.2.2,same.2.1]
  exact effect

structure Disposition (inventory : Inventory epoch) where
  private mk ::
  decision : Decision (Programme.produce inventory)
  decision_exact : decision = generate (Programme.produce inventory)
  paidEffects : ∀ stage ∈ (Programme.produce inventory).paidStages,
    stage.EffectAt (actual (Programme.produce inventory) stage).after (actual (Programme.produce inventory) stage).submitted

def produce (inventory : Inventory epoch) : Disposition inventory :=
  ⟨generate (Programme.produce inventory),rfl,
    fun stage member => every_paid_stage_has_its_effect_in_the_direct_source (Programme.produce inventory) stage member⟩

def Disposition.packet {inventory : Inventory epoch} (result : Disposition inventory) := result.decision.packet

def Disposition.financialRun {inventory : Inventory epoch} (result : Disposition inventory) := result.decision.financialRun

omit member in
theorem Disposition.every_past_cohort_continues {inventory : Inventory epoch} (result : Disposition inventory) :
    inventory.pastGrants.map GrantCohort.origin <+: result.packet.2.pastGrants.map GrantCohort.origin ∧
    inventory.pastChallenges.map ChallengeCohort.origin <+: result.packet.2.pastChallenges.map ChallengeCohort.origin ∧
    inventory.pastServices.map ServiceCohort.origin <+: result.packet.2.pastServices.map ServiceCohort.origin :=
  result.decision.every_past_cohort_continues

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion
