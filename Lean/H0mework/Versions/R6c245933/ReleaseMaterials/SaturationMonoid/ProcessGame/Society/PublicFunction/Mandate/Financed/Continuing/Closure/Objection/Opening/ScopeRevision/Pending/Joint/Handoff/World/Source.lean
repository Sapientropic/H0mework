import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Handoff

/-! Actual expiry schedules a checked review and a debt response. The
resulting review alone generates a later epoch or its typed obstruction. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def reviewMenu (_inventory : Inventory epoch) : List Future.Choice :=
  [.direct,.productive,.supplied,.financed].flatMap fun method =>
    (Delegation.members epoch.scope.task).map fun actor => ⟨actor,method⟩

def reviewFront (choice : Future.Choice) : List Action :=
  match choice.method with
  | .direct => []
  | .productive => [Exit.production choice.actor]
  | .supplied => Future.provision (current epoch inventory.inputs) choice.actor
  | .financed => Future.funding (current epoch inventory.inputs) choice.actor 1

def reviewCandidate (choice : Future.Choice) : List Action :=
  let front := reviewFront inventory choice
  let before := (Mandate.law base epoch.scope).execute (current epoch inventory.inputs) 0 front |>.final
  front ++ [Mandate.request epoch.scope before choice.actor .review,
    ⟨choice.actor,[],epoch.scope.challenge,[epoch.scope.challenge],.present⟩]

def ReviewLegal (choice : Future.Choice) : Prop :=
  epoch.scope.task.deadline < (current epoch inventory.inputs).clock ∧
    ∀ item ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) (reviewCandidate inventory choice),
      (Mandate.law base epoch.scope).Valid item.before item.request

instance (choice : Future.Choice) : Decidable (ReviewLegal inventory choice) := by unfold ReviewLegal; infer_instance

structure ReviewPaid where
  private mk ::
  choice : Future.Choice
  listed : choice ∈ reviewMenu inventory
  legal : ReviewLegal inventory choice

def chooseReview : Option (ReviewPaid inventory) :=
  match selected : (reviewMenu inventory).find? (fun choice => decide (ReviewLegal inventory choice)) with
  | some choice => some ⟨choice,List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun choice => decide (ReviewLegal inventory choice)) selected)⟩
  | none => none

theorem review_failure_covers_the_actual_finite_menu (absent : chooseReview inventory = none) :
    ∀ choice ∈ reviewMenu inventory, ¬ ReviewLegal inventory choice := by
  unfold chooseReview at absent
  split at absent
  · cases absent
  · rename_i noChoice
    intro choice inside legal
    have refused := List.find?_eq_none.mp noChoice choice inside
    rw [decide_eq_true legal] at refused
    exact refused rfl

inductive ReviewOutcome where
  | private young (early : ¬ epoch.scope.task.deadline < (current epoch inventory.inputs).clock)
  | private paid (payment : ReviewPaid inventory) (selected : chooseReview inventory = some payment)
  | private blocked (expired : epoch.scope.task.deadline < (current epoch inventory.inputs).clock)
      (absent : chooseReview inventory = none)
      (failed : ∀ choice ∈ reviewMenu inventory, ¬ ReviewLegal inventory choice)

def reviewOutcome : ReviewOutcome inventory :=
  if expired : epoch.scope.task.deadline < (current epoch inventory.inputs).clock then
    match selected : chooseReview inventory with
    | some payment => .paid payment selected
    | none => .blocked expired selected (review_failure_covers_the_actual_finite_menu inventory selected)
  else .young expired

def reviewWord : List Action :=
  if epoch.scope.task.deadline < (current epoch inventory.inputs).clock then
    reviewCandidate inventory ((chooseReview inventory).map ReviewPaid.choice |>.getD
      ⟨(Mandate.Response.firstMember epoch.scope).val,.direct⟩)
  else []

theorem paid_review_word_is_actually_checked (payment : ReviewPaid inventory) (selected : chooseReview inventory = some payment) :
    reviewWord inventory = reviewCandidate inventory payment.choice ∧
    ∀ item ∈ (Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) (reviewWord inventory),
      (Mandate.law base epoch.scope).Valid item.before item.request := by
  have same : reviewWord inventory = reviewCandidate inventory payment.choice := by
    simp only [reviewWord,if_pos payment.legal.1,selected,Option.map_some,Option.getD_some]
  exact ⟨same,by rw [same]; exact payment.legal.2⟩

def staged := submit inventory (reviewWord inventory)
def repaymentWord := Repayment.Portfolio.word (Mandate.law base epoch.scope)
  (Handoff.debtPositions (current epoch (staged inventory).inputs)) (current epoch (staged inventory).inputs)
def reviewed := submit (staged inventory) (repaymentWord inventory)
abbrev reviewInput := I epoch (reviewed inventory).inputs
def cycleResult := generate (reviewed inventory)
def next : Packet := (cycleResult inventory).packet (reviewed inventory)

theorem review_inputs_exact : (reviewed inventory).inputs = inventory.inputs ++ [reviewWord inventory,repaymentWord inventory] := by
  change (inventory.inputs ++ [reviewWord inventory]) ++ [repaymentWord inventory] = _
  rw [List.append_assoc]
  rfl

def reviewExecution := OutstandingSource.History.actualExecution epoch.source (reviewed inventory).inputs (inventory.inputs.length + 1)
def repaymentExecution := OutstandingSource.History.actualExecution epoch.source (reviewed inventory).inputs ((staged inventory).inputs.length + 1)

theorem actual_review_word_and_saved_cut : (reviewExecution inventory).submitted = reviewWord inventory ∧
    (reviewExecution inventory).before = current epoch inventory.inputs := by
  constructor
  · have inside : inventory.inputs.length < (reviewed inventory).inputs.length := by rw [review_inputs_exact]; simp
    have real := OutstandingSource.History.scheduled_input_is_actual epoch.source (reviewed inventory).inputs inventory.inputs.length inside
    have chosen : (reviewed inventory).inputs[inventory.inputs.length] = reviewWord inventory := by
      simp only [review_inputs_exact,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    exact real.trans chosen
  · have same := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix epoch.source inventory.inputs
      [reviewWord inventory,repaymentWord inventory] (inventory.inputs.length + 2) (Nat.le_refl _)
    change OutstandingSource.History.currentAt epoch.source (reviewed inventory).inputs (inventory.inputs.length + 2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,review_inputs_exact,same]
    exact (OutstandingSource.History.actual_frame _ _ _).1.symm

theorem actual_repayment_word_and_cut : (repaymentExecution inventory).submitted = repaymentWord inventory ∧
    (repaymentExecution inventory).before = current epoch (staged inventory).inputs := actual_word_and_cut _ _

def reviewFinancialRun : (Financial.Family.process sources).Run inventory.finance.current (reviewed inventory).finance.current :=
  (financialRun inventory (reviewWord inventory)).concatRuns _ (financialRun (staged inventory) (repaymentWord inventory))

def nextFinancialRun : (Financial.Family.process sources).Run inventory.finance.current (next inventory).2.finance.current :=
  (reviewFinancialRun inventory).concatRuns _ ((cycleResult inventory).financialRun (reviewed inventory))

def evolve (packet : Packet) : Nat → Packet
  | 0 => packet
  | count + 1 => evolve (next packet.2) count

def evolutionFinancialRun (packet : Packet) : (count : Nat) →
    (Financial.Family.process sources).Run packet.2.finance.current (evolve packet count).2.finance.current
  | 0 => .nil
  | count + 1 => (nextFinancialRun packet.2).concatRuns _ (evolutionFinancialRun (next packet.2) count)

def alternate (packet : Packet) : List (List Action) → Packet
  | [] => packet
  | word :: tail => alternate (next (submit packet.2 word)) tail

def alternateFinancialRun (packet : Packet) : (words : List (List Action)) →
    (Financial.Family.process sources).Run packet.2.finance.current (alternate packet words).2.finance.current
  | [] => .nil
  | word :: tail => (financialRun packet.2 word).concatRuns _
      ((nextFinancialRun (submit packet.2 word)).concatRuns _ (alternateFinancialRun (next (submit packet.2 word)) tail))

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
