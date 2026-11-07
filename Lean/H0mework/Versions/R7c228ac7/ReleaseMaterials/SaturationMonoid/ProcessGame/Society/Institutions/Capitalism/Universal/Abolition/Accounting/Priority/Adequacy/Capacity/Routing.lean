import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Realization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity

open Source.Program Innovation
open Exit.Necessity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq Technology] [DecidableEq Port]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (front : RawEvent Party Good Port Technology Instrument)
  (request : Request Party Good Port Technology Instrument)

def RawAmount : Prop :=
  match request.operation with
  | .transfer _ recipient goods =>
      (¬ ∀ key ∈ Responsibility.Family.positiveScope source past nature response, residual claim state law front key = 0) ∧
      ∀ entry ∈ goods, 0 < residual claim state law front (recipient,entry.1) ∧
        amount Good goods entry.1 ≤ residual claim state law front (recipient,entry.1)
  | .produce _ | .revise .. =>
      ¬ ∀ key ∈ Responsibility.Family.positiveScope source past nature response, residual claim state law front key = 0
  | .use actor goods .necessity => actor ∈ members ∧ goods = law.necessities state.raw actor ∧
      ¬ Bill front actor (law.necessities state.raw actor) .necessity
  | .use actor goods .maintenance => actor ∈ members ∧ goods = law.mandatoryMaintenance state.raw actor ∧
      ¬ Bill front actor (law.mandatoryMaintenance state.raw actor) .maintenance
  | .present => True
  | _ => False

instance : Decidable (RawAmount claim state law members front request) := by
  unfold RawAmount
  cases request.operation with
  | use _ _ purpose => cases purpose <;> infer_instance
  | _ => infer_instance

def RawControl : Prop :=
  let before := (Primitive.execute law state.raw 0 front).final
  let after := law.paidStep before request
  ∀ port ∈ request.purpose :: (request.gates ++ law.requiredPorts before request ++
      law.requiredPorts after request ++ members.flatMap (fun actor =>
        (law.technique before.technology actor).requiredPorts ++ (law.technique after.technology actor).requiredPorts)),
    ∀ actor ∈ members, law.allowed after.technology port actor = false →
      law.allowed before.technology port actor = false ∧ law.controller after.technology port = law.controller before.technology port

instance : Decidable (RawControl claim state law members front request) := by unfold RawControl; infer_instance

/-- Syntax, source authority and exact-dose checks on the symbolic source
prefixes. This does not inspect an actual success, payment or future current. -/
def Routing (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ pair ∈ Primitive.steps word, Policy.known members pair.2 ∧
    Responsibility.Family.materialOperation (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) pair.2 ∧
    RawAmount claim state law members pair.1 pair.2 ∧ RawControl claim state law members pair.1 pair.2

instance (word : RawEvent Party Good Port Technology Instrument) : Decidable (Routing claim state law members word) := by
  unfold Routing; infer_instance

omit [DecidableEq Technology] [DecidableEq Port] in
theorem routing_retains_the_original_material_source (word : RawEvent Party Good Port Technology Instrument)
    (routing : Routing claim state law members word) :
    ∀ request ∈ word, Responsibility.Family.materialOperation
      (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) request := by
  intro next inside
  obtain ⟨earlier,later,same⟩ := List.mem_iff_append.mp inside
  have member := Primitive.source_decomposition_is_a_generated_step [] earlier next later
  rw [List.nil_append,← same] at member
  exact (routing (earlier,next) member).2.1

omit [DecidableEq Technology] [DecidableEq Port] in
theorem original_request_conditions_are_generated
    (word : RawEvent Party Good Port Technology Instrument)
    (conditions : Primitive.Conditions law (Primitive.execute law state.raw 0 word).items)
    (routing : Routing claim state law members word)
    (suffix : RawEvent Party Good Port Technology Instrument) (same : word = front ++ request :: suffix) :
    Policy.known members request ∧
    Responsibility.Family.materialOperation (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) request ∧
    law.Valid (Policy.current claim state law front) request ∧
    Policy.amountAllowed claim state law members front request ∧ Policy.preservesControl claim state law members front request := by
  have inSteps := Primitive.source_decomposition_is_a_generated_step [] front request suffix
  rw [List.nil_append,← same] at inSteps
  obtain ⟨known,material,amount,control⟩ := routing (front,request) inSteps
  have allMaterial := routing_retains_the_original_material_source claim state law members word routing
  have frontConditions := Primitive.prefix_conditions law state.raw front (request :: suffix) (same ▸ conditions)
  have frontSame := Primitive.all_primitive_effects_become_the_same_actual_execution law state.raw 0 front frontConditions
  have frontMaterial : ∀ next ∈ front, Responsibility.Family.materialOperation
      (Responsibility.controllerCohort source past nature response)
      (Responsibility.Family.positiveScope source past nature response) next := by
    intro next member
    exact allMaterial next (same ▸ List.mem_append_left _ member)
  have validInventory := original_inventory_is_valid law state.raw word conditions
  have headMember : ⟨front.length,(law.execute state.raw 0 front).final,request⟩ ∈ law.rawItems state.raw word := by
    rw [same,RawLaw.rawItems,law.execute_append]
    simp only [RawLaw.execute,Nat.zero_add,List.mem_append,List.mem_cons]
    exact .inr (.inl trivial)
  have valid := validInventory _ headMember
  have remEq := primitive_residual_is_the_original_actual_remaining claim state law front frontConditions frontMaterial
  have amountEq : Policy.amountAllowed claim state law members front request := by
    have bills := raw_bill_becomes_actual_paid_service law state.raw front (original_inventory_is_valid law state.raw front frontConditions)
    cases operation : request.operation with
    | use actor goods purpose =>
      cases purpose <;> simp only [Policy.amountAllowed,RawAmount,operation,bills] at amount ⊢ <;> exact amount
    | _ => simp only [Policy.amountAllowed,RawAmount,operation,Policy.beforeState,
        Responsibility.Family.State.isPaid,remEq] at amount ⊢ <;> exact amount
  refine ⟨known,material,valid,amountEq,?_⟩
  have rawValid : law.Valid (Primitive.execute law state.raw 0 front).final request := by
    simpa only [frontSame] using valid
  simpa only [Policy.preservesControl,Policy.controlPorts,Policy.current,frontSame,
    RawLaw.step,if_pos rawValid,RawControl] using control

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity
