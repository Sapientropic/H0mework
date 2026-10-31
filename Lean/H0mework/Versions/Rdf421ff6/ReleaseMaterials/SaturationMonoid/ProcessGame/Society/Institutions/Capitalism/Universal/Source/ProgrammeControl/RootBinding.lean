import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.OriginalRows
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Reproduction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder.RegisteredEffects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Inquiry.Foundation

/-! The original root's execution face consumes the checked economic
circuit.  Actors and control lineage come from its registered genesis;
failed identity admission returns no binding and leaves the exact original
instruction row available to the caller's typed disposition. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.RootBinding

open Program ProgrammeFace ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Decoder.RegisteredEffects

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  {current : (Root.ProgrammeSource.V input).Current}
  (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)

abbrev ReproductionAt := CapitalContributionReproduction input.law
  (Root.ProgrammeSource.rawCurrent input current) (Root.ProgrammeSource.rawEvent input current)

theorem anchored_target_role {Index : Type}
    (law : RawLaw Party Good Port Technology Instrument)
    (read : Index → ProgrammeFace.Origin Party Good Port Technology Instrument)
    (birth index : Index) (seed : (Anchored.relations law read birth index).ExactRelationSeed) :
    (Anchored.relations law read birth index).roleAt
      ((Anchored.relations law read birth index).relationOf seed) .target =
      permissionRole law (law.next (read index).1 (read index).2)
        (Anchored.bornRelation law read birth seed.val).val.head? := rfl

variable (reproduction : ReproductionAt input (current := current))

def privateProduction := reproduction.privateProduction input.law _ _

def production := (privateProduction input reproduction).proposal.circuit.production

def disposition := (privateProduction input reproduction).proposal.disposition

def need := (privateProduction input reproduction).proposal.circuit.necessity

def control := (privateProduction input reproduction).control input.law _ _

set_option linter.defProp false in
def productionAccepted := (control input reproduction).production_is_original_control_use input.law _ _ |>.1

set_option linter.defProp false in
def productionPort := (control input reproduction).production_is_original_control_use input.law _ _ |>.2

private theorem proposal_exact :
    (control input reproduction).proposal = (privateProduction input reproduction).proposal.circuit :=
  (privateProduction input reproduction).control_proposal_exact input.law _ _

def controlAction? : Option (((Registered.society input).controllers event).ExactActionSeed) :=
  authorization? input event (production input reproduction).val (production input reproduction).property
    (by simpa only [proposal_exact, production] using productionAccepted input reproduction)
    (privateProduction input reproduction).proposal.circuit.port

def rightRelation? : Option (((Registered.society input).relations event).ExactRelationSeed) :=
  itemRelation? input event (production input reproduction).val (production input reproduction).property
    (privateProduction input reproduction).proposal.circuit.port
    (input.law.controller (production input reproduction).val.before.technology (privateProduction input reproduction).proposal.circuit.port)
    (List.mem_cons_of_mem _ (by simpa only [proposal_exact, production] using productionPort input reproduction))
    (controller_mem_itemParties input.law (production input reproduction).val
      (privateProduction input reproduction).proposal.circuit.port (by simpa only [proposal_exact, production] using productionPort input reproduction))

def surplusAction? : Option (((Registered.society input).controllers event).ExactActionSeed) :=
  execution? input event (disposition input reproduction).val (disposition input reproduction).property
    ((privateProduction input reproduction).actual_surplus_and_all_source_needs input.law _ _).2.1

private theorem recipient_present :
    (privateProduction input reproduction).proposal.circuit.recipient ∈ parties input.law (origin input event) := by
  obtain ⟨_, goods, operation, _, _⟩ := (control input reproduction).actual_necessary_life input.law _ _
  rw [proposal_exact] at operation
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(need input reproduction).val, (need input reproduction).property, ?_⟩
  simp only [itemParties, need, operation, operationParties, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (Or.inr (Or.inl trivial)))

def recipient? : Option ((Registered.society input).Actor event) :=
  if born : (privateProduction input reproduction).proposal.circuit.recipient ∈ parties input.law (bornOrigin input) then
    some (Anchored.actor input.law (Registered.reader input).raw (Registered.genesis input)
      (originalOccurrence event)
      (ProgrammeFace.exactParty input.law (Registered.reader input).raw (Registered.genesis input)
        (privateProduction input reproduction).proposal.circuit.recipient born)
      (recipient_present input event reproduction))
  else none

structure Bound where
  private mk ::
  authorization : ((Registered.society input).controllers event).ExactActionSeed
  right : ((Registered.society input).relations event).ExactRelationSeed
  beneficiary : (Registered.society input).Actor event
  surplusExecution : ((Registered.society input).controllers event).ExactActionSeed
  authorization_exact : controlAction? input event reproduction = some authorization
  right_exact : rightRelation? input event reproduction = some right
  beneficiary_exact : recipient? input event reproduction = some beneficiary
  surplus_exact : surplusAction? input event reproduction = some surplusExecution

def bind : Option (Bound input event reproduction) :=
  match authorizationEq : controlAction? input event reproduction with
  | none => none
  | some authorization =>
      match rightEq : rightRelation? input event reproduction with
      | none => none
      | some right =>
          match beneficiaryEq : recipient? input event reproduction with
          | none => none
          | some beneficiary =>
              match surplusEq : surplusAction? input event reproduction with
              | none => none
              | some surplusExecution =>
                  some ⟨authorization, right, beneficiary, surplusExecution,
                    authorizationEq, rightEq, beneficiaryEq, surplusEq⟩

namespace Bound
variable (bound : Bound input event reproduction)

def relation : (Registered.society input).Relation event :=
  ((Registered.society input).relations event).relationOf bound.right

def productionRow (fixed : input.emission? = none) := originalInstructionRow input fixed event (production input reproduction)
def needRow (fixed : input.emission? = none) := originalInstructionRow input fixed event (need input reproduction)
def surplusRow (fixed : input.emission? = none) := originalInstructionRow input fixed event (disposition input reproduction)

def productionDisposition (fixed : input.emission? = none) := originalInstructionDisposition input fixed event (production input reproduction)
def needDisposition (fixed : input.emission? = none) := originalInstructionDisposition input fixed event (need input reproduction)
def surplusDisposition (fixed : input.emission? = none) := originalInstructionDisposition input fixed event (disposition input reproduction)

theorem relation_is_original_genesis_lineage :
    (bound.relation input event reproduction).val =
      Anchored.bornRelation input.law (Registered.reader input).raw (Registered.genesis input) bound.right.val := rfl

theorem next_role_is_original_native_target :
    ((Registered.society input).relations event).roleAt (bound.relation input event reproduction) .target =
      permissionRole input.law (Root.ProgrammeSource.rawCurrent input (actualTarget event))
        (Anchored.bornRelation input.law (Registered.reader input).raw
          (Registered.genesis input) bound.right.val).val.head? := by
  have phase : ((Registered.society input).relations event).roleAt
      (bound.relation input event reproduction) .target =
      permissionRole input.law
        (input.law.next (Root.ProgrammeSource.rawCurrent input current) (Root.ProgrammeSource.rawEvent input current))
        (Anchored.bornRelation input.law (Registered.reader input).raw
          (Registered.genesis input) bound.right.val).val.head? :=
    anchored_target_role input.law (Registered.reader input).raw (Registered.genesis input)
      (originalOccurrence event) bound.right
  exact phase.trans (congrArg (fun state => permissionRole input.law state
    (Anchored.bornRelation input.law (Registered.reader input).raw
      (Registered.genesis input) bound.right.val).val.head?) ((Registered.reader input).next_exact event).symm)

omit [DecidableEq Port] in

/-- The returned face is literally the installed root execution, not a
second interpretation selected after the economic checker succeeded. -/
theorem actual_root_consumer :
    (Root.ProgrammeLiving.executionFace input event.val).interpreted.items =
      input.law.rawItems (Root.ProgrammeSource.rawCurrent input current)
        (Root.ProgrammeSource.rawEvent input current) ∧
    (Root.ProgrammeLiving.executionFace input event.val).after =
      Root.ProgrammeSource.rawCurrent input (actualTarget event) := by
  refine ⟨rfl, ?_⟩
  exact (Registered.reader input).next_exact event |>.symm

end Bound

#print axioms bind
#print axioms Bound.relation_is_original_genesis_lineage
#print axioms Bound.next_role_is_original_native_target

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.RootBinding
