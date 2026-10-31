import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.RootBinding

/-! The general constitutive kernel is read from the original programme
occurrence.  Actual authorization generates an action; the alternative
proving disposal ability does not.  Claim coordinates retain their original
instruction row for the native financial-origin consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.RootBinding

open Program ProgrammeFace ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Decoder.RegisteredEffects

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  {current : (Root.ProgrammeSource.V input).Current}
  (event : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) current)

abbrev KernelAt := CapitalRelationKernel input.law
  (Root.ProgrammeSource.rawCurrent input current) (Root.ProgrammeSource.rawEvent input current)

variable (kernel : KernelAt input (current := current))

def accessItem := kernel.proposal.access.access
def needItem := kernel.proposal.access.necessity

def controlAction? : Option (((Registered.society input).controllers event).ExactActionSeed) :=
  authorization? input event (accessItem input kernel).val (accessItem input kernel).property
    (kernel.original_control_and_reproduced_phase input.law _ _).1 kernel.proposal.access.port

def rightRelation? : Option (((Registered.society input).relations event).ExactRelationSeed) :=
  itemRelation? input event (accessItem input kernel).val (accessItem input kernel).property
    kernel.proposal.access.port
    (input.law.controller (accessItem input kernel).val.before.technology kernel.proposal.access.port)
    (List.mem_cons_of_mem _ (kernel.original_control_and_reproduced_phase input.law _ _).2.1)
    (controller_mem_itemParties input.law (accessItem input kernel).val kernel.proposal.access.port
      (kernel.original_control_and_reproduced_phase input.law _ _).2.1)

private theorem recipient_present : kernel.proposal.access.recipient ∈ parties input.law (origin input event) := by
  obtain ⟨_, _, _, goods, kind, operation, _, _⟩ :=
    (kernel.access input.law _ _).original_access_and_real_necessity input.law _ _
  rw [kernel.access_proposal_exact input.law _ _] at operation
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(needItem input kernel).val, (needItem input kernel).property, ?_⟩
  simp only [itemParties, needItem, operation, operationParties, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (Or.inr (Or.inl trivial)))

def recipient? : Option ((Registered.society input).Actor event) :=
  if born : kernel.proposal.access.recipient ∈ parties input.law (bornOrigin input) then
    some (Anchored.actor input.law (Registered.reader input).raw (Registered.genesis input)
      (originalOccurrence event)
      (ProgrammeFace.exactParty input.law (Registered.reader input).raw (Registered.genesis input)
        kernel.proposal.access.recipient born)
      (recipient_present input event kernel))
  else none

def disposalActor? : Option ((Registered.society input).Actor event) :=
  let holder := kernel.proposal.disposal.holder input.law _ _ kernel.proposal.access
  if present : holder ∈ parties input.law (origin input event) then
    if born : holder ∈ parties input.law (bornOrigin input) then
      some (Anchored.actor input.law (Registered.reader input).raw (Registered.genesis input)
        (originalOccurrence event)
        (ProgrammeFace.exactParty input.law (Registered.reader input).raw (Registered.genesis input) holder born)
        present)
    else none
  else none

structure Bound where
  private mk ::
  authorization : ((Registered.society input).controllers event).ExactActionSeed
  right : ((Registered.society input).relations event).ExactRelationSeed
  beneficiary : (Registered.society input).Actor event
  disposalBeneficiary : (Registered.society input).Actor event
  authorization_exact : controlAction? input event kernel = some authorization
  right_exact : rightRelation? input event kernel = some right
  beneficiary_exact : recipient? input event kernel = some beneficiary
  disposal_beneficiary_exact : disposalActor? input event kernel = some disposalBeneficiary

def bind : Option (Bound input event kernel) :=
  match authorizationEq : controlAction? input event kernel with
  | none => none
  | some authorization =>
      match rightEq : rightRelation? input event kernel with
      | none => none
      | some right =>
          match beneficiaryEq : recipient? input event kernel with
          | none => none
          | some beneficiary =>
              match disposerEq : disposalActor? input event kernel with
              | none => none
              | some disposer => some ⟨authorization, right, beneficiary, disposer,
                  authorizationEq, rightEq, beneficiaryEq, disposerEq⟩

namespace Bound
variable (bound : Bound input event kernel)

def relation : (Registered.society input).Relation event :=
  ((Registered.society input).relations event).relationOf bound.right

def accessRow (fixed : input.emission? = none) := originalInstructionRow input fixed event (accessItem input kernel)
def needRow (fixed : input.emission? = none) := originalInstructionRow input fixed event (needItem input kernel)
def accessDisposition (fixed : input.emission? = none) := originalInstructionDisposition input fixed event (accessItem input kernel)
def needDisposition (fixed : input.emission? = none) := originalInstructionDisposition input fixed event (needItem input kernel)

def financialRow (fixed : input.emission? = none) :=
  (kernel.financialOrigin input.law _ _).map (originalInstructionRow input fixed event)

def financialDisposition (fixed : input.emission? = none) := (kernel.financialOrigin input.law _ _).map
  (fun item => (⟨originalInstructionRow input fixed event item,
    originalInstructionDisposition input fixed event item⟩ :
      Sigma fun row => LedgerEntryDispositionAt (Root.ProgrammeSource.N input) row))

theorem relation_is_original_genesis_lineage :
    (bound.relation input event kernel).val =
      Anchored.bornRelation input.law (Registered.reader input).raw (Registered.genesis input) bound.right.val := rfl

theorem next_role_is_original_native_target :
    ((Registered.society input).relations event).roleAt (bound.relation input event kernel) .target =
      permissionRole input.law (Root.ProgrammeSource.rawCurrent input (actualTarget event))
        (Anchored.bornRelation input.law (Registered.reader input).raw
          (Registered.genesis input) bound.right.val).val.head? := by
  have phase := ProgrammeControl.RootBinding.anchored_target_role input.law
    (Registered.reader input).raw (Registered.genesis input) (originalOccurrence event) bound.right
  exact phase.trans (congrArg (fun state => permissionRole input.law state
    (Anchored.bornRelation input.law (Registered.reader input).raw
      (Registered.genesis input) bound.right.val).val.head?) ((Registered.reader input).next_exact event).symm)

set_option linter.defProp false in
/-- An ability witness stays an ability; no actual action seed is minted
for a command absent from the original occurrence. -/
def original_disposal_ability := kernel.disposal_is_a_lawful_local_alternative input.law
  (Root.ProgrammeSource.rawCurrent input current) (Root.ProgrammeSource.rawEvent input current)

end Bound

#print axioms bind
#print axioms Bound.relation_is_original_genesis_lineage
#print axioms Bound.next_role_is_original_native_target

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.RootBinding
