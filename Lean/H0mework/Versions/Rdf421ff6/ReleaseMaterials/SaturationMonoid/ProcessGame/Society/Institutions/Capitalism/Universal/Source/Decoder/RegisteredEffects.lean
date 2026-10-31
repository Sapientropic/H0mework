import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.RegisteredProgramme
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder.DispositionRights
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Fold

/-! The only inputs to this decoder are the original root occurrence and its
original instruction row.  Complete authorization lists are traversed
without dropping failed genesis resolutions.  Such an instruction retains
its full material receipt as pending on the same original row. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder.RegisteredEffects

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Program ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

private def collect {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some head :: tail => (collect tail).map (head :: ·)

private theorem collect_keeps_every_entry {α : Type} (entries : List (Option α)) (values : List α)
    (complete : collect entries = some values) (entry : Option α) (member : entry ∈ entries) :
    ∃ value ∈ values, entry = some value := by
  induction entries generalizing values with
  | nil => simp at member
  | cons head tail ih =>
      cases head with
      | none => simp only [collect, reduceCtorEq] at complete
      | some value =>
          cases remaining : collect tail with
          | none => simp only [collect, remaining, Option.map_none, reduceCtorEq] at complete
          | some rest =>
              have same : value :: rest = values := by
                simpa only [collect, remaining, Option.map_some, Option.some.injEq] using complete
              subst values
              rcases List.mem_cons.mp member with first | later
              · exact ⟨value, List.mem_cons_self, first⟩
              · obtain ⟨other, inTail, decoded⟩ := ih rest remaining later
                exact ⟨other, List.mem_cons_of_mem _ inTail, decoded⟩

abbrev rootSource := Root.ProgrammeSource.ledgerSource input
abbrev rootSociety := Registered.society input

def origin {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) :=
  (Registered.reader input).raw (originalOccurrence event)

def bornOrigin := (Registered.reader input).raw (Registered.genesis input)

def action? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (action : ActionSeed Party)
    (present : action ∈ actions input.law (origin input event)) :
    Option ((rootSociety input).controllers event).ExactActionSeed :=
  if born : action.party ∈ parties input.law (bornOrigin input) then
    some (Anchored.exactAction input.law (Registered.reader input).raw (Registered.genesis input)
      (originalOccurrence event) action born present)
  else none

def relation? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (port : Port) (party : Party)
    (present : (port, party) ∈ relationIncidences input.law (origin input event)) :
    Option ((rootSociety input).relations event).ExactRelationSeed :=
  if born : (port, party) ∈ relationIncidences input.law (bornOrigin input) then
    some (Anchored.exactRelation input.law (Registered.reader input).raw (Registered.genesis input)
      (originalOccurrence event) (port, party) born present)
  else none

def itemRelation? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (port : Port) (party : Party) (portMem : port ∈ itemPorts input.law item)
    (partyMem : party ∈ itemParties input.law item) :
    Option ((rootSociety input).relations event).ExactRelationSeed :=
  relation? input event port party
    (item_relation_present input.law (origin input event) item itemMem port party portMem partyMem)

def execution? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request) :
    Option ((rootSociety input).controllers event).ExactActionSeed :=
  action? input event ⟨item.index, .execution, item.request.signer⟩
    (List.mem_flatMap.mpr ⟨item, itemMem, by
      simp only [itemActions, if_pos accepted]
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      exact List.mem_cons_self⟩)

def authorization? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request) (port : Port) :
    Option ((rootSociety input).controllers event).ExactActionSeed :=
  action? input event (authorizingAction input.law item port)
    (authorizingAction_in_original_occurrence input.law (origin input event) item itemMem accepted port)

def restrictedPorts (item : ExecutionItem Party Good Port Technology Instrument) (beneficiary : Party) :=
  (input.law.requiredPorts item.before item.request).attach.filter
    (fun port => !(input.law.allowed item.before.technology port.val beneficiary))

def guard? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request)
    (beneficiary : Party) (beneficiaryMem : beneficiary ∈ itemParties input.law item)
    (port : { port // port ∈ input.law.requiredPorts item.before item.request }) :
    Option ((rootSociety input).RequiredAuthorityPort event) := do
  let action ← authorization? input event item itemMem accepted port.val
  let relation ← itemRelation? input event item itemMem port.val beneficiary
    (List.mem_cons_of_mem _ port.property) beneficiaryMem
  return ⟨action, relation⟩

def guards? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request)
    (beneficiary : Party) (beneficiaryMem : beneficiary ∈ itemParties input.law item) :
    Option (List ((rootSociety input).RequiredAuthorityPort event)) :=
  collect ((restrictedPorts input item beneficiary).map
    (guard? input event item itemMem accepted beneficiary beneficiaryMem))

theorem guards_cover_all_restricted_ports {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request)
    (beneficiary : Party) (beneficiaryMem : beneficiary ∈ itemParties input.law item)
    (guards : List ((rootSociety input).RequiredAuthorityPort event))
    (decoded : guards? input event item itemMem accepted beneficiary beneficiaryMem = some guards)
    (port : { port // port ∈ input.law.requiredPorts item.before item.request })
    (dependent : input.law.allowed item.before.technology port.val beneficiary = false) :
    ∃ guard ∈ guards,
      guard? input event item itemMem accepted beneficiary beneficiaryMem port = some guard := by
  apply collect_keeps_every_entry _ guards decoded
  apply List.mem_map.mpr
  refine ⟨port, ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_attach _ _, by simp only [dependent, Bool.not_false]⟩

def rightsAtPort? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request) (beneficiary : Party)
    (port : { port // port ∈ input.law.requiredPorts item.before item.request }) :
    Option (List ((rootSociety input).DispositionRightPort event)) :=
  match disposalRights input.law (origin input event) item beneficiary port.val with
  | [] => some []
  | _ :: _ => do
      let action ← authorization? input event item itemMem accepted port.val
      let purpose ← itemRelation? input event item itemMem port.val
        (input.law.controller item.before.technology port.val)
        (List.mem_cons_of_mem _ port.property)
        (controller_mem_itemParties input.law item port.val port.property)
      return [⟨action, purpose, original⟩]

def rights? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request) (beneficiary : Party) :
    Option (List ((rootSociety input).DispositionRightPort event)) :=
  (collect ((restrictedPorts input item beneficiary).map
    (rightsAtPort? input event original item itemMem accepted beneficiary))).map List.flatten

def rawAcquired {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (location : Party × Good) : ℚ :=
  match Registered.originalInstruction input event original with
  | none => 0
  | some item => acquired input.law item location.1 location.2

def maintenanceActions? {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) :
    Option (List ((rootSociety input).controllers event).ExactActionSeed) :=
  (collect ((input.law.rawItems (origin input event).1 (origin input event).2).attach.map
    (fun item => match item.val.request.operation with
      | .use _ _ .maintenance =>
          if accepted : input.law.Valid item.val.before item.val.request then
            (execution? input event item.val item.property accepted).map (fun action => [action])
          else some []
      | _ => some []))).map List.flatten

def maintenancePaid {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (location : Party × Good) : ℚ :=
  ((input.law.rawItems (origin input event).1 (origin input event).2).map
    (fun item => consumedFor input.law .maintenance item location.1 location.2)).sum

def necessaryPaid {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (location : Party × Good) : ℚ :=
  ((input.law.rawItems (origin input event).1 (origin input event).2).map
    (fun item => consumedFor input.law .necessity item location.1 location.2)).sum

def netPhysicalAccumulation {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (location : Party × Good) : ℚ :=
  max 0 ((input.law.next (origin input event).1 (origin input event).2).stock location.1 location.2 -
    (origin input event).1.stock location.1 location.2)

/-- These entries are positive net accumulations in the original physical
unit.  They are never summed across goods.  A settlement receipt is excluded:
its principal simultaneously discharges the old financial claim. -/
def netAccumulations {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (action : ((rootSociety input).controllers event).ExactActionSeed)
    (purpose : ((rootSociety input).relations event).ExactRelationSeed) :
    List ((rootSociety input).SurplusDispositionPort event ℚ) :=
  match item.request.operation with
  | .produce _ | .transfer _ _ _ =>
      (input.law.actualCredit item.before item.request).filterMap (fun lot =>
        if 0 < lot.2 ∧ 0 < netPhysicalAccumulation input event lot.1 then
          some ⟨action, action, purpose, original, netPhysicalAccumulation input event lot.1⟩
        else none)
  | _ => []

structure CompiledEffect {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request)
    (beneficiary : Party) (beneficiaryMem : beneficiary ∈ itemParties input.law item) where
  private mk ::
  face : (rootSociety input).AcquisitionEffect event (Party × Good) ℚ original
  execution : ((rootSociety input).controllers event).ExactActionSeed
  execution_exact : execution? input event item itemMem accepted = some execution
  recipient_exact : itemRelation? input event item itemMem item.request.purpose beneficiary
    List.mem_cons_self beneficiaryMem = some face.recipient
  gates_exact : guards? input event item itemMem accepted beneficiary beneficiaryMem =
    some face.requiredPorts
  rights_exact : rights? input event original item itemMem accepted beneficiary =
    some face.dispositionRights
  maintenance_exact : maintenanceActions? input event = some face.maintenanceActions
  quantity_exact : face.acquired = rawAcquired input event original
  physical_exact : face.physicallyProduced =
    fun location => produced input.law item location.1 location.2
  necessities_exact : face.receivedForNecessities = necessaryPaid input event
  surplus_exact : face.surplusPorts = netAccumulations input event original item execution face.recipient
  reproduction_required_exact : face.reproductionRequired = fun location =>
    if location.1 = beneficiary then
      amount Good (input.law.mandatoryMaintenance item.before beneficiary) location.2 else 0
  reproduction_paid_exact : face.reproductionPaid = maintenancePaid input event
  self_request_exact : face.selfRequestAllowed =
    decide (input.law.Valid item.before { item.request with signer := beneficiary, consents := [] })

def compileKnown {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (originalExact : Registered.originalInstruction input event original = some item)
    (accepted : input.law.Valid item.before item.request)
    (beneficiary : Party) (selected : recipient item.request.operation = some beneficiary) :
    Option (CompiledEffect input event original item
      (Registered.originalInstruction_mem input event original item originalExact) accepted beneficiary
      (recipient_mem_itemParties input.law item beneficiary selected)) :=
  let itemMem := Registered.originalInstruction_mem input event original item originalExact
  let beneficiaryMem := recipient_mem_itemParties input.law item beneficiary selected
  match recipientEq : itemRelation? input event item itemMem item.request.purpose beneficiary
      List.mem_cons_self beneficiaryMem with
  | none => none
  | some recipientSeed =>
    match executionEq : execution? input event item itemMem accepted with
    | none => none
    | some action =>
      match gatesEq : guards? input event item itemMem accepted beneficiary beneficiaryMem with
      | none => none
      | some guards =>
        match rightsEq : rights? input event original item itemMem accepted beneficiary with
        | none => none
        | some rights =>
          match maintenanceEq : maintenanceActions? input event with
          | none => none
          | some maintenance =>
            some {
              face := {
                recipient := recipientSeed
                acquired := rawAcquired input event original
                physicallyProduced := fun location => produced input.law item location.1 location.2
                receivedForNecessities := necessaryPaid input event
                requiredPorts := guards
                dispositionRights := rights
                surplusPorts := netAccumulations input event original item action recipientSeed
                contributions := match item.request.operation with
                  | .produce _ => [⟨action, recipientSeed,
                      fun location => paid input.law item location.1 location.2⟩]
                  | _ => []
                reproductionRequired := fun location =>
                  if location.1 = beneficiary then
                    amount Good (input.law.mandatoryMaintenance item.before beneficiary) location.2
                  else 0
                reproductionPaid := maintenancePaid input event
                maintenanceActions := maintenance
                selfRequestAllowed := decide (input.law.Valid item.before
                  { item.request with signer := beneficiary, consents := [] }) }
              execution := action
              execution_exact := executionEq
              recipient_exact := recipientEq
              gates_exact := gatesEq
              rights_exact := rightsEq
              maintenance_exact := maintenanceEq
              quantity_exact := rfl
              physical_exact := rfl
              necessities_exact := rfl
              surplus_exact := rfl
              reproduction_required_exact := rfl
              reproduction_paid_exact := rfl
              self_request_exact := rfl }

def decode {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event) :
    Option ((rootSociety input).AcquisitionEffect event (Party × Good) ℚ original) :=
  match originalExact : Registered.originalInstruction input event original with
  | none => none
  | some item =>
    if accepted : input.law.Valid item.before item.request then
      match selected : recipient item.request.operation with
      | none => none
      | some beneficiary =>
          (compileKnown input event original item originalExact accepted beneficiary selected).map
            (fun compiled => compiled.face)
    else none

theorem decode_quantity_exact {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (face : (rootSociety input).AcquisitionEffect event (Party × Good) ℚ original)
    (decoded : decode input event original = some face) :
    face.acquired = rawAcquired input event original := by
  unfold decode at decoded
  split at decoded
  · contradiction
  next item originalExact =>
    split at decoded
    next accepted =>
      split at decoded
      · contradiction
      next beneficiary selected =>
        obtain ⟨compiled, _generated, exactFace⟩ := Option.map_eq_some_iff.mp decoded
        cases exactFace
        exact compiled.quantity_exact
    · contradiction

theorem decoded_has_original_instruction_and_compiler
    {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (face : (rootSociety input).AcquisitionEffect event (Party × Good) ℚ original)
    (decoded : decode input event original = some face) :
    ∃ item, ∃ originalExact : Registered.originalInstruction input event original = some item,
      ∃ accepted : input.law.Valid item.before item.request,
      ∃ beneficiary, ∃ selected : recipient item.request.operation = some beneficiary,
      ∃ compiled : CompiledEffect input event original item
        (Registered.originalInstruction_mem input event original item originalExact) accepted beneficiary
        (recipient_mem_itemParties input.law item beneficiary selected),
        compileKnown input event original item originalExact accepted beneficiary selected = some compiled ∧
        face = compiled.face := by
  unfold decode at decoded
  split at decoded
  · contradiction
  next item originalExact =>
    split at decoded
    next accepted =>
      split at decoded
      · contradiction
      next beneficiary selected =>
        obtain ⟨compiled, generated, exactFace⟩ := Option.map_eq_some_iff.mp decoded
        exact ⟨item, originalExact, accepted, beneficiary, selected, compiled, generated, exactFace.symm⟩
    · contradiction

def rawEffects : (rootSociety input).RawEffectLaw (Party × Good) ℚ where
  rawAcquired := rawAcquired input
  decode := decode input
  decoded_exact := decode_quantity_exact input

/-- A positive source witness for an invoked exclusive disposition port.
The full reproduction relation also needs the production and livelihood
circuit; a private transfer alone is not a capitalist society. -/
def capitalPort {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (port : Port) : Bool :=
  (input.law.rawItems (origin input event).1 (origin input event).2).any (fun item =>
    match recipient item.request.operation with
    | none => false
    | some beneficiary => !(disposalRights input.law (origin input event) item beneficiary port).isEmpty)

def capitalRelation {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (relation : (rootSociety input).Relation event) : Prop :=
  relation.val.val.head?.any (capitalPort input event) = true

/-- A required source guard stays in the decision scope even when its
disposition basis has not been recognized.  Otherwise failure of a finite
right search would silently become a certificate of independence. -/
def scopedPort {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (port : Port) : Bool :=
  (input.law.rawItems (origin input event).1 (origin input event).2).any (fun item =>
    match recipient item.request.operation with
    | none => false
    | some beneficiary => decide (input.law.Valid item.before item.request) &&
        decide (port ∈ input.law.requiredPorts item.before item.request) &&
        !(input.law.allowed item.before.technology port beneficiary))

def classificationScope {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (relation : (rootSociety input).Relation event) : Prop :=
  relation.val.val.head?.any (scopedPort input event) = true

instance {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) : DecidablePred (classificationScope input event) := by
  intro relation
  unfold classificationScope
  infer_instance

instance {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) : DecidablePred (capitalRelation input event) := by
  intro relation
  unfold capitalRelation
  infer_instance

theorem compiled_keeps_all_original_gates {current : (Root.ProgrammeSource.V input).Current}
    (event : ContinuingEventAt (rootSource input) current) (original : OriginalInventoryItem event)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (itemMem : item ∈ input.law.rawItems (origin input event).1 (origin input event).2)
    (accepted : input.law.Valid item.before item.request)
    (beneficiary : Party) (beneficiaryMem : beneficiary ∈ itemParties input.law item)
    (compiled : CompiledEffect input event original item itemMem accepted beneficiary beneficiaryMem)
    (port : { port // port ∈ input.law.requiredPorts item.before item.request })
    (dependent : input.law.allowed item.before.technology port.val beneficiary = false) :
    ∃ guard ∈ compiled.face.requiredPorts,
      guard? input event item itemMem accepted beneficiary beneficiaryMem port = some guard :=
  guards_cover_all_restricted_ports input event item itemMem accepted beneficiary beneficiaryMem
    compiled.face.requiredPorts compiled.gates_exact port dependent

#print axioms rawEffects

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder.RegisteredEffects
