import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.Root.TraceOrigin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RelationHistory

/-! Proper-C findings are bound to actual root visits.  Actors and relation
origins are folded from that root's already generated history, so a later
holder is not rejected for missing the programme's first participant list.
Local title/disposal alternatives do not mint actual action seeds. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RootFace

open Program ProgrammeFace ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

def event (visit : Visit input) :
    ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) visit.current :=
  ⟨Root.ProgrammeSource.emitted input visit.current, rfl⟩

abbrev CapitalAt (visit : Visit input) := SourceCapital input.law
  (Root.ProgrammeSource.rawCurrent input visit.current) (Root.ProgrammeSource.rawEvent input visit.current)
    input.localAttempts

def capitals (visit : Visit input) : List (CapitalAt input visit) :=
  discovered input.law (Root.ProgrammeSource.rawCurrent input visit.current)
    (Root.ProgrammeSource.rawEvent input visit.current) input.localAttempts

variable (visit : Visit input) (capital : CapitalAt input visit)

def accessItem : Item input visit := capital.dependency.proposal.access.access
def needItem : Item input visit := capital.dependency.proposal.access.necessity
def authority : Party := input.law.controller (accessItem input visit capital).val.before.technology
  capital.dependency.proposal.access.port
def disposer : Party := capital.dependency.proposal.disposal.holder input.law _ _
  capital.dependency.proposal.access

private theorem signer_present : ActualBirth.presentAt input visit (accessItem input visit capital).val.request.signer := by
  apply List.mem_dedup.mpr
  exact List.mem_flatMap.mpr ⟨(accessItem input visit capital).val,
    (accessItem input visit capital).property, List.mem_cons_self⟩

private theorem authority_present : ActualBirth.presentAt input visit (authority input visit capital) := by
  apply List.mem_dedup.mpr
  exact List.mem_flatMap.mpr ⟨(accessItem input visit capital).val,
    (accessItem input visit capital).property,
    controller_mem_itemParties input.law (accessItem input visit capital).val
      capital.dependency.proposal.access.port capital.dependency.checked.1.2.1⟩

private theorem recipient_present : ActualBirth.presentAt input visit capital.dependency.proposal.access.recipient := by
  obtain ⟨_, _, _, goods, kind, operation, _, _⟩ :=
    (capital.dependency.access input.law _ _).original_access_and_real_necessity input.law _ _
  rw [capital.dependency.access_proposal_exact input.law _ _] at operation
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(needItem input visit capital).val, (needItem input visit capital).property, ?_⟩
  simp only [itemParties, needItem, operation, operationParties, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (Or.inr (Or.inl trivial)))

def executorBirth := ActualBirth.generate input visit (accessItem input visit capital).val.request.signer
  (signer_present input visit capital)
def authorityBirth := ActualBirth.generate input visit (authority input visit capital)
  (authority_present input visit capital)
def recipientBirth := ActualBirth.generate input visit capital.dependency.proposal.access.recipient
  (recipient_present input visit capital)

def actualExecution : (ProgrammeFace.controllers input.law (Registered.reader input).raw
    (ActualBirth.occurrence input visit)).ExactActionSeed :=
  ProgrammeFace.exactAction input.law (Registered.reader input).raw (ActualBirth.occurrence input visit)
    ⟨(accessItem input visit capital).val.index, .execution, (accessItem input visit capital).val.request.signer⟩
    (by
      have accepted : input.law.Valid (accessItem input visit capital).val.before
          (accessItem input visit capital).val.request := capital.dependency.checked.1.1
      apply List.mem_flatMap.mpr
      refine ⟨(accessItem input visit capital).val, (accessItem input visit capital).property, ?_⟩
      simp [itemActions, accepted])

private theorem relation_present : RelationHistory.presentAt input visit capital.dependency.proposal.access.port := by
  refine ⟨(capital.dependency.proposal.access.port, authority input visit capital), ?_, rfl⟩
  apply item_relation_present input.law (RelationHistory.origin input visit)
    (accessItem input visit capital).val (accessItem input visit capital).property
  · exact List.mem_cons_of_mem _ capital.dependency.checked.1.2.1
  · exact controller_mem_itemParties input.law (accessItem input visit capital).val _
      capital.dependency.checked.1.2.1

def relationBirth := RelationHistory.generate input visit capital.dependency.proposal.access.port
  (relation_present input visit capital)

structure Bound (visit : Visit input) where
  private mk ::
  capital : CapitalAt input visit
  source_generated : capital ∈ capitals input visit
  disposalBirth : ActualBirth.Witness input
  disposal_original : ActualBirth.lookup input visit (disposer input visit capital) = some disposalBirth

inductive Finding (visit : Visit input) where
  | bound (value : Bound input visit)
  | unresolvedDisposer (capital : CapitalAt input visit)
      (source_generated : capital ∈ capitals input visit)
      (missing : ActualBirth.lookup input visit (disposer input visit capital) = none)

private def bind (candidate : { capital : CapitalAt input visit // capital ∈ capitals input visit }) :
    Finding input visit :=
  match original : ActualBirth.lookup input visit (disposer input visit candidate.val) with
  | none => .unresolvedDisposer candidate.val candidate.property original
  | some born => .bound ⟨candidate.val, candidate.property, born, original⟩

def atVisit : List (Finding input visit) := (capitals input visit).attach.map (bind input visit)

/-- The unresolved interpretation retains its exact original request and
responsibility disposition.  It is not silently filtered out as no-C. -/
def Finding.original (finding : Finding input visit) : Root.Financial.InstructionOrigin input :=
  match finding with
  | .bound value => RootFace.original input visit (accessItem input visit value.capital)
  | .unresolvedDisposer capital _ _ => RootFace.original input visit capital.dependency.proposal.disposal.position

def Finding.disposition (finding : Finding input visit) := (finding.original input visit).disposition input

namespace Bound
variable (bound : Bound input visit)

def accessOrigin := original input visit (accessItem input visit bound.capital)
def needOrigin := original input visit (needItem input visit bound.capital)
def financialOrigin := (bound.capital.dependency.financialOrigin input.law _ _).map
  (original input visit)
def accessDisposition := (bound.accessOrigin input visit).disposition input
def needDisposition := (bound.needOrigin input visit).disposition input

def actor := (executorBirth input visit bound.capital).actor input
def controllingActor := (authorityBirth input visit bound.capital).actor input
def recipientActor := (recipientBirth input visit bound.capital).actor input
def beneficialActor := bound.disposalBirth.actor input
def relation := (relationBirth input visit bound.capital).relation input

theorem actual_executor_has_its_original_M0_birth :
    (executorBirth input visit bound.capital).original.party =
      (actualExecution input visit bound.capital).val.party :=
  (executorBirth input visit bound.capital).key_exact input

theorem original_trace_and_whole_row :
    (bound.accessOrigin input visit).instruction? input =
        some (accessItem input visit bound.capital).val ∧
      (bound.accessOrigin input visit).row input = Registered.traceRow input visit.current ∧
      (bound.needOrigin input visit).instruction? input = some (needItem input visit bound.capital).val :=
  ⟨original_decodes_exact_item input visit _, original_row_is_same_interpreter input visit _,
    original_decodes_exact_item input visit _⟩

omit [DecidableEq Port] in
theorem native_next_is_original_source :
    Root.ProgrammeSource.rawCurrent input (actualTarget (event input visit)) =
      input.law.next (Root.ProgrammeSource.rawCurrent input visit.current)
        (Root.ProgrammeSource.rawEvent input visit.current) :=
  (Registered.reader input).next_exact (event input visit)

theorem next_keeps_actor_and_relation {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((ActualBirth.root input).evolutionAt visit.current).nextCurrent? = some target) :
    ((executorBirth input visit bound.capital).next input nextEq).actor input = bound.actor input visit ∧
    ((relationBirth input visit bound.capital).next input nextEq).relation input = bound.relation input visit :=
  ⟨rfl, rfl⟩

theorem next_relation_role_is_actual_permission {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((ActualBirth.root input).evolutionAt visit.current).nextCurrent? = some target) :
    ((relationBirth input visit bound.capital).next input nextEq).role input =
      input.law.allowed (Root.ProgrammeSource.rawCurrent input target).technology
        bound.capital.dependency.proposal.access.port :=
  (relationBirth input visit bound.capital).role_at_native_successor input nextEq

end Bound

#print axioms atVisit
#print axioms Bound.actual_executor_has_its_original_M0_birth
#print axioms Bound.original_trace_and_whole_row
#print axioms Bound.next_keeps_actor_and_relation
#print axioms Bound.next_relation_role_is_actual_permission

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RootFace
