import H0mework.Versions.R2.Foundation.Inquiry.MinimalCoface

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ObstructionGeneratedMinimalCoface

universe u

/-- A causal view of obstructions on an existing network. A coface archives
obstructions from every old support. Only the archive entries belonging to
the active support's restriction can emit its next U7 event. -/
structure ObstructionSlice (N : WorldRelationNetwork.{u}) where
  At : N.Support → Type u
  present : {s : N.Support} → At s → N.ObstructionAt s

def ObstructionSlice.asWorld {N : WorldRelationNetwork.{u}} (slice : ObstructionSlice N) :
    WorldRelationNetwork.{u} where
  __ := N
  ObstructionAt := slice.At
  obstructionClaim := fun obstruction => N.obstructionClaim (slice.present obstruction)

structure LocalU7 (N : WorldRelationNetwork.{u}) where
  private mk ::
  slice : ObstructionSlice N
  producer : U7ProducerCalculus slice.asWorld
  calculus : U7ObstructionEvolutionCalculus slice.asWorld producer

namespace LocalU7

variable {N : WorldRelationNetwork.{u}}

abbrev asWorld (lane : LocalU7 N) : WorldRelationNetwork.{u} := lane.slice.asWorld

def native (inherited : Σ U7 : U7ProducerCalculus N, U7ObstructionEvolutionCalculus N U7) :
    LocalU7 N where
  slice := ⟨N.ObstructionAt, id⟩
  producer := inherited.1
  calculus := inherited.2

/-- Keep the resident's actual law inventory and expression/holding fibres.
Only the obstruction index of the realization check is restricted. -/
def restrictTheory (lane : LocalU7 N) (old : TheoryState N) : TheoryState lane.asWorld where
  inventory := {
    Version := old.inventory.Version
    version := old.inventory.version
    Law := old.inventory.Law
    RealizationAt := fun {_} obstruction => old.inventory.RealizationAt (lane.slice.present obstruction)
    RealizationWithoutAt := fun law {_} obstruction =>
      old.inventory.RealizationWithoutAt law (lane.slice.present obstruction) }
  ExpressionAt := old.ExpressionAt
  denotes := old.denotes
  TheoremAt := old.TheoremAt
  theoremPresentation := old.theoremPresentation

def translation (lane : LocalU7 N) : TypedSemanticWorldNetworkTranslationAt N lane.asWorld where
  support := ⟨id, id, fun _ => rfl⟩
  anchor := ⟨id, id, fun _ => rfl⟩
  incidence := ⟨id, id, fun _ => rfl⟩
  lineage := ⟨id, id, fun _ => rfl⟩
  responsibility := ⟨id, id, fun _ => rfl⟩
  claim := ⟨id, id, fun _ => rfl⟩
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ => ⟨id, id, fun _ => rfl⟩
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ holds => holds
  oldDispositionSurvives := fun _ _ receipt => receipt

variable {OldV : ConstructiveRoot.Vocabulary.{u}}
  {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
  {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
  {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
  {support : N.Support} {obstruction : N.ObstructionAt support}
  {failure : ActualExpressibilityFailure oldTheory obstruction}
  (rooted : RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure)

local notation "Coface" => root_obstruction_generates_minimal_coface rooted

private def cofaceSupportRestriction (s : (Coface).worldNetwork.Support) : N.Support :=
  (Coface).translation.support.backward s

local notation "OldAt" s => cofaceSupportRestriction rooted s

private def cofaceSlice : ObstructionSlice (Coface).worldNetwork where
  At := fun s => N.ObstructionAt (OldAt s)
  present := fun {s} obstruction => ⟨OldAt s, obstruction⟩

local notation "W" => ObstructionSlice.asWorld (cofaceSlice rooted)

private def cofaceEntry {s : (W).Support} (entry : OpenResponsibilityAt N (OldAt s)) :
    OpenResponsibilityAt W s :=
  match s with
  | .inl _ => ⟨.inl entry.1, entry.2⟩
  | .inr _ => ⟨.inl entry.1, entry.2⟩

private def cofaceReceipt {s : (W).Support} {kind : WorldDispositionKind}
    (receipt : N.DispositionAt (OldAt s) kind) : (W).DispositionAt s kind :=
  match s with
  | .inl _ => receipt
  | .inr _ => GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget receipt

private theorem coface_entry_claim {s : (W).Support} (entry : OpenResponsibilityAt N (OldAt s)) :
    (cofaceEntry rooted entry).claim = Sum.inl entry.claim := by
  cases s <;> rfl

private theorem coface_entry_budget {s : (W).Support} (entry : OpenResponsibilityAt N (OldAt s)) :
    (cofaceEntry rooted entry).progressBudget = entry.progressBudget := by
  cases s <;> rfl

variable (oldU7 : U7ProducerCalculus N)

private def cofaceProducer : U7ProducerCalculus W where
  DemandAt := fun obstruction => oldU7.DemandAt obstruction
  generateDemand := fun obstruction => oldU7.generateDemand obstruction

variable (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)

private def cofaceSource : U7ActualSuccessorSource W (cofaceProducer rooted oldU7) where
  EventAt := fun obstruction demand => oldCalculus.source.EventAt obstruction demand
  emit := fun obstruction => oldCalculus.source.emit obstruction
  demandGeneratedAt := by
    intro s obstruction demand event
    have exactDemand := (oldCalculus.source.demandGeneratedAt event).payload_eq_generated
    subst demand
    exact .canonical obstruction
  demandEntryAt := fun {_ _ _} event => cofaceEntry rooted (oldCalculus.source.demandEntryAt event)

local notation "Source" => cofaceSource rooted oldU7 oldCalculus

private def cofaceEvolution
    {s : (W).Support} {obstruction : (W).ObstructionAt s}
    {demand : (cofaceProducer rooted oldU7).DemandAt obstruction}
    (event : (Source).EventAt obstruction demand) :
    GeneratedU7ObstructionEvolutionAt (Source) event := by
  obtain ⟨disposition, entry⟩ := oldCalculus.compile event
  cases disposition with
  | settled receipt =>
      exact ⟨.settled (cofaceReceipt rooted receipt),
        ⟨⟨cofaceReceipt rooted entry.1.receipt⟩, congrArg (cofaceReceipt rooted) entry.2⟩⟩
  | @redirected successor change =>
      refine ⟨.redirected (successor := successor)
        ⟨cofaceReceipt rooted change.worldReceipt, congrArg Sum.inl change.claim_eq⟩, ?_⟩
      obtain ⟨evolution, exactReceipt⟩ := entry
      cases evolution with
      | carried _ _ => exact False.elim exactReceipt
      | maintained _ _ _ _ _ _ => exact False.elim exactReceipt
      | transferred receipt _ claim budget =>
          refine ⟨.transferred (cofaceReceipt rooted receipt) rfl ?_ ?_,
            congrArg (cofaceReceipt rooted) exactReceipt⟩
          · exact (coface_entry_claim rooted _).trans ((congrArg Sum.inl claim).trans
              (coface_entry_claim rooted _).symm)
          · calc
              _ = OpenResponsibilityAt.progressBudget (N := N)
                  (U7ActualSuccessorSource.demandEntry (oldCalculus.source.emit successor)) :=
                coface_entry_budget rooted _
              _ ≤ OpenResponsibilityAt.progressBudget (N := N)
                  (U7ActualSuccessorSource.demandEntry event) := budget
              _ = _ := (coface_entry_budget rooted _).symm
  | requiresTheoryAudit receipt =>
      exact ⟨.requiresTheoryAudit (cofaceReceipt rooted receipt), PUnit.unit⟩

/-- Retain the rooted failure's exact U7 calculus on the generated coface's
causal supports. The archive stays in the literal canonical network. -/
def afterCoface : LocalU7 (Coface).worldNetwork where
  slice := cofaceSlice rooted
  producer := cofaceProducer rooted U7
  calculus := ⟨cofaceSource rooted U7 rooted.calculus, cofaceEvolution rooted U7 rooted.calculus⟩

theorem archived_obstruction_is_local_iff
    (active : (Coface).worldNetwork.Support) (origin : N.Support)
    (obstruction : N.ObstructionAt origin) :
    (∃ member : (afterCoface rooted).slice.At active,
      (afterCoface rooted).slice.present member = ⟨origin, obstruction⟩) ↔
      origin = (Coface).translation.support.backward active := by
  constructor
  · rintro ⟨_, exactArchive⟩
    exact (congrArg Sigma.fst exactArchive).symm
  · intro sameSupport
    subst origin
    exact ⟨obstruction, rfl⟩

end LocalU7

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
