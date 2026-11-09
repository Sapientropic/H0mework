import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Theory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Old Effect : Type}
  (N : WorldRelationNetwork) (focus : N.Support) (bearer : OpenResponsibilityAt N focus)
  (grammar : Language Old Effect) (observed : Set Effect)
  (oldU7 : U7ProducerCalculus N)

local notation "W" => world N focus bearer grammar observed

def u7 : U7ProducerCalculus W where
  DemandAt := fun obstruction => match obstruction with
    | .inl original => oldU7.DemandAt original
    | .inr _ => Unit
  generateDemand := by
    intro support obstruction
    cases obstruction with
    | inl original => exact oldU7.generateDemand original
    | inr _ => exact ()

variable (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)

local notation "U" => u7 N focus bearer grammar observed oldU7

private def source : U7ActualSuccessorSource W U where
  EventAt := by
    intro support obstruction demand
    cases obstruction with
    | inl original => exact oldCalculus.source.EventAt original demand
    | inr gap => exact SourceGeneratedU7DemandAt U (.inr gap) demand
  emit := by
    intro support obstruction
    cases obstruction with
    | inl original => exact oldCalculus.source.emit original
    | inr gap => exact @SourceGeneratedU7DemandAt.canonical W U support (Sum.inr gap)
  demandGeneratedAt := by
    intro support obstruction demand event
    cases obstruction with
    | inl original =>
        have exactDemand := (oldCalculus.source.demandGeneratedAt event).payload_eq_generated
        subst demand
        exact @SourceGeneratedU7DemandAt.canonical W U support (Sum.inl original)
    | inr _ => exact event
  demandEntryAt := by
    intro support obstruction demand event
    cases obstruction with
    | inl original => exact oldCalculus.source.demandEntryAt event
    | inr gap =>
        exact gap.down.1.symm ▸ inheritedBearer N focus bearer grammar observed

local notation "Source" => source N focus bearer grammar observed oldU7 oldCalculus

private def inheritedEvent {support : N.Support} {original : N.ObstructionAt support}
    {demand : oldU7.DemandAt original} (event : oldCalculus.source.EventAt original demand) :
    (Source).EventAt (.inl original) demand :=
  event

private def inheritedEvolution {support : N.Support} {original : N.ObstructionAt support}
    {demand : oldU7.DemandAt original} (event : oldCalculus.source.EventAt original demand) :
    @GeneratedU7ObstructionEvolutionAt W U Source support (.inl original) demand
      (inheritedEvent N focus bearer grammar observed oldU7 oldCalculus event) := by
  obtain ⟨disposition, entry⟩ := oldCalculus.compile event
  cases disposition with
  | settled receipt =>
      exact ⟨.settled receipt, ⟨⟨entry.1.receipt⟩, entry.2⟩⟩
  | @redirected successor change =>
      refine ⟨.redirected (successor := Sum.inl successor)
        ⟨change.worldReceipt, congrArg Sum.inl change.claim_eq⟩, ?_⟩
      obtain ⟨evolution, exactReceipt⟩ := entry
      cases evolution with
      | carried _ _ => exact False.elim exactReceipt
      | maintained _ _ _ _ _ _ => exact False.elim exactReceipt
      | transferred receipt lineage claim budget =>
          exact ⟨.transferred receipt lineage (congrArg Sum.inl claim) budget, exactReceipt⟩
  | requiresTheoryAudit receipt =>
      exact ⟨.requiresTheoryAudit (Sum.inl receipt), PUnit.unit⟩

/-- Inherited obstructions keep the old compiler's actual disposition.
The paid gap requires audit and carries the exact existing bearer row. -/
def calculus : U7ObstructionEvolutionCalculus W U where
  source := Source
  compile := by
    intro support obstruction demand event
    cases obstruction with
    | inl original => exact inheritedEvolution N focus bearer grammar observed oldU7 oldCalculus event
    | inr gap => exact ⟨.requiresTheoryAudit (Sum.inr gap), PUnit.unit⟩

local notation "Calculus" => calculus N focus bearer grammar observed oldU7 oldCalculus

def audit (novel : ¬ observed ⊆ grammar.covered) :
    SourceNativeU7TheoryAuditAt Calculus
      ((Calculus).source.emit (obstruction N focus bearer grammar observed novel)) :=
  PUnit.unit

theorem audit_demand_entry (novel : ¬ observed ⊆ grammar.covered) :
    U7ActualSuccessorSource.demandEntry
      ((Calculus).source.emit (obstruction N focus bearer grammar observed novel)) =
      inheritedBearer N focus bearer grammar observed :=
  rfl

theorem audit_entry_disposition (novel : ¬ observed ⊆ grammar.covered) :
    HEq ((Calculus).compile ((Calculus).source.emit
      (obstruction N focus bearer grammar observed novel))).entryDisposition
      (LedgerEntryDispositionAt.evolved (.carried rfl HEq.rfl) :
        LedgerEntryDispositionAt W (inheritedBearer N focus bearer grammar observed)) :=
  HEq.rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
