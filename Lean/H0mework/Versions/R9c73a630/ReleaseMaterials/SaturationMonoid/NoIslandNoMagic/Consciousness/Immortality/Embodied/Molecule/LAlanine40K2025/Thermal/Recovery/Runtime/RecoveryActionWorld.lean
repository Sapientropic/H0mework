import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Producer.SourceGeneratedLAlanineRecovery

/-! # The load occurrence's entire ledger enters its thermal-recovery action -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Producer

def recoverySourceSupport : Load.Runtime.LoadSupport :=
  Load.Runtime.loadCurrentSupport Load.Runtime.loadRuntimeAfterFirst.state.current

abbrev RecoverySupport := Load.Runtime.LoadSupport ⊕ LoadState

inductive RecoveryCurrent
  | ingress
  | running (state : LoadState)

def recoveryCurrentSupport : RecoveryCurrent → RecoverySupport
  | .ingress => .inl recoverySourceSupport
  | .running state => .inr state

def recoveryCurrentState : RecoveryCurrent → LoadState
  | .ingress => recoveryReceivedState
  | .running state => state

def recoveryNext (current : RecoveryCurrent) : RecoveryCurrent :=
  .running (match current with
    | .ingress => recoveryStateFirst
    | .running state => loadStateNext state)

def recoveryOpenAt : RecoverySupport → Root.LAlanineLedgerResponsibility → Type
  | .inl stage, responsibility => Load.Runtime.LoadN.OpenAt stage responsibility
  | .inr _, _ => PUnit

def recoveryNetwork : WorldRelationNetwork where
  Support := RecoverySupport
  Anchor := Load.Runtime.LoadN.Anchor
  Incidence := RecoverySupport
  Lineage := Load.Runtime.LoadN.Lineage
  Responsibility := Root.LAlanineLedgerResponsibility
  Claim := Root.LAlanineClaim
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := id
  lineageAt := fun _ => LAlanine40K2025.Source.key
  OpenAt := recoveryOpenAt
  openClaimAt := fun _ => .registeredExperimentalGeometryModelBondTopology
  openProgressBudgetAt := fun {support} {_responsibility} receipt =>
    match support with
    | .inl _ => Load.Runtime.LoadN.openProgressBudgetAt receipt
    | .inr _ => 0
  HoldsAt := fun _ claim => PLift (claim = .registeredExperimentalGeometryModelBondTopology)
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PUnit
  DispositionAt := fun _ _ => PUnit

abbrev RecoveryN := recoveryNetwork

def recoveryEntry : (support : RecoverySupport) → OpenResponsibilityAt RecoveryN support
  | .inl stage => ⟨(Load.Runtime.loadEntry stage).1, (Load.Runtime.loadEntry stage).2⟩
  | .inr _ => ⟨.bondDensityIncidenceAdjudication, PUnit.unit⟩

theorem recoveryEntry_unique (support : RecoverySupport) (entry : OpenResponsibilityAt RecoveryN support) :
    entry = recoveryEntry support := by
  cases support with
  | inl stage =>
    have old := Load.Runtime.loadEntry_unique stage (⟨entry.1, entry.2⟩ : OpenResponsibilityAt Load.Runtime.LoadN stage)
    exact congrArg (fun oldEntry : OpenResponsibilityAt Load.Runtime.LoadN stage =>
      (⟨oldEntry.1, oldEntry.2⟩ : OpenResponsibilityAt RecoveryN (.inl stage))) old
  | inr state =>
    rcases entry with ⟨responsibility, receipt⟩
    cases responsibility
    cases receipt
    rfl

def recoveryInventory (support : RecoverySupport) : ConstructivePresentation PUnit (OpenResponsibilityAt RecoveryN support) where
  forward := fun _ => recoveryEntry support
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun entry => (recoveryEntry_unique support entry).symm

def recoveryTranslation : TypedSemanticWorldNetworkTranslationAt Load.Runtime.LoadN RecoveryN where
  support :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => recoverySourceSupport
      backward_forward := fun _ => rfl }
  anchor := { forward := id, backward := id, backward_forward := fun _ => rfl }
  incidence :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => recoverySourceSupport
      backward_forward := fun _ => rfl }
  lineage := { forward := id, backward := id, backward_forward := fun _ => rfl }
  responsibility := { forward := id, backward := id, backward_forward := fun _ => rfl }
  claim := { forward := id, backward := id, backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ =>
    { forward := fun entry => ⟨entry.1, entry.2⟩
      backward := fun entry => ⟨entry.1, entry.2⟩
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ evidence => evidence
  oldDispositionSurvives := fun _ _ receipt => receipt

theorem recoveryIngress_no_fresh_rows (stage : Load.Runtime.LoadSupport)
    (entry : OpenResponsibilityAt RecoveryN (.inl stage)) :
    Nonempty (Sigma fun oldEntry : OpenResponsibilityAt Load.Runtime.LoadN stage =>
      PLift ((recoveryTranslation.oldOpenLedger stage).forward oldEntry = entry)) :=
  ⟨⟨⟨entry.1, entry.2⟩, PLift.up rfl⟩⟩

end

end LAlanine40K2025.Thermal.Recovery.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
