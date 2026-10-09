import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineLoadCurrent

/-! # The powered occurrence's entire ledger enters its thermal-load action -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer

def loadSourceSupport : Powered.Runtime.PoweredSupport :=
  Powered.Runtime.poweredCurrentSupport Powered.Runtime.poweredRuntimeAfterFirst.tick.next.state.current

abbrev LoadSupport := Powered.Runtime.PoweredSupport ⊕ LoadState

inductive LoadCurrent
  | ingress
  | running (state : LoadState)

def loadCurrentSupport : LoadCurrent → LoadSupport
  | .ingress => .inl loadSourceSupport
  | .running state => .inr state

def loadCurrentState : LoadCurrent → LoadState
  | .ingress => loadInitialState
  | .running state => state

def loadNext (current : LoadCurrent) : LoadCurrent := .running (loadStateNext (loadCurrentState current))

def loadOpenAt : LoadSupport → Root.LAlanineLedgerResponsibility → Type
  | .inl stage, responsibility => Powered.Runtime.PoweredN.OpenAt stage responsibility
  | .inr _, _ => PUnit

def loadNetwork : WorldRelationNetwork where
  Support := LoadSupport
  Anchor := Powered.Runtime.PoweredN.Anchor
  Incidence := LoadSupport
  Lineage := Powered.Runtime.PoweredN.Lineage
  Responsibility := Root.LAlanineLedgerResponsibility
  Claim := Root.LAlanineClaim
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := id
  lineageAt := fun _ => LAlanine40K2025.Source.key
  OpenAt := loadOpenAt
  openClaimAt := fun _ => .registeredExperimentalGeometryModelBondTopology
  openProgressBudgetAt := fun {support} {_responsibility} receipt =>
    match support with
    | .inl _ => Powered.Runtime.PoweredN.openProgressBudgetAt receipt
    | .inr _ => 0
  HoldsAt := fun _ claim => PLift (claim = .registeredExperimentalGeometryModelBondTopology)
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PUnit
  DispositionAt := fun _ _ => PUnit

abbrev LoadN := loadNetwork

def loadEntry : (support : LoadSupport) → OpenResponsibilityAt LoadN support
  | .inl stage => ⟨(Powered.Runtime.poweredEntry stage).1, (Powered.Runtime.poweredEntry stage).2⟩
  | .inr _ => ⟨.bondDensityIncidenceAdjudication, PUnit.unit⟩

theorem loadEntry_unique (support : LoadSupport) (entry : OpenResponsibilityAt LoadN support) :
    entry = loadEntry support := by
  cases support with
  | inl stage =>
    have old := Powered.Runtime.poweredEntry_unique stage (⟨entry.1, entry.2⟩ : OpenResponsibilityAt Powered.Runtime.PoweredN stage)
    exact congrArg (fun oldEntry : OpenResponsibilityAt Powered.Runtime.PoweredN stage =>
      (⟨oldEntry.1, oldEntry.2⟩ : OpenResponsibilityAt LoadN (.inl stage))) old
  | inr state =>
    rcases entry with ⟨responsibility, receipt⟩
    cases responsibility
    cases receipt
    rfl

def loadInventory (support : LoadSupport) : ConstructivePresentation PUnit (OpenResponsibilityAt LoadN support) where
  forward := fun _ => loadEntry support
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun entry => (loadEntry_unique support entry).symm

def loadTranslation : TypedSemanticWorldNetworkTranslationAt Powered.Runtime.PoweredN LoadN where
  support :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => loadSourceSupport
      backward_forward := fun _ => rfl }
  anchor := { forward := id, backward := id, backward_forward := fun _ => rfl }
  incidence :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => loadSourceSupport
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

theorem loadIngress_no_fresh_rows (stage : Powered.Runtime.PoweredSupport)
    (entry : OpenResponsibilityAt LoadN (.inl stage)) :
    Nonempty (Sigma fun oldEntry : OpenResponsibilityAt Powered.Runtime.PoweredN stage =>
      PLift ((loadTranslation.oldOpenLedger stage).forward oldEntry = entry)) :=
  ⟨⟨⟨entry.1, entry.2⟩, PLift.up rfl⟩⟩

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
