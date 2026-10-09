import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalRuntime.GeneratedPoweredCurrent

/-! # The field occurrence's entire ledger enters its finite-controller action -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Producer

def poweredSourceSupport : Work.Runtime.FieldSupport :=
  Work.Runtime.fieldCurrentSupport Work.Runtime.fieldRuntimeAfterFirst.state.current

abbrev PoweredSupport := Work.Runtime.FieldSupport ⊕ PoweredState

inductive PoweredCurrent
  | ingress
  | running (state : PoweredState)

def poweredCurrentSupport : PoweredCurrent → PoweredSupport
  | .ingress => .inl poweredSourceSupport
  | .running state => .inr state

def poweredCurrentState : PoweredCurrent → PoweredState
  | .ingress => sourceInitialState
  | .running state => state

def poweredNext (current : PoweredCurrent) : PoweredCurrent := .running (poweredStateNext (poweredCurrentState current))

def poweredOpenAt : PoweredSupport → Root.LAlanineLedgerResponsibility → Type
  | .inl stage, responsibility => Work.Runtime.FieldN.OpenAt stage responsibility
  | .inr _, _ => PUnit

def poweredNetwork : WorldRelationNetwork where
  Support := PoweredSupport
  Anchor := Work.Runtime.FieldN.Anchor
  Incidence := PoweredSupport
  Lineage := Work.Runtime.FieldN.Lineage
  Responsibility := Root.LAlanineLedgerResponsibility
  Claim := Root.LAlanineClaim
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := id
  lineageAt := fun _ => LAlanine40K2025.Source.key
  OpenAt := poweredOpenAt
  openClaimAt := fun _ => .registeredExperimentalGeometryModelBondTopology
  openProgressBudgetAt := fun {support} {_responsibility} receipt =>
    match support with
    | .inl _ => Work.Runtime.FieldN.openProgressBudgetAt receipt
    | .inr _ => 0
  HoldsAt := fun _ claim => PLift (claim = .registeredExperimentalGeometryModelBondTopology)
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PUnit
  DispositionAt := fun _ _ => PUnit

abbrev PoweredN := poweredNetwork

def poweredEntry : (support : PoweredSupport) → OpenResponsibilityAt PoweredN support
  | .inl stage => ⟨(Work.Runtime.fieldEntry stage).1, (Work.Runtime.fieldEntry stage).2⟩
  | .inr _ => ⟨.bondDensityIncidenceAdjudication, PUnit.unit⟩

theorem poweredEntry_unique (support : PoweredSupport) (entry : OpenResponsibilityAt PoweredN support) :
    entry = poweredEntry support := by
  cases support with
  | inl stage =>
    have old := Work.Runtime.fieldEntry_unique stage (⟨entry.1, entry.2⟩ : OpenResponsibilityAt Work.Runtime.FieldN stage)
    exact congrArg (fun oldEntry : OpenResponsibilityAt Work.Runtime.FieldN stage =>
      (⟨oldEntry.1, oldEntry.2⟩ : OpenResponsibilityAt PoweredN (.inl stage))) old
  | inr state =>
    rcases entry with ⟨responsibility, receipt⟩
    cases responsibility
    cases receipt
    rfl

def poweredInventory (support : PoweredSupport) : ConstructivePresentation PUnit (OpenResponsibilityAt PoweredN support) where
  forward := fun _ => poweredEntry support
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun entry => (poweredEntry_unique support entry).symm

def poweredTranslation : TypedSemanticWorldNetworkTranslationAt Work.Runtime.FieldN PoweredN where
  support :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => poweredSourceSupport
      backward_forward := fun _ => rfl }
  anchor := { forward := id, backward := id, backward_forward := fun _ => rfl }
  incidence :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => poweredSourceSupport
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

theorem poweredIngress_no_fresh_rows (stage : Work.Runtime.FieldSupport)
    (entry : OpenResponsibilityAt PoweredN (.inl stage)) :
    Nonempty (Sigma fun oldEntry : OpenResponsibilityAt Work.Runtime.FieldN stage =>
      PLift ((poweredTranslation.oldOpenLedger stage).forward oldEntry = entry)) :=
  ⟨⟨⟨entry.1, entry.2⟩, PLift.up rfl⟩⟩

end

end LAlanine40K2025.Thermal.Powered.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
