import H0mework.Chemistry.LAlanineWork.FieldActionCurrent

/-! # Conservative ingress of the original ledger into its field-controlled action -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

abbrev FieldSupport := Root.LAlanineStage ⊕ FieldState

inductive FieldCurrent
  | ingress
  | running (state : FieldState)

def fieldCurrentSupport : FieldCurrent → FieldSupport
  | .ingress => .inl (.nativeElectronicCurrent fieldSourceTime)
  | .running state => .inr state

def fieldCurrentState : FieldCurrent → FieldState
  | .ingress => fieldInitialState
  | .running state => state

def fieldNext (current : FieldCurrent) : FieldCurrent := .running (fieldStateNext (fieldCurrentState current))

def fieldOpenAt : FieldSupport → Root.LAlanineLedgerResponsibility → Type
  | .inl stage, responsibility => Root.N.OpenAt stage responsibility
  | .inr _, _ => PUnit

def fieldNetwork : WorldRelationNetwork where
  Support := FieldSupport
  Anchor := Root.N.Anchor
  Incidence := FieldSupport
  Lineage := Root.N.Lineage
  Responsibility := Root.LAlanineLedgerResponsibility
  Claim := Root.LAlanineClaim
  anchorAt := fun _ => Source.key
  incidenceAt := id
  lineageAt := fun _ => Source.key
  OpenAt := fieldOpenAt
  openClaimAt := fun _ => .registeredExperimentalGeometryModelBondTopology
  openProgressBudgetAt := fun {support} {_responsibility} receipt =>
    match support with
    | .inl _ => Root.N.openProgressBudgetAt receipt
    | .inr _ => 0
  HoldsAt := fun _ claim => PLift (claim = .registeredExperimentalGeometryModelBondTopology)
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PUnit
  DispositionAt := fun _ _ => PUnit

abbrev FieldN := fieldNetwork

def fieldEntry : (support : FieldSupport) → OpenResponsibilityAt FieldN support
  | .inl stage => ⟨(Root.entryAt stage).1, (Root.entryAt stage).2⟩
  | .inr _ => ⟨.bondDensityIncidenceAdjudication, PUnit.unit⟩

theorem fieldEntry_unique (support : FieldSupport) (entry : OpenResponsibilityAt FieldN support) :
    entry = fieldEntry support := by
  cases support with
  | inl stage =>
    have old := Root.entryAt_unique (⟨entry.1, entry.2⟩ : OpenResponsibilityAt Root.N stage)
    exact congrArg (fun oldEntry : OpenResponsibilityAt Root.N stage =>
      (⟨oldEntry.1, oldEntry.2⟩ : OpenResponsibilityAt FieldN (.inl stage))) old
  | inr state =>
    rcases entry with ⟨responsibility, receipt⟩
    cases responsibility
    cases receipt
    rfl

def fieldInventory (support : FieldSupport) : ConstructivePresentation PUnit (OpenResponsibilityAt FieldN support) where
  forward := fun _ => fieldEntry support
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun entry => (fieldEntry_unique support entry).symm

def fieldTranslation : TypedSemanticWorldNetworkTranslationAt Root.N FieldN where
  support :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => .nativeElectronicCurrent fieldSourceTime
      backward_forward := fun _ => rfl }
  anchor := { forward := id, backward := id, backward_forward := fun _ => rfl }
  incidence :=
    { forward := Sum.inl
      backward := fun | .inl stage => stage | .inr _ => .nativeElectronicCurrent fieldSourceTime
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

theorem fieldIngress_no_fresh_rows (stage : Root.LAlanineStage)
    (entry : OpenResponsibilityAt FieldN (.inl stage)) :
    Nonempty (Sigma fun oldEntry : OpenResponsibilityAt Root.N stage =>
      PLift ((fieldTranslation.oldOpenLedger stage).forward oldEntry = entry)) :=
  ⟨⟨⟨entry.1, entry.2⟩, PLift.up rfl⟩⟩

end

end LAlanine40K2025.Thermal.Work.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
