import H0mework.Versions.R9c73a630.Chemistry.LAlanineWork.FieldActionLedger

/-! # The controlled law installs its material and quantitative consumers before emission -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Drive

noncomputable section

private def fieldRestructuringLaw : SourceNativeLedgerRestructuringLaw fieldSource :=
  identityOnlyWorldLedgerRestructuringLaw fieldSource Source.key (by
    intro support responsibility
    cases support with
    | inl stage => exact Root.networkOpenAtSubsingleton stage responsibility
    | inr _ =>
      change Subsingleton PUnit
      infer_instance)

private def fieldRestructuringCompiler : SourceNativeRestructuringLedgerCompiler fieldSource where
  ledgerCompiler := fieldLedgerCompiler
  restructuringLaw := fieldRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (fieldEntry_unique _ left).trans (fieldEntry_unique _ right).symm)
    (fun left right _ => (fieldEntry_unique _ left).trans (fieldEntry_unique _ right).symm)

def fieldRestructuringSource : SourceNativeRestructuringLedgerSource FieldN FieldV where
  source := fieldSource
  compiler := fieldRestructuringCompiler

inductive FieldProjection
  | current
  | next
  | work
  | capacityBalance
  | wholeLedger

def fieldProjectionLaw : SourceNativeProjectionLaw fieldRestructuringSource.toLedgerSource where
  Projection := FieldProjection
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .current => FieldState
    | .next => FieldState
    | .work => ℝ
    | .capacityBalance => PLift (type_of% (fieldStateNext_capacity (fieldCurrentState current)))
    | .wholeLedger => SourceNativeLedgerEvolutionAt fieldSource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .current => fieldCurrentState current
    | .next => fieldStateNext (fieldCurrentState current)
    | .work => fieldCycleWork (fieldCurrentState current).pair
    | .capacityBalance => ⟨fieldStateNext_capacity (fieldCurrentState current)⟩
    | .wholeLedger => fieldLedgerCompiler.compile occurrence

def fieldAuthoritySource : SourceNativeAuthoritySource FieldN FieldV where
  restructuringSource := fieldRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal fieldRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic FieldN
  projectionLaw := fieldProjectionLaw

def fieldAuthoritativeRoot : SourceNativeAuthoritativeRootClosure FieldN FieldV where
  source := fieldAuthoritySource
  emitted := fieldEmitted
  compiler_commutes := fun _ => rfl

def fieldLivingRoot : SourceNativeLivingRootClosure FieldN FieldV :=
  fieldAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def fieldInitialVisit : SourceNativeTemporalVisitAt fieldLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite fieldLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def fieldInitialGenerated :=
  fieldLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit fieldInitialVisit

def fieldInitialEntry := fieldEntry (fieldCurrentSupport .ingress)

def fieldInitialEntryRow : fieldInitialGenerated.GeneratedEntryRowAt fieldInitialEntry :=
  (fieldInitialGenerated.canonicalGeneratedEntryRow? fieldInitialEntry).get (by rfl)

def fieldFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    fieldInitialGenerated.occurrence fieldInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? fieldInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end

end LAlanine40K2025.Thermal.Work.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
