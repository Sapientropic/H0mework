import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Compiler
import H0mework.Foundation.Ledger.ProofRelevantRestructuring
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext
import H0mework.Realization.Operations.Execution.Relations.History.Source

/-! Proof-relevant certification is generated from the actual full step's two
inverse laws. The old law epoch and every old face stay tied to the original
occurrence; raw and paid-state faces belong to this source before emission. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationEffects DebtActivationWorld DebtActivationLedger
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

def restructuringCertification {state : Current old origin reader}
    (occurrence : (source old origin reader).toRootSource.actual.OccurrenceAt state) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
      ((compiler old origin reader).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact (image old origin reader state).2.2.2

def restructuringSource : SourceNativeRestructuringLedgerSource (World old origin reader) (vocabulary old origin reader) where
  source := source old origin reader
  compiler := {
    ledgerCompiler := compiler old origin reader
    restructuringLaw := restructuringLaw old origin reader
    certifyRestructuring := restructuringCertification old origin reader }

def lawSurface : TheoryState (World old origin reader) where
  inventory := {
    Version := old.source.lawSurface.inventory.Version
    version := old.source.lawSurface.inventory.version
    Law := old.source.lawSurface.inventory.Law
    RealizationAt := fun {support} obstruction => match obstruction with
      | .inl prior => old.source.lawSurface.inventory.RealizationAt prior
      | .inr _ => (World old origin reader).HoldsAt support (.inr (law old origin reader).debtClaim)
    RealizationWithoutAt := fun deleted {support} obstruction => match obstruction with
      | .inl prior => old.source.lawSurface.inventory.RealizationWithoutAt deleted prior
      | .inr _ => (World old origin reader).HoldsAt support (.inr (law old origin reader).debtClaim) }
  ExpressionAt := fun support => old.source.lawSurface.ExpressionAt support.1 ⊕ (law old origin reader).DebtClaim
  denotes := fun expression => match expression with
    | .inl prior => .inl (old.source.lawSurface.denotes prior)
    | .inr claim => .inr claim
  TheoremAt := fun {_support} expression => match expression with
    | .inl prior => old.source.lawSurface.TheoremAt prior
    | .inr claim => (World old origin reader).HoldsAt _ (.inr claim)
  theoremPresentation := fun expression => match expression with
    | .inl prior => old.source.lawSurface.theoremPresentation prior
    | .inr _ => ConstructivePresentation.refl _

-- The relation coordinate is generated from this state’s paid past; raw and
-- state coordinates keep their original payloads.
def projectionLaw : SourceNativeProjectionLaw (ledgerRoot old origin reader).source where
  Projection := old.source.projectionLaw.Projection ⊕ (Bool ⊕ PUnit)
  ActiveAt := fun projection {_state} _ => match projection with
    | .inl prior => old.source.projectionLaw.ActiveAt prior (old.emitted origin)
    | .inr _ => PUnit
  InactiveAt := fun projection {_state} _ => match projection with
    | .inl prior => old.source.projectionLaw.InactiveAt prior (old.emitted origin)
    | .inr _ => PEmpty
  classify := fun projection {_state} _ => match projection with
    | .inl prior => old.source.projectionLaw.classify prior (old.emitted origin)
    | .inr _ => .inl PUnit.unit
  PayloadAt := fun projection {_state} _ active => match projection with
    | .inl prior => old.source.projectionLaw.PayloadAt prior (old.emitted origin) active
    | .inr (.inl false) => Raw (Value := Value) (Var := Var) (sort := sort)
    | .inr (.inl true) => Current old origin reader
    | .inr (.inr _) => Current old origin reader ×
        RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt
          (SourceOperationEffects.Expr Value Var sort)) ×
        RootedAccountedUnfolding (SourceOperationEffects.Expr Value Var sort → Value sort)
  project := fun projection {state} _ active => match projection with
    | .inl prior => old.source.projectionLaw.project prior (old.emitted origin) active
    | .inr (.inl false) => raw old origin reader
    | .inr (.inl true) => state
    | .inr (.inr _) => ⟨state,SourceOperationPaidRelations.exposure state.2,
        SourceOperationPaidRelations.evaluator (raw old origin reader).environment⟩

def baseAuthority : SourceNativeAuthoritySource (World old origin reader) (vocabulary old origin reader) where
  restructuringSource := restructuringSource old origin reader
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource old origin reader)
    (fun _ => ⟨fun impossible => nomatch impossible⟩)
  lawSurface := lawSurface old origin reader
  projectionLaw := projectionLaw old origin reader

abbrev OriginalMaterial :=
  Σ occurrence : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin,
  Σ generated : SourceNativeLedgerEvolutionAt old.toLedgerRoot.source.source occurrence,
    SourceNativeFiniteLedgerPatchAt old.toLedgerRoot.source.source
      old.toLedgerRoot.source.ledgerCompiler.ExactTransitionAt old.toLedgerRoot.source.ledgerCompiler.writeRowSource
      old.toLedgerRoot.source.ledgerCompiler.terminalRowSource generated ×
    SourceNativeLedgerRestructuringCertificationAt old.source.restructuringSource.compiler.restructuringLaw generated

def originalLaw : SourceNativeProjectionLaw (ledgerRoot old origin reader).source where
  Projection := PUnit
  ActiveAt := fun _ {_state} _ => PUnit
  InactiveAt := fun _ {_state} _ => PEmpty
  classify := fun _ {_state} _ => .inl PUnit.unit
  PayloadAt := fun _ {_state} _ _ => OriginalMaterial old origin
  project := fun _ {_state} _ _ =>
    ⟨old.emitted origin, old.generatedLedgerAt origin, old.generatedPatchAt origin,
      old.source.restructuringSource.compiler.certifyRestructuring (old.emitted origin)⟩

def archivedSource := (baseAuthority old origin reader).withProjectionCoface (originalLaw old origin reader)

def observationLaw : SourceNativeProjectionLaw (ledgerRoot old origin reader).source where
  Projection := PUnit
  ActiveAt := fun _ {_state} _ => PUnit
  InactiveAt := fun _ {_state} _ => PEmpty
  classify := fun _ {_state} _ => .inl PUnit.unit
  PayloadAt := fun _ {_state} _ _ => (old.source.observationAt (old.emitted origin)).1
  project := fun _ {_state} _ _ => (old.source.observationAt (old.emitted origin)).2

def authoritySource := (archivedSource old origin reader).withProjectionCoface (observationLaw old origin reader)

def baseInstallation := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (baseAuthority old origin reader) (originalLaw old origin reader)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (archivedSource old origin reader) (observationLaw old origin reader))

def originalInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (baseAuthority old origin reader) (originalLaw old origin reader)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (archivedSource old origin reader) (observationLaw old origin reader))

def observationInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (archivedSource old origin reader) (observationLaw old origin reader)

def authoritativeRoot : SourceNativeAuthoritativeRootClosure (World old origin reader) (vocabulary old origin reader) where
  source := authoritySource old origin reader
  emitted := (ledgerRoot old origin reader).emitted
  compiler_commutes := (ledgerRoot old origin reader).compiler_commutes

def livingRoot := (authoritativeRoot old origin reader).toLivingWithoutFaithfulTerminal
  (fun _ => ⟨fun impossible => nomatch impossible⟩)

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
