import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Certificate
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Projection
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Registration.Source
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

/-! The packet programme retains the original law epoch, every dependent
projection and the original material observation before emitting its root. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Restructuring
open SourceOperationEffects DebtActivationWorld CompilerFromPacketSourceLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (packetAt : (current : V.Current) → Packet old.toLedgerRoot current)

/-- Old laws and their realizations retain their exact fibres. The added
language denotes only the debt world's existing mathematical claim. -/
def lawSurface : TheoryState (World registered) where
  inventory := {
    Version := old.source.lawSurface.inventory.Version
    version := old.source.lawSurface.inventory.version
    Law := old.source.lawSurface.inventory.Law
    RealizationAt := fun {support} obstruction => match obstruction with
      | .inl prior => old.source.lawSurface.inventory.RealizationAt prior
      | .inr _ => (World registered).HoldsAt support (.inr (scope registered).debtClaim)
    RealizationWithoutAt := fun deleted {support} obstruction => match obstruction with
      | .inl prior => old.source.lawSurface.inventory.RealizationWithoutAt deleted prior
      | .inr _ => (World registered).HoldsAt support (.inr (scope registered).debtClaim) }
  ExpressionAt := fun support => old.source.lawSurface.ExpressionAt support.1 ⊕ (scope registered).DebtClaim
  denotes := fun expression => match expression with
    | .inl prior => .inl (old.source.lawSurface.denotes prior)
    | .inr claim => .inr claim
  TheoremAt := fun {_support} expression => match expression with
    | .inl prior => old.source.lawSurface.TheoremAt prior
    | .inr claim => (World registered).HoldsAt _ (.inr claim)
  theoremPresentation := fun expression => match expression with
    | .inl prior => old.source.lawSurface.theoremPresentation prior
    | .inr _ => ConstructivePresentation.refl _

def projectionLaw : SourceNativeProjectionLaw (ledgerRoot registered packetAt).source where
  Projection := old.source.projectionLaw.Projection ⊕ PUnit
  ActiveAt := fun projection {_current} occurrence => match projection with
    | .inl prior => old.source.projectionLaw.ActiveAt prior (originalOccurrence registered packetAt occurrence)
    | .inr _ => PUnit
  InactiveAt := fun projection {_current} occurrence => match projection with
    | .inl prior => old.source.projectionLaw.InactiveAt prior (originalOccurrence registered packetAt occurrence)
    | .inr _ => PEmpty
  classify := fun projection {_current} occurrence => match projection with
    | .inl prior => old.source.projectionLaw.classify prior (originalOccurrence registered packetAt occurrence)
    | .inr _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence active => match projection with
    | .inl prior => old.source.projectionLaw.PayloadAt prior (originalOccurrence registered packetAt occurrence) active
    | .inr _ => Native.MathReadout registered
  project := fun projection {current} occurrence active => match projection with
    | .inl prior => old.source.projectionLaw.project prior (originalOccurrence registered packetAt occurrence) active
    | .inr _ => Native.mathReadout registered current

def observationLaw : SourceNativeProjectionLaw (ledgerRoot registered packetAt).source where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ =>
    (old.source.observationAt (originalOccurrence registered packetAt occurrence)).1
  project := fun _ {_current} occurrence _ =>
    (old.source.observationAt (originalOccurrence registered packetAt occurrence)).2

def completeRawLaw : SourceNativeProjectionLaw (ledgerRoot registered packetAt).source where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => RawInputAt (Value := Value) (Var := Var) (sort := sort)
    old.toLedgerRoot origin (old.emitted origin)
  project := fun _ {_current} _ _ => registered.input

def rawLaw : SourceNativeProjectionLaw (ledgerRoot registered packetAt).source where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort)
  project := fun _ {_current} _ _ => ⟨registered.input.environment, registered.input.expression⟩

theorem projection_original {current : Current registered}
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current)
    (projection : old.source.projectionLaw.Projection) :
    HEq ((projectionLaw old registered packetAt).outcomeAt (.inl projection) occurrence)
      (old.source.projectionLaw.outcomeAt projection (originalOccurrence registered packetAt occurrence)) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [projectionLaw]
  cases old.source.projectionLaw.classify projection (originalOccurrence registered packetAt occurrence) <;> rfl


def restructuringCertification {current : Current registered}
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (law old registered packetAt)
      ((compiler registered packetAt).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact certificate old registered packetAt current

def appendCompiler : SourceNativeRestructuringLedgerCompiler (source registered packetAt) where
  ledgerCompiler := compiler registered packetAt
  restructuringLaw := law old registered packetAt
  certifyRestructuring := restructuringCertification old registered packetAt

def restructuringSource : SourceNativeRestructuringLedgerSource (World registered) (JointV registered packetAt) where
  source := source registered packetAt
  compiler := appendCompiler old registered packetAt

private theorem source_terminal_empty (current : Current registered) :
    IsEmpty ((JointV registered packetAt).FaithfulTerminalAt current) := by
  constructor
  intro terminal
  have actualNext := (packetAt current.1).actual_next
  rw [terminal.2] at actualNext
  cases actualNext

def baseAuthority : SourceNativeAuthoritySource (World registered) (JointV registered packetAt) where
  restructuringSource := restructuringSource old registered packetAt
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource old registered packetAt)
    (source_terminal_empty old registered packetAt)
  lawSurface := lawSurface old registered
  projectionLaw := projectionLaw old registered packetAt

def observedSource := (baseAuthority old registered packetAt).withProjectionCoface (observationLaw old registered packetAt)
def completeSource := (observedSource old registered packetAt).withProjectionCoface (completeRawLaw old registered packetAt)

def authoritySource : SourceNativeAuthoritySource (World registered) (JointV registered packetAt) :=
  { (completeSource old registered packetAt).withProjectionCoface (rawLaw old registered packetAt) with
    observationAt := fun {_current} occurrence =>
      ⟨Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort),
        (rawLaw old registered packetAt).project PUnit.unit occurrence PUnit.unit⟩ }

def rawInstallation : SourceNativeProjectionLaw.InstallationAt (rawLaw old registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  .componentCoface (completeSource old registered packetAt) (rawLaw old registered packetAt)

def completeInstallation : SourceNativeProjectionLaw.InstallationAt (completeRawLaw old registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (observedSource old registered packetAt) (completeRawLaw old registered packetAt)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (completeSource old registered packetAt) (rawLaw old registered packetAt))

def observationInstallation : SourceNativeProjectionLaw.InstallationAt (observationLaw old registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (baseAuthority old registered packetAt) (observationLaw old registered packetAt)).trans
    ((SourceNativeProjectionLaw.InstallationAt.inheritedCoface (observedSource old registered packetAt) (completeRawLaw old registered packetAt)).trans
      (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (completeSource old registered packetAt) (rawLaw old registered packetAt)))

def oldInstallation : SourceNativeProjectionLaw.InstallationAt (projectionLaw old registered packetAt)
    (authoritySource old registered packetAt).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (baseAuthority old registered packetAt) (observationLaw old registered packetAt)).trans
    ((SourceNativeProjectionLaw.InstallationAt.inheritedCoface (observedSource old registered packetAt) (completeRawLaw old registered packetAt)).trans
      (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (completeSource old registered packetAt) (rawLaw old registered packetAt)))

def authoritativeRoot : SourceNativeAuthoritativeRootClosure (World registered) (JointV registered packetAt) where
  source := authoritySource old registered packetAt
  emitted := emitted registered packetAt
  compiler_commutes := (ledgerRoot registered packetAt).compiler_commutes

def livingRoot : SourceNativeLivingRootClosure (World registered) (JointV registered packetAt) :=
  (authoritativeRoot old registered packetAt).toLivingWithoutFaithfulTerminal
    (source_terminal_empty old registered packetAt)

theorem root_ledger_preserved : (authoritativeRoot old registered packetAt).toLedgerRoot =
    ledgerRoot registered packetAt := rfl

theorem living_ledger_preserved : (livingRoot old registered packetAt).toAuthoritativeRoot.toLedgerRoot =
    ledgerRoot registered packetAt := rfl

theorem law_surface_preserved : (authoritySource old registered packetAt).lawSurface = lawSurface old registered := rfl

theorem observation_generated {current : Current registered}
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current) :
    (authoritySource old registered packetAt).observationAt occurrence =
      ⟨Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort),
        ⟨registered.input.environment, registered.input.expression⟩⟩ := rfl

theorem old_projection_outcome {current : Current registered}
    (occurrence : (source registered packetAt).toRootSource.actual.OccurrenceAt current)
    (projection : old.source.projectionLaw.Projection) :
    HEq ((authoritySource old registered packetAt).projectionLaw.outcomeAt
      ((oldInstallation old registered packetAt).embed (.inl projection)) occurrence)
      (old.source.projectionLaw.outcomeAt projection (originalOccurrence registered packetAt occurrence)) :=
  ((oldInstallation old registered packetAt).outcome_heq occurrence (.inl projection)).trans
    (projection_original old registered packetAt occurrence projection)

end RootGeneratedDebtActivationJointSource.Successor.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
