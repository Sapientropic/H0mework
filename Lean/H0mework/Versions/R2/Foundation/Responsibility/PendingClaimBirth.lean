import H0mework.Versions.R2.Foundation.Runtime.Activation
import H0mework.Foundation.Responsibility.DebtLedgerReadback
import H0mework.Foundation.Ledger.OriginOrBirth

/-!
# Source-exact pending-claim ledger birth

A named source face may emit a positive pending responsibility before it has
generated a payment or settlement.  Such a face projects a package whose
payload is definitionally the debt law, initial state and positive budget.
There is no secondary payload-to-claim map: the claim is `law.debtClaim`.

The result is only a heterogeneous old-ledger to extended-ledger birth.  Every
old row has a typed origin; the distinguished debt row has exact fresh-birth
provenance.  This kernel creates neither a living root nor a next current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace PendingClaimBirth

open DebtActivationLedger DebtActivationWorld

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}}

/-- Exact payload of a pending-claim projection.  The law is a dependent type
index fixed by the projection itself, so the package remains in `Type u`. -/
structure SourceGeneratedPendingClaimPackage
    (law : DebtActivationLaw.{u}) : Type u where
  initial : law.DebtState
  initialBudget_positive : 0 < law.budget initial

/-- Strong pending-claim projection law.  Unlike an arbitrary projection plus
an external mapper, its projected payload is definitionally the package. -/
structure SourceNativePendingClaimProjectionLaw
    {V : Vocabulary.{u}} (source : SourceNativeLedgerSource N V) :
    Type (u + 1) where
  Projection : Type u
  ActiveAt : (projection : Projection) ->
    {current : V.Current} ->
      source.source.toRootSource.actual.OccurrenceAt current -> Type u
  InactiveAt : (projection : Projection) ->
    {current : V.Current} ->
      source.source.toRootSource.actual.OccurrenceAt current -> Type u
  classify : (projection : Projection) ->
    {current : V.Current} ->
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) ->
      ActiveAt projection occurrence ⊕ InactiveAt projection occurrence
  lawAt : (projection : Projection) ->
    {current : V.Current} ->
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) ->
    ActiveAt projection occurrence -> DebtActivationLaw.{u}
  project : (projection : Projection) ->
    {current : V.Current} ->
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) ->
    (active : ActiveAt projection occurrence) ->
      SourceGeneratedPendingClaimPackage
        (lawAt projection occurrence active)

def SourceNativePendingClaimProjectionLaw.toProjectionLaw
    {V : Vocabulary.{u}} {source : SourceNativeLedgerSource N V}
    (law : SourceNativePendingClaimProjectionLaw source) :
    SourceNativeProjectionLaw source where
  Projection := law.Projection
  ActiveAt := law.ActiveAt
  InactiveAt := law.InactiveAt
  classify := law.classify
  PayloadAt := fun projection _ occurrence active =>
    SourceGeneratedPendingClaimPackage
      (law.lawAt projection occurrence active)
  project := law.project

/-- Named inventory of installed package-valued faces.  Each component must
be genuinely installed in the base authority projection. -/
structure SourceNativePendingClaimRuntimeFacade
    (N : WorldRelationNetwork.{u}) : Type (u + 4) where
  base : SourceNativeLivingRuntimeFacade N
  PendingFaceAt : (runtime : LivingRuntimeState base.process) -> Type u
  componentAt : (runtime : LivingRuntimeState base.process) ->
    PendingFaceAt runtime ->
      SourceNativePendingClaimProjectionLaw
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.source
  installationAt : (runtime : LivingRuntimeState base.process) ->
    (face : PendingFaceAt runtime) ->
      SourceNativeProjectionLaw.InstallationAt
        (componentAt runtime face).toProjectionLaw
        runtime.current.root.toAuthoritativeRoot.source.projectionLaw
  projectionAt : (runtime : LivingRuntimeState base.process) ->
    (face : PendingFaceAt runtime) -> (componentAt runtime face).Projection

namespace SourceNativePendingClaimRuntimeFacade

variable (facade : SourceNativePendingClaimRuntimeFacade N)
  (runtime : LivingRuntimeState facade.base.process)
  (face : facade.PendingFaceAt runtime)
  (active : (facade.componentAt runtime face).ActiveAt
    (facade.projectionAt runtime face) runtime.emittedOccurrence)

def law : DebtActivationLaw.{u} :=
  (facade.componentAt runtime face).lawAt
    (facade.projectionAt runtime face) runtime.emittedOccurrence active

def package : SourceGeneratedPendingClaimPackage
    (facade.law runtime face active) :=
  (facade.componentAt runtime face).project
    (facade.projectionAt runtime face) runtime.emittedOccurrence active

end SourceNativePendingClaimRuntimeFacade

/-- Exact active read of one installed package-valued face. -/
structure SourceInstalledPendingClaimFaceAt
    (facade : SourceNativePendingClaimRuntimeFacade N)
    (runtime : LivingRuntimeState facade.base.process)
    (face : facade.PendingFaceAt runtime) : Type (u + 4) where
  active : (facade.componentAt runtime face).ActiveAt
    (facade.projectionAt runtime face) runtime.emittedOccurrence
  classifier_eq :
    (facade.componentAt runtime face).classify
        (facade.projectionAt runtime face) runtime.emittedOccurrence =
      .inl active

namespace SourceInstalledPendingClaimFaceAt

variable
  {facade : SourceNativePendingClaimRuntimeFacade N}
  {runtime : LivingRuntimeState facade.base.process}
  {face : facade.PendingFaceAt runtime}

/-- One named face and occurrence have only one active package read. -/
theorem eq
    (left right : SourceInstalledPendingClaimFaceAt facade runtime face) :
    left = right := by
  cases left with
  | mk leftActive leftClassifier =>
      cases right with
      | mk rightActive rightClassifier =>
          have active_eq : leftActive = rightActive :=
            (facade.componentAt runtime face).toProjectionLaw
              |>.active_eq_of_classify_eq leftClassifier rightClassifier
          cases active_eq
          rfl

def package (read : SourceInstalledPendingClaimFaceAt facade runtime face) :
    SourceGeneratedPendingClaimPackage
      (facade.law runtime face read.active) :=
  facade.package runtime face read.active

theorem installed_outcome_heq
    (_read : SourceInstalledPendingClaimFaceAt facade runtime face) :
    HEq
      ((facade.componentAt runtime face).toProjectionLaw.outcomeAt
        (facade.projectionAt runtime face) runtime.emittedOccurrence)
      (runtime.tick.generated.projectionOutcome
        ((facade.installationAt runtime face).embed
          (facade.projectionAt runtime face))) :=
  ((facade.installationAt runtime face).outcome_heq
    runtime.emittedOccurrence (facade.projectionAt runtime face)).symm

end SourceInstalledPendingClaimFaceAt

/-- The exact birth indices contain the named facade, runtime event and its
active package-valued face; no law or claim is accepted separately. -/
structure SourceExactPendingClaimBirthReceiptAt
    (facade : SourceNativePendingClaimRuntimeFacade N)
    (runtime : LivingRuntimeState facade.base.process)
    (activated : ExactActivatedRootOccurrenceAt runtime)
    {face : facade.PendingFaceAt runtime}
    (_read : SourceInstalledPendingClaimFaceAt facade runtime face) :
    Type (u + 4) where
  private mk ::

def generate
    (facade : SourceNativePendingClaimRuntimeFacade N)
    (runtime : LivingRuntimeState facade.base.process)
    (activated : ExactActivatedRootOccurrenceAt runtime)
    {face : facade.PendingFaceAt runtime}
    (read : SourceInstalledPendingClaimFaceAt facade runtime face) :
    SourceExactPendingClaimBirthReceiptAt facade runtime activated read :=
  .mk

namespace SourceExactPendingClaimBirthReceiptAt

variable
  {facade : SourceNativePendingClaimRuntimeFacade N}
  {runtime : LivingRuntimeState facade.base.process}
  {activated : ExactActivatedRootOccurrenceAt runtime}
  {face : facade.PendingFaceAt runtime}
  {read : SourceInstalledPendingClaimFaceAt facade runtime face}

def package
    (_birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    SourceGeneratedPendingClaimPackage
      (facade.law runtime face read.active) :=
  read.package

def law
    (_birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) : DebtActivationLaw.{u} :=
  facade.law runtime face read.active

def initial
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) : birth.law.DebtState :=
  birth.package.initial

def sourceLedger
    (_birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) : CompleteLiveLedgerAt N :=
  ⟨runtime.current.root.toAuthoritativeRoot.toLedgerRoot.source.source
    |>.toRootSource.account.supportOf runtime.emittedOccurrence⟩

def targetLedger
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    CompleteLiveLedgerAt (ExtendedNetwork N birth.law) :=
  activeLedger birth.sourceLedger.support birth.initial

def debtEntry
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) : birth.targetLedger.Entry :=
  DebtActivationWorld.debtEntry birth.sourceLedger.support birth.initial

def oldTarget
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read)
    (entry : birth.sourceLedger.Entry) : birth.targetLedger.Entry :=
  oldEntry (law := birth.law) (state? := some birth.initial) entry

structure OldOriginAt
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read)
    (targetEntry : birth.targetLedger.Entry) : Type u where
  sourceEntry : birth.sourceLedger.Entry
  target_eq : targetEntry = birth.oldTarget sourceEntry

structure FreshOriginAt
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read)
    (targetEntry : birth.targetLedger.Entry) : Type (u + 4) where
  private mk ::
  target_eq : targetEntry = birth.debtEntry

inductive TargetOriginAt
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read)
    (targetEntry : birth.targetLedger.Entry) : Type (u + 4)
  | old (origin : OldOriginAt birth targetEntry)
  | fresh (origin : FreshOriginAt birth targetEntry)

def targetOrigin
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read)
    (targetEntry : birth.targetLedger.Entry) :
    TargetOriginAt birth targetEntry := by
  rcases targetEntry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl oldResponsibility =>
      exact .old ⟨⟨oldResponsibility, opened⟩, rfl⟩
  | inr debtId =>
      rcases opened with ⟨⟨debtId_eq⟩⟩
      subst debtId
      exact .fresh ⟨rfl⟩

def oldTargetOrigin
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read)
    (entry : birth.sourceLedger.Entry) :
    OldOriginAt birth (birth.oldTarget entry) :=
  ⟨entry, rfl⟩

def debtFresh
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    RootDebtFreshAt (ExtendedNetwork N birth.law)
      ⟨birth.sourceLedger.support, none⟩ birth.debtEntry :=
  ⟨by
    intro source sameDebt
    rcases source with ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => exact nomatch sameDebt.claim_eq
    | inr _ => exact nomatch opened⟩

theorem debtEntry_claim_eq_package
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    birth.debtEntry.claim = .inr birth.law.debtClaim := rfl

theorem debtEntry_budget_positive
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    0 < birth.debtEntry.progressBudget :=
  birth.package.initialBudget_positive

theorem target_anchor_eq_source
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    (ExtendedNetwork N birth.law).anchorAt birth.targetLedger.support =
      N.anchorAt birth.sourceLedger.support := rfl

theorem target_incidence_eq_source
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    (ExtendedNetwork N birth.law).incidenceAt birth.targetLedger.support =
      N.incidenceAt birth.sourceLedger.support := rfl

theorem target_lineage_eq_source
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    (ExtendedNetwork N birth.law).lineageAt birth.targetLedger.support =
      N.lineageAt birth.sourceLedger.support := rfl

theorem activated_eq_tick
    (_birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) : activated = runtime.tick :=
  activated.eq_tick

theorem face_factorizes
    (_birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) :
    facade.base.process.toAnswerNextCausalWorld.emitted
        (ULift.up runtime.state) = ULift.up runtime.tick.generated ∧
      runtime.tick.generated.occurrence = runtime.emittedOccurrence ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) :=
  ⟨rfl, rfl, runtime.tick.generated.wholeLedgerWriteBack_eq⟩

def GeneratedNextAt
    (_birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) : Type := PEmpty

end SourceExactPendingClaimBirthReceiptAt

end


end PendingClaimBirth
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
