import H0mework.Foundation.Semantics.TheoryEvolution
import H0mework.Versions.R2.Foundation.Inquiry.MinimalCoface

/-!
# Source-generated mother-law audit

A mother-law contract is indexed by an existing authoritative root and its
existing theory surface.  It declares only source laws: exact scope,
occurrence-local breaking classifiers, and an occurrence-local deletion-audit
compiler.  It contains no breaking witness, falsifier, expressibility
failure, revised theory, coface, or future audit table.

An authoritative audit is generated only when the fixed classifier selects
an active branch at the root's exact emitted occurrence and that same
occurrence already carries an installed expressibility-failure face.  The
per-law deletion audit remains a diagnostic readout.  Neither its `nearMiss`
nor its `unresolved` constructor can replace the installed failure face,
causal-entry authority, or successor required by the existing U7/U8 gate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Theory
namespace Audit

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface

universe u

noncomputable section

variable {N : WorldRelationNetwork.{u}}
variable {V : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeAuthoritativeRootClosure N V}
variable {oldTheory : TheoryState N}

/-- Source contract for auditing arbitrary laws of the root's current theory.

`BreakingActiveAt` and `BreakingInactiveAt` are classifier fibres, not stored
outcomes.  A law, scoped root responsibility, obstruction, and audit compiler
can only be read after an actual active classifier witness has been emitted. -/
structure SourceOwnedMotherLawContractAt
    (root : SourceNativeAuthoritativeRootClosure N V)
    (oldTheory : TheoryState N) : Type (u + 3) where
  lawSurface_eq : oldTheory = root.source.lawSurface
  ScopeAt : (law : oldTheory.inventory.Law) →
    {current : V.Current} →
    (occurrence : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current) →
    OpenResponsibilityAt N
      (root.toLedgerRoot.source.source.toRootSource.account.supportOf
        occurrence) → Type u
  BreakingActiveAt : (law : oldTheory.inventory.Law) →
    {current : V.Current} →
    root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
      Type u
  BreakingInactiveAt : (law : oldTheory.inventory.Law) →
    {current : V.Current} →
    root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
      Type u
  classify : (law : oldTheory.inventory.Law) → {current : V.Current} →
    (occurrence : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current) →
      BreakingActiveAt law occurrence ⊕ BreakingInactiveAt law occurrence
  scopeEntryAt : {law : oldTheory.inventory.Law} → {current : V.Current} →
    {occurrence : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current} → BreakingActiveAt law occurrence →
      OpenResponsibilityAt N
        (root.toLedgerRoot.source.source.toRootSource.account.supportOf
          occurrence)
  scopeReceiptAt : {law : oldTheory.inventory.Law} → {current : V.Current} →
    {occurrence : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current} → (active : BreakingActiveAt law occurrence) →
      ScopeAt law occurrence (scopeEntryAt active)
  obstructionAt : {law : oldTheory.inventory.Law} → {current : V.Current} →
    {occurrence : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current} → (active : BreakingActiveAt law occurrence) →
      N.ObstructionAt
        (root.toLedgerRoot.source.source.toRootSource.account.supportOf
          occurrence)
  obstructionClaim_eq_scopeClaim : {law : oldTheory.inventory.Law} →
    {current : V.Current} →
    {occurrence : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current} → (active : BreakingActiveAt law occurrence) →
      N.obstructionClaim (obstructionAt active) = (scopeEntryAt active).claim
  deletionAuditSourceAt : {law : oldTheory.inventory.Law} →
    {current : V.Current} →
    {occurrence : root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current} → (active : BreakingActiveAt law occurrence) →
      LawDeletionAuditSourceAt oldTheory.inventory (obstructionAt active)

namespace SourceOwnedMotherLawContractAt

variable (contract : SourceOwnedMotherLawContractAt root oldTheory)
variable {current : V.Current}
variable {occurrence :
  root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current}
variable (law : oldTheory.inventory.Law)
variable (active : contract.BreakingActiveAt law occurrence)

/-- Exact root claim-bearing responsibility selected as the law's scope. -/
def scopedEntry : OpenResponsibilityAt N
    (root.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence) :=
  contract.scopeEntryAt active

/-- Exact scope receipt generated by the active classifier branch. -/
def scopeReceipt :
    contract.ScopeAt law occurrence
      (contract.scopedEntry law active) :=
  contract.scopeReceiptAt active

/-- Exact obstruction emitted for the selected law at this occurrence. -/
def obstruction : N.ObstructionAt
    (root.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence) :=
  contract.obstructionAt active

/-- The breaking obstruction is the claim carried by the scoped root row. -/
theorem obstructionClaim_eq_scopedClaim :
    N.obstructionClaim (contract.obstruction law active) =
      (contract.scopedEntry law active).claim :=
  contract.obstructionClaim_eq_scopeClaim (law := law) active

/-- Occurrence-local deletion-audit compiler for this selected law. -/
def deletionAuditSource :
    LawDeletionAuditSourceAt oldTheory.inventory
      (contract.obstruction law active) :=
  contract.deletionAuditSourceAt active

/-- Canonical per-law diagnostic occurrence.  This token alone has no U8
authority. -/
def generatedDeletionAudit :
    GeneratedLawDeletionAuditAt (contract.deletionAuditSource law active)
      law :=
  (contract.deletionAuditSource law active).generated
    law

/-- Diagnostic result recomputed from the exact per-law audit occurrence. -/
def deletionAudit :
    LawDeletionAuditAt oldTheory.inventory (contract.obstruction law active)
      law :=
  (contract.generatedDeletionAudit law active).audit

end SourceOwnedMotherLawContractAt

/-! ## Same-occurrence authoritative activation -/

variable {contract : SourceOwnedMotherLawContractAt root oldTheory}
variable {visit : SourceNativeTemporalVisitAt root.toLedgerRoot}
variable {law : oldTheory.inventory.Law}
variable {active : contract.BreakingActiveAt law
  (root.emitted visit.current)}
variable {classified : contract.classify law (root.emitted visit.current) =
  .inl active}
variable {U7 : U7ProducerCalculus N}
variable {failure : ActualExpressibilityFailure oldTheory
  (contract.obstruction law active)}
variable {face : SourceNativeRootExpressibilityFailureFaceAt
  root visit (U7 := U7) failure}
variable {scopeEntry_eq : contract.scopedEntry law active = face.rootEntry}

/-- Exact mother-law audit at one already generated root occurrence.

The empty private constructor stores none of the active data.  Its indices
retain the classifier branch, exact per-law scope, installed failure face, and
the commuting equality between the scoped responsibility and the failure row. -/
structure SourceGeneratedMotherLawAuditAt
    (contract : SourceOwnedMotherLawContractAt root oldTheory)
    {visit : SourceNativeTemporalVisitAt root.toLedgerRoot}
    (law : oldTheory.inventory.Law)
    (active : contract.BreakingActiveAt law (root.emitted visit.current))
    (_classified : contract.classify law (root.emitted visit.current) = .inl active)
    {U7 : U7ProducerCalculus N}
    {failure : ActualExpressibilityFailure oldTheory
      (contract.obstruction law active)}
    (face : SourceNativeRootExpressibilityFailureFaceAt
      root visit (U7 := U7) failure)
    (_scopeEntry_eq : contract.scopedEntry law active = face.rootEntry) :
    Type (u + 3) where
  private mk ::

namespace SourceGeneratedMotherLawAuditAt

/-- Sole authoritative audit producer.  The caller supplies only exact
same-occurrence commuting data; it cannot submit an audit outcome or U8
branch. -/
def generate
    (contract : SourceOwnedMotherLawContractAt root oldTheory)
    {visit : SourceNativeTemporalVisitAt root.toLedgerRoot}
    (law : oldTheory.inventory.Law)
    (active : contract.BreakingActiveAt law (root.emitted visit.current))
    (classified : contract.classify law (root.emitted visit.current) = .inl active)
    {U7 : U7ProducerCalculus N}
    {failure : ActualExpressibilityFailure oldTheory
      (contract.obstruction law active)}
    (face : SourceNativeRootExpressibilityFailureFaceAt
      root visit (U7 := U7) failure)
    (scopeEntry_eq : contract.scopedEntry law active = face.rootEntry) :
    SourceGeneratedMotherLawAuditAt contract law active classified face
      scopeEntry_eq :=
  ⟨⟩

variable (audit : SourceGeneratedMotherLawAuditAt
  contract law active classified face scopeEntry_eq)

theorem eq_generate : audit =
    generate contract law active classified face scopeEntry_eq := by
  cases audit
  rfl

/-- Exact source-emitted root occurrence carrying both the classified law and
the installed failure face. -/
def rootOccurrence
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) := by
  cases audit
  exact root.emitted visit.current

/-- The exact source classifier selected this active branch at the same root
occurrence. -/
theorem classifier_eq_active
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) :
    contract.classify law audit.rootOccurrence = .inl active := by
  cases audit
  exact classified

/-- Arbitrary indexed law; no finite mother-law registry is introduced. -/
def auditedLaw
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) :
    oldTheory.inventory.Law := by
  cases audit
  exact law

@[simp] theorem auditedLaw_eq_index : audit.auditedLaw = law := by
  cases audit
  rfl

/-- Exact scoped root responsibility. -/
def scopedEntry
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) : OpenResponsibilityAt N
    (root.toLedgerRoot.source.source.toRootSource.account.supportOf
      audit.rootOccurrence) := by
  cases audit
  exact contract.scopedEntry law active

/-- Exact scope receipt generated by the source classifier. -/
def scopeReceipt
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) :
    contract.ScopeAt audit.auditedLaw audit.rootOccurrence audit.scopedEntry := by
  cases audit
  exact contract.scopeReceipt law active

/-- Exact obstruction generated at the classified occurrence. -/
def obstruction
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) : N.ObstructionAt
    (root.toLedgerRoot.source.source.toRootSource.account.supportOf
      audit.rootOccurrence) := by
  cases audit
  exact contract.obstruction law active

/-- The obstruction claim is exactly the claim of this audit's scoped root
responsibility. -/
theorem obstructionClaim_eq_scopedClaim :
    N.obstructionClaim audit.obstruction = audit.scopedEntry.claim :=
  SourceOwnedMotherLawContractAt.obstructionClaim_eq_scopedClaim
    contract law active

/-- Canonical per-law diagnostic occurrence. -/
def generatedDeletionAudit
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) :
    GeneratedLawDeletionAuditAt (contract.deletionAuditSource law active)
      audit.auditedLaw := by
  cases audit
  exact contract.generatedDeletionAudit law active

/-- `nearMiss` or `unresolved` remains only this diagnostic readout. -/
def deletionAudit
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) :
    LawDeletionAuditAt oldTheory.inventory audit.obstruction audit.auditedLaw := by
  cases audit
  exact (contract.generatedDeletionAudit law active).audit

/-- Exact installed expressibility-failure face.  This, not
`deletionAudit`, is the U8-facing boundary. -/
def failureFace
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) :
    SourceNativeRootExpressibilityFailureFaceAt
      root visit (U7 := U7) failure := by
  cases audit
  exact face

/-- The root law surface and the audited theory are literally the same epoch. -/
theorem lawSurface_eq_root
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq) :
    oldTheory = root.source.lawSurface := by
  cases audit
  exact SourceOwnedMotherLawContractAt.lawSurface_eq contract

/-- Exact scoped responsibility and installed failure row commute. -/
theorem scopedEntry_eq_failureRow :
    audit.scopedEntry = audit.failureFace.rootEntry := by
  cases audit
  exact scopeEntry_eq

/-- Consequently the failure row carries the exact scoped mother-law claim. -/
theorem obstructionClaim_eq_failureRowClaim :
    N.obstructionClaim audit.obstruction = audit.failureFace.rootEntry.claim := by
  rw [← audit.scopedEntry_eq_failureRow]
  exact audit.obstructionClaim_eq_scopedClaim

set_option linter.defProp false in
/-- Deletion-test witness: the failure authority is an installed coordinate
of this exact root occurrence. -/
def failureFaceFactorization :=
  audit.failureFace.installedAuthority_factorizes

end SourceGeneratedMotherLawAuditAt

/-! ## Explicit U8 gate separation -/

/-- A mother-law audit opens the existing rooted U8 route only after the same
failure row also carries causal-entry authority and its compiler-generated
successor.  The private seal contains no audit result, revised theory, coface,
or next current. -/
structure SourceGeneratedMotherLawU8GateAt
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq)
    (authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      root visit face.rootEntry)
    (successor : CausalEntrySuccessorAt root.toLedgerRoot visit
      face.rootEntry) : Type (u + 10) where
  private mk ::

namespace SourceGeneratedMotherLawU8GateAt

def generate
    (audit : SourceGeneratedMotherLawAuditAt
      contract law active classified face scopeEntry_eq)
    (authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      root visit face.rootEntry)
    (successor : CausalEntrySuccessorAt root.toLedgerRoot visit
      face.rootEntry) :
    SourceGeneratedMotherLawU8GateAt audit authority successor :=
  ⟨⟩

variable {audit : SourceGeneratedMotherLawAuditAt
  contract law active classified face scopeEntry_eq}
variable {authority : SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
  root visit face.rootEntry}
variable {successor : CausalEntrySuccessorAt root.toLedgerRoot visit
  face.rootEntry}
variable (gate : SourceGeneratedMotherLawU8GateAt
  audit authority successor)

/-- Existing rooted-failure producer.  No deletion-audit constructor enters
this term. -/
def rooted
    (gate : SourceGeneratedMotherLawU8GateAt
      audit authority successor) :
    RootedActualExpressibilityFailureAt root visit U7 failure := by
  cases gate
  exact RootedActualExpressibilityFailureAt.ofRootFailureFace
    face authority successor

/-- Canonical minimal coface generated from the rooted failure. -/
def minimalCoface : GeneratedMinimalCofaceAt gate.rooted :=
  root_obstruction_generates_minimal_coface gate.rooted

/-- Exact source-generated attaching direction. -/
def attachingDirection : SourceGeneratedAttachingDirectionAt gate.rooted :=
  gate.minimalCoface.attachingDirection

end SourceGeneratedMotherLawU8GateAt

end
end Audit
end Theory
end Society
end ProcessGame
end SaturationMonoid
