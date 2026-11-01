import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Audit.SourceGeneratedMotherLawAudit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Failure

/-!
# M13 actual mother-law breaking occurrence

The fixture consumes the existing M9 joint root and its already installed
failure coordinate.  Its sole old law has a genuine deletion near miss while
the whole old theory has an actual expressibility failure.  The near miss is
diagnostic; only the same-occurrence installed failure face plus causal row
authority opens the rooted U8 gate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M13MotherLawBreakingRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Theory.Audit
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure

noncomputable section

abbrev OldTheory := RootInquiryU8CompletionRegression.oldTheory
abbrev Root := jointRoot.toAuthoritativeRoot

/-- Occurrence-local diagnostic compiler.  Deleting the one old law realizes
the obstruction, so the selected law is a genuine single-law near miss. -/
def deletionAuditSource : LawDeletionAuditSourceAt
    OldTheory.inventory RootInquiryU8CompletionRegression.obstruction where
  OccurrenceAt := fun _ => Unit
  emit := fun _ => ()
  event_eq_emit := by intros; rfl
  compileAudit := fun _ _ => .nearMiss ()

/-- Source-owned contract.  It defines a classifier and compiler for every
actual root occurrence but stores no failure, falsifier, revised theory, or
future audit result. -/
def contract : SourceOwnedMotherLawContractAt Root OldTheory where
  lawSurface_eq := rfl
  ScopeAt := fun _ {_current} _occurrence _entry => Unit
  BreakingActiveAt := fun _law {_current} _occurrence => Unit
  BreakingInactiveAt := fun _law {_current} _occurrence => PEmpty
  classify := fun _law {_current} _occurrence => .inl ()
  scopeEntryAt := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact entry
  scopeReceiptAt := fun _active => ()
  obstructionAt := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact RootInquiryU8CompletionRegression.obstruction
  obstructionClaim_eq_scopeClaim := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => rfl
  deletionAuditSourceAt := by
    intro law current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact deletionAuditSource

def active : contract.BreakingActiveAt ()
    (Root.emitted jointVisit.current) := ()

theorem classified :
    contract.classify () (Root.emitted jointVisit.current) = .inl active :=
  rfl

/-- Exact classified law audit and installed failure face at one root visit. -/
def audit : SourceGeneratedMotherLawAuditAt contract () active classified
    failureFace rfl :=
  SourceGeneratedMotherLawAuditAt.generate contract () active classified
    failureFace rfl

@[simp] theorem selected_law_is_exact_old_law : audit.auditedLaw = () :=
  rfl

@[simp] theorem deletion_audit_is_nearMiss :
    audit.deletionAudit = LawDeletionAuditAt.nearMiss () :=
  rfl

@[simp] theorem audit_failure_face_is_installed_face :
    audit.failureFace = failureFace :=
  rfl

theorem audit_scope_is_failure_row :
    audit.scopedEntry = audit.failureFace.rootEntry :=
  audit.scopedEntry_eq_failureRow

set_option linter.defProp false in
def failure_face_factorizes := audit.failureFaceFactorization

/-- Causal authority and successor are supplied by the same existing M9 row;
the diagnostic audit does not manufacture them. -/
def u8Gate : SourceGeneratedMotherLawU8GateAt audit
    authority.toAuthoritativeAuthority successor :=
  SourceGeneratedMotherLawU8GateAt.generate audit
    authority.toAuthoritativeAuthority successor

@[simp] theorem rooted_is_existing_joint_rooted :
    u8Gate.rooted = M9ProofCarryingRenewalU8Failure.rooted :=
  rfl

@[simp] theorem minimalCoface_is_existing_joint_coface :
    u8Gate.minimalCoface = M9ProofCarryingRenewalU8Failure.coface :=
  rfl

/-- The diagnostic result alone has no producer mouth for the U8 gate. -/
theorem nearMiss_alone_cannot_open_U8 : True := by
  fail_if_success
    exact SourceGeneratedMotherLawU8GateAt.generate audit.deletionAudit
  trivial

/-- A bare expressibility failure likewise has no producer mouth for this
same-occurrence mother-law gate. -/
theorem bare_failure_cannot_open_motherLaw_U8 : True := by
  fail_if_success
    exact SourceGeneratedMotherLawU8GateAt.generate
      RootInquiryU8CompletionRegression.failure
  trivial

end
end M13MotherLawBreakingRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M13MotherLawBreakingRegression.audit
#print axioms SaturationMonoid.ProcessGame.Society.M13MotherLawBreakingRegression.failure_face_factorizes
#print axioms SaturationMonoid.ProcessGame.Society.M13MotherLawBreakingRegression.u8Gate
#print axioms SaturationMonoid.ProcessGame.Society.M13MotherLawBreakingRegression.minimalCoface_is_existing_joint_coface
