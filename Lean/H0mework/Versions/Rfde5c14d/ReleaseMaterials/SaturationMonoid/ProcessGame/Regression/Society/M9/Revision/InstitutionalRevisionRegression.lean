import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalRevision
import H0mework.Versions.R2.Checks.Runtime.Inquiry
import H0mework.Checks.Runtime.RootNativeLedgerCompilerRegression

/-!
# M9 canonical institutional revision regression

One canonical inquiry runtime generates both sides of the institutional
dichotomy at different exact ticks.  Depth zero is the existing U8 macro and
therefore generates revolution, first write, two-row revised answer-and-next,
and the heterogeneous revised current.  Depth one runs inside that revised
root and generates an ordinary same-law reform.  Neither branch tag is
supplied by this fixture.

The independent authoritative-terminal control remains rupture: it has no
same-ledger successor, no installed renewal, and no expressibility failure
from which U8 could be generated.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9InstitutionalRevisionRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Revision Renewal
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.CanonicalInquiryRuntimeRegression
open ConstructiveRoot.RootInquiryU8CompletionRegression

/-! ## One source runtime generates both institutional phases -/

def revolutionaryDichotomy : SourceGeneratedInstitutionalDichotomyAt
    CanonicalInquiryRuntimeRegression.runtime 0 :=
  SourceGeneratedInstitutionalDichotomyAt.generate
    CanonicalInquiryRuntimeRegression.runtime 0

@[simp] theorem revolutionary_kind_is_generated :
    revolutionaryDichotomy.revisionKind = .revolution :=
  rfl

def revolutionaryTick : SourceGeneratedRevolutionaryTickAt
    CanonicalInquiryRuntimeRegression.runtime 0 :=
  revolutionaryDichotomy.revolutionaryTick?.get (by rfl)

@[simp] theorem revolutionary_tick_is_exact_runtime_core :
    HEq revolutionaryTick.core generatedRevisionCore :=
  HEq.rfl

theorem revolutionary_runtime_resumes_exact_core :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      revolutionaryTick.core CanonicalInquiryRuntimeRegression.runtime 0 :=
  revolutionaryTick.resumption

def revolutionaryFirstWrite := revolutionaryTick.firstWrite

def revolutionaryTwoRowAnswerAndNext :=
  revolutionaryTick.twoRowAnswerAndNext

theorem revolutionary_rows_share_generated_next :
    revolutionaryTick.oldRowAnswerAndNext.nextCurrent =
      revolutionaryTick.newRowAnswerAndNext.nextCurrent :=
  revolutionaryTick.twoRows_share_generatedNext

@[simp] theorem revolutionary_actual_next_is_revised_next :
    revolutionaryDichotomy.actualNext = revolutionaryTick.revisedNext :=
  rfl

def reformDichotomy : SourceGeneratedInstitutionalDichotomyAt
    CanonicalInquiryRuntimeRegression.runtime 1 :=
  SourceGeneratedInstitutionalDichotomyAt.generate
    CanonicalInquiryRuntimeRegression.runtime 1

@[simp] theorem reform_kind_is_generated :
    reformDichotomy.revisionKind = .reform :=
  rfl

@[simp] theorem reform_has_no_revolutionary_core :
    reformDichotomy.revolutionaryTick? = none :=
  rfl

/-- The reform is reached through one source-generated macro-runtime step;
the production theorem remains polymorphic over every runtime and depth. -/
def reformFinitePrefix :
    SourceNativeInquiryRuntime.HistoryAt
      CanonicalInquiryRuntimeRegression.runtime 1
      CanonicalInquiryRuntimeRegression.runtime.initialState :=
  reformDichotomy.finitePrefix

theorem reform_tick_is_revised_root_direct_answer :
    reformDichotomy.resolution =
      .directlyAnswered (revisedAnswerFaceAt 2)
        (revisedAnswerConsumerAt 2) :=
  secondTick_is_revised_root_answer

set_option linter.defProp false in
/-- The ordinary branch resumes inside the exact living root selected by the
runtime compiler; it does not return to the pre-U8 root or a sibling law. -/
def reform_next_preserves_generated_living_law :=
  reformDichotomy.tick.next_preservesGeneratedLivingLaw

/-! ## Source-owned rupture -/

open ResponsibilityLifecycle.LivingLawEvolution.SourceNativeLedgerCompilerRegression

abbrev RuptureN :=
  ResponsibilityLifecycle.LivingLawEvolution.SourceNativeLedgerCompilerRegression.N
abbrev RuptureV :=
  ResponsibilityLifecycle.LivingLawEvolution.SourceNativeLedgerCompilerRegression.TerminalV

def ruptureProjectionLaw : SourceNativeProjectionLaw
    terminalRestructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => PUnit
  project := fun _ {_} _ _ => PUnit.unit

def ruptureAuthoritySource : SourceNativeAuthoritySource RuptureN RuptureV where
  restructuringSource := terminalRestructuringSource
  eventInventoryAdmission :=
    .reflOfNoActualSuccessor terminalRestructuringSource (fun _ =>
      ⟨fun outgoing => by
        rcases outgoing with ⟨occurrence, successor⟩
        rcases occurrence with ⟨support, event⟩
        cases event
        exact nomatch successor⟩)
  lawSurface := .rootSemantic RuptureN
  projectionLaw := ruptureProjectionLaw

def ruptureWorld : SourceNativeAuthoritativeRootClosure RuptureN RuptureV where
  source := ruptureAuthoritySource
  emitted := terminalEmitted
  compiler_commutes := fun _ => True.intro

def ruptureVisit : SourceNativeTemporalVisitAt ruptureWorld.toLedgerRoot :=
  .finite ruptureWorld.toRoot.initialVisit

def ruptureTerminal : SourceFaithfulTerminalOccurrenceAt ruptureWorld.source
    (ruptureWorld.emitted ruptureVisit.current) where
  terminal := ()
  structural_eq := rfl
  ledgerEvolution := terminalLedgerEvolution
  generated_eq := rfl

def rupture : SourceOwnedInstitutionalRuptureAt
    (sourceEntry := falseEntry) ruptureTerminal :=
  SourceOwnedInstitutionalRuptureAt.generate ruptureTerminal

theorem rupture_disposes_existing_residual :
    (SourceOwnedInstitutionalRuptureAt.terminalReceipt rupture).receipt = () :=
  rfl

theorem rupture_has_no_root_installed_renewal :
    RootInstalledRenewalAt
      (ruptureWorld.toLedgerRoot.generatedAtTemporalVisit ruptureVisit)
      falseEntry → False :=
  SourceOwnedInstitutionalRuptureAt.noRootInstalledRenewal rupture

theorem rupture_root_semantic_has_no_expressibility_failure
    (exactObstruction : RuptureN.ObstructionAt false) :
    ActualExpressibilityFailure ruptureWorld.source.lawSurface
      exactObstruction → False := by
  intro impossible
  exact impossible.notExpressible.false
    ⟨RuptureN.obstructionClaim exactObstruction, rfl⟩

/-! ## Independent whole consumer -/

structure InstitutionalRevisionCertificate : Type 15 where
  revolution : SourceGeneratedInstitutionalDichotomyAt
    CanonicalInquiryRuntimeRegression.runtime 0
  revolutionKind : revolution.revisionKind = .revolution
  revolutionaryTick : SourceGeneratedRevolutionaryTickAt
    CanonicalInquiryRuntimeRegression.runtime 0
  runtimeResumption :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      revolutionaryTick.core CanonicalInquiryRuntimeRegression.runtime 0
  firstWrite :
    CanonicalFirstRootWriteAt
      (revolutionaryTick.core.revision.generate.newLivingRoot
        |>.toAuthoritativeRoot.toLedgerRoot)
  rowsSameNext :
    revolutionaryTick.oldRowAnswerAndNext.nextCurrent =
      revolutionaryTick.newRowAnswerAndNext.nextCurrent
  actualNextIsRevised : revolution.actualNext = revolutionaryTick.revisedNext
  reform : SourceGeneratedInstitutionalDichotomyAt
    CanonicalInquiryRuntimeRegression.runtime 1
  reformKind : reform.revisionKind = .reform
  reformNoRevolution : reform.revolutionaryTick? = none
  reformPrefix : SourceNativeInquiryRuntime.HistoryAt
    CanonicalInquiryRuntimeRegression.runtime 1
    CanonicalInquiryRuntimeRegression.runtime.initialState
  rupture : SourceOwnedInstitutionalRuptureAt
    (sourceEntry := falseEntry) ruptureTerminal
  ruptureNoReformRow : RootInstalledRenewalAt
    (ruptureWorld.toLedgerRoot.generatedAtTemporalVisit ruptureVisit)
    falseEntry → False
  ruptureNoU8Failure : ∀ exactObstruction : RuptureN.ObstructionAt false,
    ActualExpressibilityFailure ruptureWorld.source.lawSurface
      exactObstruction → False

def institutionalRevisionDirectConsumer : InstitutionalRevisionCertificate where
  revolution := revolutionaryDichotomy
  revolutionKind := revolutionary_kind_is_generated
  revolutionaryTick := revolutionaryTick
  runtimeResumption := revolutionary_runtime_resumes_exact_core
  firstWrite := revolutionaryFirstWrite
  rowsSameNext := revolutionary_rows_share_generated_next
  actualNextIsRevised := revolutionary_actual_next_is_revised_next
  reform := reformDichotomy
  reformKind := reform_kind_is_generated
  reformNoRevolution := reform_has_no_revolutionary_core
  reformPrefix := reformFinitePrefix
  rupture := rupture
  ruptureNoReformRow := rupture_has_no_root_installed_renewal
  ruptureNoU8Failure := rupture_root_semantic_has_no_expressibility_failure

end
end M9InstitutionalRevisionRegression
end Society
end ProcessGame
end SaturationMonoid
