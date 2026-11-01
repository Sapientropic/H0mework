import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Effect.TheoryFeedbackTrace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingLegislation

/-!
# Source-installed causal theory adoption

Causal theory adoption is a dependent face of one already-installed
proof-carrying renewal and one exact runtime splice.  The adopted theory is
definitionally the fixed root law surface.  Classification, policy, actual
effect, effect consumer, the domain's existing local consumer, observer
kernel, lifecycle and disposition are all read from the same pre-emitter
renewal payload and source-generated feedback trace.

No theory text, readout result, numeric value, revised theory, root, ledger or
next current is accepted from a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Theory
namespace Adoption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Observer Legislation
open Effect
open ConstructiveRoot.RootInquiryCompletion

universe u

variable {N : WorldRelationNetwork.{u}}
variable {RootV : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N RootV}
variable {oldTheory : TheoryState N}

variable {LocalSource LocalState Seed : Type u}
variable {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {SeedAt : LocalSource → LocalState → Seed → Prop}

variable {feedbackCompiler : SourceOwnedTheoryFeedbackCompilerAt
  oldTheory game Seed SeedAt}

variable {W : ResponsibilityLifecycle.Vocabulary.{u}}
variable {P : NativeResponsibilityProcess W}
variable {ObserverOccurrence Visible AuthorityResidual : Type u}
variable {observer :
  AuthorityObserver ObserverOccurrence Visible AuthorityResidual}

noncomputable section

/-! ## Pre-emitter local adoption restriction -/

/-- Zero-field local restriction generated for every exact source seed by the
fixed feedback compiler. -/
structure CausalTheoryAdoptionRestrictionAt
    (feedbackCompiler : SourceOwnedTheoryFeedbackCompilerAt
      oldTheory game Seed SeedAt)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) : Type u where
  private mk ::

/-- Sole local restriction producer. -/
def sourceGeneratedCausalTheoryAdoptionRestriction
    (feedbackCompiler : SourceOwnedTheoryFeedbackCompilerAt
      oldTheory game Seed SeedAt)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) :
    CausalTheoryAdoptionRestrictionAt feedbackCompiler seed :=
  ⟨⟩

namespace CausalTheoryAdoptionRestrictionAt

variable {seed : SourceSeed occurrenceOf Seed SeedAt game.source}
variable (restriction :
  CausalTheoryAdoptionRestrictionAt feedbackCompiler seed)

/-- Exact source-generated feedback trace fixed by the restriction indices. -/
def feedbackTrace :
    SourceGeneratedTheoryFeedbackTraceAt feedbackCompiler seed := by
  cases restriction
  exact SourceGeneratedTheoryFeedbackTraceAt.generate feedbackCompiler seed

def theoryState : TheoryState N :=
  restriction.feedbackTrace.theoryState

@[simp] theorem theoryState_eq_oldTheory :
    restriction.theoryState = oldTheory :=
  rfl

def exactSourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source :=
  restriction.feedbackTrace.exactSourceSeed

def classificationReadout : OccurrenceReadout
    (SourceSeed occurrenceOf Seed SeedAt game.source)
    feedbackCompiler.Classification :=
  restriction.feedbackTrace.classificationReadout

def policyReadout : OccurrencePolicy
    (SourceSeed occurrenceOf Seed SeedAt game.source)
    feedbackCompiler.PolicyDecision :=
  restriction.feedbackTrace.policyReadout

def actualEffect : feedbackCompiler.EffectAt restriction.exactSourceSeed :=
  restriction.feedbackTrace.actualEffect

def effectConsumer : feedbackCompiler.EffectConsumerAt
    restriction.exactSourceSeed restriction.actualEffect :=
  restriction.feedbackTrace.effectConsumer

end CausalTheoryAdoptionRestrictionAt

/-- Pre-emitter composite preserving the domain's existing local consumer
beside the source-generated causal-theory restriction.  Its private
constructor prevents an installed sibling consumer from being relabelled as
an adoption after emission. -/
structure CausalTheoryAdoptionConsumerAt
    (feedbackCompiler : SourceOwnedTheoryFeedbackCompilerAt
      oldTheory game Seed SeedAt)
    (ExistingLocalConsumerAt :
      SourceSeed occurrenceOf Seed SeedAt game.source → Type u)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) : Type u where
  private mk ::
  existingLocalConsumer : ExistingLocalConsumerAt seed
  adoptionRestriction : CausalTheoryAdoptionRestrictionAt feedbackCompiler seed

namespace CausalTheoryAdoptionConsumerAt

variable {ExistingLocalConsumerAt :
  SourceSeed occurrenceOf Seed SeedAt game.source → Type u}
variable {seed : SourceSeed occurrenceOf Seed SeedAt game.source}

/-- Sole composite producer.  The existing domain consumer is joined to the
automatically generated adoption restriction before the renewal is emitted. -/
def generate
    (feedbackCompiler : SourceOwnedTheoryFeedbackCompilerAt
      oldTheory game Seed SeedAt)
    (existingLocalConsumer : ExistingLocalConsumerAt seed) :
    CausalTheoryAdoptionConsumerAt
      feedbackCompiler ExistingLocalConsumerAt seed :=
  ⟨existingLocalConsumer,
    sourceGeneratedCausalTheoryAdoptionRestriction feedbackCompiler seed⟩

end CausalTheoryAdoptionConsumerAt

/-- Recognition wrapper joining an already-constructible proof-carrying
recognition to the final root law-surface equation.  The feedback compiler is
therefore built from `oldTheory` before the final root exists. -/
structure SourceNativeCausalTheoryAdoptionRecognitionAt
    (root : SourceNativeLivingRootClosure N RootV)
    (oldTheory : TheoryState N)
    (P : NativeResponsibilityProcess W)
    (observer : AuthorityObserver
      ObserverOccurrence Visible AuthorityResidual)
    (feedbackCompiler : SourceOwnedTheoryFeedbackCompilerAt
      oldTheory game Seed SeedAt)
    (ExistingLocalConsumerAt LocalLifecycleAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt game.source → Type u) : Type (u + 2) where
  proofCarrying : SourceNativeProofCarryingRenewalRecognitionAt root P observer
    (CausalTheoryAdoptionConsumerAt feedbackCompiler ExistingLocalConsumerAt)
    LocalLifecycleAt DispositionAt
  lawSurface_eq : oldTheory = root.source.base.lawSurface

variable {ExistingLocalConsumerAt LocalLifecycleAt DispositionAt :
  SourceSeed occurrenceOf Seed SeedAt game.source → Type u}
variable {recognition : SourceNativeCausalTheoryAdoptionRecognitionAt
  root oldTheory P observer feedbackCompiler ExistingLocalConsumerAt
    LocalLifecycleAt DispositionAt}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {installed : SourceInstalledRenewalAt recognition.proofCarrying visit}

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable {runtime : SourceNativeInquiryRuntime process}
variable {depth : Nat}
variable {splice : SourceInstalledRenewalRuntimeSpliceAt
  installed runtime depth}

/-! ## Installed adoption seal -/

/-- Zero-field seal over one exact installed renewal/runtime splice. -/
structure SourceInstalledCausallyAdoptedTheoryAt
    (installed : SourceInstalledRenewalAt recognition.proofCarrying visit)
    (runtime : SourceNativeInquiryRuntime process)
    (depth : Nat)
    (_splice : SourceInstalledRenewalRuntimeSpliceAt
      installed runtime depth) : Type (u + 14) where
  private mk ::

/-- Sole installed adoption producer. -/
def sourceInstalledCausalTheoryAdoption
    (installed : SourceInstalledRenewalAt recognition.proofCarrying visit)
    (runtime : SourceNativeInquiryRuntime process)
    (depth : Nat)
    (splice : SourceInstalledRenewalRuntimeSpliceAt
      installed runtime depth) :
    SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice :=
  ⟨⟩

namespace SourceInstalledCausallyAdoptedTheoryAt

variable (adoption : SourceInstalledCausallyAdoptedTheoryAt
  installed runtime depth splice)

/-- Exact proof-carrying restriction read from the pre-emitter payload. -/
def proofCarryingRestriction : ProofCarryingRenewalRestrictionAt
    P observer
      (CausalTheoryAdoptionConsumerAt feedbackCompiler ExistingLocalConsumerAt)
      LocalLifecycleAt installed.payload.sourceSeed := by
  cases adoption
  exact installed.payload.consumer

/-- Composite local consumer installed before emission. -/
def compositeConsumer : CausalTheoryAdoptionConsumerAt
    feedbackCompiler ExistingLocalConsumerAt installed.payload.sourceSeed :=
  adoption.proofCarryingRestriction.localConsumer

/-- The domain's original local consumer, preserved inside the pre-emitter
composite rather than reconstructed from the installed adoption. -/
def existingLocalConsumer :
    ExistingLocalConsumerAt installed.payload.sourceSeed :=
  adoption.compositeConsumer.existingLocalConsumer

/-- Exact local adoption restriction generated by the same payload. -/
def restriction : CausalTheoryAdoptionRestrictionAt
    feedbackCompiler installed.payload.sourceSeed :=
  adoption.compositeConsumer.adoptionRestriction

/-- Exact source-generated feedback trace. -/
def feedbackTrace : SourceGeneratedTheoryFeedbackTraceAt
    feedbackCompiler installed.payload.sourceSeed :=
  adoption.restriction.feedbackTrace

/-- Pre-uplift theory retained by the feedback compiler. -/
def compilerTheoryState : TheoryState N :=
  adoption.feedbackTrace.theoryState

/-- Adopted theory is read definitionally from the final root law surface. -/
def theoryState
    (_adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) : TheoryState N :=
  root.source.base.lawSurface

@[simp] theorem theoryState_eq_root_lawSurface :
    adoption.theoryState = root.source.base.lawSurface :=
  rfl

@[simp] theorem compilerTheoryState_eq_oldTheory :
    adoption.compilerTheoryState = oldTheory :=
  rfl

theorem compilerTheoryState_eq_adoptedTheory :
    adoption.compilerTheoryState = adoption.theoryState := by
  exact recognition.lawSurface_eq

def exactSourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source :=
  adoption.feedbackTrace.exactSourceSeed

@[simp] theorem exactSourceSeed_eq_payload :
    adoption.exactSourceSeed = installed.payload.sourceSeed :=
  rfl

def classificationReadout : OccurrenceReadout
    (SourceSeed occurrenceOf Seed SeedAt game.source)
      feedbackCompiler.Classification :=
  adoption.feedbackTrace.classificationReadout

@[simp] theorem classificationReadout_eq_compiler :
    adoption.classificationReadout = feedbackCompiler.classificationReadout :=
  rfl

def policyReadout : OccurrencePolicy
    (SourceSeed occurrenceOf Seed SeedAt game.source)
      feedbackCompiler.PolicyDecision :=
  adoption.feedbackTrace.policyReadout

@[simp] theorem policyReadout_eq_compiler :
    adoption.policyReadout = feedbackCompiler.policyReadout :=
  rfl

/-- Actual effect generated from this exact payload seed. -/
def actualEffect : feedbackCompiler.EffectAt adoption.exactSourceSeed :=
  adoption.feedbackTrace.actualEffect

/-- Dependent effect consumer generated with the actual effect. -/
def effectConsumer : feedbackCompiler.EffectConsumerAt
    adoption.exactSourceSeed adoption.actualEffect :=
  adoption.feedbackTrace.effectConsumer

/-- Existing observer from the proof-carrying recognition. -/
def authorityObserver
    (_adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) : AuthorityObserver
    ObserverOccurrence Visible AuthorityResidual :=
  observer

/-- Canonical existing authority kernel generated by the same payload. -/
def observerKernel : AuthorityKernelPair observer :=
  adoption.proofCarryingRestriction.observerKernel

/-- Exact lifecycle face generated in the same pre-emitter payload. -/
def localLifecycle : LocalLifecycleAt installed.payload.sourceSeed :=
  adoption.proofCarryingRestriction.localLifecycle

/-- Exact responsibility disposition generated beside the local consumer. -/
def responsibilityDisposition
    (_adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) :
    DispositionAt installed.payload.sourceSeed :=
  installed.payload.disposition

/-! ## Root/runtime splice mouths -/

theorem sameRoot
    (_adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt runtime depth).1.state.base.root
    root :=
  SourceInstalledRenewalRuntimeSpliceAt.sameRoot splice

theorem sameVisit
    (_adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt runtime depth).1.state.base.visit
    visit :=
  SourceInstalledRenewalRuntimeSpliceAt.sameVisit splice

theorem sameRow
    (_adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt runtime depth).1.state.base.entryAt
      (sourceGeneratedRuntimeInquiryCoordinateAt runtime depth).2)
    installed.payload.sourceEntry :=
  SourceInstalledRenewalRuntimeSpliceAt.sameRow splice

theorem sameOccurrence
    (_adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt runtime depth).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt runtime depth).1.state.base.visit)
    (root.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt visit) :=
  SourceInstalledRenewalRuntimeSpliceAt.sameOccurrence splice

/-- Independent root responsibility consumer at the exact installed row. -/
def rootConsumer :
    RenewalResponsibilityConsumerAt installed.operationalAuthority := by
  cases adoption
  exact installed.rootResponsibilityConsumer

/-- Whole-ledger write-back at the exact root occurrence. -/
def wholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence := by
  cases adoption
  exact (root.toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit visit).wholeLedgerWriteBack

/-- Existing root-generated next. -/
def generatedNext : SourceNativeAuthoritativeRootCurrentAt N := by
  cases adoption
  exact root.generatedNextCurrentAt visit

@[simp] theorem generatedNext_eq_root :
    adoption.generatedNext = root.generatedNextCurrentAt visit :=
  rfl

theorem rootAnswerAndNext_factorizes
    (adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) :
    installed.RootAnswerAndNextFactorizes := by
  cases adoption
  exact installed.rootAnswerAndNext_factorizes

/-- Every authority-bearing effect has its generated dependent consumer. -/
theorem actualEffect_has_consumer :
    Nonempty (feedbackCompiler.EffectConsumerAt
      adoption.exactSourceSeed adoption.actualEffect) :=
  ⟨adoption.effectConsumer⟩

end SourceInstalledCausallyAdoptedTheoryAt

/-! ## Independent consumer -/

/-- Independent adoption consumer.  It carries exact seals, effect authority
and root provenance, but no classification/policy result or numeric field. -/
structure CausalTheoryAdoptionIndependentConsumerAt
    (adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) : Type (u + 15) where
  private mk ::
  feedbackTrace : SourceGeneratedTheoryFeedbackTraceAt
    feedbackCompiler installed.payload.sourceSeed
  feedbackTrace_eq : feedbackTrace = adoption.feedbackTrace
  existingLocalConsumer : ExistingLocalConsumerAt installed.payload.sourceSeed
  theoryState : TheoryState N
  theoryState_eq : theoryState = root.source.base.lawSurface
  classificationReadout : OccurrenceReadout
    (SourceSeed occurrenceOf Seed SeedAt game.source)
      feedbackCompiler.Classification
  policyReadout : OccurrencePolicy
    (SourceSeed occurrenceOf Seed SeedAt game.source)
      feedbackCompiler.PolicyDecision
  actualEffect : feedbackCompiler.EffectAt installed.payload.sourceSeed
  effectConsumer : feedbackCompiler.EffectConsumerAt
    installed.payload.sourceSeed actualEffect
  observerKernel : AuthorityKernelPair observer
  localLifecycle : LocalLifecycleAt installed.payload.sourceSeed
  responsibilityDisposition : DispositionAt installed.payload.sourceSeed
  rootConsumer : RenewalResponsibilityConsumerAt installed.operationalAuthority
  wholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence
  generatedNext : SourceNativeAuthoritativeRootCurrentAt N
  generatedNext_eq : generatedNext = root.generatedNextCurrentAt visit
  rootFactorization : installed.RootAnswerAndNextFactorizes

/-- Sole independent consumer producer. -/
def SourceInstalledCausallyAdoptedTheoryAt.independentConsumer
    (adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice) :
    CausalTheoryAdoptionIndependentConsumerAt adoption where
  feedbackTrace := adoption.feedbackTrace
  feedbackTrace_eq := rfl
  existingLocalConsumer := adoption.existingLocalConsumer
  theoryState := adoption.theoryState
  theoryState_eq := adoption.theoryState_eq_root_lawSurface
  classificationReadout := adoption.classificationReadout
  policyReadout := adoption.policyReadout
  actualEffect := adoption.actualEffect
  effectConsumer := adoption.effectConsumer
  observerKernel := adoption.observerKernel
  localLifecycle := adoption.localLifecycle
  responsibilityDisposition := adoption.responsibilityDisposition
  rootConsumer := adoption.rootConsumer
  wholeLedgerWriteBack := adoption.wholeLedgerWriteBack
  generatedNext := adoption.generatedNext
  generatedNext_eq := rfl
  rootFactorization := adoption.rootAnswerAndNext_factorizes

/-! ## Type-level negative readouts -/

/-- A different bare theory cannot replace the fixed root law surface. -/
theorem bareTheory_ne_adoptedTheory
    (adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice)
    (bareTheory : TheoryState N)
    (different : bareTheory ≠ root.source.base.lawSurface) :
    bareTheory ≠ adoption.theoryState := by
  rw [adoption.theoryState_eq_root_lawSurface]
  exact different

/-- A different bare classification readout cannot replace the source-owned
readout installed through the feedback compiler. -/
theorem bareReadout_ne_adoptionReadout
    (adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice)
    (bareReadout : OccurrenceReadout
      (SourceSeed occurrenceOf Seed SeedAt game.source)
        feedbackCompiler.Classification)
    (different : bareReadout ≠ feedbackCompiler.classificationReadout) :
    bareReadout ≠ adoption.classificationReadout := by
  rw [adoption.classificationReadout_eq_compiler]
  exact different

/-- A bare effect whose dependent consumer fibre is empty cannot equal the
source-generated actual effect carried by adoption authority. -/
theorem bareEffect_withoutConsumer_ne_actualEffect
    (adoption : SourceInstalledCausallyAdoptedTheoryAt
      installed runtime depth splice)
    (bare : BareTheoryEffectAt
      feedbackCompiler installed.payload.sourceSeed)
    (noConsumer : IsEmpty
      (feedbackCompiler.EffectConsumerAt installed.payload.sourceSeed
        bare.effect)) :
    bare.effect ≠ adoption.actualEffect := by
  intro equality
  apply noConsumer.false
  rw [equality]
  exact adoption.effectConsumer

end
end Adoption
end Theory
end Society
end ProcessGame
end SaturationMonoid
