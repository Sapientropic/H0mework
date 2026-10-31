import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization
import H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection

/-!
# Source-generated theory feedback trace

A feedback trace is generated from one exact `ProcessGame.SourceSeed` under a
fixed pre-uplift `TheoryState`.  A source-owned compiler supplies occurrence-indexed
classification and policy readouts, an actual dependent effect, and the
effect's dependent consumer together.

The generated trace is a zero-field seal.  It stores no numeric value,
classification result, policy result, completed decision, revised theory or
next current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Theory
namespace Effect

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer

universe u

variable {N : WorldRelationNetwork.{u}}
variable {oldTheory : TheoryState N}

variable {LocalSource LocalState Seed : Type u}
variable {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {SeedAt : LocalSource → LocalState → Seed → Prop}

noncomputable section

/-- One fixed source law for theory feedback at exact local source seeds. -/
structure SourceOwnedTheoryFeedbackCompilerAt
    (oldTheory : TheoryState N)
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type u)
    (SeedAt : LocalSource → LocalState → Seed → Prop) : Type (u + 1) where
  Classification : Type u
  PolicyDecision : Type u
  classificationReadout : OccurrenceReadout
    (SourceSeed occurrenceOf Seed SeedAt game.source) Classification
  policyReadout : OccurrencePolicy
    (SourceSeed occurrenceOf Seed SeedAt game.source) PolicyDecision
  EffectAt : SourceSeed occurrenceOf Seed SeedAt game.source → Type u
  actualEffectAt : (seed : SourceSeed occurrenceOf Seed SeedAt game.source) →
    EffectAt seed
  EffectConsumerAt : (seed : SourceSeed occurrenceOf Seed SeedAt game.source) →
    EffectAt seed → Type u
  consumeEffect : (seed : SourceSeed occurrenceOf Seed SeedAt game.source) →
    EffectConsumerAt seed (actualEffectAt seed)

namespace SourceOwnedTheoryFeedbackCompilerAt

variable (compiler : SourceOwnedTheoryFeedbackCompilerAt
  oldTheory game Seed SeedAt)

/-- The only theory state available to this compiler. -/
def theoryState
    (_compiler : SourceOwnedTheoryFeedbackCompilerAt
      oldTheory game Seed SeedAt) : TheoryState N :=
  oldTheory

@[simp] theorem theoryState_eq_oldTheory :
    compiler.theoryState = oldTheory :=
  rfl

end SourceOwnedTheoryFeedbackCompilerAt

/-- Zero-field feedback occurrence generated at one exact source seed. -/
inductive SourceGeneratedTheoryFeedbackTraceAt
    (compiler : SourceOwnedTheoryFeedbackCompilerAt oldTheory game Seed SeedAt)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) : Type (u + 1) where
  | private generated

namespace SourceGeneratedTheoryFeedbackTraceAt

/-- Sole feedback-trace producer. -/
def generate
    (compiler : SourceOwnedTheoryFeedbackCompilerAt oldTheory game Seed SeedAt)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) :
    SourceGeneratedTheoryFeedbackTraceAt compiler seed :=
  .generated

variable {compiler : SourceOwnedTheoryFeedbackCompilerAt
  oldTheory game Seed SeedAt}
variable {seed : SourceSeed occurrenceOf Seed SeedAt game.source}
variable (trace : SourceGeneratedTheoryFeedbackTraceAt compiler seed)

theorem eq_generate : trace = generate compiler seed := by
  cases trace
  rfl

/-- Exact local source seed retained as a dependent index. -/
def exactSourceSeed
    (_trace : SourceGeneratedTheoryFeedbackTraceAt compiler seed) :
    SourceSeed occurrenceOf Seed SeedAt game.source :=
  seed

/-- Exact occurrence provenance already carried by the source seed. -/
theorem sourceSeed_incidence :
    ∃ state ∈ game.occurrence.trace,
      SeedAt game.source state trace.exactSourceSeed.1 :=
  trace.exactSourceSeed.2

/-- Theory is read directly from the fixed pre-uplift theory state. -/
def theoryState
    (_trace : SourceGeneratedTheoryFeedbackTraceAt compiler seed) :
    TheoryState N :=
  oldTheory

@[simp] theorem theoryState_eq_oldTheory :
    trace.theoryState = oldTheory :=
  rfl

/-- Full source-generated classification readout. -/
def classificationReadout
    (_trace : SourceGeneratedTheoryFeedbackTraceAt compiler seed) :
    OccurrenceReadout
      (SourceSeed occurrenceOf Seed SeedAt game.source)
      compiler.Classification :=
  compiler.classificationReadout

/-- Classification at this exact source occurrence. -/
def classification : compiler.Classification :=
  trace.classificationReadout.read trace.exactSourceSeed

/-- Full source-generated policy readout. -/
def policyReadout
    (_trace : SourceGeneratedTheoryFeedbackTraceAt compiler seed) :
    OccurrencePolicy
      (SourceSeed occurrenceOf Seed SeedAt game.source)
      compiler.PolicyDecision :=
  compiler.policyReadout

/-- Policy decision at this exact source occurrence. -/
def policyDecision : compiler.PolicyDecision :=
  trace.policyReadout.read trace.exactSourceSeed

/-- Actual effect generated at the same exact source seed. -/
def actualEffect : compiler.EffectAt trace.exactSourceSeed :=
  compiler.actualEffectAt trace.exactSourceSeed

/-- Dependent effect consumer generated together with that actual effect. -/
def effectConsumer :
    compiler.EffectConsumerAt trace.exactSourceSeed trace.actualEffect :=
  compiler.consumeEffect trace.exactSourceSeed

end SourceGeneratedTheoryFeedbackTraceAt

/-! ## Neutral negative carrier -/

/-- A bare effect value has no source seed, policy, dependent consumer, root
theory or adoption authority. -/
structure BareTheoryEffectAt
    (compiler : SourceOwnedTheoryFeedbackCompilerAt oldTheory game Seed SeedAt)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) : Type u where
  effect : compiler.EffectAt seed

end
end Effect
end Theory
end Society
end ProcessGame
end SaturationMonoid
