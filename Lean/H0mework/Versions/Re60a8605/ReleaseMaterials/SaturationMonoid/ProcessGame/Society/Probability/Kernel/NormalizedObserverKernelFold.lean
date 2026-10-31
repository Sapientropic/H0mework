import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Kernel.NormalizedFiniteObserverKernelFold
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Measure.SourceOwnedFlowMeasureCompiler

/-!
# Source-generated normalized observer-kernel fold

A fixed source-generated M11 flow measure is conditioned through an existing
`AuthorityObserver`.  This source specialization retains the established API
while delegating all finite-measure normalization to
`NormalizedFiniteObserverKernelFoldAt`.

The generated seal stores no mass or decision.  Its measure remains the sole
`SourceGeneratedFiniteMeasureAt` emitted from the M11 crossing trace, so the
neutral core cannot manufacture source authority or caller-supplied support.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Probability
namespace Kernel

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space Observer
open Measure

universe uSource uState uSeed uLineage uUnit
universe uSiteSeed uSiteLineage uFlow
universe uBoundarySeed uBoundaryLineage uBoundaryClass
universe uVisible uAuthorityResidual

variable {Source : Type uSource}
variable {State : Type uState}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {Seed : Type uSeed}
variable {SeedAt : Source → State → Seed → Prop}
variable {Lineage : Source → Type uLineage}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
variable {focal : SourceSeed occurrenceOf Seed SeedAt game.source}
variable {rateCompiler : SourceOwnedOccurrenceRateCompiler
  game Seed SeedAt Lineage lineageOf focal}
variable {crossingCompiler : SourceOwnedCrossingCompiler rateCompiler}
variable {socialSpace : SourceGeneratedSocialSpaceAt crossingCompiler}
variable {measureCompiler : SourceOwnedFiniteMeasureCompilerAt socialSpace}

variable {Visible : Type uVisible}
variable {AuthorityResidual : Type uAuthorityResidual}

noncomputable section

/-! ## Source-generated specialization -/

/-- Zero-field source seal over one generated M11 measure, one observer, and
one event.  Its public API delegates to the occurrence-polymorphic normalized
finite fold below. -/
inductive SourceGeneratedObserverKernelFoldAt
    (sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler)
    (observer : AuthorityObserver crossingCompiler.ExactCrossing Visible
      AuthorityResidual)
    (event : crossingCompiler.ExactCrossing → Prop) : Type where
  | private generated

namespace SourceGeneratedObserverKernelFoldAt

/-- Sole source-specialized fold producer. -/
def generate
    (sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler)
    (observer : AuthorityObserver crossingCompiler.ExactCrossing Visible
      AuthorityResidual)
    (event : crossingCompiler.ExactCrossing → Prop) :
    SourceGeneratedObserverKernelFoldAt sourceMeasure observer event :=
  .generated

variable {sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler}
variable {observer : AuthorityObserver crossingCompiler.ExactCrossing Visible
  AuthorityResidual}
variable {event : crossingCompiler.ExactCrossing → Prop}
variable (fold : SourceGeneratedObserverKernelFoldAt
  sourceMeasure observer event)

theorem eq_generate : fold = generate sourceMeasure observer event := by
  cases fold
  rfl

/-- Forget only the source-specialization seal.  The exact generated measure,
observer, and event remain indices of the shared normalized finite fold. -/
def toNormalizedFiniteFold
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event) :
    NormalizedFiniteObserverKernelFoldAt
      sourceMeasure.measure observer event :=
  NormalizedFiniteObserverKernelFoldAt.generate
    sourceMeasure.measure observer event

section ComputableReadouts

variable [DecidableEq Visible]
variable [DecidablePred event]

/-- Exact retained crossings in one visible observer fibre. -/
def fibre
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible) : List crossingCompiler.ExactCrossing :=
  sourceMeasure.measure.occurrenceTrace.filter fun crossing =>
    observer.forget crossing = visible

/-- Exact retained event crossings in that same observer fibre. -/
def eventFibre
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible) : List crossingCompiler.ExactCrossing :=
  sourceMeasure.measure.occurrenceTrace.filter fun crossing =>
    observer.forget crossing = visible ∧ event crossing

omit [DecidablePred event] in
theorem fibre_sublist_occurrenceTrace (visible : Visible) :
    List.Sublist (fold.fibre visible) sourceMeasure.measure.occurrenceTrace :=
  fold.toNormalizedFiniteFold.fibre_sublist_occurrenceTrace visible

theorem eventFibre_sublist_occurrenceTrace (visible : Visible) :
    List.Sublist (fold.eventFibre visible)
      sourceMeasure.measure.occurrenceTrace :=
  fold.toNormalizedFiniteFold.eventFibre_sublist_occurrenceTrace visible

omit [DecidablePred event] in
/-- Every conditioning-fibre occurrence comes from the sole M11 crossing
trace used by the source measure. -/
theorem fibre_mem_crossingTrace
    {visible : Visible}
    {crossing : crossingCompiler.ExactCrossing}
    (membership : crossing ∈ fold.fibre visible) :
    crossing ∈ socialSpace.crossingTrace := by
  have occurrenceMembership :=
    (fold.fibre_sublist_occurrenceTrace visible).mem membership
  rw [sourceMeasure.measure_eq_generatedMeasure,
    measureCompiler.occurrenceTrace_eq_crossingTrace] at occurrenceMembership
  exact occurrenceMembership

/-- Conditioning mass is the shared core's exact fibre fold. -/
def fibreMass
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible) : ℚ≥0 :=
  sourceMeasure.eventMass fun crossing => observer.forget crossing = visible

/-- Event mass is the shared core's exact event/fibre fold. -/
def eventMass
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible) : ℚ≥0 :=
  sourceMeasure.eventMass fun crossing =>
    observer.forget crossing = visible ∧ event crossing

theorem eventMass_le_fibreMass (visible : Visible) :
    fold.eventMass visible ≤ fold.fibreMass visible :=
  fold.toNormalizedFiniteFold.eventMass_le_fibreMass visible

/-- Zero-mass fibres remain undefined; otherwise this is the exact normalized
event/fibre ratio. -/
def readVisible
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible) : Option ℚ≥0 :=
  if _fold.fibreMass visible = 0 then none
  else some (_fold.eventMass visible / _fold.fibreMass visible)

theorem readVisible_eq_none_iff (visible : Visible) :
    fold.readVisible visible = none ↔ fold.fibreMass visible = 0 :=
  fold.toNormalizedFiniteFold.readVisible_eq_none_iff visible

theorem readVisible_eq_some_ratio
    {visible : Visible}
    (positive : 0 < fold.fibreMass visible) :
    fold.readVisible visible =
      some (fold.eventMass visible / fold.fibreMass visible) :=
  fold.toNormalizedFiniteFold.readVisible_eq_some_ratio positive

theorem positive_event_readVisible_some_positive
    {visible : Visible}
    (positiveEvent : 0 < fold.eventMass visible) :
    ∃ probability : ℚ≥0,
      fold.readVisible visible = some probability ∧ 0 < probability :=
  fold.toNormalizedFiniteFold
    |>.positive_event_readVisible_some_positive positiveEvent

theorem readVisible_probability_le_one
    {visible : Visible}
    {probability : ℚ≥0}
    (readout : fold.readVisible visible = some probability) :
    probability ≤ 1 :=
  fold.toNormalizedFiniteFold.readVisible_probability_le_one readout

theorem empty_fibre_readVisible_none
    {visible : Visible}
    (empty : fold.fibre visible = []) :
    fold.readVisible visible = none :=
  fold.toNormalizedFiniteFold.empty_fibre_readVisible_none empty

omit [DecidablePred event] in
/-- Existing source-specific coefficient boundary.  The coefficient is still
read only from the exact crossing's dependent flow payload. -/
theorem fibreMass_eq_zero_of_all_coefficients_zero
    {visible : Visible}
    (allZero : ∀ crossing, crossing ∈ fold.fibre visible →
      sourceMeasure.coefficient crossing = 0) :
    fold.fibreMass visible = 0 := by
  apply fold.toNormalizedFiniteFold.fibreMass_eq_zero_of_all_weights_zero
  intro weighted membership observed
  change weighted ∈ measureCompiler.weightedCrossings at membership
  rcases List.mem_map.mp membership with
    ⟨crossing, crossingMembership, weightedEq⟩
  have occurrenceMembership :
      crossing ∈ sourceMeasure.measure.occurrenceTrace := by
    rw [sourceMeasure.measure_eq_generatedMeasure,
      measureCompiler.occurrenceTrace_eq_crossingTrace]
    exact crossingMembership
  have crossingObserved : observer.forget crossing = visible := by
    have occurrenceEq : crossing = weighted.1 :=
      congrArg Prod.fst weightedEq
    rw [occurrenceEq]
    exact observed
  have fibreMembership : crossing ∈ fold.fibre visible := by
    simp [fibre, occurrenceMembership, crossingObserved]
  have coefficientZero := allZero crossing fibreMembership
  rw [← weightedEq]
  exact coefficientZero

/-- A nonempty all-zero source fibre remains visibly present but has no
probability readout. -/
theorem nonempty_allZero_fibre_readVisible_none
    {visible : Visible}
    (nonempty : fold.fibre visible ≠ [])
    (allZero : ∀ crossing, crossing ∈ fold.fibre visible →
      sourceMeasure.coefficient crossing = 0) :
    fold.readVisible visible = none ∧ fold.fibre visible ≠ [] :=
  ⟨(fold.readVisible_eq_none_iff visible).2
      (fold.fibreMass_eq_zero_of_all_coefficients_zero allZero),
    nonempty⟩

theorem positive_fibre_empty_event_readVisible_some_zero
    {visible : Visible}
    (positiveFibre : 0 < fold.fibreMass visible)
    (emptyEvent : fold.eventFibre visible = []) :
    fold.readVisible visible = some 0 :=
  fold.toNormalizedFiniteFold
    |>.positive_fibre_empty_event_readVisible_some_zero
      positiveFibre emptyEvent

/-! ## Visible factorization and hidden-authority no-go -/

def probabilityReadout
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event) :
    OccurrenceReadout crossingCompiler.ExactCrossing (Option ℚ≥0) :=
  OccurrenceReadout.ofVisible observer _fold.readVisible

@[simp] theorem probabilityReadout_read
    (crossing : crossingCompiler.ExactCrossing) :
    fold.probabilityReadout.read crossing =
      fold.readVisible (observer.forget crossing) :=
  rfl

def probabilityReadoutFactorization
    (_fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event) :
    ReadoutFactorization observer _fold.probabilityReadout :=
  ReadoutFactorization.ofVisible observer _fold.readVisible

theorem kernelPair_equivalence
    (pair : AuthorityKernelPair observer) :
    fold.probabilityReadout.read pair.left =
      fold.probabilityReadout.read pair.right :=
  fold.toNormalizedFiniteFold.kernelPair_equivalence pair

theorem noAuthorityCompleteProbability
    (pair : AuthorityKernelPair observer) :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt observer fold.probabilityReadout) :=
  fold.toNormalizedFiniteFold.noAuthorityCompleteProbability pair

end ComputableReadouts

end SourceGeneratedObserverKernelFoldAt

end
end Kernel
end Probability
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.Probability.Kernel.SourceGeneratedObserverKernelFoldAt.readVisible_probability_le_one
#print axioms SaturationMonoid.ProcessGame.Society.Probability.Kernel.SourceGeneratedObserverKernelFoldAt.empty_fibre_readVisible_none
#print axioms SaturationMonoid.ProcessGame.Society.Probability.Kernel.SourceGeneratedObserverKernelFoldAt.noAuthorityCompleteProbability
