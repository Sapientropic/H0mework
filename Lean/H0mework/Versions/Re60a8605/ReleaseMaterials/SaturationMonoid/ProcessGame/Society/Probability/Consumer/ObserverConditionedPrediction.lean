import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Kernel.NormalizedObserverKernelFold

/-!
# Observer-conditioned prediction consumers

An observer-conditioned probability can be consumed as a prediction without
turning the probability value or the resulting prediction into stored source
data.  The classification below is a derived readout: `none` stays
unclassified, while every positive readout `some p` is compared with the fixed
half threshold.

The source-generated kernel-fold consumer is added below the neutral
classification layer.  This module creates no phase, policy authority, root,
ledger, or next current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Probability
namespace Consumer

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space Observer Measure Kernel

universe uSource uState uSeed uLineage uUnit
universe uSiteSeed uSiteLineage uFlow
universe uBoundarySeed uBoundaryLineage uBoundaryClass
universe uVisible uAuthorityResidual

noncomputable section

/-- Three exhaustive prediction classes for a defined normalized readout. -/
inductive ObserverConditionedPredictionClass where
  | belowHalf
  | equalHalf
  | aboveHalf
  deriving DecidableEq, Repr

namespace ObserverConditionedPredictionClass

/-- Fixed descriptive threshold.  It is not a policy parameter. -/
def half : ℚ≥0 := 1 / 2

/-- Derived classification of one defined normalized probability. -/
noncomputable def ofProbability
    (probability : ℚ≥0) : ObserverConditionedPredictionClass :=
  if probability < half then .belowHalf
  else if probability = half then .equalHalf
  else .aboveHalf

theorem ofProbability_eq_belowHalf_iff (probability : ℚ≥0) :
    ofProbability probability = .belowHalf ↔ probability < half := by
  unfold ofProbability
  by_cases below : probability < half
  · simp [below]
  · by_cases equal : probability = half <;> simp [below, equal]

theorem ofProbability_eq_equalHalf_iff (probability : ℚ≥0) :
    ofProbability probability = .equalHalf ↔ probability = half := by
  unfold ofProbability
  by_cases below : probability < half
  · have notEqual : probability ≠ half := by
      intro equal
      subst probability
      exact (lt_irrefl half) below
    simp [below, notEqual]
  · by_cases equal : probability = half
    · simp [equal]
    · simp [below, equal]

theorem ofProbability_eq_aboveHalf_iff (probability : ℚ≥0) :
    ofProbability probability = .aboveHalf ↔ half < probability := by
  unfold ofProbability
  by_cases below : probability < half
  · have notAbove : ¬ half < probability := by
      exact fun above => lt_asymm below above
    simp [below, notAbove]
  · by_cases equal : probability = half
    · simp [equal]
    · have above : half < probability :=
        lt_of_le_of_ne (not_lt.mp below) (Ne.symm equal)
      simp [below, equal, above]

/-- Lift the derived classification through the zero-mass/empty-fibre
boundary represented by `Option`. -/
noncomputable def ofReadout
    (readout : Option ℚ≥0) : Option ObserverConditionedPredictionClass :=
  readout.map ofProbability

theorem ofReadout_eq_none_iff (readout : Option ℚ≥0) :
    ofReadout readout = none ↔ readout = none := by
  cases readout <;> simp [ofReadout]

theorem ofReadout_eq_some_belowHalf_iff (readout : Option ℚ≥0) :
    ofReadout readout = some .belowHalf ↔
      ∃ probability, readout = some probability ∧ probability < half := by
  cases readout with
  | none => simp [ofReadout]
  | some probability =>
      simp [ofReadout, ofProbability_eq_belowHalf_iff]

theorem ofReadout_eq_some_equalHalf_iff (readout : Option ℚ≥0) :
    ofReadout readout = some .equalHalf ↔
      ∃ probability, readout = some probability ∧ probability = half := by
  cases readout with
  | none => simp [ofReadout]
  | some probability =>
      simp [ofReadout, ofProbability_eq_equalHalf_iff]

theorem ofReadout_eq_some_aboveHalf_iff (readout : Option ℚ≥0) :
    ofReadout readout = some .aboveHalf ↔
      ∃ probability, readout = some probability ∧ half < probability := by
  cases readout with
  | none => simp [ofReadout]
  | some probability =>
      simp [ofReadout, ofProbability_eq_aboveHalf_iff]

/-- Every defined probability readout receives exactly one of the three
derived classes. -/
theorem positive_readout_classification_exhaustive
    (readout : Option ℚ≥0)
    (probability : ℚ≥0)
    (positive : readout = some probability) :
    ofReadout readout = some .belowHalf ∨
      ofReadout readout = some .equalHalf ∨
      ofReadout readout = some .aboveHalf := by
  subst readout
  cases classification : ofProbability probability with
  | belowHalf => exact Or.inl (by simp [ofReadout, classification])
  | equalHalf =>
      exact Or.inr (Or.inl (by simp [ofReadout, classification]))
  | aboveHalf =>
      exact Or.inr (Or.inr (by simp [ofReadout, classification]))

/-- Changing an observer or measure can only be compared after both
predictions have been derived.  This relation carries no update authority. -/
def ReadoutDiffers
    (left right : Option ObserverConditionedPredictionClass) : Prop :=
  left ≠ right

end ObserverConditionedPredictionClass

/-! ## Source-generated prediction consumer -/

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
variable {sourceMeasure : SourceGeneratedFiniteMeasureAt measureCompiler}

variable {Visible : Type uVisible}
variable {AuthorityResidual : Type uAuthorityResidual}
variable {observer : AuthorityObserver crossingCompiler.ExactCrossing Visible
  AuthorityResidual}
variable {event : crossingCompiler.ExactCrossing → Prop}

/-- Zero-field prediction consumer over one exact normalized kernel fold and
one conditioning visible.  Probability and classification are always
recomputed from these indices. -/
inductive SourceGeneratedObserverConditionedPredictionAt
    (fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible) : Type where
  | private generated

namespace SourceGeneratedObserverConditionedPredictionAt

/-- Sole prediction-consumer producer. -/
def generate
    (fold : SourceGeneratedObserverKernelFoldAt
      sourceMeasure observer event)
    (visible : Visible) :
    SourceGeneratedObserverConditionedPredictionAt fold visible :=
  .generated

variable {fold : SourceGeneratedObserverKernelFoldAt
  sourceMeasure observer event}
variable {visible : Visible}
variable (prediction :
  SourceGeneratedObserverConditionedPredictionAt fold visible)

theorem eq_generate : prediction = generate fold visible := by
  cases prediction
  rfl

section ComputableReadouts

variable [DecidableEq Visible]
variable [DecidablePred event]

/-- Exact normalized fold retained by the consumer index. -/
def kernelFold
    (prediction :
      SourceGeneratedObserverConditionedPredictionAt fold visible) :
    SourceGeneratedObserverKernelFoldAt sourceMeasure observer event := by
  cases prediction
  exact fold

/-- Exact source-generated measure seal retained by the consumer index. -/
def sourceMeasureSeal
    (prediction :
      SourceGeneratedObserverConditionedPredictionAt fold visible) :
    SourceGeneratedFiniteMeasureAt measureCompiler := by
  cases prediction
  exact sourceMeasure

/-- Exact occurrence inventory remains the sole M11 crossing trace. -/
def sourceOccurrenceTrace : List crossingCompiler.ExactCrossing :=
  prediction.sourceMeasureSeal.measure.occurrenceTrace

omit [DecidableEq Visible] [DecidablePred event] in
theorem sourceOccurrenceTrace_eq_crossingTrace :
    prediction.sourceOccurrenceTrace = socialSpace.crossingTrace :=
  SourceGeneratedFiniteMeasureAt.occurrenceTrace_eq_crossingTrace
    prediction.sourceMeasureSeal

/-- Existing observer retained by the consumer index. -/
def authorityObserver
    (prediction :
      SourceGeneratedObserverConditionedPredictionAt fold visible) :
    AuthorityObserver crossingCompiler.ExactCrossing Visible
      AuthorityResidual := by
  cases prediction
  exact observer

/-- Exact conditioning visible retained by the consumer index. -/
def conditionedVisible
    (prediction :
      SourceGeneratedObserverConditionedPredictionAt fold visible) : Visible := by
  cases prediction
  exact visible

/-- Exact event predicate retained by the consumer index. -/
def eventPredicate
    (prediction :
      SourceGeneratedObserverConditionedPredictionAt fold visible) :
    crossingCompiler.ExactCrossing → Prop := by
  cases prediction
  exact event

/-- Normalized probability read directly from the indexed kernel fold. -/
def probability : Option ℚ≥0 :=
  prediction.kernelFold.readVisible prediction.conditionedVisible

/-- Prediction class derived from the normalized readout.  No result is
stored in the consumer. -/
def classification : Option ObserverConditionedPredictionClass :=
  ObserverConditionedPredictionClass.ofReadout prediction.probability

theorem classification_eq_none_iff :
    prediction.classification = none ↔ prediction.probability = none :=
  ObserverConditionedPredictionClass.ofReadout_eq_none_iff
    prediction.probability

theorem classification_eq_some_belowHalf_iff :
    prediction.classification =
        some ObserverConditionedPredictionClass.belowHalf ↔
      ∃ probability, prediction.probability = some probability ∧
        probability < ObserverConditionedPredictionClass.half :=
  ObserverConditionedPredictionClass.ofReadout_eq_some_belowHalf_iff
    prediction.probability

theorem classification_eq_some_equalHalf_iff :
    prediction.classification =
        some ObserverConditionedPredictionClass.equalHalf ↔
      ∃ probability, prediction.probability = some probability ∧
        probability = ObserverConditionedPredictionClass.half :=
  ObserverConditionedPredictionClass.ofReadout_eq_some_equalHalf_iff
    prediction.probability

theorem classification_eq_some_aboveHalf_iff :
    prediction.classification =
        some ObserverConditionedPredictionClass.aboveHalf ↔
      ∃ probability, prediction.probability = some probability ∧
        ObserverConditionedPredictionClass.half < probability :=
  ObserverConditionedPredictionClass.ofReadout_eq_some_aboveHalf_iff
    prediction.probability

/-- Every defined normalized readout is classified exhaustively. -/
theorem positive_classification_exhaustive
    (probability : ℚ≥0)
    (positive : prediction.probability = some probability) :
    prediction.classification =
        some ObserverConditionedPredictionClass.belowHalf ∨
      prediction.classification =
          some ObserverConditionedPredictionClass.equalHalf ∨
      prediction.classification =
        some ObserverConditionedPredictionClass.aboveHalf :=
  ObserverConditionedPredictionClass.positive_readout_classification_exhaustive
    prediction.probability probability positive

/-- Exact occurrence probability readout supplied by the same kernel fold. -/
def probabilityReadout :
    OccurrenceReadout crossingCompiler.ExactCrossing (Option ℚ≥0) :=
  prediction.kernelFold.probabilityReadout

/-- Exact visible factorization retained without recomputation or a second
factorization theorem. -/
def exactReadoutFactorization :
    ReadoutFactorization observer prediction.probabilityReadout :=
  prediction.kernelFold.probabilityReadoutFactorization

/-- Direct downstream use of the kernel fold's existing M6 obstruction:
this prediction consumer cannot decode hidden authority. -/
theorem noAuthorityCompleteConsumer
    (pair : AuthorityKernelPair observer) :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt observer prediction.probabilityReadout) :=
  prediction.kernelFold.noAuthorityCompleteProbability pair

end ComputableReadouts

end SourceGeneratedObserverConditionedPredictionAt

end
end Consumer
end Probability
end Society
end ProcessGame
end SaturationMonoid
