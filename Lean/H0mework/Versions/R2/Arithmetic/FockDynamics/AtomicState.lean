import H0mework.Versions.R2.Arithmetic.FockState.ParityMeasurement
import H0mework.Versions.R2.Arithmetic.FockState.PhysicalDecay

/-!
# Source-generated atomic particle process state

One effective arithmetic split generates its pure Fock state, refined atomic
measurement, and complete finite inventory of applicable factor-decay
channels.  The existing full factor-decay classifier then emits exactly one
terminal or one actual channel; neither branch is supplied by a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockAtomicProcess

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open ParticleWaveFock

noncomputable section

/-- Finite code for one channel applicable at a fixed split. -/
abbrev ChannelCode (index : Nat) :=
  Bool × Fin (repairTargetValue index + 1) × Bool

def alternativeSide {index : Nat} {source : EffectiveSplitAt index} :
    FactorRepairAlternativeAt source → Bool
  | .left _ _ => false
  | .right _ _ => true

def alternativeFactorCode {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    Fin (repairTargetValue index + 1) :=
  ⟨alternative.factor, by
    cases alternative with
    | left leftNotPrime factor =>
        have factorLt : factor.1 < splitLeft source :=
          FactorRepairAlternativeAt.factorProper
            (.left leftNotPrime factor)
        exact factorLt.trans_le
          (Nat.le_succ_of_le (splitLeft_le_target source))
    | right rightNotPrime factor =>
        have factorLt : factor.1 < splitRight source :=
          FactorRepairAlternativeAt.factorProper
            (.right rightNotPrime factor)
        have endpointLe : splitRight source ≤ repairTargetValue index := by
          have landing := split_landing source
          omega
        exact factorLt.trans_le (Nat.le_succ_of_le endpointLe)⟩

def encodeChannel {index : Nat} {source : EffectiveSplitAt index} :
    FactorDecayChannelAt source → ChannelCode index
  | .repair alternative =>
      (alternativeSide alternative, alternativeFactorCode alternative, false)
  | .emission alternative =>
      (alternativeSide alternative, alternativeFactorCode alternative, true)

theorem encodeChannel_injective {index : Nat}
    {source : EffectiveSplitAt index} :
    Function.Injective (encodeChannel (source := source)) := by
  intro left right equality
  cases left with
  | repair leftAlternative =>
      cases right with
      | repair rightAlternative =>
          cases leftAlternative with
          | left leftNotPrime leftFactor =>
              cases rightAlternative with
              | left rightNotPrime rightFactor =>
                  have factorCodeEq :
                      alternativeFactorCode
                          (.left leftNotPrime leftFactor) =
                        alternativeFactorCode
                          (.left rightNotPrime rightFactor) :=
                    congrArg (fun code : ChannelCode index => code.2.1)
                      equality
                  have factorEq : leftFactor = rightFactor :=
                    Subtype.ext (congrArg Fin.val factorCodeEq)
                  cases factorEq
                  rfl
              | right rightNotPrime rightFactor =>
                  have impossible : (false : Bool) = true :=
                    congrArg (fun code : ChannelCode index => code.1) equality
                  cases impossible
          | right leftNotPrime leftFactor =>
              cases rightAlternative with
              | left rightNotPrime rightFactor =>
                  have impossible : (true : Bool) = false :=
                    congrArg (fun code : ChannelCode index => code.1) equality
                  cases impossible
              | right rightNotPrime rightFactor =>
                  have factorCodeEq :
                      alternativeFactorCode
                          (.right leftNotPrime leftFactor) =
                        alternativeFactorCode
                          (.right rightNotPrime rightFactor) :=
                    congrArg (fun code : ChannelCode index => code.2.1)
                      equality
                  have factorEq : leftFactor = rightFactor :=
                    Subtype.ext (congrArg Fin.val factorCodeEq)
                  cases factorEq
                  rfl
      | emission rightAlternative =>
          have impossible : (false : Bool) = true :=
            congrArg (fun code : ChannelCode index => code.2.2) equality
          cases impossible
  | emission leftAlternative =>
      cases right with
      | repair rightAlternative =>
          have impossible : (true : Bool) = false :=
            congrArg (fun code : ChannelCode index => code.2.2) equality
          cases impossible
      | emission rightAlternative =>
          cases leftAlternative with
          | left leftNotPrime leftFactor =>
              cases rightAlternative with
              | left rightNotPrime rightFactor =>
                  have factorCodeEq :
                      alternativeFactorCode
                          (.left leftNotPrime leftFactor) =
                        alternativeFactorCode
                          (.left rightNotPrime rightFactor) :=
                    congrArg (fun code : ChannelCode index => code.2.1)
                      equality
                  have factorEq : leftFactor = rightFactor :=
                    Subtype.ext (congrArg Fin.val factorCodeEq)
                  cases factorEq
                  rfl
              | right rightNotPrime rightFactor =>
                  have impossible : (false : Bool) = true :=
                    congrArg (fun code : ChannelCode index => code.1) equality
                  cases impossible
          | right leftNotPrime leftFactor =>
              cases rightAlternative with
              | left rightNotPrime rightFactor =>
                  have impossible : (true : Bool) = false :=
                    congrArg (fun code : ChannelCode index => code.1) equality
                  cases impossible
              | right rightNotPrime rightFactor =>
                  have factorCodeEq :
                      alternativeFactorCode
                          (.right leftNotPrime leftFactor) =
                        alternativeFactorCode
                          (.right rightNotPrime rightFactor) :=
                    congrArg (fun code : ChannelCode index => code.2.1)
                      equality
                  have factorEq : leftFactor = rightFactor :=
                    Subtype.ext (congrArg Fin.val factorCodeEq)
                  cases factorEq
                  rfl

noncomputable instance factorDecayChannelFinite {index : Nat}
    (source : EffectiveSplitAt index) :
    Finite (FactorDecayChannelAt source) :=
  Finite.of_injective (encodeChannel (source := source))
    encodeChannel_injective

noncomputable instance factorDecayChannelFintype {index : Nat}
    (source : EffectiveSplitAt index) :
    Fintype (FactorDecayChannelAt source) :=
  Fintype.ofFinite _

noncomputable local instance factorDecayChannelDecidableEq {index : Nat}
    (source : EffectiveSplitAt index) :
    DecidableEq (FactorDecayChannelAt source) := Classical.decEq _

abbrev ApplicableChannelInventoryAt {index : Nat}
    (current : EffectiveSplitAt index) :=
  Finset (FactorDecayChannelAt current)

def completeApplicableInventory {index : Nat}
    (current : EffectiveSplitAt index) :
    ApplicableChannelInventoryAt current :=
  Finset.univ

@[simp] theorem mem_completeApplicableInventory {index : Nat}
    {current : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt current) :
    channel ∈ completeApplicableInventory current :=
  Finset.mem_univ channel

/-- Complete physical current generated by one actual effective split. -/
structure PhysicalCurrentAt (index : Nat) : Type where
  private mk ::
  current : EffectiveSplitAt index
  particleState : ParentCarrier
  particleState_eq : particleState = splitParticleState current
  measurement : AtomicJointMeasurementTarget
  measurement_eq : measurement = atomicJointMeasurement current
  applicableInventory : ApplicableChannelInventoryAt current
  applicableInventory_eq :
    applicableInventory = completeApplicableInventory current

def generateCurrent {index : Nat}
    (current : EffectiveSplitAt index) : PhysicalCurrentAt index :=
  { current := current
    particleState := splitParticleState current
    particleState_eq := rfl
    measurement := atomicJointMeasurement current
    measurement_eq := rfl
    applicableInventory := completeApplicableInventory current
    applicableInventory_eq := rfl }

@[simp] theorem generateCurrent_particleState {index : Nat}
    (current : EffectiveSplitAt index) :
    (generateCurrent current).particleState = splitParticleState current :=
  rfl

@[simp] theorem generateCurrent_measurement {index : Nat}
    (current : EffectiveSplitAt index) :
    (generateCurrent current).measurement = atomicJointMeasurement current :=
  rfl

theorem PhysicalCurrentAt.everyChannelApplicable {index : Nat}
    (current : PhysicalCurrentAt index)
    (channel : FactorDecayChannelAt current.current) :
    channel ∈ current.applicableInventory := by
  rw [current.applicableInventory_eq]
  exact mem_completeApplicableInventory channel

private theorem splitLeftUnit_eq_splitLeftUnit_implies
    {index : Nat} {left right : EffectiveSplitAt index}
    (unitEq : splitLeftUnit left = splitLeftUnit right) :
    splitLeft left = splitLeft right := by
  have valueEq := congrArg
    (fun unit : Units NNReal => (((unit : NNReal) : ℝ))) unitEq
  rw [splitLeftUnit_value, splitLeftUnit_value] at valueEq
  exact_mod_cast valueEq

private theorem splitLeftUnit_eq_splitRightUnit_implies
    {index : Nat} {left right : EffectiveSplitAt index}
    (unitEq : splitLeftUnit left = splitRightUnit right) :
    splitLeft left = splitRight right := by
  have valueEq := congrArg
    (fun unit : Units NNReal => (((unit : NNReal) : ℝ))) unitEq
  rw [splitLeftUnit_value, splitRightUnit_value] at valueEq
  exact_mod_cast valueEq

/-- A factor-two repair changes the indistinguishable-pair state because its
species flip cannot be hidden by either orientation of the unordered key. -/
theorem repairFactorTwo_physicalProgress {index : Nat}
    {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorTwo : alternative.factor = 2) :
    PhysicalFactorDecayProgressAt (.repair alternative) := by
  intro actionZero
  have endpointEq :=
    (physicalFactorDecayAction_eq_zero_iff (.repair alternative)).1 actionZero
  have keyEq :=
    (physicalSplitParticleState_eq_iff_key_eq _ _).1 endpointEq
  rw [physicalSplitKey, physicalSplitKey, Sym2.eq_iff] at keyEq
  have speciesFlip :=
    repair_orderedSpeciesGrade_both_flip_of_factor_eq_two
      alternative factorTwo
  apply speciesFlip.1
  rcases keyEq with ⟨leftEq, _rightEq⟩ | ⟨leftEq, _rightEq⟩
  · exact congrArg endpointSpeciesGrade
      (splitLeftUnit_eq_splitLeftUnit_implies leftEq)
  · have crossSpeciesEq := congrArg endpointSpeciesGrade
      (splitLeftUnit_eq_splitRightUnit_implies leftEq)
    exact crossSpeciesEq.trans
      (orderedSpeciesGrade_diagonal source).symm

/-! ## Physical source selection -/

abbrev TerminalSelectionAt {index : Nat}
    (current : PhysicalCurrentAt index) :=
  CanonicalUnitArithmeticFullFactorEmissionProducer.PhysicalTerminalSelectionAt
    current.current

abbrev PhysicalProgressChannelAt {index : Nat}
    (current : PhysicalCurrentAt index) :=
  CanonicalUnitArithmeticFullFactorEmissionProducer.PhysicalProgressChannelAt
    current.current

abbrev PhysicalSourceOutcomeAt {index : Nat}
    (current : PhysicalCurrentAt index) :=
  CanonicalUnitArithmeticFullFactorEmissionProducer.FullPhysicalFactorDecayOutcomeAt
    current.current

/-- The Fock source consumes the unique arithmetic physical selector; it does
not maintain a second repair/emission choice. -/
def generatePhysicalSourceOutcome {index : Nat}
    (current : PhysicalCurrentAt index) : PhysicalSourceOutcomeAt current :=
  fullPhysicalFactorDecayClassify current.current

/-- Exact physical source event.  Its private constructor prevents callers
from supplying a terminal or channel. -/
structure SourceEventAt {index : Nat}
    (current : PhysicalCurrentAt index) : Type where
  private mk ::
  outcome : PhysicalSourceOutcomeAt current
  outcome_eq : outcome = generatePhysicalSourceOutcome current

def generateEvent {index : Nat}
    (current : PhysicalCurrentAt index) : SourceEventAt current :=
  ⟨generatePhysicalSourceOutcome current, rfl⟩

@[simp] theorem generateEvent_outcome {index : Nat}
    (current : PhysicalCurrentAt index) :
    (generateEvent current).outcome = generatePhysicalSourceOutcome current :=
  rfl

theorem SourceEventAt.eq_generateEvent {index : Nat}
    {current : PhysicalCurrentAt index}
    (event : SourceEventAt current) : event = generateEvent current := by
  rcases event with ⟨outcome, outcome_eq⟩
  cases outcome_eq
  rfl

structure GeneratedTerminalAt {index : Nat}
    (current : PhysicalCurrentAt index)
    (event : SourceEventAt current) : Type where
  private mk ::
  selected : TerminalSelectionAt current
  event_eq : event.outcome = .inl selected

abbrev GeneratedTerminalAt.terminal {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedTerminalAt current event) :=
  generated.selected.terminal

theorem GeneratedTerminalAt.classifier_eq {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedTerminalAt current event) :
    (fullFactorDecayLaw index).classify current.current =
      .inl generated.terminal :=
  generated.selected.classifier_eq

structure GeneratedStepAt {index : Nat}
    (current : PhysicalCurrentAt index)
    (event : SourceEventAt current) : Type where
  private mk ::
  selected : PhysicalProgressChannelAt current
  event_eq : event.outcome = .inr selected
  target : PhysicalCurrentAt index
  target_eq : target = generateCurrent selected.channel.target

abbrev GeneratedStepAt.channel {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedStepAt current event) :=
  generated.selected.channel

theorem GeneratedStepAt.applicable {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedStepAt current event) :
    generated.channel ∈ current.applicableInventory :=
  current.everyChannelApplicable generated.channel

theorem GeneratedStepAt.physicalProgress {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedStepAt current event) :
    PhysicalFactorDecayProgressAt generated.channel :=
  (physicalFactorDecayAction_ne_zero_iff_arithmeticProgress _).2
    generated.selected.physicalProgress

theorem GeneratedStepAt.sourceClassifier_eq {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedStepAt current event) :
    (fullFactorDecayLaw index).classify current.current =
      .inr (.repair generated.selected.classifierAlternative) :=
  generated.selected.classifier_eq

/-- Equality to the physical source selector, not to the historical
repair-only arithmetic classifier. -/
theorem GeneratedStepAt.classifier_eq {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedStepAt current event) :
    generatePhysicalSourceOutcome current = .inr generated.selected :=
  event.outcome_eq.symm.trans generated.event_eq

theorem GeneratedStepAt.channel_eq_preferredRepair {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedStepAt current event)
    (alternative : FactorRepairAlternativeAt current.current)
    (classifierEq :
      (fullFactorDecayLaw index).classify current.current =
        .inr (.repair alternative))
    (repairProgress :
      PhysicalFactorDecayProgressAt
        (FactorDecayChannelAt.repair alternative)) :
    generated.channel = .repair alternative :=
  generated.selected.channel_eq_preferredRepair alternative classifierEq
    ((physicalFactorDecayAction_ne_zero_iff_arithmeticProgress _).1
      repairProgress)

theorem GeneratedStepAt.channel_eq_preferredEmission {index : Nat}
    {current : PhysicalCurrentAt index} {event : SourceEventAt current}
    (generated : GeneratedStepAt current event)
    (alternative : FactorRepairAlternativeAt current.current)
    (classifierEq :
      (fullFactorDecayLaw index).classify current.current =
        .inr (.repair alternative))
    (repairIdentity :
      physicalFactorDecayAction (.repair alternative) = 0)
    (emissionProgress :
      PhysicalFactorDecayProgressAt
        (FactorDecayChannelAt.emission alternative)) :
    generated.channel = .emission alternative := by
  have repairArithmeticIdentity :
      unorderedSplitKey alternative.target = unorderedSplitKey current.current := by
    apply not_ne_iff.mp
    intro arithmeticProgress
    exact
      ((physicalFactorDecayAction_ne_zero_iff_arithmeticProgress
        (FactorDecayChannelAt.repair alternative)).2
        arithmeticProgress) repairIdentity
  exact generated.selected.channel_eq_preferredEmission alternative
    classifierEq repairArithmeticIdentity
      ((physicalFactorDecayAction_ne_zero_iff_arithmeticProgress _).1
        emissionProgress)

inductive GeneratedDispositionAt {index : Nat}
    (current : PhysicalCurrentAt index) : Type
  | terminal
      (generated : GeneratedTerminalAt current (generateEvent current))
  | step
      (generated : GeneratedStepAt current (generateEvent current))

def generateDisposition {index : Nat}
    (current : PhysicalCurrentAt index) : GeneratedDispositionAt current := by
  generalize outcomeEq : generatePhysicalSourceOutcome current = outcome
  cases outcome with
  | inl terminal =>
      exact .terminal
        { selected := terminal
          event_eq := by
            change generatePhysicalSourceOutcome current = .inl terminal
            exact outcomeEq }
  | inr selected =>
      exact .step
        { selected := selected
          event_eq := by
            change generatePhysicalSourceOutcome current = .inr selected
            exact outcomeEq
          target := generateCurrent selected.channel.target
          target_eq := rfl }

/-- Canonical source start `2 + (N - 2)` with all physical faces generated. -/
def canonicalCurrent (index : Nat) (indexInRange : 1 ≤ index) :
    PhysicalCurrentAt index :=
  generateCurrent (canonicalSplit index indexInRange)

def canonicalEvent (index : Nat) (indexInRange : 1 ≤ index) :
    SourceEventAt (canonicalCurrent index indexInRange) :=
  generateEvent (canonicalCurrent index indexInRange)

@[simp] theorem canonicalCurrent_current
    (index : Nat) (indexInRange : 1 ≤ index) :
    (canonicalCurrent index indexInRange).current =
      canonicalSplit index indexInRange :=
  rfl

@[simp] theorem canonicalEvent_outcome
    (index : Nat) (indexInRange : 1 ≤ index) :
    (canonicalEvent index indexInRange).outcome =
      generatePhysicalSourceOutcome (canonicalCurrent index indexInRange) :=
  rfl

end

end ParticleWaveFockAtomicProcess
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
