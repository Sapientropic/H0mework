import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.ExactOperationalFace
import H0mework.Versions.R2.Arithmetic.FockState.FactorDecay
import H0mework.Versions.R2.Arithmetic.FockState.IndistinguishablePairs
import H0mework.Versions.R2.Arithmetic.FockUnitAction.Transfer

/-!
# Prime-three and Fock faces of the existing-unit action

The primitive action comes from the same-whole existing-unit transfer kernel.
This module derives its source-generated prime-three two-fold, joint
measurement/inverse-fibre write, exact-occurrence receipt, and the enlarged
factor/unit law.  No terminal, complement primality, occupancy, or nonzero
claim enters an action payload.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockUnitChargeAction

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticRoot
open ParticleWaveFock
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

def primeThreeIndex (index : Nat) (indexInRange : 1 ≤ index) :
    GeneratedPrimeIndexAt index :=
  terminalPrimeIndex 3 Nat.prime_three (by
    rw [evenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]
    omega)

def exchangeQuantum (index : Nat) (indexInRange : 1 ≤ index) : Nat :=
  (generatedPrimeHistory (primeThreeIndex index indexInRange)).cardinalShadow - 1

theorem exchangeQuantum_eq_two (index : Nat) (indexInRange : 1 ≤ index) :
    exchangeQuantum index indexInRange = 2 := by
  rw [exchangeQuantum, generatedPrimeHistory_cardinalShadow]
  rfl

/-- The prime-three exchange is the exact two-fold of the native unit-charge
action because its source-generated quantum is `3-1=2`. -/
structure PrimeThreeExchangeAt {index : Nat}
    (indexInRange : 1 ≤ index) (source : EffectiveSplitAt index) : Type where
  private mk ::
  rightRoom : exchangeQuantum index indexInRange + 2 ≤ splitRight source
  primeIndex : GeneratedPrimeIndexAt index
  primeIndex_eq : primeIndex = primeThreeIndex index indexInRange
  quantum : Nat
  quantum_eq : quantum = exchangeQuantum index indexInRange
  quantum_eq_two : quantum = 2
  first : UnitChargeActionAt source
  second : UnitChargeActionAt first.target

def generatePrimeThreeExchange {index : Nat}
    (indexInRange : 1 ≤ index) (source : EffectiveSplitAt index)
    (rightRoom : exchangeQuantum index indexInRange + 2 ≤ splitRight source) :
    PrimeThreeExchangeAt indexInRange source := by
  have quantumEq := exchangeQuantum_eq_two index indexInRange
  have sourceRoom : 4 ≤ splitRight source := by omega
  let first := generateUnitChargeAction source (by omega)
  have secondRoom : 3 ≤ splitRight first.target := by
    rw [first.target_eq, unitChargeTarget_right]
    omega
  let second := generateUnitChargeAction first.target secondRoom
  exact
    { rightRoom := rightRoom
      primeIndex := primeThreeIndex index indexInRange
      primeIndex_eq := rfl
      quantum := exchangeQuantum index indexInRange
      quantum_eq := rfl
      quantum_eq_two := quantumEq
      first := first
      second := second }

def exchangeTarget {index : Nat} {indexInRange : 1 ≤ index}
    {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    EffectiveSplitAt index :=
  action.second.target

@[simp] theorem exchangeTarget_left {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    splitLeft (exchangeTarget action) = splitLeft source + 2 := by
  rw [exchangeTarget, action.second.target_eq, unitChargeTarget_left,
    action.first.target_eq, unitChargeTarget_left]

@[simp] theorem exchangeTarget_right {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    splitRight (exchangeTarget action) = splitRight source - 2 := by
  rw [exchangeTarget, action.second.target_eq, unitChargeTarget_right,
    action.first.target_eq, unitChargeTarget_right]
  have sourceRoom : 4 ≤ splitRight source := by
    have room := action.rightRoom
    rw [exchangeQuantum_eq_two] at room
    exact room
  omega

theorem exchangeTarget_lands {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    splitLeft (exchangeTarget action) + splitRight (exchangeTarget action) =
      repairTargetValue index :=
  split_landing _

theorem exchangeTarget_ne_source {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    exchangeTarget action ≠ source := by
  intro targetEq
  have leftEq := congrArg splitLeft targetEq
  rw [exchangeTarget_left] at leftEq
  omega

def exchangeSourceOrdered {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (_action : PrimeThreeExchangeAt indexInRange source) : Nat × Nat :=
  (splitLeft source, splitRight source)

def exchangeTargetOrdered {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) : Nat × Nat :=
  (splitLeft (exchangeTarget action), splitRight (exchangeTarget action))

def exchangeSourceUnordered {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (_action : PrimeThreeExchangeAt indexInRange source) :=
  unorderedSplitKey source

def exchangeTargetUnordered {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :=
  unorderedSplitKey (exchangeTarget action)

theorem exchange_measurement_eq {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    jointMeasurement (splitParticleState source) =
      jointMeasurement (splitParticleState (exchangeTarget action)) := by
  rw [jointMeasurement_splitParticleState,
    jointMeasurement_splitParticleState]

def exchangeKernelTrace {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    JointMeasurementKernel :=
  ⟨splitParticleState source - splitParticleState (exchangeTarget action),
    (jointMeasurement_eq_iff_sub_mem_kernel _ _).mp
      (exchange_measurement_eq action)⟩

theorem exchange_recollects {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    splitParticleState (exchangeTarget action) + exchangeKernelTrace action =
      splitParticleState source := by
  change splitParticleState (exchangeTarget action) +
      (splitParticleState source - splitParticleState (exchangeTarget action)) = _
  abel

theorem exchange_physical_measurement_eq {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    physicalJointMeasurement
        (physicalParentProjection (splitParticleState source)) =
      physicalJointMeasurement
        (physicalParentProjection (splitParticleState (exchangeTarget action))) := by
  rw [physicalJointMeasurement_projection,
    physicalJointMeasurement_projection]
  exact exchange_measurement_eq action

def exchangeSourceFibre {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (_action : PrimeThreeExchangeAt indexInRange source) :
    JointMeasurementFibreAt (jointMeasurement (splitParticleState source)) :=
  measuredStateFibre _

def exchangeTargetFibre {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index}
    (action : PrimeThreeExchangeAt indexInRange source) :
    JointMeasurementFibreAt (jointMeasurement (splitParticleState source)) :=
  ⟨splitParticleState (exchangeTarget action),
    (exchange_measurement_eq action).symm⟩

structure RootedPrimeThreeExchangeReceiptAt
    {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index)
    (source : EffectiveSplitAt index)
    (action : PrimeThreeExchangeAt indexInRange source) : Type where
  private mk ::
  rootSource : RootGeneratedExactOccurrenceOperationalFactorDecayAt
    rootOccurrence index indexInRange
  rootSource_eq : rootSource =
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      rootOccurrence index indexInRange
  primeIndex : GeneratedPrimeIndexAt index
  primeIndex_eq : primeIndex = primeThreeIndex index indexInRange
  target : EffectiveSplitAt index
  target_eq : target = exchangeTarget action
  trace : JointMeasurementKernel
  trace_eq : trace = exchangeKernelTrace action
  sourceFibre : JointMeasurementFibreAt
    (jointMeasurement (splitParticleState source))
  sourceFibre_eq : sourceFibre = exchangeSourceFibre action
  targetFibre : JointMeasurementFibreAt
    (jointMeasurement (splitParticleState source))
  targetFibre_eq : targetFibre = exchangeTargetFibre action
  sourceOrdered : Nat × Nat
  sourceOrdered_eq : sourceOrdered = exchangeSourceOrdered action
  targetOrdered : Nat × Nat
  targetOrdered_eq : targetOrdered = exchangeTargetOrdered action
  sourceUnordered : Sym2 Nat
  sourceUnordered_eq : sourceUnordered = exchangeSourceUnordered action
  targetUnordered : Sym2 Nat
  targetUnordered_eq : targetUnordered = exchangeTargetUnordered action
  sourcePhysicalState : PhysicalParentCarrier
  sourcePhysicalState_eq : sourcePhysicalState =
    physicalParentProjection (splitParticleState source)
  targetPhysicalState : PhysicalParentCarrier
  targetPhysicalState_eq : targetPhysicalState =
    physicalParentProjection (splitParticleState target)
  physicalMeasurementConserved :
    physicalJointMeasurement sourcePhysicalState =
      physicalJointMeasurement targetPhysicalState
  recollects : splitParticleState target + trace = splitParticleState source

def generateRootedPrimeThreeExchange
    {Occurrence : Type} (rootOccurrence : Occurrence)
    (index : Nat) (indexInRange : 1 ≤ index)
    (source : EffectiveSplitAt index)
    (action : PrimeThreeExchangeAt indexInRange source) :
    RootedPrimeThreeExchangeReceiptAt rootOccurrence index indexInRange
      source action :=
  { rootSource :=
      CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
        rootOccurrence index indexInRange
    rootSource_eq := rfl
    primeIndex := action.primeIndex
    primeIndex_eq := action.primeIndex_eq
    target := exchangeTarget action
    target_eq := rfl
    trace := exchangeKernelTrace action
    trace_eq := rfl
    sourceFibre := exchangeSourceFibre action
    sourceFibre_eq := rfl
    targetFibre := exchangeTargetFibre action
    targetFibre_eq := rfl
    sourceOrdered := exchangeSourceOrdered action
    sourceOrdered_eq := rfl
    targetOrdered := exchangeTargetOrdered action
    targetOrdered_eq := rfl
    sourceUnordered := exchangeSourceUnordered action
    sourceUnordered_eq := rfl
    targetUnordered := exchangeTargetUnordered action
    targetUnordered_eq := rfl
    sourcePhysicalState := physicalParentProjection (splitParticleState source)
    sourcePhysicalState_eq := rfl
    targetPhysicalState :=
      physicalParentProjection (splitParticleState (exchangeTarget action))
    targetPhysicalState_eq := rfl
    physicalMeasurementConserved := exchange_physical_measurement_eq action
    recollects := exchange_recollects action }

/-- Both same-unit transfers are literal dependent restrictions of the same
fixed occurrence fold; neither action creates, drops, or replaces a unit. -/
theorem RootedPrimeThreeExchangeReceiptAt.action_wholeOccurrence
    {Occurrence : Type} {rootOccurrence : Occurrence}
    {index : Nat} {indexInRange : 1 ≤ index}
    {source : EffectiveSplitAt index}
    {action : PrimeThreeExchangeAt indexInRange source}
    (receipt : RootedPrimeThreeExchangeReceiptAt rootOccurrence index
      indexInRange source action) :
    action.first.sourceLeftHistory.parallel action.first.sourceRightHistory =
        receipt.rootSource.occurrence.fold
          CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra ∧
      action.first.targetLeftHistory.parallel action.first.targetRightHistory =
        receipt.rootSource.occurrence.fold
          CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra ∧
      action.second.targetLeftHistory.parallel action.second.targetRightHistory =
        receipt.rootSource.occurrence.fold
          CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra := by
  rw [receipt.rootSource.targetFold]
  exact ⟨action.first.sourceWholeEquation,
    action.first.targetWholeEquation,
    action.second.targetWholeEquation⟩

/-! ## Complete factor/unit-action inventory -/

inductive FactorUnitChargeActionAt {index : Nat}
    (indexInRange : 1 ≤ index) (source : EffectiveSplitAt index) : Type
  | factor (channel : FactorDecayChannelAt source)
  | unit (action : UnitChargeActionAt source)

def FactorUnitChargeActionAt.target {index : Nat}
    {indexInRange : 1 ≤ index} {source : EffectiveSplitAt index} :
    FactorUnitChargeActionAt indexInRange source → EffectiveSplitAt index
  | .factor channel => channel.target
  | .unit action => action.target

noncomputable def factorUnitChargeLaw (index : Nat) (indexInRange : 1 ≤ index) :
    Law (EffectiveSplitAt index) where
  TerminalAt := PrimePairTerminalAt
  StepAt := FactorUnitChargeActionAt indexInRange
  target := FactorUnitChargeActionAt.target
  classify := fun state =>
    match (fullFactorDecayLaw index).classify state with
    | .inl terminal => .inl terminal
    | .inr channel => .inr (.factor channel)

end
end ParticleWaveFockUnitChargeAction
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
