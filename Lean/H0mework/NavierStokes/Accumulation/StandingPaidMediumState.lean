import H0mework.NavierStokes.Butterfly.StackedKineticInvariant

/-!
# Source-generated standing paid medium state

The horizontal root occurrence is already complete.  This module introduces
the missing vertical carrier: one runtime current carries its exact
standing-valued material, one source-owned paying face and a finite remaining
clock potential.  A lawful advance must generate the next paid state and the
exact local settlement

`potential = contactTime + nextPotential + waste`.

The generic finite-prefix fold below consumes only a source seed and one local
advance function.  It never accepts a completed future state family.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStandingPaidMediumState

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedKineticAdvance
open RationalVorticityEvaluator.ButterflyStackedKineticInvariant

noncomputable section

def standingPaidFaceMass
    {nu : Viscosity}
    (current : GeneratedWholeRestartRuntimeCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  finiteStateVorticityCoefficientEnstrophy modes
    current.physical.contact.physicalState

def standingPaidFaceCapacity
    {nu : Viscosity}
    (current : GeneratedWholeRestartRuntimeCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  finiteModeKineticAmbientFactor modes *
    puncturedWholeVorticityKineticMass
      current.physical.contact.physicalState

def standingPaidKineticCapacityPotential
    {nu : Viscosity}
    (current : GeneratedWholeRestartRuntimeCurrent nu)
    (modes : Finset IntegerWavevector)
    (charge : Real) : Real :=
  (standingPaidFaceCapacity current modes -
      standingPaidFaceMass current modes) / charge

theorem standingPaidFaceMass_le_capacity
    {nu : Viscosity}
    (current : GeneratedWholeRestartRuntimeCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    standingPaidFaceMass current modes ≤
      standingPaidFaceCapacity current modes := by
  have transverse : FiniteStateTransverseOn modes
      current.physical.contact.physicalState := by
    intro wave _waveMem
    exact current.physical.contact.transverse wave
  have coefficientLe :=
    finiteStateVorticityCoefficientEnstrophy_le_kineticEnergy_factor
      modes zeroNotMem current.physical.contact.physicalState transverse
  have finiteKineticLe :=
    two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
      modes zeroNotMem current.physical.contact.physicalState transverse
  have finiteKineticNonneg :=
    finiteStateVorticityKineticEnergy_nonneg modes
      current.physical.contact.physicalState
  have finiteLeWhole :
      finiteStateVorticityKineticEnergy modes
          current.physical.contact.physicalState ≤
        puncturedWholeVorticityKineticMass
          current.physical.contact.physicalState := by
    linarith
  exact coefficientLe.trans
    (mul_le_mul_of_nonneg_left finiteLeWhole
      (finiteModeKineticAmbientFactor_nonneg modes))

/-- One source-owned paying instruction at an exact runtime current.  The
material field prevents a face/payment instruction from being paired with a
different standing occurrence. -/
structure SourceGeneratedStandingPaidStateAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartRuntimeCurrent nu) : Type where
  modes : Finset IntegerWavevector
  zeroNotMem : (0 : IntegerWavevector) ∉ modes
  charge : Real
  charge_pos : 0 < charge
  edgePayment :
    current.physical.nextContact.time.1 * charge ≤
      finiteStateVorticityCoefficientEnstrophy modes
          current.physical.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy modes
          current.physical.contact.physicalState
  potential : Real
  potential_nonneg : 0 ≤ potential

namespace SourceGeneratedStandingPaidStateAt

/-- The live material is computed from the indexed runtime current; a caller
cannot submit a second material coordinate. -/
def material
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (_state : SourceGeneratedStandingPaidStateAt current) :
    NativeRestartStandingValuedArithmeticMaterialAt current.standing :=
  nativeRestartStandingValuedArithmeticMaterial current.cellEffect

/-- A paid state has an actual positive finite gain on its own edge. -/
theorem faceGain_pos
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    0 < finiteStateVorticityCoefficientEnstrophy state.modes
          current.physical.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy state.modes
          current.physical.contact.physicalState := by
  have clockChargePos :
      0 < current.physical.nextContact.time.1 * state.charge :=
    mul_pos current.physical.nextContact.time_pos state.charge_pos
  exact clockChargePos.trans_le state.edgePayment

/-- Aggregate payment cannot hide in a scalar row: one mode of the same
source-owned face genuinely gains amplitude on this occurrence. -/
theorem exists_mode_gain
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    ∃ wave ∈ state.modes,
      complexCoordinateAmplitudeSq
          (current.physical.contact.physicalState wave) <
        complexCoordinateAmplitudeSq
          (current.physical.nextContact.physicalState wave) := by
  by_contra noGain
  push Not at noGain
  have sumLe :
      finiteStateVorticityCoefficientEnstrophy state.modes
          current.physical.nextContact.physicalState ≤
        finiteStateVorticityCoefficientEnstrophy state.modes
          current.physical.contact.physicalState := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_le_sum fun wave waveMem => noGain wave waveMem
  linarith [state.faceGain_pos]

/-- Physical valuation retained by the complete paid material.  Its modes
are source-owned by this exact occurrence; they are not truncated back to
the coefficient-level standing anchor. -/
def faceDebit
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) : Real :=
  finiteStateVorticityCoefficientEnstrophy state.modes
      current.physical.nextContact.physicalState -
    finiteStateVorticityCoefficientEnstrophy state.modes
      current.physical.contact.physicalState

theorem faceDebit_pos
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    0 < state.faceDebit :=
  state.faceGain_pos

/-- Arithmetic normalization now uses the complete paid state as provenance.
Consequently its source-owned Fourier face, Real valuation, charge and clock
potential cannot be forgotten before the exact/residual split. -/
def parallelNormalForm
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    ParallelIncidenceNormalFormAt state
      state.material.arithmeticMaterial :=
  normalizeParallel state state.material.arithmeticMaterial

/-- One normalize of the complete standing-valued material is already paid
by the state that owns its physical face. -/
def paidNormalForm
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) : Type :=
  match state.parallelNormalForm with
  | .exact _rooted _commutes => PUnit
  | .generatedResidual _residual => PLift <| 0 < state.faceDebit

def generatedPaidNormalForm
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    state.paidNormalForm := by
  unfold paidNormalForm
  generalize normalFormEq : state.parallelNormalForm = normalForm
  cases normalForm with
  | exact => exact PUnit.unit
  | generatedResidual residual =>
      exact ⟨state.faceDebit_pos⟩

theorem faceMass_le_capacity
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    standingPaidFaceMass current state.modes ≤
      standingPaidFaceCapacity current state.modes :=
  standingPaidFaceMass_le_capacity current state.modes state.zeroNotMem

theorem kineticCapacityPotential_nonneg
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    0 ≤ standingPaidKineticCapacityPotential
      current state.modes state.charge := by
  unfold standingPaidKineticCapacityPotential
  exact div_nonneg (sub_nonneg.mpr state.faceMass_le_capacity)
    state.charge_pos.le

theorem capacity_next_le
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    standingPaidFaceCapacity current.next state.modes ≤
      standingPaidFaceCapacity current state.modes := by
  unfold standingPaidFaceCapacity
  apply mul_le_mul_of_nonneg_left
  · change
      puncturedWholeVorticityKineticMass
          current.physical.nextContact.physicalState ≤
        puncturedWholeVorticityKineticMass
          current.physical.contact.physicalState
    exact nextContact_kineticMass_le current.physical
  · exact finiteModeKineticAmbientFactor_nonneg state.modes

end SourceGeneratedStandingPaidStateAt

/-- One exact vertical source transition.  Normalization, next paid state and
clock settlement are stored on the same current material. -/
structure SourceGeneratedStandingPaidAdvanceAt
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) : Type where
  currentPaid : state.paidNormalForm
  nextState : SourceGeneratedStandingPaidStateAt current.next
  waste : Real
  waste_nonneg : 0 ≤ waste
  settlement :
    state.potential = current.physical.nextContact.time.1 +
      nextState.potential + waste

namespace SourceGeneratedStandingPaidAdvanceAt

/-- Same-face settlement.  This is a transporter, not the longitudinal
producer: its `nextState` argument must already contain the next edge's
source-generated payment instruction. -/
def ofSameFace
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current)
    (nextState : SourceGeneratedStandingPaidStateAt current.next)
    (modes_eq : nextState.modes = state.modes)
    (charge_eq : nextState.charge = state.charge)
    (statePotential : state.potential =
      standingPaidKineticCapacityPotential
        current state.modes state.charge)
    (nextPotential : nextState.potential =
      standingPaidKineticCapacityPotential
        current.next nextState.modes nextState.charge) :
    SourceGeneratedStandingPaidAdvanceAt state := by
  let massDropPayment :=
    (finiteStateVorticityCoefficientEnstrophy state.modes
          current.physical.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy state.modes
          current.physical.contact.physicalState) / state.charge -
      current.physical.nextContact.time.1
  let capacityDrop :=
    (standingPaidFaceCapacity current state.modes -
      standingPaidFaceCapacity current.next state.modes) / state.charge
  have massDropPaymentNonneg : 0 ≤ massDropPayment := by
    dsimp only [massDropPayment]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ state.charge_pos).2
    simpa only [mul_comm] using state.edgePayment
  have capacityDropNonneg : 0 ≤ capacityDrop := by
    dsimp only [capacityDrop]
    exact div_nonneg
      (sub_nonneg.mpr state.capacity_next_le) state.charge_pos.le
  have faceMassNextEq :
      standingPaidFaceMass current.next state.modes =
        finiteStateVorticityCoefficientEnstrophy state.modes
          current.physical.nextContact.physicalState := by
    unfold standingPaidFaceMass
    unfold GeneratedWholeRestartRuntimeCurrent.next
    rw [next_contact]
    rfl
  exact
    { currentPaid := state.generatedPaidNormalForm
      nextState := nextState
      waste := massDropPayment + capacityDrop
      waste_nonneg := add_nonneg massDropPaymentNonneg capacityDropNonneg
      settlement := by
        rw [statePotential, nextPotential]
        unfold standingPaidKineticCapacityPotential
        rw [modes_eq, charge_eq]
        rw [faceMassNextEq]
        unfold standingPaidFaceMass
        dsimp only [massDropPayment, capacityDrop]
        field_simp [state.charge_pos.ne']
        ring }

end SourceGeneratedStandingPaidAdvanceAt

/-- Total vertical compiler result.  Classical choice is used only inside
the full advance fibre: it cannot choose a next state unless that state,
same-material normalization and exact clock settlement are all present. -/
inductive SourceGeneratedStandingPaidTransitionAt
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) : Type
  | advanced (advance : SourceGeneratedStandingPaidAdvanceAt state)
  | incompatible
      (noAdvance : IsEmpty (SourceGeneratedStandingPaidAdvanceAt state))

noncomputable def sourceGeneratedStandingPaidTransition
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (state : SourceGeneratedStandingPaidStateAt current) :
    SourceGeneratedStandingPaidTransitionAt state := by
  by_cases available : Nonempty (SourceGeneratedStandingPaidAdvanceAt state)
  · exact .advanced (Classical.choice available)
  · exact .incompatible
      ⟨fun advance => available ⟨advance⟩⟩

/-! ## Total root transition and generated local clock state -/

/-- Finite clock state carried by one exact root current. -/
structure SourceGeneratedRootClockStateAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (_state : source.State) : Type where
  potential : Real
  potential_nonneg : 0 ≤ potential

/-- One current-edge clock settlement.  The successor current is already
fixed by the source; `nextClock` is only the dependent clock face installed
on that current. -/
structure SourceGeneratedRootClockAdvanceAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (currentClock : SourceGeneratedRootClockStateAt source state)
    (nextClock : SourceGeneratedRootClockStateAt
      source (source.successor state)) : Type where
  waste : Real
  waste_nonneg : 0 ≤ waste
  settlement :
    currentClock.potential = source.clockAt state +
      nextClock.potential + waste

/-- The source settles the outcome already generated by the root compiler.
Paid and obstruction alternatives all preserve the exact outcome index.
`obstructionIncompatible` is a real contradiction, not a dormant next. -/
inductive SourceGeneratedRootClockSettlementAt
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu)
    (state : source.State)
    (currentClock : SourceGeneratedRootClockStateAt source state)
    (nextClock : SourceGeneratedRootClockStateAt
      source (source.successor state)) :
    NativeFluidMediumRootOperationalOutcomeAt source state → Type
  | exactPayment
      {effect : NativeFluidMediumExactOperationalEffectAt source state}
      {rooted : IncidenceProvenanceAt effect.effect}
      {commutes : effect.arithmeticMaterial.whole =
        effect.arithmeticMaterial.left.parallel
          effect.arithmeticMaterial.right}
      (advance : SourceGeneratedRootClockAdvanceAt
        source state currentClock nextClock) :
      SourceGeneratedRootClockSettlementAt source state currentClock nextClock
        (.exactPayment effect rooted commutes)
  | generatedResidual
      {effect : NativeFluidMediumExactOperationalEffectAt source state}
      {residual : GeneratedParallelResidualAt
        effect.effect effect.arithmeticMaterial}
      {expansion : source.OperationalResidualExpansionAt effect.effect residual}
      {expansion_eq : expansion =
        source.generateOperationalResidualExpansionAt effect.effect residual}
      {payment : NativeFluidMediumResidualPaymentAt effect residual expansion}
      (advance : SourceGeneratedRootClockAdvanceAt
        source state currentClock nextClock) :
      SourceGeneratedRootClockSettlementAt source state currentClock nextClock
        (.generatedResidual effect residual expansion expansion_eq payment)
  | obstructionAlternative
      {obstruction : NativeFluidMediumOperationalObstructionAt source state}
      {demand : SourceGeneratedU7DemandAt
        (nativeFluidMediumU7Producer source) obstruction
          ((nativeFluidMediumU7Producer source).generateDemand obstruction)}
      (advance : SourceGeneratedRootClockAdvanceAt
        source state currentClock nextClock) :
      SourceGeneratedRootClockSettlementAt source state currentClock nextClock
        (.obstruction obstruction demand)
  | obstructionIncompatible
      {obstruction : NativeFluidMediumOperationalObstructionAt source state}
      {demand : SourceGeneratedU7DemandAt
        (nativeFluidMediumU7Producer source) obstruction
          ((nativeFluidMediumU7Producer source).generateDemand obstruction)}
      (incompatible : False) :
      SourceGeneratedRootClockSettlementAt source state currentClock nextClock
        (.obstruction obstruction demand)

namespace SourceGeneratedRootClockSettlementAt

/-- Resolve only the local source vocabulary.  The result keeps the
root-generated successor current and the exact settlement together. -/
def resolved
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    {currentClock : SourceGeneratedRootClockStateAt source state}
    {nextClock : SourceGeneratedRootClockStateAt
      source (source.successor state)}
    {outcome : NativeFluidMediumRootOperationalOutcomeAt source state}
    (settlement : SourceGeneratedRootClockSettlementAt
      source state currentClock nextClock outcome) :
    SourceGeneratedRootClockAdvanceAt
      source state currentClock nextClock := by
  cases settlement with
  | exactPayment advance => exact advance
  | generatedResidual advance => exact advance
  | obstructionAlternative advance => exact advance
  | obstructionIncompatible incompatible => exact False.elim incompatible

end SourceGeneratedRootClockSettlementAt

/-- Finite recursive clock law over one fixed medium root.  The source gives
one initial clock face and one local outcome-indexed transition.  That
transition generates the successor instruction together with the current
settlement; there is no independent future-instruction mouth.  The
framework—not a state-indexed future table—generates the history. -/
structure SourceGeneratedRootClockLaw
    {nu : Viscosity}
    (source : NativeFluidMediumSource nu) : Type 1 where
  ClockInstructionAt : source.State → Type
  clockState : {state : source.State} → ClockInstructionAt state →
    SourceGeneratedRootClockStateAt source state
  initialInstruction : ClockInstructionAt source.initial
  transitionAt : ∀ {state : source.State}
    (instruction : ClockInstructionAt state),
    Σ nextInstruction : ClockInstructionAt (source.successor state),
      SourceGeneratedRootClockSettlementAt source state
        (clockState instruction) (clockState nextInstruction)
        (nativeFluidMediumRootOperationalOutcomeAt source state)

namespace SourceGeneratedRootClockLaw

/-- The successor instruction is generated only by resolving the current
root transition. -/
def nextInstruction
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source)
    {state : source.State}
    (instruction : law.ClockInstructionAt state) :
    law.ClockInstructionAt (source.successor state) :=
  (law.transitionAt instruction).1

/-- Outcome-indexed settlement carried by the same dependent transition that
generates the successor instruction. -/
def transitionSettlement
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source)
    {state : source.State}
    (instruction : law.ClockInstructionAt state) :
    SourceGeneratedRootClockSettlementAt source state
      (law.clockState instruction)
      (law.clockState (law.nextInstruction instruction))
      (nativeFluidMediumRootOperationalOutcomeAt source state) :=
  (law.transitionAt instruction).2

/-- Install the finite instruction seed and one local transition on the exact
living-root process.  The private framework carrier prevents replacement by
a completed stage table. -/
def toGeneratedInvariantLaw
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source) :
    SourceNativeGeneratedInvariantLaw
      (nativeFluidMediumLivingProcess source) :=
  SourceNativeGeneratedInvariantLaw.create
    (process := nativeFluidMediumLivingProcess source)
    (InvariantAt := fun index =>
      law.ClockInstructionAt (source.stateAfter index))
    (initialAt := law.initialInstruction)
    (advanceAt := fun _index instruction =>
      law.nextInstruction instruction)

def generatedHistory
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source) :
    SourceNativeGeneratedInvariantHistoryAt law.toGeneratedInvariantLaw :=
  law.toGeneratedInvariantLaw.generateHistory

def instructionAt
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source) :
    (stage : Nat) → law.ClockInstructionAt (source.stateAfter stage)
  | 0 => law.initialInstruction
  | stage + 1 => law.nextInstruction (law.instructionAt stage)

def clockStateAt
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source)
    (stage : Nat) :
    SourceGeneratedRootClockStateAt source (source.stateAfter stage) :=
  law.clockState (law.instructionAt stage)

def clockAdvanceAt
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source)
    (stage : Nat) :
    SourceGeneratedRootClockAdvanceAt source (source.stateAfter stage)
      (law.clockStateAt stage) (law.clockStateAt (stage + 1)) :=
  (law.transitionSettlement (law.instructionAt stage)).resolved

theorem clockPrefix_add_potential_le_initial
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source) :
    ∀ length : Nat,
      (∑ stage ∈ Finset.range length,
          source.clockAt (source.stateAfter stage)) +
          (law.clockStateAt length).potential ≤
        (law.clockStateAt 0).potential
  | 0 => by simp
  | length + 1 => by
      have prior := law.clockPrefix_add_potential_le_initial length
      have settlement := (law.clockAdvanceAt length).settlement
      have wasteNonneg := (law.clockAdvanceAt length).waste_nonneg
      simp only [Finset.sum_range_succ]
      linarith

theorem clockPrefix_le_initial
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        source.clockAt (source.stateAfter stage)) ≤
      (law.clockStateAt 0).potential := by
  have generated := law.clockPrefix_add_potential_le_initial length
  have terminalNonneg := (law.clockStateAt length).potential_nonneg
  linarith

theorem clock_summable
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    (law : SourceGeneratedRootClockLaw source) :
    Summable fun stage => source.clockAt (source.stateAfter stage) := by
  apply summable_of_sum_range_le
  · intro stage
    exact (source.clock_pos (source.stateAfter stage)).le
  · exact law.clockPrefix_le_initial

/-- The fixed classical whole-restart root exposes its physical contact clock
as the root clock.  The framework fold restores the finite initial term. -/
theorem classicalWholeRestart_contactTime_summable
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedRootClockLaw
      (classicalWholeRestartMediumSource initial)) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  have nextSummable := law.clock_summable
  have nextSummable' : Summable fun stage =>
      (run initial stage).nextContact.time.1 := by
    apply nextSummable.congr
    intro stage
    rw [classicalWholeRestartMediumSource_stateAfter]
    rfl
  have shifted : Summable fun stage =>
      (run initial (stage + 1)).contact.time.1 := by
    simpa only [run_succ, next_contact] using nextSummable'
  exact (summable_nat_add_iff 1).mp shifted

end SourceGeneratedRootClockLaw

/-- The finite vertical source law.  There is no field containing
`∀ n, paidStateAt n`; the whole history is generated by this one local
advance. -/
structure SourceGeneratedStandingPaidLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type where
  initialPaidState : SourceGeneratedStandingPaidStateAt (runRuntime initial 0)
  advancePaidState :
    {current : GeneratedWholeRestartRuntimeCurrent nu} →
    (state : SourceGeneratedStandingPaidStateAt current) →
      SourceGeneratedStandingPaidAdvanceAt state

namespace SourceGeneratedStandingPaidLaw

def paidStateAt
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidLaw initial) :
    (stage : Nat) →
      SourceGeneratedStandingPaidStateAt (runRuntime initial stage)
  | 0 => law.initialPaidState
  | stage + 1 => (law.advancePaidState (law.paidStateAt stage)).nextState

def paidAdvanceAt
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidLaw initial)
    (stage : Nat) :
    SourceGeneratedStandingPaidAdvanceAt (law.paidStateAt stage) :=
  law.advancePaidState (law.paidStateAt stage)

theorem nextClockPrefix_add_potential_le_initial
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidLaw initial) :
    ∀ length : Nat,
      (∑ stage ∈ Finset.range length,
          (run initial stage).nextContact.time.1) +
          (law.paidStateAt length).potential ≤
        law.initialPaidState.potential
  | 0 => by simp [paidStateAt]
  | length + 1 => by
      have prior := law.nextClockPrefix_add_potential_le_initial length
      have settlement := (law.paidAdvanceAt length).settlement
      have wasteNonneg := (law.paidAdvanceAt length).waste_nonneg
      simp only [Finset.sum_range_succ]
      change
        (∑ stage ∈ Finset.range length,
            (run initial stage).nextContact.time.1) +
            (run initial length).nextContact.time.1 +
            (law.paidStateAt (length + 1)).potential ≤ _
      change
        (law.paidStateAt length).potential =
          (run initial length).nextContact.time.1 +
            (law.paidStateAt (length + 1)).potential +
              (law.paidAdvanceAt length).waste at settlement
      linarith

theorem nextClockPrefix_le_initial
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidLaw initial)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        (run initial stage).nextContact.time.1) ≤
      law.initialPaidState.potential := by
  have generated := law.nextClockPrefix_add_potential_le_initial length
  have terminalNonneg := (law.paidStateAt length).potential_nonneg
  linarith

theorem contactTime_summable
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidLaw initial) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  have nextSummable : Summable fun stage =>
      (run initial stage).nextContact.time.1 := by
    apply summable_of_sum_range_le
    · intro stage
      exact (run initial stage).nextContact.time_pos.le
    · exact law.nextClockPrefix_le_initial
  have shifted : Summable fun stage =>
      (run initial (stage + 1)).contact.time.1 := by
    simpa only [run_succ, next_contact] using nextSummable
  exact (summable_nat_add_iff 1).mp shifted

end SourceGeneratedStandingPaidLaw

/-! ## Source-owned medium instruction -/

/-- The genuinely extensible vertical law.  `PayingInstructionAt` is the
finite medium coordinate which a concrete source must preserve.  Its paid
face is only a dependent projection; the instruction may additionally carry
phase, scale or constitutive coordinates needed to generate its successor. -/
structure SourceGeneratedStandingPaidMediumLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 1 where
  PayingInstructionAt : GeneratedWholeRestartRuntimeCurrent nu → Type
  paidState : {current : GeneratedWholeRestartRuntimeCurrent nu} →
    PayingInstructionAt current → SourceGeneratedStandingPaidStateAt current
  initialInstruction : PayingInstructionAt (runRuntime initial 0)
  advanceInstruction : {current : GeneratedWholeRestartRuntimeCurrent nu} →
    PayingInstructionAt current → PayingInstructionAt current.next
  advancePaidState : {current : GeneratedWholeRestartRuntimeCurrent nu} →
    (instruction : PayingInstructionAt current) →
      SourceGeneratedStandingPaidAdvanceAt (paidState instruction)
  advance_nextState : {current : GeneratedWholeRestartRuntimeCurrent nu} →
    (instruction : PayingInstructionAt current) →
      (advancePaidState instruction).nextState =
        paidState (advanceInstruction instruction)

namespace SourceGeneratedStandingPaidMediumLaw

def instructionAt
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial) :
    (stage : Nat) → law.PayingInstructionAt (runRuntime initial stage)
  | 0 => law.initialInstruction
  | stage + 1 => law.advanceInstruction (law.instructionAt stage)

def paidStateAt
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial)
    (stage : Nat) :
    SourceGeneratedStandingPaidStateAt (runRuntime initial stage) :=
  law.paidState (law.instructionAt stage)

def paidAdvanceAt
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial)
    (stage : Nat) :
    SourceGeneratedStandingPaidAdvanceAt (law.paidStateAt stage) :=
  law.advancePaidState (law.instructionAt stage)

@[simp] theorem paidStateAt_succ
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial)
    (stage : Nat) :
    (law.paidAdvanceAt stage).nextState = law.paidStateAt (stage + 1) :=
  law.advance_nextState (law.instructionAt stage)

theorem nextClockPrefix_add_potential_le_initial
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial) :
    ∀ length : Nat,
      (∑ stage ∈ Finset.range length,
          (run initial stage).nextContact.time.1) +
          (law.paidStateAt length).potential ≤
        (law.paidStateAt 0).potential
  | 0 => by simp
  | length + 1 => by
      have prior := law.nextClockPrefix_add_potential_le_initial length
      have settlement := (law.paidAdvanceAt length).settlement
      have wasteNonneg := (law.paidAdvanceAt length).waste_nonneg
      rw [law.paidStateAt_succ length] at settlement
      change
        (law.paidStateAt length).potential =
          (run initial length).nextContact.time.1 +
            (law.paidStateAt (length + 1)).potential +
              (law.paidAdvanceAt length).waste at settlement
      simp only [Finset.sum_range_succ]
      linarith

theorem nextClockPrefix_le_initial
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        (run initial stage).nextContact.time.1) ≤
      (law.paidStateAt 0).potential := by
  have generated := law.nextClockPrefix_add_potential_le_initial length
  have terminalNonneg := (law.paidStateAt length).potential_nonneg
  linarith

theorem contactTime_summable
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  have nextSummable : Summable fun stage =>
      (run initial stage).nextContact.time.1 := by
    apply summable_of_sum_range_le
    · intro stage
      exact (run initial stage).nextContact.time_pos.le
    · exact law.nextClockPrefix_le_initial
  have shifted : Summable fun stage =>
      (run initial (stage + 1)).contact.time.1 := by
    simpa only [run_succ, next_contact] using nextSummable
  exact (summable_nat_add_iff 1).mp shifted

/-- Compatibility embedding of the face-only law.  Concrete work should
target the richer medium law; this embedding exists only so the generic
clock algebra has one canonical specialization. -/
def ofPaidStateLaw
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidLaw initial) :
    SourceGeneratedStandingPaidMediumLaw initial where
  PayingInstructionAt := SourceGeneratedStandingPaidStateAt
  paidState := fun state => state
  initialInstruction := law.initialPaidState
  advanceInstruction := fun state =>
    (law.advancePaidState state).nextState
  advancePaidState := law.advancePaidState
  advance_nextState := fun _ => rfl

end SourceGeneratedStandingPaidMediumLaw

/-! ## The paid state as the authoritative medium carrier -/

/-- The authoritative refinement of the classical whole-restart medium.
Its state is the dependent pair of the exact runtime occurrence and the
paying instruction generated at that occurrence.  The physical update is
still the original `current.next`; only `advancePaidState` can construct the
dependent fibre over that successor. -/
def standingPaidWholeRestartMediumSource
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial) :
    NativeFluidMediumSource nu where
  State := Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
    law.PayingInstructionAt current
  InternalState := PUnit
  Action := PUnit
  initial := ⟨runRuntime initial 0, law.initialInstruction⟩
  actionAt := fun _ => PUnit.unit
  evolve := fun state _ =>
    ⟨state.1.next, law.advanceInstruction state.2⟩
  OperationalEffectAt := fun state =>
    SourceGeneratedStandingPaidStateAt state.1
  operationalEffectAt := fun state => law.paidState state.2
  operationalArithmeticMaterialAt := fun paid =>
    paid.material.arithmeticMaterial
  operationalNetEnstrophyDebitAt := fun paid =>
    paid.material.rawValuedMaterial.netEnstrophyDebit
  operationalContactTimeAt := fun paid => paid.material.contactTime
  operationalContactTime_pos := fun paid => paid.material.contactTime_pos
  OperationalResidualExpansionAt := fun _paid _residual => PUnit
  generateOperationalResidualExpansionAt := fun _paid _residual => PUnit.unit
  operationalResidualExpansionDebitAt := fun paid _residual _expansion =>
    paid.faceDebit
  operationalResidualExpansionDebit_nonneg :=
    fun paid _residual _expansion => paid.faceDebit_pos.le
  vorticityAt := fun state => state.1.physical.contact.physicalState
  pressureAt := fun _ => 0
  internalAt := fun _ => PUnit.unit
  zeroInternal := PUnit.unit
  constitutiveStressOf := fun _ _ => 0
  constitutiveStress_zero := fun _ => rfl
  vorticityTangentOf := fun state _ =>
    classicalWholeNSVorticityTangent nu
      state.1.physical.contact.physicalState
  action_constitutive := by
    intro state
    rw [nativeFluidConstitutiveVorticityAction_zero, add_zero]
  vorticity_transverse := fun state =>
    wholeRestartPhysicalTransverse state.1.physical.contact
  vorticity_reality := fun state =>
    wholeRestartPhysicalReality state.1.physical.contact
  clockAt := fun state => state.1.physical.nextContact.time.1
  potentialAt := fun state =>
    puncturedWholeVorticityKineticMass
      state.1.physical.contact.physicalState
  densityAt := fun state =>
    2 * nu.coeff * successorMeanWholeVorticityDensity state.1.physical 0
  scaleAt := fun state =>
    wholeRestartCoefficientCeiling state.1.physical.contact
  clock_pos := fun state => state.1.physical.nextContact.time_pos
  density_nonneg := fun state =>
    mul_nonneg (mul_nonneg (by norm_num) nu.coeff_pos.le)
      (successorMeanWholeVorticityDensity_nonneg state.1.physical 0)
  temporal_action := by
    intro state
    have balance :=
      (sourceGeneratedWholeRestartKineticEntropyDefect state.1.physical 0).balance
    have clockLaw :=
      kineticDefect_eq_clock_mul_nativeDensity state.1.physical 0
    change
      puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState -
          puncturedWholeVorticityKineticMass
            state.1.physical.next.contact.physicalState =
        state.1.physical.nextContact.time.1 *
          (2 * nu.coeff *
            successorMeanWholeVorticityDensity state.1.physical 0)
    simpa only [wholeRestartKineticEntropy, wholeRestartKineticDefect,
      wholeRestartNextKineticDissipationPayment, run_zero, run_succ,
      GeneratedWholeRestartCurrent.next] using
      (show
        wholeRestartKineticEntropy state.1.physical 0 -
            wholeRestartKineticEntropy state.1.physical 1 =
          (run state.1.physical 1).contact.time.1 *
            (2 * nu.coeff *
              successorMeanWholeVorticityDensity state.1.physical 0) by
        rw [← clockLaw]
        linarith [balance])
  PatchAt := fun state =>
    { patch : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
        law.PayingInstructionAt current // patch = state }
  BoundaryAt := fun _ => ComplexVorticityHilbertState
  initialPatch := ⟨⟨runRuntime initial 0, law.initialInstruction⟩, rfl⟩
  advancePatch := by
    intro state patch
    rcases patch with ⟨patch, rfl⟩
    exact
      ⟨⟨patch.1.next,
          law.advanceInstruction patch.2⟩, rfl⟩
  restrictPatch := fun state _ => ⟨state, rfl⟩
  advance_restricts := fun _ patch => Subtype.ext patch.2.symm
  outgoingBoundaryAt := fun _ patch =>
    patch.1.1.physical.contact.physicalState
  incomingBoundaryAt := fun _ targetPatch =>
    targetPatch.1.1.physical.initialState
  boundary_commutes := by
    intro state patch
    rcases patch with ⟨patch, rfl⟩
    rfl

theorem standingPaidWholeRestartMediumSource_stateAfter_eq
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial) :
    ∀ stage : Nat,
      (standingPaidWholeRestartMediumSource law).stateAfter stage =
        ⟨runRuntime initial stage, law.instructionAt stage⟩
  | 0 => rfl
  | stage + 1 => by
      rw [NativeFluidMediumSource.stateAfter_succ,
        standingPaidWholeRestartMediumSource_stateAfter_eq law stage]
      rfl

/-- The vertical state is not an external recurrence court: its material,
paid-potential settlement and successor are read from one exact occurrence
of the authoritative medium living root. -/
theorem standingPaidWholeRestart_run_rootStep_factorizes
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingPaidMediumLaw initial)
    (stage : Nat) :
    let source := standingPaidWholeRestartMediumSource law
    let visit : SourceNativeTemporalVisitAt
        (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot :=
      .finite (nativeFluidMediumRootVisit source stage)
    HEq (nativeFluidMediumExactOperationalEffectAt source
          (source.stateAfter stage)).effect
        (law.paidStateAt stage) ∧
      ((nativeFluidMediumLivingRoot source).generatedNextCurrentAt visit
        ).visit.current = source.stateAfter (stage + 1) ∧
      (law.paidStateAt stage).potential =
        (run initial stage).nextContact.time.1 +
          (law.paidStateAt (stage + 1)).potential +
            (law.paidAdvanceAt stage).waste := by
  dsimp only
  have stateEq :=
    standingPaidWholeRestartMediumSource_stateAfter_eq law stage
  refine ⟨?_, ?_, ?_⟩
  · rw [stateEq]
    rfl
  · change
      (standingPaidWholeRestartMediumSource law).successor
          (nativeFluidMediumRootVisit
            (standingPaidWholeRestartMediumSource law) stage).current =
        (standingPaidWholeRestartMediumSource law).successor
          ((standingPaidWholeRestartMediumSource law).stateAfter stage)
    rw [nativeFluidMediumRootVisit_current]
  · have settlement := (law.paidAdvanceAt stage).settlement
    rw [law.paidStateAt_succ stage] at settlement
    change
      (law.paidStateAt stage).potential =
        (run initial stage).nextContact.time.1 +
          (law.paidStateAt (stage + 1)).potential +
            (law.paidAdvanceAt stage).waste at settlement
    exact settlement

/-! ## Concrete initial vertical states -/

/-- Final source-selected viscosity for the paid-medium route. -/
def concreteCounterexampleViscosity : Viscosity :=
  RationalVorticityEvaluator.butterflyGainViscosity

/-- Final source-selected initial current.  The viscosity, receipt, short
source window and actual contact are all generated upstream. -/
def concreteCounterexampleInitial :
    GeneratedWholeRestartCurrent concreteCounterexampleViscosity :=
  stackedShortCurrent

theorem stackedInitialEdgePayment :
    (runRuntime stackedShortCurrent 0).physical.nextContact.time.1 *
        (3998 / 1000 : Real) ≤
      finiteStateVorticityCoefficientEnstrophy stackedSidebandModes
          (runRuntime stackedShortCurrent 0).physical.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy stackedSidebandModes
          (runRuntime stackedShortCurrent 0).physical.contact.physicalState := by
  rw [show (runRuntime stackedShortCurrent 0).physical = stackedShortCurrent by
    rfl]
  have paid := stackedRunPayingFaceMass_edge_payment 0
    butterflyStackedKineticInvariantAt_zero
  unfold stackedRunPayingFaceMass at paid
  rw [show (0 : Nat) + 1 = 1 by omega, run_succ, next_contact,
    run_zero] at paid
  rw [mul_comm]
  convert paid using 1 <;> rfl

def stackedInitialPaidState : SourceGeneratedStandingPaidStateAt
    (runRuntime stackedShortCurrent 0) where
  modes := stackedSidebandModes
  zeroNotMem := stackedSidebandCone.zeroNotMem
  charge := 3998 / 1000
  charge_pos := by norm_num
  edgePayment := stackedInitialEdgePayment
  potential := standingPaidKineticCapacityPotential
    (runRuntime stackedShortCurrent 0) stackedSidebandModes (3998 / 1000)
  potential_nonneg := by
    unfold standingPaidKineticCapacityPotential
    exact div_nonneg
      (sub_nonneg.mpr (standingPaidFaceMass_le_capacity
        (runRuntime stackedShortCurrent 0) stackedSidebandModes
        stackedSidebandCone.zeroNotMem)) (by norm_num)

theorem stackedStageOneEdgePayment :
    (runRuntime stackedShortCurrent 1).physical.nextContact.time.1 *
        (3998 / 1000 : Real) ≤
      finiteStateVorticityCoefficientEnstrophy stackedSidebandModes
          (runRuntime stackedShortCurrent 1).physical.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy stackedSidebandModes
          (runRuntime stackedShortCurrent 1).physical.contact.physicalState := by
  have paid := stackedRunPayingFaceMass_edge_payment 1
    butterflyStackedKineticInvariantAt_one
  unfold stackedRunPayingFaceMass at paid
  rw [show (runRuntime stackedShortCurrent 1).physical =
    run stackedShortCurrent 1 by rfl]
  rw [mul_comm]
  convert paid using 1 <;> rfl

def stackedStageOnePaidState : SourceGeneratedStandingPaidStateAt
    (runRuntime stackedShortCurrent 1) where
  modes := stackedSidebandModes
  zeroNotMem := stackedSidebandCone.zeroNotMem
  charge := 3998 / 1000
  charge_pos := by norm_num
  edgePayment := stackedStageOneEdgePayment
  potential := standingPaidKineticCapacityPotential
    (runRuntime stackedShortCurrent 1) stackedSidebandModes (3998 / 1000)
  potential_nonneg := by
    unfold standingPaidKineticCapacityPotential
    exact div_nonneg
      (sub_nonneg.mpr (standingPaidFaceMass_le_capacity
        (runRuntime stackedShortCurrent 1) stackedSidebandModes
        stackedSidebandCone.zeroNotMem)) (by norm_num)

def stackedInitialPaidAdvance :
    SourceGeneratedStandingPaidAdvanceAt stackedInitialPaidState :=
  SourceGeneratedStandingPaidAdvanceAt.ofSameFace
    stackedInitialPaidState stackedStageOnePaidState rfl rfl rfl rfl

/-
def stackedStageTwoPaidState : SourceGeneratedStandingPaidStateAt
    (runRuntime stackedShortCurrent 2) :=
  stackedPaidStateAt 2 butterflyStackedKineticInvariantAt_two

def stackedStageOnePaidAdvance :
    SourceGeneratedStandingPaidAdvanceAt stackedStageOnePaidState :=
  SourceGeneratedStandingPaidAdvanceAt.ofSameFace
    stackedStageOnePaidState stackedStageTwoPaidState rfl rfl
-/

/-- Exact remaining longitudinal responsibility.  Its concrete inhabitant
must select a finite source-owned instruction type, generate that instruction
at the initial occurrence and preserve it by one actual local advance. -/
abbrev ButterflyStandingPaidMediumLaw :=
  SourceGeneratedStandingPaidMediumLaw concreteCounterexampleInitial

end
end ThreeDimensionalVorticityCoefficientStandingPaidMediumState
end NavierStokes
end SaturationMonoid
