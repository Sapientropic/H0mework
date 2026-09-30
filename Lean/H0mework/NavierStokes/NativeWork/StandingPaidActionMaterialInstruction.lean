import H0mework.NavierStokes.Accumulation.StandingPaidMediumState
import H0mework.NavierStokes.Accumulation.FiniteSupportWholeActionTube
import H0mework.NavierStokes.NativeWorkButterfly.SidebandOrthantInward
import H0mework.NavierStokes.NativeWorkButterfly.ParametricOrientedCell
import H0mework.NavierStokes.NativeWork.FullReceiptNormalizedWorkEulerEscrow

/-!
# Source-owned action material in the standing paid medium

The paid root effect may observe Fourier modes beyond the arithmetic
coefficient-level anchor.  This module installs the missing vertical
coordinate which makes that observation source generated: one finite action
radius, its current capture law, its quadratic action closure and its unique
local successor radius.

The complete whole tangent is split exactly into the action of the current
finite projection and one named source residual.  No residual bound or next
paid face is accepted here; those are the remaining constitutive coordinates
which a concrete paying instruction must regenerate.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticGeneration
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace
open ThreeDimensionalVorticityCoefficientFullReceiptNormalizedWorkEulerEscrow
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptNativeFluxSettlement
open ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube
open ThreeDimensionalVorticityCoefficientWholeActionTube
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
open RationalVorticityEvaluator.ButterflySidebandOrthantInward
open RationalVorticityEvaluator.ButterflyParametricOrientedCell

noncomputable section

private theorem wholeRestartModes_mono
    {smaller larger : Nat} (radiusLe : smaller ≤ larger) :
    wholeRestartModes smaller ⊆ wholeRestartModes larger := by
  intro wave waveMem
  rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
    Finset.mem_erase] at waveMem ⊢
  exact ⟨waveMem.1, integerWaveFrequencyCube_mono radiusLe waveMem.2⟩

def nonzeroActionClosure
    (modes : Finset IntegerWavevector) : Finset IntegerWavevector :=
  (wholeFiniteSupportActionModes modes).erase 0

/-- A finite action carrier generated at one exact runtime occurrence.  Its
radius captures the current receipt at a source-selected tolerance. -/
structure SourceGeneratedActionMaterialInstructionAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartRuntimeCurrent nu) : Type where
  floor : Real
  floor_pos : 0 < floor
  radius : Nat
  capture_le :
    currentFullReceiptResolvedCaptureRadius current.physical
        (currentFullReceiptScaleTolerance current.physical floor floor_pos) ≤
      radius
  cellScale : Nat
  cellScale_two : 2 ≤ cellScale
  cellScale_four : 4 ≤ cellScale
  cellScale_le_radius : cellScale ≤ radius

namespace SourceGeneratedActionMaterialInstructionAt

def tolerance
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    {value : Real // 0 < value} :=
  currentFullReceiptScaleTolerance current.physical
    instruction.floor instruction.floor_pos

def modes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    Finset IntegerWavevector :=
  wholeRestartModes instruction.radius

theorem modes_zeroNotMem
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    (0 : IntegerWavevector) ∉ instruction.modes :=
  zero_not_mem_puncturedIntegerWaveFrequencyCube instruction.radius

theorem currentTail_lt
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    wholeTailVorticityMass instruction.modes
        current.physical.contact.physicalState <
      instruction.tolerance.1 := by
  exact current_fullReceipt_initialTail_lt_of_captureRadius_le
    current.physical instruction.tolerance instruction.radius
      instruction.capture_le

/-- The unique local action-radius update.  It reads the already generated
physical successor, captures its receipt and retains the entire quadratic
action closure of the current carrier. -/
def next
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    SourceGeneratedActionMaterialInstructionAt current.next where
  floor := instruction.floor
  floor_pos := instruction.floor_pos
  radius := max
    (currentFullReceiptResolvedCaptureRadius current.next.physical
      (currentFullReceiptScaleTolerance current.next.physical
        instruction.floor instruction.floor_pos))
    (2 * instruction.radius)
  capture_le := le_max_left _ _
  cellScale := 2 * instruction.cellScale
  cellScale_two := by
    have scaleTwo := instruction.cellScale_two
    omega
  cellScale_four := by
    have scaleFour := instruction.cellScale_four
    omega
  cellScale_le_radius :=
    (Nat.mul_le_mul_left 2 instruction.cellScale_le_radius).trans
      (le_max_right _ _)

@[simp] theorem next_floor
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.next.floor = instruction.floor := rfl

theorem doubleRadius_le_next
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    2 * instruction.radius ≤ instruction.next.radius :=
  le_max_right _ _

/-- Every nonzero output emitted by the current projected NS action is
already a cell of the compiler-owned next action material. -/
theorem actionClosure_subset_nextModes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    nonzeroActionClosure instruction.modes ⊆
      instruction.next.modes := by
  have closureToDouble :
      nonzeroActionClosure instruction.modes ⊆
        wholeRestartModes (2 * instruction.radius) := by
    simpa only [modes, wholeRestartModes,
      nonzeroActionClosure] using
      (nonzeroWholeActionClosure_puncturedCube_subset_doubled
        instruction.radius)
  exact closureToDouble.trans
    (wholeRestartModes_mono instruction.doubleRadius_le_next)

def projectedState
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    ComplexVorticityHilbertState :=
  complexSharpSupportProjection instruction.modes
    current.physical.contact.physicalState

def projectedTangent
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    ComplexVorticityHilbertState :=
  wholeFiniteSupportActionState nu.coeff instruction.modes
    instruction.projectedState

/-- Evolution-sensitive coordinate still missing from the finite action
carrier: the exact whole NS tangent minus the current projected action. -/
def actionResidual
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    NativeFluidVorticityTangent :=
  classicalWholeNSVorticityTangent nu
      current.physical.contact.physicalState -
    instruction.projectedTangent

theorem wholeTangent_eq_projected_add_residual
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    classicalWholeNSVorticityTangent nu
        current.physical.contact.physicalState =
      instruction.projectedTangent + instruction.actionResidual := by
  unfold actionResidual
  funext wave
  change
    classicalWholeNSVorticityTangent nu
        current.physical.contact.physicalState wave =
      instruction.projectedTangent wave +
        (classicalWholeNSVorticityTangent nu
            current.physical.contact.physicalState wave -
          instruction.projectedTangent wave)
  abel

theorem projectedState_supported
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ instruction.modes) :
    instruction.projectedState wave = 0 := by
  simp [projectedState, complexSharpSupportProjection_apply, waveNotMem]

theorem projectedState_transverse
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    WholeStateTransverse instruction.projectedState := by
  intro wave
  by_cases waveMem : wave ∈ instruction.modes
  · exact complexSharpSupportProjection_transverse _ _
      current.physical.contact.transverse wave waveMem
  · rw [instruction.projectedState_supported wave waveMem]
    simp

theorem projectedTangent_zero
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.projectedTangent 0 = 0 := by
  unfold projectedTangent
  rw [wholeFiniteSupportActionState_apply_eq_wholeTangent
    nu.coeff instruction.modes instruction.projectedState
    instruction.projectedState_supported]
  apply wholeLatticeVorticityFourierTangentAt_zero
  · exact instruction.projectedState_transverse
  · exact instruction.projectedState_supported 0
      instruction.modes_zeroNotMem

theorem projectedTangent_supported_next
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ instruction.next.modes) :
    instruction.projectedTangent wave = 0 := by
  by_cases waveZero : wave = 0
  · simpa only [waveZero] using instruction.projectedTangent_zero
  · apply wholeFiniteSupportActionState_supported
      nu.coeff instruction.modes instruction.projectedState wave
    intro waveAction
    exact waveNotMem (instruction.actionClosure_subset_nextModes
      (Finset.mem_erase.mpr ⟨waveZero, waveAction⟩))

end SourceGeneratedActionMaterialInstructionAt

/-! ## Exact y-cell / complement action decomposition -/

def SourceGeneratedActionMaterialInstructionAt.dyadicX
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Rat :=
  (instruction.cellScale : Rat) ^ 2 / 64

def SourceGeneratedActionMaterialInstructionAt.dyadicZ
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Rat :=
  -15 * instruction.dyadicX

def SourceGeneratedActionMaterialInstructionAt.dyadicY
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Rat :=
  -instruction.dyadicX

def SourceGeneratedActionMaterialInstructionAt.dyadicW
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Rat :=
  15 * instruction.dyadicX

theorem SourceGeneratedActionMaterialInstructionAt.dyadicX_pos
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    0 < instruction.dyadicX := by
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicX
  have scalePos : (0 : Rat) < instruction.cellScale := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2)
      instruction.cellScale_two)
  positivity

def SourceGeneratedActionMaterialInstructionAt.dyadicYCellState
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    ComplexVorticityHilbertState :=
  yCellPhysicalState (instruction.cellScale : Int)
    (-1) instruction.dyadicX instruction.dyadicZ
      instruction.dyadicY instruction.dyadicW

theorem SourceGeneratedActionMaterialInstructionAt.dyadicYCellState_transverse
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    WholeStateTransverse instruction.dyadicYCellState := by
  apply yCellPhysicalState_transverse
  exact_mod_cast instruction.cellScale_two

@[simp] theorem SourceGeneratedActionMaterialInstructionAt.next_cellScale
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.next.cellScale = 2 * instruction.cellScale :=
  rfl

def SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    IntegerWavevector :=
  axisWave (2 * (instruction.cellScale : Int))

def SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    IntegerWavevector :=
  instruction.dyadicChildAxis + pumpY

def SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    IntegerWavevector :=
  instruction.dyadicChildAxis - pumpY

def SourceGeneratedActionMaterialInstructionAt.dyadicChildModes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    Finset IntegerWavevector :=
  {instruction.dyadicChildAxis,
    instruction.dyadicChildPlus,
    instruction.dyadicChildMinus}

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis_ne_zero
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildAxis ≠ 0 := by
  intro equality
  have xEq := congrArg (fun wave : IntegerWavevector => wave 0) equality
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis at xEq
  simp [axisWave] at xEq
  have scaleTwo := instruction.cellScale_two
  omega

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus_ne_zero
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildPlus ≠ 0 := by
  intro equality
  have xEq := congrArg (fun wave : IntegerWavevector => wave 0) equality
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus
    SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis at xEq
  simp [axisWave, pumpY] at xEq
  have scaleTwo := instruction.cellScale_two
  omega

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus_ne_zero
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildMinus ≠ 0 := by
  intro equality
  have xEq := congrArg (fun wave : IntegerWavevector => wave 0) equality
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus
    SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis at xEq
  simp [axisWave, pumpY] at xEq
  have scaleTwo := instruction.cellScale_two
  omega

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis_ne_plus
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildAxis ≠ instruction.dyadicChildPlus := by
  intro equality
  have yEq := congrArg (fun wave : IntegerWavevector => wave 1) equality
  simp [SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus,
    SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
    axisWave, pumpY] at yEq

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis_ne_minus
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildAxis ≠ instruction.dyadicChildMinus := by
  intro equality
  have yEq := congrArg (fun wave : IntegerWavevector => wave 1) equality
  simp [SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus,
    SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
    axisWave, pumpY] at yEq

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus_ne_minus
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildPlus ≠ instruction.dyadicChildMinus := by
  intro equality
  have yEq := congrArg (fun wave : IntegerWavevector => wave 1) equality
  simp [SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus,
    SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus,
    SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
    axisWave, pumpY] at yEq

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildModes_zeroNotMem
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    (0 : IntegerWavevector) ∉ instruction.dyadicChildModes := by
  simp only [SourceGeneratedActionMaterialInstructionAt.dyadicChildModes,
    Finset.mem_insert, Finset.mem_singleton]
  push_neg
  exact ⟨instruction.dyadicChildAxis_ne_zero.symm,
    instruction.dyadicChildPlus_ne_zero.symm,
    instruction.dyadicChildMinus_ne_zero.symm⟩

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildModes_subset_nextModes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildModes ⊆ instruction.next.modes := by
  intro wave waveMem
  simp only [SourceGeneratedActionMaterialInstructionAt.dyadicChildModes,
    Finset.mem_insert, Finset.mem_singleton] at waveMem
  rw [SourceGeneratedActionMaterialInstructionAt.modes, wholeRestartModes,
    puncturedIntegerWaveFrequencyCube, Finset.mem_erase]
  refine ⟨?_, ?_⟩
  · rcases waveMem with rfl | rfl | rfl
    · exact instruction.dyadicChildAxis_ne_zero
    · exact instruction.dyadicChildPlus_ne_zero
    · exact instruction.dyadicChildMinus_ne_zero
  · rw [integerWaveFrequencyCube, Fintype.mem_piFinset]
    intro coordinate
    rw [Finset.mem_Icc]
    have scaleLeRadius := instruction.cellScale_le_radius
    have doubleRadiusLeNext := instruction.doubleRadius_le_next
    have doubleScaleLeNext : 2 * instruction.cellScale ≤
        instruction.next.radius :=
      (Nat.mul_le_mul_left 2 scaleLeRadius).trans doubleRadiusLeNext
    have castLe : (2 * instruction.cellScale : Nat) ≤
        instruction.next.radius := doubleScaleLeNext
    have castLeInt : ((2 * instruction.cellScale : Nat) : Int) ≤
        (instruction.next.radius : Int) := by
      exact_mod_cast castLe
    have scaleTwo := instruction.cellScale_two
    have oneLeNext : (1 : Int) ≤ (instruction.next.radius : Int) := by
      exact_mod_cast (show 1 ≤ instruction.next.radius by omega)
    have nextNonneg : (0 : Int) ≤ (instruction.next.radius : Int) :=
      Int.ofNat_nonneg _
    rcases waveMem with rfl | rfl | rfl <;>
      fin_cases coordinate <;>
      simp [SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
        SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus,
        SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus,
        axisWave, pumpY] <;>
      omega

theorem SourceGeneratedActionMaterialInstructionAt.next_projectedState_eq_target_on_child
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ instruction.dyadicChildModes) :
    instruction.next.projectedState wave =
      current.physical.nextContact.physicalState wave := by
  unfold SourceGeneratedActionMaterialInstructionAt.projectedState
  rw [complexSharpSupportProjection_apply,
    if_pos (instruction.dyadicChildModes_subset_nextModes waveMem)]
  rfl

def SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (rows : IntegerWavevector → ComplexCoordinateVector) : Real :=
  (rows instruction.dyadicChildAxis 1).re +
    (rows instruction.dyadicChildPlus 0).re -
    (rows instruction.dyadicChildPlus 2).re +
    (rows instruction.dyadicChildMinus 0).re -
    (rows instruction.dyadicChildMinus 2).re

def SourceGeneratedActionMaterialInstructionAt.dyadicChildReadout
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (state : ComplexVorticityHilbertState) : Real :=
  instruction.dyadicChildReadoutOf state

def SourceGeneratedActionMaterialInstructionAt.dyadicCoreCharge
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  instruction.dyadicChildReadoutOf
    (wholeLatticeVorticityFourierTangentAt nu.coeff
      instruction.dyadicYCellState)

theorem SourceGeneratedActionMaterialInstructionAt.dyadicCoreRows_oriented
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    0 < (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildAxis 1).re ∧
      0 < (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildPlus 0).re ∧
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildPlus 2).re < 0 ∧
      0 < (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildMinus 0).re ∧
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildMinus 2).re < 0 := by
  let m : Int := instruction.cellScale
  have mTwo : (2 : Int) ≤ m := by
    dsimp only [m]
    exact_mod_cast instruction.cellScale_two
  let x := instruction.dyadicX
  let z := instruction.dyadicZ
  let y := instruction.dyadicY
  let w := instruction.dyadicW
  have xPos : (0 : Rat) < x := instruction.dyadicX_pos
  have zNeg : z < 0 := by
    dsimp only [z]
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicZ
    linarith
  have yNeg : y < 0 := by
    dsimp only [y]
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicY
    linarith
  have wPos : (0 : Rat) < w := by
    dsimp only [w]
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicW
    positivity
  have oriented := yCellAction_childRows_oriented m mTwo
    (-1) (1 / 100) x z y w
    (by norm_num) xPos zNeg yNeg wPos
  have bridge := fun output => yCellAction_toComplex
    butterflyGainViscosity m mTwo (-1) (1 / 100)
      x z y w
      butterflyGainViscosity_scaled output
  have axisPos :
      0 < (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff instruction.dyadicYCellState
          instruction.dyadicChildAxis 1).re := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicYCellState
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    rw [← bridge (axisWave (2 * m))]
    simpa [m, x, z, y, w,
      SourceGeneratedActionMaterialInstructionAt.dyadicYCellState,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
      GaussianRatVector.toComplex, GaussianRat.toComplex] using oriented.1
  have plusZeroPos :
      0 < (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff instruction.dyadicYCellState
          instruction.dyadicChildPlus 0).re := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicYCellState
      SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    rw [← bridge (axisWave (2 * m) + pumpY)]
    simpa [m, x, z, y, w,
      SourceGeneratedActionMaterialInstructionAt.dyadicYCellState,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus,
      GaussianRatVector.toComplex, GaussianRat.toComplex] using oriented.2.1
  have plusTwoNeg :
      (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff instruction.dyadicYCellState
          instruction.dyadicChildPlus 2).re < 0 := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicYCellState
      SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    rw [← bridge (axisWave (2 * m) + pumpY)]
    simpa [m, x, z, y, w,
      SourceGeneratedActionMaterialInstructionAt.dyadicYCellState,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus,
      GaussianRatVector.toComplex, GaussianRat.toComplex] using oriented.2.2.1
  have minusZeroPos :
      0 < (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff instruction.dyadicYCellState
          instruction.dyadicChildMinus 0).re := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicYCellState
      SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    rw [← bridge (axisWave (2 * m) - pumpY)]
    simpa [m, x, z, y, w,
      SourceGeneratedActionMaterialInstructionAt.dyadicYCellState,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus,
      GaussianRatVector.toComplex, GaussianRat.toComplex] using oriented.2.2.2.1
  have minusTwoNeg :
      (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff instruction.dyadicYCellState
          instruction.dyadicChildMinus 2).re < 0 := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicYCellState
      SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    rw [← bridge (axisWave (2 * m) - pumpY)]
    simpa [m, x, z, y, w,
      SourceGeneratedActionMaterialInstructionAt.dyadicYCellState,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
      SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus,
      GaussianRatVector.toComplex, GaussianRat.toComplex] using oriented.2.2.2.2
  exact ⟨axisPos, plusZeroPos, plusTwoNeg, minusZeroPos, minusTwoNeg⟩

theorem SourceGeneratedActionMaterialInstructionAt.dyadicCoreCharge_pos
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    0 < instruction.dyadicCoreCharge := by
  have rows := instruction.dyadicCoreRows_oriented
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicCoreCharge
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
  linarith [rows.1, rows.2.1, rows.2.2.1, rows.2.2.2.1,
    rows.2.2.2.2]

theorem SourceGeneratedActionMaterialInstructionAt.dyadicCoreAxis_le_charge
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildAxis 1).re ≤
      instruction.dyadicCoreCharge := by
  have rows := instruction.dyadicCoreRows_oriented
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicCoreCharge
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
  linarith [rows.2.1, rows.2.2.1, rows.2.2.2.1,
    rows.2.2.2.2]

theorem SourceGeneratedActionMaterialInstructionAt.dyadicCoreAxis_eq
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildAxis 1).re =
      (((4 * (instruction.cellScale : Rat) ^ 2 /
          ((instruction.cellScale : Rat) ^ 2 + 1)) *
        (instruction.dyadicX * instruction.dyadicW +
          instruction.dyadicZ * instruction.dyadicY) : Rat) : Real) := by
  let m : Int := instruction.cellScale
  have mTwo : (2 : Int) ≤ m := by
    dsimp only [m]
    exact_mod_cast instruction.cellScale_two
  have bridge := yCellAction_toComplex butterflyGainViscosity m mTwo
    (-1) (1 / 100) instruction.dyadicX instruction.dyadicZ
      instruction.dyadicY instruction.dyadicW
      butterflyGainViscosity_scaled (axisWave (2 * m))
  have bridgeAt := congrArg
    (fun row : ComplexCoordinateVector => (row 1).re) bridge
  have actionAt := congrArg
    (fun row : GaussianRatVector => row 1)
    (yCellAction_childAxis_eq m mTwo
      (-1) (1 / 100) instruction.dyadicX instruction.dyadicZ
        instruction.dyadicY instruction.dyadicW)
  have realGaussian_toComplex_re (value : Rat) :
      (GaussianRat.toComplex (realGaussian value)).re = (value : Real) := by
    simp [GaussianRat.toComplex, realGaussian]
  calc
    (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildAxis 1).re =
      ((yCellAction m (-1) (1 / 100) instruction.dyadicX
          instruction.dyadicZ instruction.dyadicY instruction.dyadicW
          (axisWave (2 * m))).toComplex 1).re := by
        simpa [m,
          SourceGeneratedActionMaterialInstructionAt.dyadicYCellState,
          SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis]
          using bridgeAt.symm
    _ = (((4 * (m : Rat) ^ 2 / ((m : Rat) ^ 2 + 1)) *
          (instruction.dyadicX * instruction.dyadicW +
            instruction.dyadicZ * instruction.dyadicY) : Rat) : Real) := by
        change
          (GaussianRat.toComplex
            (yCellAction m (-1) (1 / 100) instruction.dyadicX
              instruction.dyadicZ instruction.dyadicY instruction.dyadicW
              (axisWave (2 * m)) 1)).re = _
        rw [actionAt]
        change
          (GaussianRat.toComplex
            (realGaussian
              ((4 * (m : Rat) ^ 2 / ((m : Rat) ^ 2 + 1)) *
                (instruction.dyadicX * instruction.dyadicW +
                  instruction.dyadicZ * instruction.dyadicY)))).re = _
        exact realGaussian_toComplex_re _
    _ = _ := by norm_num [m]

theorem SourceGeneratedActionMaterialInstructionAt.scaleFourth_div_hundred_le_dyadicCoreAxis
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    (instruction.cellScale : Real) ^ 4 / 100 ≤
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff instruction.dyadicYCellState
        instruction.dyadicChildAxis 1).re := by
  rw [instruction.dyadicCoreAxis_eq]
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicZ
    SourceGeneratedActionMaterialInstructionAt.dyadicY
    SourceGeneratedActionMaterialInstructionAt.dyadicW
    SourceGeneratedActionMaterialInstructionAt.dyadicX
  norm_num
  have scaleFour : (4 : Real) ≤ instruction.cellScale := by
    exact_mod_cast instruction.cellScale_four
  have denominatorPos :
      0 < (instruction.cellScale : Real) ^ 2 + 1 := by positivity
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ denominatorPos).2
  ring_nf
  have scaleSq :
      (16 : Real) ≤ (instruction.cellScale : Real) ^ 2 := by
    nlinarith
  have scaleFourthNonneg :
      0 ≤ (instruction.cellScale : Real) ^ 4 := by positivity
  have multiplied :=
    mul_le_mul_of_nonneg_right scaleSq scaleFourthNonneg
  have powerEq :
      (instruction.cellScale : Real) ^ 2 *
          (instruction.cellScale : Real) ^ 4 =
        (instruction.cellScale : Real) ^ 6 := by ring
  rw [powerEq] at multiplied
  nlinarith

theorem SourceGeneratedActionMaterialInstructionAt.scaleFourth_div_hundred_le_dyadicCoreCharge
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    (instruction.cellScale : Real) ^ 4 / 100 ≤
      instruction.dyadicCoreCharge :=
  instruction.scaleFourth_div_hundred_le_dyadicCoreAxis.trans
    instruction.dyadicCoreAxis_le_charge

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildReadout_le_finiteMass_add_five
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (state : ComplexVorticityHilbertState) :
    instruction.dyadicChildReadout state ≤
      finiteStateVorticityCoefficientEnstrophy
          instruction.dyadicChildModes state + 5 := by
  have axisSq :=
    sq_nonneg ((state instruction.dyadicChildAxis 1).re - 1 / 2)
  have plusZeroSq :=
    sq_nonneg ((state instruction.dyadicChildPlus 0).re - 1 / 2)
  have plusTwoSq :=
    sq_nonneg ((state instruction.dyadicChildPlus 2).re + 1 / 2)
  have minusZeroSq :=
    sq_nonneg ((state instruction.dyadicChildMinus 0).re - 1 / 2)
  have minusTwoSq :=
    sq_nonneg ((state instruction.dyadicChildMinus 2).re + 1 / 2)
  have axisPlus := instruction.dyadicChildAxis_ne_plus
  have axisMinus := instruction.dyadicChildAxis_ne_minus
  have plusMinus := instruction.dyadicChildPlus_ne_minus
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildReadout
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
    SourceGeneratedActionMaterialInstructionAt.dyadicChildModes
    finiteStateVorticityCoefficientEnstrophy complexCoordinateAmplitudeSq
  simp [Finset.sum_insert, Finset.sum_singleton, Fin.sum_univ_succ,
    Complex.normSq_apply, axisPlus, axisMinus, plusMinus,
    Ne.symm axisPlus, Ne.symm axisMinus, Ne.symm plusMinus]
  nlinarith [axisSq, plusZeroSq, plusTwoSq, minusZeroSq, minusTwoSq]

theorem SourceGeneratedActionMaterialInstructionAt.neg_dyadicChildReadout_le_finiteMass_add_five
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (state : ComplexVorticityHilbertState) :
    -instruction.dyadicChildReadout state ≤
      finiteStateVorticityCoefficientEnstrophy
          instruction.dyadicChildModes state + 5 := by
  have axisSq :=
    sq_nonneg ((state instruction.dyadicChildAxis 1).re + 1 / 2)
  have plusZeroSq :=
    sq_nonneg ((state instruction.dyadicChildPlus 0).re + 1 / 2)
  have plusTwoSq :=
    sq_nonneg ((state instruction.dyadicChildPlus 2).re - 1 / 2)
  have minusZeroSq :=
    sq_nonneg ((state instruction.dyadicChildMinus 0).re + 1 / 2)
  have minusTwoSq :=
    sq_nonneg ((state instruction.dyadicChildMinus 2).re - 1 / 2)
  have axisPlus := instruction.dyadicChildAxis_ne_plus
  have axisMinus := instruction.dyadicChildAxis_ne_minus
  have plusMinus := instruction.dyadicChildPlus_ne_minus
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildReadout
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
    SourceGeneratedActionMaterialInstructionAt.dyadicChildModes
    finiteStateVorticityCoefficientEnstrophy complexCoordinateAmplitudeSq
  simp [Finset.sum_insert, Finset.sum_singleton, Fin.sum_univ_succ,
    Complex.normSq_apply, axisPlus, axisMinus, plusMinus,
    Ne.symm axisPlus, Ne.symm axisMinus, Ne.symm plusMinus]
  nlinarith [axisSq, plusZeroSq, plusTwoSq, minusZeroSq, minusTwoSq]

theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildAmbientFactor_le
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    finiteModeKineticAmbientFactor instruction.dyadicChildModes ≤
      2000 * (instruction.cellScale : Real) ^ 2 := by
  have axisPlus := instruction.dyadicChildAxis_ne_plus
  have axisMinus := instruction.dyadicChildAxis_ne_minus
  have plusMinus := instruction.dyadicChildPlus_ne_minus
  have scaleFour : (4 : Real) ≤ instruction.cellScale := by
    exact_mod_cast instruction.cellScale_four
  have twoPiPos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have twoPiLt : 2 * Real.pi < 8 := by
    nlinarith [Real.pi_lt_four]
  have twoPiSqLe : (2 * Real.pi) ^ 2 ≤ 64 := by
    nlinarith [sq_nonneg (2 * Real.pi - 8)]
  have factorEq :
      finiteModeKineticAmbientFactor instruction.dyadicChildModes =
        2 * (2 * Real.pi) ^ 2 *
          (12 * (instruction.cellScale : Real) ^ 2 + 2) := by
    unfold finiteModeKineticAmbientFactor
      SourceGeneratedActionMaterialInstructionAt.dyadicChildModes
    simp [axisPlus, axisMinus, plusMinus,
      Ne.symm axisPlus, Ne.symm axisMinus, Ne.symm plusMinus]
    unfold
      SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus
      SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus
      SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    simp [SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis,
      integerWaveNormSq, axisWave, pumpY, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Pi.add_apply, Pi.sub_apply]
    ring
  rw [factorEq]
  have parenthesisNonneg :
      0 ≤ 12 * (instruction.cellScale : Real) ^ 2 + 2 := by positivity
  have boundedPi := mul_le_mul_of_nonneg_right twoPiSqLe parenthesisNonneg
  nlinarith [sq_nonneg (instruction.cellScale : Real)]

/-- Fixed rational y-cell used only to kernel-check the parametric domain
table.  The authoritative current submaterial is extracted below. -/
def butterflyReferenceYCellState : ComplexVorticityHilbertState :=
  yCellPhysicalState 4 (-1) (1 / 4) (-(15 / 4))
    (-(1 / 4)) (15 / 4)

theorem butterflyReferenceYCellState_transverse :
    WholeStateTransverse butterflyReferenceYCellState := by
  exact yCellPhysicalState_transverse 4 (by norm_num)
    (-1) (1 / 4) (-(15 / 4)) (-(1 / 4)) (15 / 4)

/-- Exact additive complement of the source-fixed candidate cell.  A world
where that cell is cancelled is retained by this residual rather than being
misclassified as a payment. -/
def SourceGeneratedActionMaterialInstructionAt.yCellComplement
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    ComplexVorticityHilbertState :=
  instruction.projectedState - instruction.dyadicYCellState

theorem SourceGeneratedActionMaterialInstructionAt.yCellComplement_transverse
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    WholeStateTransverse instruction.yCellComplement :=
  wholeStateTransverse_sub _ _ instruction.projectedState_transverse
    instruction.dyadicYCellState_transverse

theorem SourceGeneratedActionMaterialInstructionAt.projectedState_eq_yCell_add_complement
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.projectedState =
      instruction.dyadicYCellState + instruction.yCellComplement := by
  unfold SourceGeneratedActionMaterialInstructionAt.yCellComplement
  abel

/-- Exact complementary and cross action.  This is the complete affine
convolution identity: it is not an error bound. -/
def SourceGeneratedActionMaterialInstructionAt.yCellComplementCrossAction
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  wholeGeneratorLinearizationRow nu.coeff instruction.dyadicYCellState
      instruction.yCellComplement output +
    wholeGeneratorQuadraticRow instruction.yCellComplement output

theorem SourceGeneratedActionMaterialInstructionAt.projectedTangent_eq_yCell_add_complementCross
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (output : IntegerWavevector) :
    instruction.projectedTangent output =
      wholeLatticeVorticityFourierTangentAt nu.coeff
          instruction.dyadicYCellState output +
        instruction.yCellComplementCrossAction output := by
  have affine :=
    wholeLatticeVorticityFourierTangentAt_affine_eq_actionTube
      nu.coeff 1 instruction.dyadicYCellState instruction.yCellComplement
      instruction.dyadicYCellState_transverse
      instruction.yCellComplement_transverse output
  simp only [one_smul, one_pow] at affine
  rw [← instruction.projectedState_eq_yCell_add_complement] at affine
  unfold SourceGeneratedActionMaterialInstructionAt.projectedTangent
  rw [wholeFiniteSupportActionState_apply_eq_wholeTangent
    nu.coeff instruction.modes instruction.projectedState
    instruction.projectedState_supported output]
  unfold SourceGeneratedActionMaterialInstructionAt.yCellComplementCrossAction
  simpa only [add_assoc] using affine

/-- The complete whole tangent has exactly three rows: the y-cell table,
the projected complement/cross action and the source-owned whole-action
residual. -/
theorem SourceGeneratedActionMaterialInstructionAt.wholeTangent_eq_yCell_add_complementCross_add_residual
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (output : IntegerWavevector) :
    classicalWholeNSVorticityTangent nu
        current.physical.contact.physicalState output =
      wholeLatticeVorticityFourierTangentAt nu.coeff
          instruction.dyadicYCellState output +
        instruction.yCellComplementCrossAction output +
        instruction.actionResidual output := by
  have whole := congrFun instruction.wholeTangent_eq_projected_add_residual
    output
  change classicalWholeNSVorticityTangent nu
      current.physical.contact.physicalState output =
    instruction.projectedTangent output + instruction.actionResidual output
    at whole
  rw [instruction.projectedTangent_eq_yCell_add_complementCross] at whole
  exact whole

/-- The exact endpoint remainder after the actual y-cell action row is
removed.  This is an actual current-edge object, not a norm bound. -/
def SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidual
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  current.physical.nextContact.physicalState output -
    (current.physical.contact.physicalState output +
      current.physical.nextContact.time.1 •
        wholeLatticeVorticityFourierTangentAt nu.coeff
          instruction.dyadicYCellState output)

theorem SourceGeneratedActionMaterialInstructionAt.endpoint_eq_yCellAction_add_residual
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (output : IntegerWavevector) :
    current.physical.nextContact.physicalState output =
      current.physical.contact.physicalState output +
        current.physical.nextContact.time.1 •
          wholeLatticeVorticityFourierTangentAt nu.coeff
            instruction.dyadicYCellState output +
        instruction.yCellEndpointResidual output := by
  unfold SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidual
  abel

/-- Longitudinal source law on the actual child face.  The current action
writes the physical successor row; the compiler-owned next instruction then
splits that very row into its doubled-scale cell and the retained transport
residual.  No next endpoint, recurrence hypothesis or equality to a hand-built
state is supplied. -/
theorem SourceGeneratedActionMaterialInstructionAt.dyadicChildTransport_commutes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ instruction.dyadicChildModes) :
    instruction.next.dyadicYCellState wave +
        instruction.next.yCellComplement wave =
      current.physical.contact.physicalState wave +
        current.physical.nextContact.time.1 •
          wholeLatticeVorticityFourierTangentAt nu.coeff
            instruction.dyadicYCellState wave +
        instruction.yCellEndpointResidual wave := by
  have nextSplit := congrArg
    (fun state : ComplexVorticityHilbertState => state wave)
    instruction.next.projectedState_eq_yCell_add_complement
  calc
    instruction.next.dyadicYCellState wave +
        instruction.next.yCellComplement wave =
        instruction.next.projectedState wave := nextSplit.symm
    _ = current.physical.nextContact.physicalState wave :=
      instruction.next_projectedState_eq_target_on_child wave waveMem
    _ = current.physical.contact.physicalState wave +
          current.physical.nextContact.time.1 •
            wholeLatticeVorticityFourierTangentAt nu.coeff
              instruction.dyadicYCellState wave +
          instruction.yCellEndpointResidual wave :=
      instruction.endpoint_eq_yCellAction_add_residual wave

/-- Exact action provenance of the endpoint remainder: current
complement/cross plus whole-action residual, followed by the already
generated full-replay Euler remainder. -/
theorem SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidual_eq_actionSettlement
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    instruction.yCellEndpointResidual output =
      current.physical.nextContact.time.1 •
          (instruction.yCellComplementCrossAction output +
            instruction.actionResidual output) +
        ∫ actual in (0 : Real)..current.physical.nextContact.time.1,
          fullReplayEulerErrorDerivative current.physical output actual := by
  have integralEq := fullReplayEulerError_integral_eq
    current.physical output outputNe current.physical.nextContact.time
  have whole :=
    instruction.wholeTangent_eq_yCell_add_complementCross_add_residual output
  have whole' :
      wholeLatticeVorticityFourierTangentAt nu.coeff
          current.physical.contact.physicalState output =
        wholeLatticeVorticityFourierTangentAt nu.coeff
            instruction.dyadicYCellState output +
          instruction.yCellComplementCrossAction output +
          instruction.actionResidual output := by
    simpa only [classicalWholeNSVorticityTangent,
      wholeLatticeVorticityFourierTangentAt] using whole
  unfold SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidual
  rw [integralEq]
  unfold fullReplayEulerRow
  rw [show current.physical.nextReceipt.wholePath
      current.physical.nextContact.time =
        current.physical.nextContact.physicalState by rfl]
  rw [whole']
  module

private theorem GaussianRatVector.sub_ratScale_zero
    (row : GaussianRatVector) (scale : Rat) :
    GaussianRatVector.sub row (GaussianRatVector.ratScale scale 0) = row := by
  funext coordinate
  apply GaussianRat.ext <;>
    simp [GaussianRatVector.sub, GaussianRatVector.ratScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg,
      GaussianRat.ratScale]

/-- Kernel-checked physical image of the parametric domain table. -/
theorem butterflyReferenceYCellTangent_childRows :
    wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff butterflyReferenceYCellState
          butterflyFirstStackAxisEight =
        GaussianRatVector.toComplex (realRow 0 (120 / 17) 0) ∧
      wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff butterflyReferenceYCellState
          butterflyFirstStackAxisEightPlusY =
        GaussianRatVector.toComplex
          (realRow (1 / 16) (-1 / 2) (-15 / 272)) ∧
      wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff butterflyReferenceYCellState
          butterflyFirstStackAxisEightMinusY =
        GaussianRatVector.toComplex
          (realRow (1 / 16) (1 / 2) (-15 / 272)) := by
  have bridge := fun output => yCellAction_toComplex
    butterflyGainViscosity 4 (by norm_num) (-1) (1 / 100)
      (1 / 4) (-(15 / 4)) (-(1 / 4)) (15 / 4)
      butterflyGainViscosity_scaled output
  unfold butterflyReferenceYCellState
  constructor
  · rw [← bridge butterflyFirstStackAxisEight]
    congr 1
    change yCellAction 4 (-1) (1 / 100) (1 / 4) (-(15 / 4))
      (-(1 / 4)) (15 / 4) (axisWave (2 * 4)) = _
    unfold yCellAction rationalVorticityGeneratorCoefficientAt
    rw [yCellNonlinear_childAxis_eq 4 (by norm_num)]
    rw [yCellState_supported 4 (-1) (1 / 4) (-(15 / 4))
      (-(1 / 4)) (15 / 4) (axisWave (2 * 4)) (by decide)]
    rw [GaussianRatVector.sub_ratScale_zero]
    simp [butterflyFirstStackAxisEight, axisWave, realRow,
      GaussianRatVector.sub, GaussianRatVector.ratScale,
      GaussianRat.sub, GaussianRat.neg, GaussianRat.ratScale,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
  constructor
  · rw [← bridge butterflyFirstStackAxisEightPlusY]
    congr 1
    change yCellAction 4 (-1) (1 / 100) (1 / 4) (-(15 / 4))
      (-(1 / 4)) (15 / 4) (axisWave (2 * 4) + pumpY) = _
    unfold yCellAction rationalVorticityGeneratorCoefficientAt
    rw [yCellNonlinear_childPlus_eq 4 (by norm_num)]
    rw [yCellState_supported 4 (-1) (1 / 4) (-(15 / 4))
      (-(1 / 4)) (15 / 4) (axisWave (2 * 4) + pumpY) (by decide)]
    rw [GaussianRatVector.sub_ratScale_zero]
    simp [butterflyFirstStackAxisEightPlusY, axisWave, pumpY, realRow,
      GaussianRatVector.sub, GaussianRatVector.ratScale,
      GaussianRat.sub, GaussianRat.neg, GaussianRat.ratScale,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
  · rw [← bridge butterflyFirstStackAxisEightMinusY]
    congr 1
    change yCellAction 4 (-1) (1 / 100) (1 / 4) (-(15 / 4))
      (-(1 / 4)) (15 / 4) (axisWave (2 * 4) - pumpY) = _
    unfold yCellAction rationalVorticityGeneratorCoefficientAt
    rw [yCellNonlinear_childMinus_eq 4 (by norm_num)]
    rw [yCellState_supported 4 (-1) (1 / 4) (-(15 / 4))
      (-(1 / 4)) (15 / 4) (axisWave (2 * 4) - pumpY) (by decide)]
    rw [GaussianRatVector.sub_ratScale_zero]
    simp [butterflyFirstStackAxisEightMinusY, axisWave, pumpY, realRow,
      GaussianRatVector.sub, GaussianRatVector.ratScale,
      GaussianRat.sub, GaussianRat.neg, GaussianRat.ratScale,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num

/-- One signed cardinal/valuation readout of the three exact child rows. -/
def butterflyYCellFaceReadoutOf
    (rows : IntegerWavevector → ComplexCoordinateVector) : Real :=
  (rows butterflyFirstStackAxisEight 1).re +
    (rows butterflyFirstStackAxisEightPlusY 0).re -
    (rows butterflyFirstStackAxisEightPlusY 2).re +
    (rows butterflyFirstStackAxisEightMinusY 0).re -
    (rows butterflyFirstStackAxisEightMinusY 2).re

def butterflyYCellFaceReadout
    (state : ComplexVorticityHilbertState) : Real :=
  butterflyYCellFaceReadoutOf state

def butterflyYCellCoreCharge : Real :=
  120 / 17 + 1 / 16 + 15 / 272 + 1 / 16 + 15 / 272

theorem butterflyYCellCoreCharge_pos : 0 < butterflyYCellCoreCharge := by
  norm_num [butterflyYCellCoreCharge]

theorem butterflyYCellFaceReadout_le_finiteMass_add_five
    (state : ComplexVorticityHilbertState) :
    butterflyYCellFaceReadout state ≤
      finiteStateVorticityCoefficientEnstrophy
          butterflyFirstStackChildFaceModes state + 5 := by
  have axisSq :=
    sq_nonneg ((state butterflyFirstStackAxisEight 1).re - 1 / 2)
  have plusZeroSq :=
    sq_nonneg ((state butterflyFirstStackAxisEightPlusY 0).re - 1 / 2)
  have plusTwoSq :=
    sq_nonneg ((state butterflyFirstStackAxisEightPlusY 2).re + 1 / 2)
  have minusZeroSq :=
    sq_nonneg ((state butterflyFirstStackAxisEightMinusY 0).re - 1 / 2)
  have minusTwoSq :=
    sq_nonneg ((state butterflyFirstStackAxisEightMinusY 2).re + 1 / 2)
  unfold butterflyYCellFaceReadout butterflyYCellFaceReadoutOf
    finiteStateVorticityCoefficientEnstrophy
    butterflyFirstStackChildFaceModes complexCoordinateAmplitudeSq
  simp [Finset.sum_insert, Finset.sum_singleton,
    Fin.sum_univ_succ, Complex.normSq_apply,
    butterflyFirstStackAxisEight, butterflyFirstStackAxisEightPlusY,
    butterflyFirstStackAxisEightMinusY, axisWave, pumpY]
  simp [butterflyFirstStackAxisEight,
    butterflyFirstStackAxisEightPlusY,
    butterflyFirstStackAxisEightMinusY, axisWave, pumpY] at axisSq plusZeroSq plusTwoSq minusZeroSq minusTwoSq
  nlinarith [axisSq, plusZeroSq, plusTwoSq, minusZeroSq, minusTwoSq]

def SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidualReadout
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  instruction.dyadicChildReadoutOf instruction.yCellEndpointResidual

/-- Actual current-side charge emitted by the faithful y-cell restriction. -/
def SourceGeneratedActionMaterialInstructionAt.yCellCoreCharge
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  instruction.dyadicCoreCharge

theorem SourceGeneratedActionMaterialInstructionAt.yCellCoreCharge_pos
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    0 < instruction.yCellCoreCharge := by
  exact instruction.dyadicCoreCharge_pos

/-- The exact endpoint ledger of the y-cell incidence.  Complement/cross,
whole-action residual and Euler remainder are all retained in the single
residual readout on the right. -/
theorem SourceGeneratedActionMaterialInstructionAt.yCellFaceReadout_commutes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.dyadicChildReadout
          current.physical.nextContact.physicalState -
        instruction.dyadicChildReadout
          current.physical.contact.physicalState =
      current.physical.nextContact.time.1 * instruction.yCellCoreCharge +
        instruction.yCellEndpointResidualReadout := by
  have axis := congrArg (fun row : ComplexCoordinateVector => (row 1).re)
    (instruction.endpoint_eq_yCellAction_add_residual
      instruction.dyadicChildAxis)
  have plusZero := congrArg
    (fun row : ComplexCoordinateVector => (row 0).re)
    (instruction.endpoint_eq_yCellAction_add_residual
      instruction.dyadicChildPlus)
  have plusTwo := congrArg
    (fun row : ComplexCoordinateVector => (row 2).re)
    (instruction.endpoint_eq_yCellAction_add_residual
      instruction.dyadicChildPlus)
  have minusZero := congrArg
    (fun row : ComplexCoordinateVector => (row 0).re)
    (instruction.endpoint_eq_yCellAction_add_residual
      instruction.dyadicChildMinus)
  have minusTwo := congrArg
    (fun row : ComplexCoordinateVector => (row 2).re)
    (instruction.endpoint_eq_yCellAction_add_residual
      instruction.dyadicChildMinus)
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildReadout
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
    SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidualReadout
    SourceGeneratedActionMaterialInstructionAt.yCellCoreCharge
    SourceGeneratedActionMaterialInstructionAt.dyadicCoreCharge
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.add_re, Complex.smul_re, smul_eq_mul]
      at axis plusZero plusTwo minusZero minusTwo
  unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.add_re, Complex.smul_re]
  linarith

/-- Signed valuation of the exact complement/cross plus whole-action residual
on the three child rows. -/
def SourceGeneratedActionMaterialInstructionAt.yCellComplementActionReadout
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  instruction.dyadicChildReadoutOf fun output =>
    instruction.yCellComplementCrossAction output +
      instruction.actionResidual output

/-- Signed valuation of the already generated full-replay Euler remainder on
the same child rows. -/
def SourceGeneratedActionMaterialInstructionAt.yCellEulerErrorReadout
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  instruction.dyadicChildReadoutOf fun output =>
    ∫ actual in (0 : Real)..current.physical.nextContact.time.1,
      fullReplayEulerErrorDerivative current.physical output actual

/-- Exact aggregate decomposition of the endpoint residual.  No sign, norm
bound, Taylor remainder or future contact enters: complement/cross, the whole
action residual and the replay Euler row are the literal three summands of the
same selected endpoint. -/
theorem SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidualReadout_eq_action_add_euler
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.yCellEndpointResidualReadout =
      current.physical.nextContact.time.1 *
          instruction.yCellComplementActionReadout +
        instruction.yCellEulerErrorReadout := by
  have axis := congrArg (fun row : ComplexCoordinateVector => (row 1).re)
    (instruction.yCellEndpointResidual_eq_actionSettlement
      instruction.dyadicChildAxis instruction.dyadicChildAxis_ne_zero)
  have plusZero := congrArg
    (fun row : ComplexCoordinateVector => (row 0).re)
    (instruction.yCellEndpointResidual_eq_actionSettlement
      instruction.dyadicChildPlus instruction.dyadicChildPlus_ne_zero)
  have plusTwo := congrArg
    (fun row : ComplexCoordinateVector => (row 2).re)
    (instruction.yCellEndpointResidual_eq_actionSettlement
      instruction.dyadicChildPlus instruction.dyadicChildPlus_ne_zero)
  have minusZero := congrArg
    (fun row : ComplexCoordinateVector => (row 0).re)
    (instruction.yCellEndpointResidual_eq_actionSettlement
      instruction.dyadicChildMinus instruction.dyadicChildMinus_ne_zero)
  have minusTwo := congrArg
    (fun row : ComplexCoordinateVector => (row 2).re)
    (instruction.yCellEndpointResidual_eq_actionSettlement
      instruction.dyadicChildMinus instruction.dyadicChildMinus_ne_zero)
  unfold SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidualReadout
    SourceGeneratedActionMaterialInstructionAt.yCellComplementActionReadout
    SourceGeneratedActionMaterialInstructionAt.yCellEulerErrorReadout
    SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.add_re, Complex.smul_re, smul_eq_mul]
      at axis plusZero plusTwo minusZero minusTwo ⊢
  linarith

/-! The qualitative incidence is read from the complete actual action.  The
parametric table supplies the core orientation; any complement/cross
cancellation remains visible in this predicate and therefore normalizes to
a typed residual rather than being estimated away. -/
def ButterflyActualYCellChildIncidenceAt
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Prop :=
  0 < instruction.yCellCoreCharge ∧
    0 ≤ instruction.yCellEndpointResidualReadout

/-- Dyadic source scale follows the actual standing payment and nothing else.
Action incidence alone may be cancelled by complementary physical rows, while
a standing payment advances the source cell even when the action table leaves
an explicit residual. -/
def ButterflyActualStandingCellAdvanceAt
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Prop :=
  current.standing.paymentIncrement = 1

/-- Residual action material keeps the same cell standing while still taking
the compiler-owned physical successor and enlarged capture radius. -/
def SourceGeneratedActionMaterialInstructionAt.retainCellNext
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    SourceGeneratedActionMaterialInstructionAt current.next where
  floor := instruction.next.floor
  floor_pos := instruction.next.floor_pos
  radius := instruction.next.radius
  capture_le := instruction.next.capture_le
  cellScale := instruction.cellScale
  cellScale_two := instruction.cellScale_two
  cellScale_four := instruction.cellScale_four
  cellScale_le_radius := by
    have scaleLe := instruction.cellScale_le_radius
    have doubledLe := instruction.doubleRadius_le_next
    omega

/-- Unique local cell transition.  Exact action incidence advances
`m ↦ 2m`; a generated residual retains `m` and is re-normalized on the actual
successor.  The branch is computed from the current material, never supplied
by a caller. -/
noncomputable def SourceGeneratedActionMaterialInstructionAt.advance
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    SourceGeneratedActionMaterialInstructionAt current.next := by
  classical
  exact if ButterflyActualStandingCellAdvanceAt instruction then
      instruction.next
    else instruction.retainCellNext

theorem SourceGeneratedActionMaterialInstructionAt.advance_radius
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.advance.radius = instruction.next.radius := by
  unfold SourceGeneratedActionMaterialInstructionAt.advance
  split <;> rfl

theorem SourceGeneratedActionMaterialInstructionAt.advance_modes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.advance.modes = instruction.next.modes := by
  unfold SourceGeneratedActionMaterialInstructionAt.modes
  rw [instruction.advance_radius]

/-- A normalized-work margin evaluated on the compiler-owned successor
capture writes back to that successor instruction without changing modes or
choosing a second endpoint.  The endpoint is the physical current installed
by `advance`, and `advance.modes` is already its source-generated full-receipt
capture. -/
theorem SourceGeneratedActionMaterialInstructionAt.advance_normalizedWorkFloor
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (floor : Real)
    (margin : fullReplayNormalizedWorkEulerMarginAt current.physical
      instruction.advance.modes floor) :
    floor ≤ finiteNormalizedGeneratorWork instruction.advance.modes
      nu.coeff
      (complexSharpSupportProjection instruction.advance.modes
        current.next.physical.contact.physicalState) := by
  have endpoint := fullReplay_actualNormalizedWork_ge_floor_of_eulerMargin
    current.physical instruction.advance.modes
      instruction.advance.modes_zeroNotMem floor margin
        current.physical.nextContact.time
  change floor ≤ finiteNormalizedGeneratorWork instruction.advance.modes
    nu.coeff
    (complexSharpSupportProjection instruction.advance.modes
      current.physical.nextContact.physicalState)
  rw [← current.physical.nextContact.prefixReceipt_terminal]
  exact endpoint

theorem SourceGeneratedActionMaterialInstructionAt.advance_cellScale_of_payment
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (payment : ButterflyActualStandingCellAdvanceAt instruction) :
    instruction.advance.cellScale = 2 * instruction.cellScale := by
  unfold SourceGeneratedActionMaterialInstructionAt.advance
  rw [if_pos payment]
  rfl

theorem SourceGeneratedActionMaterialInstructionAt.advance_cellScale_of_nonpayment
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (nonpayment : ¬ ButterflyActualStandingCellAdvanceAt instruction) :
    instruction.advance.cellScale = instruction.cellScale := by
  unfold SourceGeneratedActionMaterialInstructionAt.advance
  rw [if_neg nonpayment]
  rfl

theorem SourceGeneratedActionMaterialInstructionAt.advance_cellScale_eq
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.advance.cellScale =
      instruction.cellScale * 2 ^ current.standing.paymentIncrement := by
  have incrementLe :=
    NativeRestartStandingValuedArithmeticMaterialAt.standing_paymentIncrement_le_one
      current.standing
  by_cases paid : current.standing.paymentIncrement = 1
  · rw [instruction.advance_cellScale_of_payment paid, paid]
    simp
    omega
  · have zero : current.standing.paymentIncrement = 0 := by omega
    rw [instruction.advance_cellScale_of_nonpayment paid, zero]
    simp

theorem SourceGeneratedActionMaterialInstructionAt.advance_projectedState_eq_target_on_child
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ instruction.dyadicChildModes) :
    instruction.advance.projectedState wave =
      current.physical.nextContact.physicalState wave := by
  unfold SourceGeneratedActionMaterialInstructionAt.projectedState
  rw [complexSharpSupportProjection_apply]
  apply if_pos
  rw [instruction.advance_modes]
  exact instruction.dyadicChildModes_subset_nextModes waveMem

/-- Authoritative specialization of the transport square: the target cell is
the branch-sensitive instruction installed by the same medium/root successor.
Exact incidence doubles its scale; residual material retains the scale and is
re-expanded. -/
theorem SourceGeneratedActionMaterialInstructionAt.advanceChildTransport_commutes
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ instruction.dyadicChildModes) :
    instruction.advance.dyadicYCellState wave +
        instruction.advance.yCellComplement wave =
      current.physical.contact.physicalState wave +
        current.physical.nextContact.time.1 •
          wholeLatticeVorticityFourierTangentAt nu.coeff
            instruction.dyadicYCellState wave +
        instruction.yCellEndpointResidual wave := by
  have nextSplit := congrArg
    (fun state : ComplexVorticityHilbertState => state wave)
    instruction.advance.projectedState_eq_yCell_add_complement
  calc
    instruction.advance.dyadicYCellState wave +
        instruction.advance.yCellComplement wave =
        instruction.advance.projectedState wave := nextSplit.symm
    _ = current.physical.nextContact.physicalState wave :=
      instruction.advance_projectedState_eq_target_on_child wave waveMem
    _ = current.physical.contact.physicalState wave +
          current.physical.nextContact.time.1 •
            wholeLatticeVorticityFourierTangentAt nu.coeff
              instruction.dyadicYCellState wave +
          instruction.yCellEndpointResidual wave :=
      instruction.endpoint_eq_yCellAction_add_residual wave


theorem SourceGeneratedActionMaterialInstructionAt.yCell_clock_mul_charge_le_faceReadoutGain
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (incidence : ButterflyActualYCellChildIncidenceAt instruction) :
    current.physical.nextContact.time.1 * instruction.yCellCoreCharge ≤
      instruction.dyadicChildReadout
          current.physical.nextContact.physicalState -
        instruction.dyadicChildReadout
          current.physical.contact.physicalState := by
  rw [instruction.yCellFaceReadout_commutes]
  exact le_add_of_nonneg_right incidence.2

/-- Existing arithmetic normalizer input generated from the actual action
incidence.  `whole` contains the one paid atom exactly when the complete
action (core plus complement/cross plus whole residual) has that incidence. -/
noncomputable def SourceGeneratedActionMaterialInstructionAt.yCellArithmeticMaterial
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    RootArithmeticMaterialAt := by
  classical
  exact
    { whole := if ButterflyActualYCellChildIncidenceAt instruction then
        UnitHistory.generate 1 else UnitHistory.generate 0
      left := UnitHistory.generate 0
      right := UnitHistory.generate 1 }

theorem SourceGeneratedActionMaterialInstructionAt.yCellArithmeticMaterial_exact_iff
    {nu : Viscosity}
    {current : GeneratedWholeRestartRuntimeCurrent nu}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    instruction.yCellArithmeticMaterial.whole =
        instruction.yCellArithmeticMaterial.left.parallel
          instruction.yCellArithmeticMaterial.right ↔
      ButterflyActualYCellChildIncidenceAt instruction := by
  unfold SourceGeneratedActionMaterialInstructionAt.yCellArithmeticMaterial
  by_cases incidence : ButterflyActualYCellChildIncidenceAt instruction
  · simp only [incidence, if_true]
    constructor
    · intro _equality
      trivial
    · intro _true
      rfl
  · simp only [incidence, if_false]
    constructor
    · intro equality
      have shadow := congrArg UnitHistory.cardinalShadow equality
      norm_num at shadow
    · intro impossible
      exact impossible.elim

theorem SourceGeneratedActionMaterialInstructionAt.yCellEndpointResidualReadout_neg_of_normalResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (residual : GeneratedParallelResidualAt instruction
      instruction.yCellArithmeticMaterial) :
    instruction.yCellEndpointResidualReadout < 0 := by
  have notIncidence : ¬ ButterflyActualYCellChildIncidenceAt instruction := by
    intro incidence
    apply residual.mismatch
    exact instruction.yCellArithmeticMaterial_exact_iff.mpr incidence
  exact lt_of_not_ge fun residualNonneg =>
    notIncidence ⟨instruction.yCellCoreCharge_pos, residualNonneg⟩

structure NativeRestartStandingActionValuedArithmeticMaterialAt
    {nu : Viscosity}
    (state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current) : Type where
  private mk ::
  standingMaterial : NativeRestartStandingValuedArithmeticMaterialAt
    state.1.standing
  standingMaterial_eq : standingMaterial =
    nativeRestartStandingValuedArithmeticMaterial state.1.cellEffect
  actionInstruction : SourceGeneratedActionMaterialInstructionAt state.1
  actionInstruction_eq : actionInstruction = state.2
  arithmeticMaterial : RootArithmeticMaterialAt
  arithmeticMaterial_eq : arithmeticMaterial =
    standingMaterial.arithmeticMaterial
  actionArithmeticMaterial : RootArithmeticMaterialAt
  actionArithmeticMaterial_eq : actionArithmeticMaterial =
    actionInstruction.yCellArithmeticMaterial
  yCellCoreCharge : Real
  yCellCoreCharge_eq : yCellCoreCharge = actionInstruction.yCellCoreCharge
  endpointResidualReadout : Real
  endpointResidualReadout_eq : endpointResidualReadout =
    actionInstruction.yCellEndpointResidualReadout
  faceValuation_commutes :
    actionInstruction.dyadicChildReadout
          state.1.physical.nextContact.physicalState -
        actionInstruction.dyadicChildReadout
          state.1.physical.contact.physicalState =
      state.1.physical.nextContact.time.1 * yCellCoreCharge +
        endpointResidualReadout
  projectedAction_commutes : ∀ output,
    actionInstruction.projectedTangent output =
      wholeLatticeVorticityFourierTangentAt nu.coeff
          actionInstruction.dyadicYCellState output +
        actionInstruction.yCellComplementCrossAction output
  wholeAction_commutes : ∀ output,
    classicalWholeNSVorticityTangent nu
        state.1.physical.contact.physicalState output =
      wholeLatticeVorticityFourierTangentAt nu.coeff
          actionInstruction.dyadicYCellState output +
        actionInstruction.yCellComplementCrossAction output +
        actionInstruction.actionResidual output
  endpointAction_commutes : ∀ output, output ≠ 0 →
    actionInstruction.yCellEndpointResidual output =
      state.1.physical.nextContact.time.1 •
          (actionInstruction.yCellComplementCrossAction output +
            actionInstruction.actionResidual output) +
        ∫ actual in (0 : Real)..state.1.physical.nextContact.time.1,
          fullReplayEulerErrorDerivative state.1.physical output actual

noncomputable def nativeRestartStandingActionValuedArithmeticMaterial
    {nu : Viscosity}
    (state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current) :
    NativeRestartStandingActionValuedArithmeticMaterialAt state where
  standingMaterial :=
    nativeRestartStandingValuedArithmeticMaterial state.1.cellEffect
  standingMaterial_eq := rfl
  actionInstruction := state.2
  actionInstruction_eq := rfl
  arithmeticMaterial :=
    (nativeRestartStandingValuedArithmeticMaterial state.1.cellEffect
      ).arithmeticMaterial
  arithmeticMaterial_eq := rfl
  actionArithmeticMaterial := state.2.yCellArithmeticMaterial
  actionArithmeticMaterial_eq := rfl
  yCellCoreCharge := state.2.yCellCoreCharge
  yCellCoreCharge_eq := rfl
  endpointResidualReadout := state.2.yCellEndpointResidualReadout
  endpointResidualReadout_eq := rfl
  faceValuation_commutes := state.2.yCellFaceReadout_commutes
  projectedAction_commutes := state.2.projectedTangent_eq_yCell_add_complementCross
  wholeAction_commutes :=
    state.2.wholeTangent_eq_yCell_add_complementCross_add_residual
  endpointAction_commutes := fun output outputNe =>
    state.2.yCellEndpointResidual_eq_actionSettlement output outputNe

namespace NativeRestartStandingActionValuedArithmeticMaterialAt

theorem actionArithmeticExact_iff_actualYCellIncidence
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state) :
    material.actionArithmeticMaterial.whole =
        material.actionArithmeticMaterial.left.parallel
          material.actionArithmeticMaterial.right ↔
      ButterflyActualYCellChildIncidenceAt state.2 := by
  rw [material.actionArithmeticMaterial_eq, material.actionInstruction_eq]
  exact state.2.yCellArithmeticMaterial_exact_iff

theorem endpointResidualReadout_neg_of_actionResidual
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity =>
        SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (residual : GeneratedParallelResidualAt
      material material.actionArithmeticMaterial) :
    material.endpointResidualReadout < 0 := by
  have notIncidence : ¬ ButterflyActualYCellChildIncidenceAt state.2 := by
    intro incidence
    apply residual.mismatch
    exact material.actionArithmeticExact_iff_actualYCellIncidence.mpr incidence
  have chargePos : 0 < material.yCellCoreCharge := by
    rw [material.yCellCoreCharge_eq, material.actionInstruction_eq]
    exact state.2.yCellCoreCharge_pos
  apply lt_of_not_ge
  intro residualNonneg
  apply notIncidence
  constructor
  · calc
      0 < material.yCellCoreCharge := chargePos
      _ = state.2.yCellCoreCharge := by
        rw [material.yCellCoreCharge_eq, material.actionInstruction_eq]
  · rw [material.endpointResidualReadout_eq,
      material.actionInstruction_eq] at residualNonneg
    exact residualNonneg

/-- On the action-residual constructor the existing frozen-face clock
consumer is unavailable in the literal opposite direction: the complete
actual face gain is strictly smaller than `clock * coreCharge`.  Any total
settlement of this constructor must therefore consume a further quantitative
row of the residual expansion; it cannot reuse the exact-incidence payment
after merely transporting `nextNormalForm`. -/
theorem faceReadoutGain_lt_clock_mul_yCellCoreCharge_of_actionResidual
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity =>
        SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (residual : GeneratedParallelResidualAt
      material material.actionArithmeticMaterial) :
    material.actionInstruction.dyadicChildReadout
          state.1.physical.nextContact.physicalState -
        material.actionInstruction.dyadicChildReadout
          state.1.physical.contact.physicalState <
      state.1.physical.nextContact.time.1 * material.yCellCoreCharge := by
  have commuting := material.faceValuation_commutes
  have residualNeg := material.endpointResidualReadout_neg_of_actionResidual
    residual
  linarith

theorem not_actualYCellIncidence_of_actionResidual
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity =>
        SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (residual : GeneratedParallelResidualAt
      material material.actionArithmeticMaterial) :
    ¬ ButterflyActualYCellChildIncidenceAt state.2 := by
  intro incidence
  apply residual.mismatch
  exact material.actionArithmeticExact_iff_actualYCellIncidence.mpr incidence

theorem yCellCoreCharge_pos_of_arithmeticExact
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (commutes : material.actionArithmeticMaterial.whole =
      material.actionArithmeticMaterial.left.parallel
        material.actionArithmeticMaterial.right) :
    0 < material.yCellCoreCharge := by
  have incidence :=
    material.actionArithmeticExact_iff_actualYCellIncidence.mp commutes
  rw [material.yCellCoreCharge_eq, material.actionInstruction_eq]
  exact incidence.1

/-- The exact arithmetic branch and its Real clock valuation are projections
of one actual material.  No naked level equality or foreign scalar enters. -/
theorem clock_mul_yCellCoreCharge_le_faceReadoutGain_of_arithmeticExact
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (commutes : material.actionArithmeticMaterial.whole =
      material.actionArithmeticMaterial.left.parallel
        material.actionArithmeticMaterial.right) :
    state.1.physical.nextContact.time.1 * material.yCellCoreCharge ≤
      material.actionInstruction.dyadicChildReadout
          state.1.physical.nextContact.physicalState -
        material.actionInstruction.dyadicChildReadout
          state.1.physical.contact.physicalState := by
  have incidence :=
    material.actionArithmeticExact_iff_actualYCellIncidence.mp commutes
  rw [material.yCellCoreCharge_eq, material.actionInstruction_eq]
  exact state.2.yCell_clock_mul_charge_le_faceReadoutGain incidence

noncomputable def actionFreshGainModes
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state) :
    Finset IntegerWavevector :=
  material.actionInstruction.advance.modes.filter fun wave =>
    complexCoordinateAmplitudeSq
        (material.standingMaterial.rawValuedMaterial.sourcePhysicalState wave) <
      complexCoordinateAmplitudeSq
        (material.standingMaterial.rawValuedMaterial.targetPhysicalState wave)

/-- Empty action-side fresh inventory is exactly coordinatewise nonincrease
on the complete capture material installed at this occurrence. -/
theorem actionFreshGainModes_eq_empty_iff
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state) :
    material.actionFreshGainModes = ∅ ↔
      ∀ wave ∈ material.actionInstruction.advance.modes,
        complexCoordinateAmplitudeSq
            (material.standingMaterial.rawValuedMaterial.targetPhysicalState
              wave) ≤
          complexCoordinateAmplitudeSq
            (material.standingMaterial.rawValuedMaterial.sourcePhysicalState
              wave) := by
  constructor
  · intro modesEmpty wave waveMem
    have waveNotMem : wave ∉ material.actionFreshGainModes := by
      rw [modesEmpty]
      simp
    by_contra targetNotLe
    exact waveNotMem (Finset.mem_filter.mpr
      ⟨waveMem, lt_of_not_ge targetNotLe⟩)
  · intro coordinateNonincrease
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨wave, waveMem⟩
    have filtered := Finset.mem_filter.mp waveMem
    exact (not_lt_of_ge (coordinateNonincrease wave filtered.1)) filtered.2

end NativeRestartStandingActionValuedArithmeticMaterialAt

/-- The root arithmetic residual and the installed standing residual are the
same mismatch under the material's definitional commuting row.  This is the
authoritative entry into the existing residual lifecycle; no new branch or
scalar sign is introduced. -/
noncomputable def NativeRestartStandingActionValuedArithmeticMaterialAt.standingResidualOf
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial) :
    GeneratedParallelResidualAt material.standingMaterial
      material.standingMaterial.arithmeticMaterial := by
  generalize normalFormEq :
    material.standingMaterial.parallelNormalForm = normalForm
  cases normalForm with
  | exact rooted commutes =>
      exact False.elim (residual.mismatch (by
        rw [material.arithmeticMaterial_eq]
        exact commutes))
  | generatedResidual standingResidual =>
      exact standingResidual

/-- Generated residual expansion on the same action occurrence.  Its exact
submaterial/complement decomposition and Real endpoint valuation share one
provenance; living-root next authority remains outside this carrier. -/
structure NativeRestartStandingActionResidualExpansionAt
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial) : Type where
  private mk ::
  standingResidual : GeneratedParallelResidualAt material.standingMaterial
    material.standingMaterial.arithmeticMaterial
  standingExpansion :
    material.standingMaterial.GeneratedResidualExpansionAt standingResidual
  endpointResidual : IntegerWavevector → ComplexCoordinateVector
  endpointResidual_eq : endpointResidual =
    material.actionInstruction.yCellEndpointResidual
  complementActionReadout : Real
  complementActionReadout_eq : complementActionReadout =
    material.actionInstruction.yCellComplementActionReadout
  eulerErrorReadout : Real
  eulerErrorReadout_eq : eulerErrorReadout =
    material.actionInstruction.yCellEulerErrorReadout
  endpointReadout_commutes :
    material.endpointResidualReadout =
      state.1.physical.nextContact.time.1 * complementActionReadout +
        eulerErrorReadout
  physicalModes : Finset IntegerWavevector
  physicalModes_eq : physicalModes = material.actionFreshGainModes
  physicalModes_zeroNotMem : (0 : IntegerWavevector) ∉ physicalModes
  finiteNetEnstrophyDebit : Real
  finiteNetEnstrophyDebit_eq :
    finiteNetEnstrophyDebit =
      finiteStateVorticityCoefficientEnstrophy physicalModes
          material.standingMaterial.rawValuedMaterial.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy physicalModes
          material.standingMaterial.rawValuedMaterial.sourcePhysicalState
  finiteNetEnstrophyDebit_nonneg : 0 ≤ finiteNetEnstrophyDebit
  projectedAction_commutes : ∀ output,
    material.actionInstruction.projectedTangent output =
      wholeLatticeVorticityFourierTangentAt nu.coeff
          material.actionInstruction.dyadicYCellState output +
        material.actionInstruction.yCellComplementCrossAction output
  wholeAction_commutes : ∀ output,
    classicalWholeNSVorticityTangent nu
        state.1.physical.contact.physicalState output =
      wholeLatticeVorticityFourierTangentAt nu.coeff
          material.actionInstruction.dyadicYCellState output +
        material.actionInstruction.yCellComplementCrossAction output +
        material.actionInstruction.actionResidual output
  endpointAction_commutes : ∀ output, output ≠ 0 →
    endpointResidual output =
      state.1.physical.nextContact.time.1 •
          (material.actionInstruction.yCellComplementCrossAction output +
            material.actionInstruction.actionResidual output) +
        ∫ actual in (0 : Real)..state.1.physical.nextContact.time.1,
          fullReplayEulerErrorDerivative state.1.physical output actual

noncomputable def nativeRestartStandingActionResidualExpansion
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    (material : NativeRestartStandingActionValuedArithmeticMaterialAt state)
    (residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial) :
    NativeRestartStandingActionResidualExpansionAt material residual := by
  let physicalModes := material.actionFreshGainModes
  let standingResidual := material.standingResidualOf residual
  exact
    { standingResidual := standingResidual
      standingExpansion :=
        material.standingMaterial.generatedResidualExpansion standingResidual
      endpointResidual := material.actionInstruction.yCellEndpointResidual
      endpointResidual_eq := rfl
      complementActionReadout :=
        material.actionInstruction.yCellComplementActionReadout
      complementActionReadout_eq := rfl
      eulerErrorReadout := material.actionInstruction.yCellEulerErrorReadout
      eulerErrorReadout_eq := rfl
      endpointReadout_commutes := by
        rw [material.endpointResidualReadout_eq,
          material.actionInstruction_eq]
        exact state.2.yCellEndpointResidualReadout_eq_action_add_euler
      physicalModes := physicalModes
      physicalModes_eq := rfl
      physicalModes_zeroNotMem := by
        intro zeroMem
        have modesMem := (Finset.mem_filter.mp zeroMem).1
        exact material.actionInstruction.advance.modes_zeroNotMem modesMem
      finiteNetEnstrophyDebit :=
        finiteStateVorticityCoefficientEnstrophy physicalModes
            material.standingMaterial.rawValuedMaterial.targetPhysicalState -
          finiteStateVorticityCoefficientEnstrophy physicalModes
            material.standingMaterial.rawValuedMaterial.sourcePhysicalState
      finiteNetEnstrophyDebit_eq := rfl
      finiteNetEnstrophyDebit_nonneg := by
        apply sub_nonneg.mpr
        unfold finiteStateVorticityCoefficientEnstrophy
        apply Finset.sum_le_sum
        intro wave waveMem
        exact (Finset.mem_filter.mp waveMem).2.le
      projectedAction_commutes := material.projectedAction_commutes
      wholeAction_commutes := material.wholeAction_commutes
      endpointAction_commutes := material.endpointAction_commutes }

namespace NativeRestartStandingActionResidualExpansionAt

/-- The action-side finite valuation is positive exactly when its generated
fresh-gain inventory contains an actual Fourier row. -/
theorem finiteNetEnstrophyDebit_pos_iff_modes_nonempty
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual) :
    0 < expansion.finiteNetEnstrophyDebit ↔
      expansion.physicalModes.Nonempty := by
  rw [expansion.finiteNetEnstrophyDebit_eq]
  constructor
  · intro debitPos
    by_contra modesNotNonempty
    have modesEmpty : expansion.physicalModes = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp modesNotNonempty
    rw [modesEmpty] at debitPos
    unfold finiteStateVorticityCoefficientEnstrophy at debitPos
    have zeroLtZero : (0 : Real) < 0 := by
      simpa only [Finset.sum_empty, sub_self] using debitPos
    exact (lt_irrefl 0) zeroLtZero
  · intro modesNonempty
    apply sub_pos.mpr
    unfold finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_lt_sum_of_nonempty modesNonempty
    intro wave waveMem
    have freshMem : wave ∈ material.actionFreshGainModes := by
      rw [← expansion.physicalModes_eq]
      exact waveMem
    exact (Finset.mem_filter.mp freshMem).2

/-- Silence of the action valuation is the exact empty-fresh-gain statement
on the same residual expansion. -/
theorem finiteNetEnstrophyDebit_eq_zero_iff_modes_empty
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual) :
    expansion.finiteNetEnstrophyDebit = 0 ↔
      expansion.physicalModes = ∅ := by
  constructor
  · intro debitZero
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro modesNonempty
    have debitPos :=
      expansion.finiteNetEnstrophyDebit_pos_iff_modes_nonempty.mpr
        modesNonempty
    linarith
  · intro modesEmpty
    have debitNotPos : ¬ 0 < expansion.finiteNetEnstrophyDebit := by
      intro debitPos
      have modesNonempty :=
        expansion.finiteNetEnstrophyDebit_pos_iff_modes_nonempty.mp debitPos
      rw [modesEmpty] at modesNonempty
      exact Finset.not_nonempty_empty modesNonempty
    exact le_antisymm (le_of_not_gt debitNotPos)
      expansion.finiteNetEnstrophyDebit_nonneg

/-- One physical inventory for the complete residual expansion.  The union
prevents a Fourier row present in both the standing and action restrictions
from being valued twice. -/
def physicalUnionModes
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual) : Finset IntegerWavevector :=
  expansion.standingExpansion.physicalModes ∪ expansion.physicalModes

/-- Non-duplicating Real valuation of the unified physical fresh-gain
inventory. -/
def unionNetEnstrophyDebit
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual) : Real :=
  finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
      material.standingMaterial.rawValuedMaterial.targetPhysicalState -
    finiteStateVorticityCoefficientEnstrophy expansion.physicalUnionModes
      material.standingMaterial.rawValuedMaterial.sourcePhysicalState

theorem physicalUnionModes_every_gain
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ expansion.physicalUnionModes) :
    complexCoordinateAmplitudeSq
        (material.standingMaterial.rawValuedMaterial.sourcePhysicalState wave) <
      complexCoordinateAmplitudeSq
        (material.standingMaterial.rawValuedMaterial.targetPhysicalState wave) := by
  rw [physicalUnionModes, Finset.mem_union] at waveMem
  rcases waveMem with standingMem | actionMem
  · have freshMem : wave ∈
        material.standingMaterial.standingValuedFreshGainModes := by
      rw [← expansion.standingExpansion.physicalModes_eq]
      exact standingMem
    exact (Finset.mem_filter.mp freshMem).2
  · have freshMem : wave ∈ material.actionFreshGainModes := by
      rw [← expansion.physicalModes_eq]
      exact actionMem
    exact (Finset.mem_filter.mp freshMem).2

theorem unionNetEnstrophyDebit_nonneg
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual) :
    0 ≤ expansion.unionNetEnstrophyDebit := by
  unfold unionNetEnstrophyDebit finiteStateVorticityCoefficientEnstrophy
  apply sub_nonneg.mpr
  apply Finset.sum_le_sum
  intro wave waveMem
  exact (expansion.physicalUnionModes_every_gain waveMem).le

theorem unionNetEnstrophyDebit_pos_iff_modes_nonempty
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual) :
    0 < expansion.unionNetEnstrophyDebit ↔
      expansion.physicalUnionModes.Nonempty := by
  constructor
  · intro positive
    by_contra empty
    have modesEmpty : expansion.physicalUnionModes = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp empty
    rw [unionNetEnstrophyDebit, modesEmpty] at positive
    simp only [finiteStateVorticityCoefficientEnstrophy,
      Finset.sum_empty, sub_self] at positive
    exact (lt_irrefl 0 positive)
  · intro nonempty
    unfold unionNetEnstrophyDebit finiteStateVorticityCoefficientEnstrophy
    apply sub_pos.mpr
    apply Finset.sum_lt_sum_of_nonempty nonempty
    intro wave waveMem
    exact expansion.physicalUnionModes_every_gain waveMem

theorem unionNetEnstrophyDebit_eq_zero_iff_modes_empty
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual) :
    expansion.unionNetEnstrophyDebit = 0 ↔
      expansion.physicalUnionModes = ∅ := by
  constructor
  · intro zero
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro nonempty
    exact (ne_of_gt
      (expansion.unionNetEnstrophyDebit_pos_iff_modes_nonempty.mpr nonempty))
      zero
  · intro empty
    unfold unionNetEnstrophyDebit
    rw [empty]
    simp [finiteStateVorticityCoefficientEnstrophy]

theorem positive_unionDebit_has_freshGain
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual)
    (positive : 0 < expansion.unionNetEnstrophyDebit) :
    expansion.standingExpansion.physicalModes.Nonempty ∨
      expansion.physicalModes.Nonempty := by
  have unionNonempty :=
    expansion.unionNetEnstrophyDebit_pos_iff_modes_nonempty.mp positive
  rcases unionNonempty with ⟨wave, waveMem⟩
  rw [physicalUnionModes, Finset.mem_union] at waveMem
  rcases waveMem with standingMem | actionMem
  · exact Or.inl ⟨wave, standingMem⟩
  · exact Or.inr ⟨wave, actionMem⟩

theorem positive_unionDebit_has_physicalGain
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual)
    (positive : 0 < expansion.unionNetEnstrophyDebit) :
    ∃ wave ∈ expansion.physicalUnionModes,
      complexCoordinateAmplitudeSq
          (material.standingMaterial.rawValuedMaterial.sourcePhysicalState
            wave) <
        complexCoordinateAmplitudeSq
          (material.standingMaterial.rawValuedMaterial.targetPhysicalState
            wave) := by
  rcases expansion.unionNetEnstrophyDebit_pos_iff_modes_nonempty.mp positive with
    ⟨wave, waveMem⟩
  exact ⟨wave, waveMem, expansion.physicalUnionModes_every_gain waveMem⟩

/-- Positivity of the complete residual-expansion valuation is already an
actual Fourier incidence statement.  At least one of the two dependent
inventories generated on this occurrence—the standing fresh-gain face or
the action fresh-gain face—is nonempty.  No detached positive scalar can be
paired with a foreign expansion. -/
theorem positive_totalDebit_has_freshGain
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual)
    (positive : 0 <
      expansion.standingExpansion.finiteNetEnstrophyDebit +
        expansion.finiteNetEnstrophyDebit) :
    expansion.standingExpansion.physicalModes.Nonempty ∨
      expansion.physicalModes.Nonempty := by
  by_cases standingPositive :
      0 < expansion.standingExpansion.finiteNetEnstrophyDebit
  · exact Or.inl
      (expansion.standingExpansion.finiteNetEnstrophyDebit_pos_iff_modes_nonempty.mp
        standingPositive)
  · right
    apply expansion.finiteNetEnstrophyDebit_pos_iff_modes_nonempty.mp
    have standingNonpositive :
        expansion.standingExpansion.finiteNetEnstrophyDebit ≤ 0 :=
      le_of_not_gt standingPositive
    linarith

/-- The nonempty face above contains a literal coefficient-mass gain between
the source and target physical states of this exact material.  The witness
is selected only after the dependent expansion has fixed which of its two
inventories paid. -/
theorem positive_totalDebit_has_physicalGain
    {nu : Viscosity}
    {state : Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
      SourceGeneratedActionMaterialInstructionAt current}
    {material : NativeRestartStandingActionValuedArithmeticMaterialAt state}
    {residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial}
    (expansion : NativeRestartStandingActionResidualExpansionAt
      material residual)
    (positive : 0 <
      expansion.standingExpansion.finiteNetEnstrophyDebit +
        expansion.finiteNetEnstrophyDebit) :
    (∃ wave ∈ expansion.standingExpansion.physicalModes,
      complexCoordinateAmplitudeSq
          (material.standingMaterial.rawValuedMaterial.sourcePhysicalState
            wave) <
        complexCoordinateAmplitudeSq
          (material.standingMaterial.rawValuedMaterial.targetPhysicalState
            wave)) ∨
      (∃ wave ∈ expansion.physicalModes,
        complexCoordinateAmplitudeSq
            (material.standingMaterial.rawValuedMaterial.sourcePhysicalState
              wave) <
          complexCoordinateAmplitudeSq
            (material.standingMaterial.rawValuedMaterial.targetPhysicalState
              wave)) := by
  rcases expansion.positive_totalDebit_has_freshGain positive with
    standingNonempty | actionNonempty
  · left
    rcases standingNonempty with ⟨wave, waveMem⟩
    refine ⟨wave, waveMem, ?_⟩
    have freshMem : wave ∈
        material.standingMaterial.standingValuedFreshGainModes := by
      rw [← expansion.standingExpansion.physicalModes_eq]
      exact waveMem
    exact (Finset.mem_filter.mp freshMem).2
  · right
    rcases actionNonempty with ⟨wave, waveMem⟩
    refine ⟨wave, waveMem, ?_⟩
    have freshMem : wave ∈ material.actionFreshGainModes := by
      rw [← expansion.physicalModes_eq]
      exact waveMem
    exact (Finset.mem_filter.mp freshMem).2

end NativeRestartStandingActionResidualExpansionAt

/-! ## The action material as the authoritative vertical root state -/

/-- Authoritative medium source with exactly one added longitudinal
coordinate: the locally generated action material.  Its operational effect
is the combined standing/action valued material above, so the existing root
normalizer sees the actual y-cell incidence while every complement/cross and
whole-action residual remains on the same provenance.  Neither a paid face
nor a future branch is stored here. -/
def standingActionWholeRestartMediumSource
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)) :
    NativeFluidMediumSource nu where
  State := Sigma fun current : GeneratedWholeRestartRuntimeCurrent nu =>
    SourceGeneratedActionMaterialInstructionAt current
  InternalState := PUnit
  Action := PUnit
  initial := ⟨runRuntime initial 0, initialActionMaterial⟩
  actionAt := fun _ => PUnit.unit
  evolve := fun state _ => ⟨state.1.next, state.2.advance⟩
  OperationalEffectAt := fun state =>
    NativeRestartStandingActionValuedArithmeticMaterialAt state
  operationalEffectAt := fun state =>
    nativeRestartStandingActionValuedArithmeticMaterial state
  operationalArithmeticMaterialAt := fun material =>
    material.arithmeticMaterial
  operationalNetEnstrophyDebitAt := fun material =>
    material.standingMaterial.rawValuedMaterial.netEnstrophyDebit
  operationalContactTimeAt := fun material =>
    material.standingMaterial.contactTime
  operationalContactTime_pos := fun material =>
    material.standingMaterial.contactTime_pos
  OperationalResidualExpansionAt := fun material residual =>
    NativeRestartStandingActionResidualExpansionAt material residual
  generateOperationalResidualExpansionAt := fun material residual =>
    nativeRestartStandingActionResidualExpansion material residual
  operationalResidualExpansionDebitAt := fun _material _residual expansion =>
    expansion.unionNetEnstrophyDebit
  operationalResidualExpansionDebit_nonneg := fun _material _residual
      expansion => expansion.unionNetEnstrophyDebit_nonneg
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
        SourceGeneratedActionMaterialInstructionAt current // patch = state }
  BoundaryAt := fun _ => ComplexVorticityHilbertState
  initialPatch := ⟨⟨runRuntime initial 0, initialActionMaterial⟩, rfl⟩
  advancePatch := by
    intro state patch
    rcases patch with ⟨patch, rfl⟩
    exact ⟨⟨patch.1.next, patch.2.advance⟩, rfl⟩
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

/-- After installing the complete action valuation, an operational
obstruction means that both dependent finite-gain rows are literally silent.
This is stronger than the former adapter, which forgot the action row before
root normalization. -/
theorem standingActionOperationalObstruction_debits_eq_zero
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    (obstruction : NativeFluidMediumOperationalObstructionAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state) :
    obstruction.expansion.standingExpansion.finiteNetEnstrophyDebit = 0 ∧
      obstruction.expansion.finiteNetEnstrophyDebit = 0 := by
  have unionZero := obstruction.residualExpansionDebit_eq_zero
  change obstruction.expansion.unionNetEnstrophyDebit = 0 at unionZero
  have unionModesEmpty : obstruction.expansion.physicalUnionModes = ∅ :=
    obstruction.expansion.unionNetEnstrophyDebit_eq_zero_iff_modes_empty.mp
      unionZero
  have standingModesEmpty :
      obstruction.expansion.standingExpansion.physicalModes = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro nonempty
    rcases nonempty with ⟨wave, waveMem⟩
    have unionMem : wave ∈ obstruction.expansion.physicalUnionModes := by
      change wave ∈ obstruction.expansion.standingExpansion.physicalModes ∪
        obstruction.expansion.physicalModes
      simp [waveMem]
    simpa [unionModesEmpty] using unionMem
  have actionModesEmpty : obstruction.expansion.physicalModes = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro nonempty
    rcases nonempty with ⟨wave, waveMem⟩
    have unionMem : wave ∈ obstruction.expansion.physicalUnionModes := by
      change wave ∈ obstruction.expansion.standingExpansion.physicalModes ∪
        obstruction.expansion.physicalModes
      simp [waveMem]
    simpa [unionModesEmpty] using unionMem
  have standingZeroIff :=
    NativeRestartStandingValuedArithmeticMaterialAt.GeneratedResidualExpansionAt.finiteNetEnstrophyDebit_eq_zero_iff_modes_empty
      obstruction.expansion.standingExpansion
  exact ⟨
    standingZeroIff.mpr standingModesEmpty,
    obstruction.expansion.finiteNetEnstrophyDebit_eq_zero_iff_modes_empty.mpr
      actionModesEmpty⟩

/-- The surviving obstruction is now an exact physical statement: every
Fourier row in the source-generated action capture is nonincreasing in
amplitude mass on this actual endpoint. -/
theorem standingActionOperationalObstruction_actionCapture_nonincrease
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    (obstruction : NativeFluidMediumOperationalObstructionAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state) :
    ∀ wave ∈ obstruction.effect.effect.actionInstruction.advance.modes,
      complexCoordinateAmplitudeSq
          (obstruction.effect.effect.standingMaterial.rawValuedMaterial.targetPhysicalState
            wave) ≤
        complexCoordinateAmplitudeSq
          (obstruction.effect.effect.standingMaterial.rawValuedMaterial.sourcePhysicalState
            wave) := by
  have actionZero :=
    (standingActionOperationalObstruction_debits_eq_zero obstruction).2
  have modesEmpty :=
    obstruction.expansion.finiteNetEnstrophyDebit_eq_zero_iff_modes_empty.mp
      actionZero
  rw [obstruction.expansion.physicalModes_eq] at modesEmpty
  exact obstruction.effect.effect.actionFreshGainModes_eq_empty_iff.mp
    modesEmpty

@[simp] theorem standingActionWholeRestartMediumSource_successor_current
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    ((standingActionWholeRestartMediumSource initialActionMaterial
      ).successor state).1 = state.1.next :=
  rfl

@[simp] theorem standingActionWholeRestartMediumSource_successor_instruction
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    ((standingActionWholeRestartMediumSource initialActionMaterial
      ).successor state).2 = state.2.advance :=
  rfl

/-- The source successor itself consumes the dyadic transport square.  This is
the longitudinal edge missing from the prior fixed-table splice. -/
theorem standingActionRoot_successorChildTransport_commutes
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ state.2.dyadicChildModes) :
    ((standingActionWholeRestartMediumSource initialActionMaterial
        ).successor state).2.dyadicYCellState wave +
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).successor state).2.yCellComplement wave =
      state.1.physical.contact.physicalState wave +
        state.1.physical.nextContact.time.1 •
          wholeLatticeVorticityFourierTangentAt nu.coeff
            state.2.dyadicYCellState wave +
        state.2.yCellEndpointResidual wave := by
  change state.2.advance.dyadicYCellState wave +
      state.2.advance.yCellComplement wave = _
  exact state.2.advanceChildTransport_commutes wave waveMem

/-- The root keeps the original standing incidence.  The action table is a
second dependent projection of the same material, never a replacement
`UnitHistory` whose exactness is chosen from a scalar sign. -/
theorem standingActionOperationalEffect_arithmeticMaterial_eq_standing
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state) :
    effect.arithmeticMaterial =
      (nativeRestartStandingActionValuedArithmeticMaterial state
        ).standingMaterial.arithmeticMaterial := by
  unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
  rw [effect.effect_eq]
  exact (nativeRestartStandingActionValuedArithmeticMaterial state
    ).arithmeticMaterial_eq

theorem standingActionRootExact_paymentIncrement_eq_one
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state)
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) :
    state.1.standing.paymentIncrement = 1 := by
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  have rootCommutes :
      material.standingMaterial.arithmeticMaterial.whole =
        material.standingMaterial.arithmeticMaterial.left.parallel
          material.standingMaterial.arithmeticMaterial.right := by
    rw [← material.arithmeticMaterial_eq]
    unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial at commutes
    rw [effect.effect_eq] at commutes
    exact commutes
  have paid := material.standingMaterial.paymentShadow_eq_one_of_commutes
    rootCommutes
  rw [material.standingMaterial.paymentShadow_eq] at paid
  exact paid

theorem cellStanding_currentLevel_eq_anchorLevel_of_paymentIncrement_eq_one
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    (standing : GeneratedWholeRestartCellStandingAt current)
    (paid : standing.paymentIncrement = 1) :
    wholeRestartCoefficientLevel current.contact = standing.anchorLevel := by
  cases standing with
  | clear => rfl
  | pending debt =>
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition at paid
      cases disposition with
      | settled settlement =>
          exact pendingCell_currentLevel_eq_originLevel_of_paid debt
            settlement.paid
      | retained notPaid =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            dispositionEq] at paid

theorem standingActionRootExact_currentLevel_eq_anchorLevel
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state)
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) :
    wholeRestartCoefficientLevel state.1.physical.contact =
      state.1.standing.anchorLevel :=
  cellStanding_currentLevel_eq_anchorLevel_of_paymentIncrement_eq_one
    state.1.standing
    (standingActionRootExact_paymentIncrement_eq_one effect commutes)

theorem standingActionRootResidual_paymentIncrement_ne_one
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state)
    (residual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial) :
    state.1.standing.paymentIncrement ≠ 1 := by
  intro paid
  let material := nativeRestartStandingActionValuedArithmeticMaterial state
  have shadowOne : material.standingMaterial.paymentShadow = 1 := by
    rw [material.standingMaterial.paymentShadow_eq]
    exact paid
  have standCommutes :=
    material.standingMaterial.commutes_of_paymentShadow_eq_one shadowOne
  apply residual.mismatch
  unfold NativeFluidMediumExactOperationalEffectAt.arithmeticMaterial
  rw [effect.effect_eq]
  change material.arithmeticMaterial.whole =
    material.arithmeticMaterial.left.parallel material.arithmeticMaterial.right
  rw [material.arithmeticMaterial_eq]
  exact standCommutes

/-- The exact finite y-cell convolution table is normalized separately but
with the complete standing/action material as provenance.  Its residual can
therefore be expanded without changing the root incidence or successor. -/
def standingActionTableNormalForm
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    ParallelIncidenceNormalFormAt
      (nativeRestartStandingActionValuedArithmeticMaterial state)
      (nativeRestartStandingActionValuedArithmeticMaterial state
        ).actionArithmeticMaterial :=
  normalizeParallel (nativeRestartStandingActionValuedArithmeticMaterial state)
    (nativeRestartStandingActionValuedArithmeticMaterial state
      ).actionArithmeticMaterial

theorem standingActionTable_exact_iff_actualYCellIncidence
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    (nativeRestartStandingActionValuedArithmeticMaterial state
        ).actionArithmeticMaterial.whole =
      (nativeRestartStandingActionValuedArithmeticMaterial state
        ).actionArithmeticMaterial.left.parallel
        (nativeRestartStandingActionValuedArithmeticMaterial state
          ).actionArithmeticMaterial.right ↔
      ButterflyActualYCellChildIncidenceAt state.2 :=
  (nativeRestartStandingActionValuedArithmeticMaterial state
    ).actionArithmeticExact_iff_actualYCellIncidence

@[simp] theorem standingActionWholeRestartMediumSource_stateAfter_current
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)) :
    ∀ stage : Nat,
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).1 = runRuntime initial stage
  | 0 => rfl
  | stage + 1 => by
      change
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage).1.next = (runRuntime initial stage).next
      rw [standingActionWholeRestartMediumSource_stateAfter_current]

theorem standingActionWholeRestartMediumSource_stateAfter_cellScale
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)) :
    ∀ stage : Nat,
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).2.cellScale =
        initialActionMaterial.cellScale *
          2 ^ runCellPaymentCount initial stage
  | 0 => by
      change initialActionMaterial.cellScale =
        initialActionMaterial.cellScale * 2 ^ 0
      simp
  | stage + 1 => by
      change
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage).2.advance.cellScale =
          initialActionMaterial.cellScale *
            2 ^ (runCellPaymentCount initial stage +
              (runCellStanding initial stage).paymentIncrement)
      rw [SourceGeneratedActionMaterialInstructionAt.advance_cellScale_eq,
        standingActionWholeRestartMediumSource_stateAfter_cellScale,
        standingActionWholeRestartMediumSource_stateAfter_current]
      rw [pow_add]
      ac_rfl


/-- One normalization of the standing incidence and one normalization of its
installed action table.  The six constructors are the literal product of the
two source-generated normal forms; neither projection can select the other or
the compiler-owned successor. -/
inductive SourceGeneratedStandingActionTotalEffectAt
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    NativeFluidMediumRootOperationalOutcomeAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state →
        Type
  | jointPayment
      {effect : NativeFluidMediumExactOperationalEffectAt
        (standingActionWholeRestartMediumSource initialActionMaterial) state}
      {rooted : IncidenceProvenanceAt effect.effect}
      {commutes : effect.arithmeticMaterial.whole =
        effect.arithmeticMaterial.left.parallel
          effect.arithmeticMaterial.right}
      (actionRooted : IncidenceProvenanceAt
        (nativeRestartStandingActionValuedArithmeticMaterial state))
      (actionCommutes :
        (nativeRestartStandingActionValuedArithmeticMaterial state
            ).actionArithmeticMaterial.whole =
          (nativeRestartStandingActionValuedArithmeticMaterial state
            ).actionArithmeticMaterial.left.parallel
            (nativeRestartStandingActionValuedArithmeticMaterial state
              ).actionArithmeticMaterial.right) :
      SourceGeneratedStandingActionTotalEffectAt state
        (.exactPayment effect rooted commutes)
  | standingPayment
      {effect : NativeFluidMediumExactOperationalEffectAt
        (standingActionWholeRestartMediumSource initialActionMaterial) state}
      {rooted : IncidenceProvenanceAt effect.effect}
      {commutes : effect.arithmeticMaterial.whole =
        effect.arithmeticMaterial.left.parallel
          effect.arithmeticMaterial.right}
      (actionResidual : GeneratedParallelResidualAt
        (nativeRestartStandingActionValuedArithmeticMaterial state)
        (nativeRestartStandingActionValuedArithmeticMaterial state
          ).actionArithmeticMaterial) :
      SourceGeneratedStandingActionTotalEffectAt state
        (.exactPayment effect rooted commutes)
  | actionIncidenceResidual
      {effect : NativeFluidMediumExactOperationalEffectAt
        (standingActionWholeRestartMediumSource initialActionMaterial) state}
      {residual : GeneratedParallelResidualAt
        effect.effect effect.arithmeticMaterial}
      {expansion : (standingActionWholeRestartMediumSource
        initialActionMaterial).OperationalResidualExpansionAt
          effect.effect residual}
      {expansion_eq : expansion =
        (standingActionWholeRestartMediumSource initialActionMaterial
          ).generateOperationalResidualExpansionAt effect.effect residual}
      {payment : NativeFluidMediumResidualPaymentAt effect residual expansion}
      (actionRooted : IncidenceProvenanceAt
        (nativeRestartStandingActionValuedArithmeticMaterial state))
      (actionCommutes :
        (nativeRestartStandingActionValuedArithmeticMaterial state
            ).actionArithmeticMaterial.whole =
          (nativeRestartStandingActionValuedArithmeticMaterial state
            ).actionArithmeticMaterial.left.parallel
            (nativeRestartStandingActionValuedArithmeticMaterial state
              ).actionArithmeticMaterial.right) :
      SourceGeneratedStandingActionTotalEffectAt state
        (.generatedResidual effect residual expansion expansion_eq payment)
  | coupledResidual
      {effect : NativeFluidMediumExactOperationalEffectAt
        (standingActionWholeRestartMediumSource initialActionMaterial) state}
      {residual : GeneratedParallelResidualAt
        effect.effect effect.arithmeticMaterial}
      {expansion : (standingActionWholeRestartMediumSource
        initialActionMaterial).OperationalResidualExpansionAt
          effect.effect residual}
      {expansion_eq : expansion =
        (standingActionWholeRestartMediumSource initialActionMaterial
          ).generateOperationalResidualExpansionAt effect.effect residual}
      {payment : NativeFluidMediumResidualPaymentAt effect residual expansion}
      (actionResidual : GeneratedParallelResidualAt
        (nativeRestartStandingActionValuedArithmeticMaterial state)
        (nativeRestartStandingActionValuedArithmeticMaterial state
          ).actionArithmeticMaterial) :
      SourceGeneratedStandingActionTotalEffectAt state
        (.generatedResidual effect residual expansion expansion_eq payment)
  | actionIncidenceObstruction
      {obstruction : NativeFluidMediumOperationalObstructionAt
        (standingActionWholeRestartMediumSource initialActionMaterial) state}
      {demand : SourceGeneratedU7DemandAt
        (nativeFluidMediumU7Producer
          (standingActionWholeRestartMediumSource initialActionMaterial))
        obstruction
        ((nativeFluidMediumU7Producer
          (standingActionWholeRestartMediumSource initialActionMaterial)
          ).generateDemand obstruction)}
      (actionRooted : IncidenceProvenanceAt
        (nativeRestartStandingActionValuedArithmeticMaterial state))
      (actionCommutes :
        (nativeRestartStandingActionValuedArithmeticMaterial state
            ).actionArithmeticMaterial.whole =
          (nativeRestartStandingActionValuedArithmeticMaterial state
            ).actionArithmeticMaterial.left.parallel
            (nativeRestartStandingActionValuedArithmeticMaterial state
              ).actionArithmeticMaterial.right) :
      SourceGeneratedStandingActionTotalEffectAt state
        (.obstruction obstruction demand)
  | coupledObstruction
      {obstruction : NativeFluidMediumOperationalObstructionAt
        (standingActionWholeRestartMediumSource initialActionMaterial) state}
      {demand : SourceGeneratedU7DemandAt
        (nativeFluidMediumU7Producer
          (standingActionWholeRestartMediumSource initialActionMaterial))
        obstruction
        ((nativeFluidMediumU7Producer
          (standingActionWholeRestartMediumSource initialActionMaterial)
          ).generateDemand obstruction)}
      (actionResidual : GeneratedParallelResidualAt
        (nativeRestartStandingActionValuedArithmeticMaterial state)
        (nativeRestartStandingActionValuedArithmeticMaterial state
          ).actionArithmeticMaterial) :
      SourceGeneratedStandingActionTotalEffectAt state
        (.obstruction obstruction demand)

noncomputable def sourceGeneratedStandingActionTotalEffect
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    SourceGeneratedStandingActionTotalEffectAt state
      (nativeFluidMediumRootOperationalOutcomeAt
        (standingActionWholeRestartMediumSource initialActionMaterial)
        state) := by
  generalize actionNormalFormEq :
    standingActionTableNormalForm state = actionNormalForm
  cases actionNormalForm with
  | exact actionRooted actionCommutes =>
      generalize outcomeEq :
        nativeFluidMediumRootOperationalOutcomeAt
          (standingActionWholeRestartMediumSource initialActionMaterial) state =
            outcome
      cases outcome with
      | exactPayment => exact .jointPayment actionRooted actionCommutes
      | generatedResidual =>
          exact .actionIncidenceResidual actionRooted actionCommutes
      | obstruction =>
          exact .actionIncidenceObstruction actionRooted actionCommutes
  | generatedResidual actionResidual =>
      generalize outcomeEq :
        nativeFluidMediumRootOperationalOutcomeAt
          (standingActionWholeRestartMediumSource initialActionMaterial) state =
            outcome
      cases outcome with
      | exactPayment => exact .standingPayment actionResidual
      | generatedResidual => exact .coupledResidual actionResidual
      | obstruction => exact .coupledObstruction actionResidual

namespace SourceGeneratedStandingActionTotalEffectAt

def actionEdgePayment
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    {outcome : NativeFluidMediumRootOperationalOutcomeAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state} :
    SourceGeneratedStandingActionTotalEffectAt state outcome → Option (PLift
      (state.1.physical.nextContact.time.1 *
          (nativeRestartStandingActionValuedArithmeticMaterial state
            ).yCellCoreCharge ≤
        (nativeRestartStandingActionValuedArithmeticMaterial state
          ).actionInstruction.dyadicChildReadout
            state.1.physical.nextContact.physicalState -
          (nativeRestartStandingActionValuedArithmeticMaterial state
            ).actionInstruction.dyadicChildReadout
              state.1.physical.contact.physicalState))
  | .jointPayment _rooted commutes =>
      some ⟨(nativeRestartStandingActionValuedArithmeticMaterial state
        ).clock_mul_yCellCoreCharge_le_faceReadoutGain_of_arithmeticExact
          commutes⟩
  | .standingPayment _ => none
  | .actionIncidenceResidual _rooted commutes =>
      some ⟨(nativeRestartStandingActionValuedArithmeticMaterial state
        ).clock_mul_yCellCoreCharge_le_faceReadoutGain_of_arithmeticExact
          commutes⟩
  | .coupledResidual _ => none
  | .actionIncidenceObstruction _rooted commutes =>
      some ⟨(nativeRestartStandingActionValuedArithmeticMaterial state
        ).clock_mul_yCellCoreCharge_le_faceReadoutGain_of_arithmeticExact
          commutes⟩
  | .coupledObstruction _ => none

theorem successorCellScale
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    {outcome : NativeFluidMediumRootOperationalOutcomeAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state}
    (total : SourceGeneratedStandingActionTotalEffectAt state outcome) :
    match total with
    | .jointPayment _actionRooted _actionCommutes =>
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).successor state).2.cellScale = 2 * state.2.cellScale
    | .standingPayment _actionResidual =>
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).successor state).2.cellScale = 2 * state.2.cellScale
    | .actionIncidenceResidual _actionRooted _actionCommutes =>
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).successor state).2.cellScale = state.2.cellScale
    | .coupledResidual _actionResidual =>
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).successor state).2.cellScale = state.2.cellScale
    | .actionIncidenceObstruction _actionRooted _actionCommutes =>
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).successor state).2.cellScale = state.2.cellScale
    | .coupledObstruction _actionResidual =>
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).successor state).2.cellScale = state.2.cellScale := by
  cases total with
  | jointPayment actionRooted actionCommutes =>
      rename_i effect rooted rootCommutes
      change state.2.advance.cellScale = 2 * state.2.cellScale
      apply state.2.advance_cellScale_of_payment
      exact standingActionRootExact_paymentIncrement_eq_one
        effect rootCommutes
  | standingPayment actionResidual =>
      rename_i effect rooted rootCommutes
      change state.2.advance.cellScale = 2 * state.2.cellScale
      apply state.2.advance_cellScale_of_payment
      exact standingActionRootExact_paymentIncrement_eq_one
        effect rootCommutes
  | actionIncidenceResidual actionRooted actionCommutes =>
      rename_i effect rootResidual expansion expansionEq payment
      change state.2.advance.cellScale = state.2.cellScale
      apply state.2.advance_cellScale_of_nonpayment
      intro paid
      exact (standingActionRootResidual_paymentIncrement_ne_one
        effect rootResidual)
        paid
  | coupledResidual actionResidual =>
      rename_i effect rootResidual expansion expansionEq payment
      change state.2.advance.cellScale = state.2.cellScale
      apply state.2.advance_cellScale_of_nonpayment
      exact standingActionRootResidual_paymentIncrement_ne_one
        effect rootResidual
  | actionIncidenceObstruction actionRooted actionCommutes =>
      rename_i obstruction demand
      change state.2.advance.cellScale = state.2.cellScale
      apply state.2.advance_cellScale_of_nonpayment
      exact (standingActionRootResidual_paymentIncrement_ne_one
        obstruction.effect obstruction.residual)
  | coupledObstruction actionResidual =>
      rename_i obstruction demand
      change state.2.advance.cellScale = state.2.cellScale
      apply state.2.advance_cellScale_of_nonpayment
      exact standingActionRootResidual_paymentIncrement_ne_one
        obstruction.effect obstruction.residual

end SourceGeneratedStandingActionTotalEffectAt

/-! ## Canonical root-payment barrier reserve -/

def standingActionBarrierModel
    (nu : Viscosity) (level : Nat) : Real :=
  (ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient
      nu * (level : Real) ^ 7)⁻¹

def standingActionBarrierTail
    (nu : Viscosity) (level : Nat) : Real :=
  ∑' offset : Nat, standingActionBarrierModel nu (level + offset)

theorem summable_standingActionBarrierModel
    (nu : Viscosity) :
    Summable (standingActionBarrierModel nu) := by
  have pSeries : Summable fun level : Nat =>
      1 / ((level : Real) ^ (7 : Nat)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have scaled := pSeries.mul_left
    (ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient
      nu)⁻¹
  apply scaled.congr
  intro level
  unfold standingActionBarrierModel
  rw [mul_inv_rev]
  simp only [one_div, mul_comm]

theorem standingActionBarrierTail_nonneg
    (nu : Viscosity) (level : Nat) :
    0 ≤ standingActionBarrierTail nu level := by
  unfold standingActionBarrierTail standingActionBarrierModel
  apply tsum_nonneg
  intro offset
  apply inv_nonneg.mpr
  exact mul_nonneg
    (ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient_pos
      nu).le
    (pow_nonneg (Nat.cast_nonneg _) 7)

theorem standingActionBarrierTail_step
    (nu : Viscosity) (level : Nat) :
    standingActionBarrierTail nu level =
      standingActionBarrierModel nu level +
        standingActionBarrierTail nu (level + 1) := by
  let shifted := fun offset : Nat =>
    standingActionBarrierModel nu (level + offset)
  have shiftedSummable : Summable shifted := by
    dsimp only [shifted]
    have shiftedRight : Summable fun offset =>
        standingActionBarrierModel nu (offset + level) :=
      (summable_nat_add_iff
        (f := standingActionBarrierModel nu) level).mpr
          (summable_standingActionBarrierModel nu)
    exact shiftedRight.congr fun offset => by
      rw [Nat.add_comm]
  have split := shiftedSummable.sum_add_tsum_nat_add 1
  simpa only [standingActionBarrierTail, shifted, Finset.sum_range_one,
    Nat.add_zero, Nat.add_assoc, Nat.one_add, Nat.add_comm,
    Nat.add_left_comm] using split.symm

theorem standingActionRootExact_clock_le_barrierModel
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage))
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) :
    (standingActionWholeRestartMediumSource initialActionMaterial).clockAt
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage) ≤
      standingActionBarrierModel butterflyGainViscosity
        (runCellStanding initial stage).anchorLevel := by
  have currentEq :=
    standingActionWholeRestartMediumSource_stateAfter_current
      initialActionMaterial stage
  have levelEq :=
    standingActionRootExact_currentLevel_eq_anchorLevel effect commutes
  rw [currentEq] at levelEq
  have ceilingEq :
      restartCoefficientCeiling initial stage =
        ((runCellStanding initial stage).anchorLevel : Real) := by
    unfold restartCoefficientCeiling wholeRestartCoefficientCeiling
    exact_mod_cast levelEq
  have ceilingPos := restartCoefficientCeiling_pos initial stage
  have coefficientPos :=
    ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient_pos
      butterflyGainViscosity
  have modelBasePos :
      0 <
        ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient
            butterflyGainViscosity *
          restartCoefficientCeiling initial stage ^ 7 :=
    mul_pos coefficientPos (pow_pos ceilingPos 7)
  have barrierLower :=
    ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventh_le
      butterflyGainViscosity (restartCoefficientCeiling initial stage)
        ceilingPos.le
  change
    ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient
          butterflyGainViscosity *
        restartCoefficientCeiling initial stage ^ 7 + 1 ≤
      restartBarrierSlope initial stage at barrierLower
  have modelBaseLe :
      ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient
            butterflyGainViscosity *
          restartCoefficientCeiling initial stage ^ 7 ≤
        restartBarrierSlope initial stage := by
    linarith
  have reciprocalLe :
      (restartBarrierSlope initial stage)⁻¹ ≤
        (ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient
            butterflyGainViscosity *
          restartCoefficientCeiling initial stage ^ 7)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le modelBasePos modelBaseLe)
  have clockLe := successorContactTime_le_reciprocalBarrier initial stage
  rw [run_succ, next_contact] at clockLe
  change
    ((standingActionWholeRestartMediumSource initialActionMaterial
      ).stateAfter stage).1.physical.nextContact.time.1 ≤ _
  rw [currentEq]
  change (run initial stage).nextContact.time.1 ≤ _
  calc
    (run initial stage).nextContact.time.1 ≤
        (restartBarrierSlope initial stage)⁻¹ := clockLe
    _ ≤
        (ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier.sourceOwnedWholeStateBarrierSeventhCoefficient
            butterflyGainViscosity *
          restartCoefficientCeiling initial stage ^ 7)⁻¹ := reciprocalLe
    _ = standingActionBarrierModel butterflyGainViscosity
        (runCellStanding initial stage).anchorLevel := by
      rw [ceilingEq]
      rfl

/-- Finite kinetic-capacity potential for one frozen dyadic face.  The face is
allowed to cross a root edge only when that edge retains the action cell
standing; the definition itself contains no future state. -/
def standingActionFrozenDyadicFacePotential
    {sourceCurrent : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt sourceCurrent)
    (runtime : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity) :
    Real :=
  (standingPaidFaceCapacity runtime instruction.dyadicChildModes + 5 -
      instruction.dyadicChildReadout
        runtime.physical.contact.physicalState) /
    instruction.yCellCoreCharge

theorem standingActionFrozenDyadicFacePotential_nonneg
    {sourceCurrent : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt sourceCurrent)
    (runtime : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity) :
    0 ≤ standingActionFrozenDyadicFacePotential instruction runtime := by
  unfold standingActionFrozenDyadicFacePotential
  apply div_nonneg _ instruction.yCellCoreCharge_pos.le
  apply sub_nonneg.mpr
  calc
    instruction.dyadicChildReadout
          runtime.physical.contact.physicalState ≤
        finiteStateVorticityCoefficientEnstrophy
            instruction.dyadicChildModes
            runtime.physical.contact.physicalState + 5 :=
      instruction.dyadicChildReadout_le_finiteMass_add_five _
    _ = standingPaidFaceMass runtime instruction.dyadicChildModes + 5 := rfl
    _ ≤ standingPaidFaceCapacity runtime instruction.dyadicChildModes + 5 := by
      linarith [standingPaidFaceMass_le_capacity runtime
        instruction.dyadicChildModes
        instruction.dyadicChildModes_zeroNotMem]

/-- The finite capacity of the current dyadic child face grows quadratically
in its source scale, while its exact action charge grows quartically.  Hence
one frozen-face clock block has a source-generated inverse-square reserve.
No endpoint sign or future branch enters this comparison. -/
theorem standingActionFrozenDyadicFacePotential_le_inverseSquare
    {sourceCurrent : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt sourceCurrent)
    (runtime : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity)
    (kineticUpper : Real)
    (kineticUpper_nonneg : 0 ≤ kineticUpper)
    (kinetic_le :
      puncturedWholeVorticityKineticMass
          runtime.physical.contact.physicalState ≤ kineticUpper) :
    standingActionFrozenDyadicFacePotential instruction runtime ≤
      (400000 * kineticUpper + 1000) /
        (instruction.cellScale : Real) ^ 2 := by
  let scale : Real := instruction.cellScale
  let capacity := standingPaidFaceCapacity runtime
    instruction.dyadicChildModes
  let readout := instruction.dyadicChildReadout
    runtime.physical.contact.physicalState
  have scaleFour : (4 : Real) ≤ scale := by
    dsimp only [scale]
    exact_mod_cast instruction.cellScale_four
  have scaleSqPos : 0 < scale ^ 2 := by positivity
  have scaleSqOne : (1 : Real) ≤ scale ^ 2 := by nlinarith
  have kineticNonneg :
      0 ≤ puncturedWholeVorticityKineticMass
        runtime.physical.contact.physicalState :=
    ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation.puncturedWholeVorticityKineticMass_nonneg _
  have capacityLe : capacity ≤ 2000 * scale ^ 2 * kineticUpper := by
    dsimp only [capacity, scale]
    unfold standingPaidFaceCapacity
    calc
      finiteModeKineticAmbientFactor instruction.dyadicChildModes *
            puncturedWholeVorticityKineticMass
              runtime.physical.contact.physicalState ≤
          (2000 * (instruction.cellScale : Real) ^ 2) *
            puncturedWholeVorticityKineticMass
              runtime.physical.contact.physicalState :=
        mul_le_mul_of_nonneg_right instruction.dyadicChildAmbientFactor_le
          kineticNonneg
      _ ≤ (2000 * (instruction.cellScale : Real) ^ 2) * kineticUpper :=
        mul_le_mul_of_nonneg_left kinetic_le (by positivity)
  have negReadoutLe : -readout ≤ capacity + 5 := by
    dsimp only [readout, capacity]
    calc
      -instruction.dyadicChildReadout
            runtime.physical.contact.physicalState ≤
          finiteStateVorticityCoefficientEnstrophy
              instruction.dyadicChildModes
              runtime.physical.contact.physicalState + 5 :=
        instruction.neg_dyadicChildReadout_le_finiteMass_add_five _
      _ = standingPaidFaceMass runtime instruction.dyadicChildModes + 5 := rfl
      _ ≤ standingPaidFaceCapacity runtime instruction.dyadicChildModes + 5 := by
        linarith [standingPaidFaceMass_le_capacity runtime
          instruction.dyadicChildModes
          instruction.dyadicChildModes_zeroNotMem]
  have numeratorLe :
      capacity + 5 - readout ≤
        (400000 * kineticUpper + 1000) * scale ^ 2 / 100 := by
    nlinarith
  have chargeLower : scale ^ 4 / 100 ≤ instruction.yCellCoreCharge := by
    dsimp only [scale]
    exact instruction.scaleFourth_div_hundred_le_dyadicCoreCharge
  have reserveNonneg :
      0 ≤ (400000 * kineticUpper + 1000) / scale ^ 2 := by positivity
  have reserveTimesCharge :
      (400000 * kineticUpper + 1000) * scale ^ 2 / 100 ≤
        ((400000 * kineticUpper + 1000) / scale ^ 2) *
          instruction.yCellCoreCharge := by
    calc
      (400000 * kineticUpper + 1000) * scale ^ 2 / 100 =
          ((400000 * kineticUpper + 1000) / scale ^ 2) *
            (scale ^ 4 / 100) := by
        field_simp [scaleSqPos.ne']
      _ ≤ ((400000 * kineticUpper + 1000) / scale ^ 2) *
            instruction.yCellCoreCharge :=
        mul_le_mul_of_nonneg_left chargeLower reserveNonneg
  unfold standingActionFrozenDyadicFacePotential
  apply (div_le_iff₀ instruction.yCellCoreCharge_pos).2
  dsimp only [capacity, readout, scale] at numeratorLe reserveTimesCharge ⊢
  exact numeratorLe.trans reserveTimesCharge

theorem standingActionFrozenDyadicFacePotential_stateAfter_le_inverseSquare
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat) :
    let state := (standingActionWholeRestartMediumSource
      initialActionMaterial).stateAfter stage
    standingActionFrozenDyadicFacePotential state.2 state.1 ≤
      (400000 * puncturedWholeVorticityKineticMass
          initial.contact.physicalState + 1000) /
        (state.2.cellScale : Real) ^ 2 := by
  dsimp only
  apply standingActionFrozenDyadicFacePotential_le_inverseSquare
    _ _ (puncturedWholeVorticityKineticMass initial.contact.physicalState)
  · exact
      ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation.puncturedWholeVorticityKineticMass_nonneg _
  · rw [standingActionWholeRestartMediumSource_stateAfter_current]
    change
      puncturedWholeVorticityKineticMass
          (run initial stage).contact.physicalState ≤
        puncturedWholeVorticityKineticMass
          (run initial 0).contact.physicalState
    exact (run_contact_kineticMass_antitone initial) (Nat.zero_le stage)

def standingActionDyadicCapacityConstant
    (initial : GeneratedWholeRestartCurrent butterflyGainViscosity) : Real :=
  400000 * puncturedWholeVorticityKineticMass
      initial.contact.physicalState + 1000

def standingActionDyadicResetReserve
    {sourceCurrent : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity}
    (initial : GeneratedWholeRestartCurrent butterflyGainViscosity)
    (instruction : SourceGeneratedActionMaterialInstructionAt sourceCurrent) :
    Real :=
  standingActionDyadicCapacityConstant initial /
    (3 * (instruction.cellScale : Real) ^ 2)

theorem standingActionDyadicCapacityConstant_nonneg
    (initial : GeneratedWholeRestartCurrent butterflyGainViscosity) :
    0 ≤ standingActionDyadicCapacityConstant initial := by
  unfold standingActionDyadicCapacityConstant
  have kineticNonneg :=
    ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation.puncturedWholeVorticityKineticMass_nonneg
      initial.contact.physicalState
  positivity

theorem standingActionDyadicResetReserve_nonneg
    {sourceCurrent : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity}
    (initial : GeneratedWholeRestartCurrent butterflyGainViscosity)
    (instruction : SourceGeneratedActionMaterialInstructionAt sourceCurrent) :
    0 ≤ standingActionDyadicResetReserve initial instruction := by
  unfold standingActionDyadicResetReserve
  positivity [standingActionDyadicCapacityConstant_nonneg initial]

theorem standingActionFrozenDyadicFacePotential_eq_of_cellScale_eq
    {leftCurrent rightCurrent : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity}
    (left : SourceGeneratedActionMaterialInstructionAt leftCurrent)
    (right : SourceGeneratedActionMaterialInstructionAt rightCurrent)
    (runtime : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity)
    (scaleEq : left.cellScale = right.cellScale) :
    standingActionFrozenDyadicFacePotential left runtime =
      standingActionFrozenDyadicFacePotential right runtime := by
  have axisEq : left.dyadicChildAxis = right.dyadicChildAxis := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildAxis
    rw [scaleEq]
  have plusEq : left.dyadicChildPlus = right.dyadicChildPlus := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildPlus
    rw [axisEq]
  have minusEq : left.dyadicChildMinus = right.dyadicChildMinus := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildMinus
    rw [axisEq]
  have modesEq : left.dyadicChildModes = right.dyadicChildModes := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildModes
    rw [axisEq, plusEq, minusEq]
  have xEq : left.dyadicX = right.dyadicX := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicX
    rw [scaleEq]
  have zEq : left.dyadicZ = right.dyadicZ := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicZ
    rw [xEq]
  have yEq : left.dyadicY = right.dyadicY := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicY
    rw [xEq]
  have wEq : left.dyadicW = right.dyadicW := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicW
    rw [xEq]
  have stateEq : left.dyadicYCellState = right.dyadicYCellState := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicYCellState
    rw [scaleEq, xEq, zEq, yEq, wEq]
  have readoutOfEq : left.dyadicChildReadoutOf =
      right.dyadicChildReadoutOf := by
    funext state
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildReadoutOf
    rw [axisEq, plusEq, minusEq]
  have readoutEq :
      left.dyadicChildReadout runtime.physical.contact.physicalState =
        right.dyadicChildReadout runtime.physical.contact.physicalState := by
    unfold SourceGeneratedActionMaterialInstructionAt.dyadicChildReadout
    rw [readoutOfEq]
  have chargeEq : left.yCellCoreCharge = right.yCellCoreCharge := by
    unfold SourceGeneratedActionMaterialInstructionAt.yCellCoreCharge
      SourceGeneratedActionMaterialInstructionAt.dyadicCoreCharge
    rw [readoutOfEq, stateEq]
  unfold standingActionFrozenDyadicFacePotential standingPaidFaceCapacity
  rw [modesEq, readoutEq, chargeEq]

def standingActionMixedClockPotential
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) : Real :=
  standingActionBarrierTail butterflyGainViscosity
      state.1.standing.anchorLevel +
    standingActionDyadicResetReserve initial state.2 +
    standingActionFrozenDyadicFacePotential state.2 state.1

theorem standingActionMixedClockPotential_nonneg
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    0 ≤ standingActionMixedClockPotential state := by
  unfold standingActionMixedClockPotential
  exact add_nonneg
    (add_nonneg
      (standingActionBarrierTail_nonneg _ _)
      (standingActionDyadicResetReserve_nonneg initial state.2))
    (standingActionFrozenDyadicFacePotential_nonneg state.2 state.1)

def standingActionMixedClockState
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    SourceGeneratedRootClockStateAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state where
  potential := standingActionMixedClockPotential state
  potential_nonneg := standingActionMixedClockPotential_nonneg state

def sourceGeneratedRootClockAdvance_of_potential_domination
    {nu : Viscosity}
    {source : NativeFluidMediumSource nu}
    {state : source.State}
    {currentClock : SourceGeneratedRootClockStateAt source state}
    {nextClock : SourceGeneratedRootClockStateAt source (source.successor state)}
    (domination : source.clockAt state + nextClock.potential ≤
      currentClock.potential) :
    SourceGeneratedRootClockAdvanceAt source state currentClock nextClock where
  waste := currentClock.potential - source.clockAt state - nextClock.potential
  waste_nonneg := by linarith
  settlement := by ring

theorem standingActionDyadicReset_add_nextFace_le
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat)
    (scaleDouble :
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter (stage + 1)).2.cellScale =
        2 * ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage).2.cellScale) :
    standingActionDyadicResetReserve initial
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).2 +
        standingActionFrozenDyadicFacePotential
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).2
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).1 ≤
      standingActionDyadicResetReserve initial
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage).2 := by
  let currentInstruction :=
    ((standingActionWholeRestartMediumSource initialActionMaterial
      ).stateAfter stage).2
  let nextInstruction :=
    ((standingActionWholeRestartMediumSource initialActionMaterial
      ).stateAfter (stage + 1)).2
  let constant := standingActionDyadicCapacityConstant initial
  have constantNonneg : 0 ≤ constant := by
    exact standingActionDyadicCapacityConstant_nonneg initial
  have scalePos : 0 < (currentInstruction.cellScale : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4)
      currentInstruction.cellScale_four)
  have nextFaceLe :=
    standingActionFrozenDyadicFacePotential_stateAfter_le_inverseSquare
      initialActionMaterial (stage + 1)
  have algebra :
      constant / (3 * ((2 * currentInstruction.cellScale : Nat) : Real) ^ 2) +
          constant / (((2 * currentInstruction.cellScale : Nat) : Real) ^ 2) =
        constant / (3 * (currentInstruction.cellScale : Real) ^ 2) := by
    norm_num [Nat.cast_mul]
    field_simp [scalePos.ne']
    ring
  change
    standingActionDyadicResetReserve initial nextInstruction +
        standingActionFrozenDyadicFacePotential nextInstruction
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).1 ≤
      standingActionDyadicResetReserve initial currentInstruction
  unfold standingActionDyadicResetReserve
  dsimp only [nextInstruction, currentInstruction, constant]
  rw [scaleDouble]
  dsimp only at nextFaceLe
  rw [scaleDouble] at nextFaceLe
  change
    standingActionFrozenDyadicFacePotential
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).2
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).1 ≤
      standingActionDyadicCapacityConstant initial /
        (((2 * ((standingActionWholeRestartMediumSource
          initialActionMaterial).stateAfter stage).2.cellScale : Nat) : Real) ^ 2)
    at nextFaceLe
  calc
    standingActionDyadicCapacityConstant initial /
          (3 * ((2 *
            ((standingActionWholeRestartMediumSource initialActionMaterial
              ).stateAfter stage).2.cellScale : Nat) : Real) ^ 2) +
        standingActionFrozenDyadicFacePotential
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).2
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1)).1 ≤
      standingActionDyadicCapacityConstant initial /
          (3 * ((2 *
            ((standingActionWholeRestartMediumSource initialActionMaterial
              ).stateAfter stage).2.cellScale : Nat) : Real) ^ 2) +
        standingActionDyadicCapacityConstant initial /
          (((2 *
            ((standingActionWholeRestartMediumSource initialActionMaterial
              ).stateAfter stage).2.cellScale : Nat) : Real) ^ 2) :=
      by linarith
    _ = standingActionDyadicCapacityConstant initial /
          (3 * (((standingActionWholeRestartMediumSource
            initialActionMaterial).stateAfter stage).2.cellScale : Real) ^ 2) :=
      algebra

def standingActionRootExactMixedClockAdvance
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage))
    (commutes : effect.arithmeticMaterial.whole =
      effect.arithmeticMaterial.left.parallel
        effect.arithmeticMaterial.right) :
    SourceGeneratedRootClockAdvanceAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage)
      (standingActionMixedClockState
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage))
      (standingActionMixedClockState
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter (stage + 1))) := by
  let state := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter stage
  let nextState := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter (stage + 1)
  have anchorCurrent : state.1.standing.anchorLevel =
      (runCellStanding initial stage).anchorLevel := by
    dsimp only [state]
    rw [standingActionWholeRestartMediumSource_stateAfter_current]
    rfl
  have paid := standingActionRootExact_paymentIncrement_eq_one effect commutes
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel + 1 := by
    dsimp only [nextState, state]
    change
      (((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).1.standing.next).anchorLevel = _
    rw [cellStanding_anchorLevel_next, paid]
  have scaleDouble : nextState.2.cellScale = 2 * state.2.cellScale := by
    dsimp only [nextState, state]
    change
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).2.advance.cellScale = _
    exact ((standingActionWholeRestartMediumSource initialActionMaterial
      ).stateAfter stage).2.advance_cellScale_of_payment paid
  have clockLe := standingActionRootExact_clock_le_barrierModel
    initialActionMaterial stage effect commutes
  have resetPays := standingActionDyadicReset_add_nextFace_le
    initialActionMaterial stage scaleDouble
  have currentFaceNonneg :=
    standingActionFrozenDyadicFacePotential_nonneg state.2 state.1
  have tailStep := standingActionBarrierTail_step butterflyGainViscosity
    state.1.standing.anchorLevel
  rw [← anchorCurrent] at clockLe
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    (standingActionWholeRestartMediumSource initialActionMaterial).clockAt state +
        standingActionMixedClockPotential nextState ≤
      standingActionMixedClockPotential state
  unfold standingActionMixedClockPotential
  rw [tailStep, anchorNext]
  dsimp only [state, nextState] at clockLe resetPays currentFaceNonneg ⊢
  linarith

def standingActionRootResidualActionExactMixedClockAdvance
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage))
    (rootResidual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial)
    (actionCommutes :
      (nativeRestartStandingActionValuedArithmeticMaterial
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter stage)).actionArithmeticMaterial.whole =
        (nativeRestartStandingActionValuedArithmeticMaterial
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter stage)).actionArithmeticMaterial.left.parallel
          (nativeRestartStandingActionValuedArithmeticMaterial
            ((standingActionWholeRestartMediumSource initialActionMaterial
              ).stateAfter stage)).actionArithmeticMaterial.right) :
    SourceGeneratedRootClockAdvanceAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage)
      (standingActionMixedClockState
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage))
      (standingActionMixedClockState
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter (stage + 1))) := by
  let state := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter stage
  let nextState := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter (stage + 1)
  have notPaid := standingActionRootResidual_paymentIncrement_ne_one
    effect rootResidual
  have incrementLe :=
    NativeRestartStandingValuedArithmeticMaterialAt.standing_paymentIncrement_le_one
      state.1.standing
  have incrementZero : state.1.standing.paymentIncrement = 0 := by
    dsimp only [state] at notPaid incrementLe ⊢
    omega
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel := by
    dsimp only [nextState, state]
    change
      (((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).1.standing.next).anchorLevel = _
    rw [cellStanding_anchorLevel_next, incrementZero, Nat.add_zero]
  have scaleSame : nextState.2.cellScale = state.2.cellScale := by
    dsimp only [nextState, state]
    change
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).2.advance.cellScale = _
    exact ((standingActionWholeRestartMediumSource initialActionMaterial
      ).stateAfter stage).2.advance_cellScale_of_nonpayment notPaid
  have edgePayment :=
    (nativeRestartStandingActionValuedArithmeticMaterial state
      ).clock_mul_yCellCoreCharge_le_faceReadoutGain_of_arithmeticExact
        actionCommutes
  have edgePayment' :
      state.1.physical.nextContact.time.1 * state.2.yCellCoreCharge ≤
        state.2.dyadicChildReadout
            state.1.physical.nextContact.physicalState -
          state.2.dyadicChildReadout
            state.1.physical.contact.physicalState := by
    simpa [nativeRestartStandingActionValuedArithmeticMaterial] using edgePayment
  have faceDomination :
      (standingActionWholeRestartMediumSource initialActionMaterial).clockAt state +
          standingActionFrozenDyadicFacePotential state.2 nextState.1 ≤
        standingActionFrozenDyadicFacePotential state.2 state.1 := by
    change
      state.1.physical.nextContact.time.1 +
          standingActionFrozenDyadicFacePotential state.2 nextState.1 ≤
        standingActionFrozenDyadicFacePotential state.2 state.1
    have capacityNextLe :
        standingPaidFaceCapacity nextState.1 state.2.dyadicChildModes ≤
          standingPaidFaceCapacity state.1 state.2.dyadicChildModes := by
      unfold standingPaidFaceCapacity
      apply mul_le_mul_of_nonneg_left
      · change
          puncturedWholeVorticityKineticMass
              state.1.physical.nextContact.physicalState ≤
            puncturedWholeVorticityKineticMass
              state.1.physical.contact.physicalState
        exact nextContact_kineticMass_le state.1.physical
      · exact finiteModeKineticAmbientFactor_nonneg _
    have contactEq : nextState.1.physical.contact.physicalState =
        state.1.physical.nextContact.physicalState := by rfl
    unfold standingActionFrozenDyadicFacePotential
    apply (le_div_iff₀ state.2.yCellCoreCharge_pos).2
    rw [add_mul, div_mul_cancel₀ _ state.2.yCellCoreCharge_pos.ne']
    rw [contactEq]
    linarith [edgePayment']
  have nextFaceEq :
      standingActionFrozenDyadicFacePotential state.2 nextState.1 =
        standingActionFrozenDyadicFacePotential nextState.2 nextState.1 :=
    standingActionFrozenDyadicFacePotential_eq_of_cellScale_eq
      state.2 nextState.2 nextState.1 scaleSame.symm
  have resetEq :
      standingActionDyadicResetReserve initial nextState.2 =
        standingActionDyadicResetReserve initial state.2 := by
    unfold standingActionDyadicResetReserve
    rw [scaleSame]
  apply sourceGeneratedRootClockAdvance_of_potential_domination
  change
    (standingActionWholeRestartMediumSource initialActionMaterial).clockAt state +
        standingActionMixedClockPotential nextState ≤
      standingActionMixedClockPotential state
  unfold standingActionMixedClockPotential
  rw [anchorNext, resetEq, ← nextFaceEq]
  linarith

/-- The exact scalar left after sending a root residual through the existing
mixed frozen-face clock consumer.  This is a readout of the same current
face and the compiler-owned successor, not a new physical estimate. -/
def standingActionRootResidualFaceCapacityDrop
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) : Real :=
  standingPaidFaceCapacity state.1 state.2.dyadicChildModes -
    standingPaidFaceCapacity state.1.next state.2.dyadicChildModes

/-- Direct expansion of the two coupled compile goals.  Once the root
normalizer emits a residual, anchor and action scale are retained; hence all
barrier/reset rows cancel.  The remaining clock coboundary is exactly the
frozen-face capacity drop plus the complete endpoint residual, divided by
the source-generated positive core charge. -/
theorem standingActionRootResidualMixedClock_coboundary
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage))
    (rootResidual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial) :
    let state := (standingActionWholeRestartMediumSource
      initialActionMaterial).stateAfter stage
    let nextState := (standingActionWholeRestartMediumSource
      initialActionMaterial).stateAfter (stage + 1)
    standingActionMixedClockPotential state -
          standingActionMixedClockPotential nextState -
        (standingActionWholeRestartMediumSource
          initialActionMaterial).clockAt state =
      (standingActionRootResidualFaceCapacityDrop state +
          (nativeRestartStandingActionValuedArithmeticMaterial
            state).endpointResidualReadout) /
        state.2.yCellCoreCharge := by
  let state := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter stage
  let nextState := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter (stage + 1)
  change
    standingActionMixedClockPotential state -
          standingActionMixedClockPotential nextState -
        (standingActionWholeRestartMediumSource
          initialActionMaterial).clockAt state =
      (standingActionRootResidualFaceCapacityDrop state +
          (nativeRestartStandingActionValuedArithmeticMaterial
            state).endpointResidualReadout) /
        state.2.yCellCoreCharge
  have notPaid := standingActionRootResidual_paymentIncrement_ne_one
    effect rootResidual
  have incrementLe :=
    NativeRestartStandingValuedArithmeticMaterialAt.standing_paymentIncrement_le_one
      state.1.standing
  have incrementZero : state.1.standing.paymentIncrement = 0 := by
    dsimp only [state] at notPaid incrementLe ⊢
    omega
  have anchorNext : nextState.1.standing.anchorLevel =
      state.1.standing.anchorLevel := by
    dsimp only [nextState, state]
    change
      (((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).1.standing.next).anchorLevel = _
    rw [cellStanding_anchorLevel_next, incrementZero, Nat.add_zero]
  have scaleSame : nextState.2.cellScale = state.2.cellScale := by
    dsimp only [nextState, state]
    change
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage).2.advance.cellScale = _
    exact ((standingActionWholeRestartMediumSource initialActionMaterial
      ).stateAfter stage).2.advance_cellScale_of_nonpayment notPaid
  have nextFaceEq :
      standingActionFrozenDyadicFacePotential nextState.2 nextState.1 =
        standingActionFrozenDyadicFacePotential state.2 nextState.1 :=
    standingActionFrozenDyadicFacePotential_eq_of_cellScale_eq
      nextState.2 state.2 nextState.1 scaleSame
  have resetEq :
      standingActionDyadicResetReserve initial nextState.2 =
        standingActionDyadicResetReserve initial state.2 := by
    unfold standingActionDyadicResetReserve
    rw [scaleSame]
  have faceCommuting :=
    (nativeRestartStandingActionValuedArithmeticMaterial
      state).faceValuation_commutes
  have contactEq : nextState.1.physical.contact.physicalState =
      state.1.physical.nextContact.physicalState := by
    dsimp only [nextState, state]
    rfl
  have nextCurrentEq : nextState.1 = state.1.next := by
    dsimp only [nextState, state]
    rfl
  have clockEq :
      (standingActionWholeRestartMediumSource
          initialActionMaterial).clockAt state =
        state.1.physical.nextContact.time.1 := rfl
  unfold standingActionMixedClockPotential
    standingActionRootResidualFaceCapacityDrop
  rw [anchorNext, resetEq, nextFaceEq]
  unfold standingActionFrozenDyadicFacePotential
  rw [contactEq, nextCurrentEq, clockEq]
  change
    state.2.dyadicChildReadout
          state.1.physical.nextContact.physicalState -
        state.2.dyadicChildReadout
          state.1.physical.contact.physicalState =
      state.1.physical.nextContact.time.1 * state.2.yCellCoreCharge +
        (nativeRestartStandingActionValuedArithmeticMaterial
          state).endpointResidualReadout at faceCommuting
  field_simp [state.2.yCellCoreCharge_pos.ne']
  linarith

theorem standingActionRootResidualMixedClock_domination_iff
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat)
    (effect : NativeFluidMediumExactOperationalEffectAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage))
    (rootResidual : GeneratedParallelResidualAt
      effect.effect effect.arithmeticMaterial) :
    let state := (standingActionWholeRestartMediumSource
      initialActionMaterial).stateAfter stage
    let nextState := (standingActionWholeRestartMediumSource
      initialActionMaterial).stateAfter (stage + 1)
    (standingActionWholeRestartMediumSource initialActionMaterial).clockAt state +
          standingActionMixedClockPotential nextState ≤
        standingActionMixedClockPotential state ↔
      -(nativeRestartStandingActionValuedArithmeticMaterial
          state).endpointResidualReadout ≤
        standingActionRootResidualFaceCapacityDrop state := by
  let state := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter stage
  let nextState := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter (stage + 1)
  change
    ((standingActionWholeRestartMediumSource
          initialActionMaterial).clockAt state +
          standingActionMixedClockPotential nextState ≤
        standingActionMixedClockPotential state) ↔
      -(nativeRestartStandingActionValuedArithmeticMaterial
          state).endpointResidualReadout ≤
        standingActionRootResidualFaceCapacityDrop state
  have coboundary := standingActionRootResidualMixedClock_coboundary
    initialActionMaterial stage effect rootResidual
  have chargePos := state.2.yCellCoreCharge_pos
  constructor
  · intro domination
    have quotientNonneg :
        0 ≤ (standingActionRootResidualFaceCapacityDrop state +
          (nativeRestartStandingActionValuedArithmeticMaterial
            state).endpointResidualReadout) / state.2.yCellCoreCharge := by
      rw [← coboundary]
      linarith
    have productNonneg := mul_nonneg quotientNonneg chargePos.le
    rw [div_mul_cancel₀ _ chargePos.ne'] at productNonneg
    linarith
  · intro capacityPays
    have sumNonneg :
        0 ≤ standingActionRootResidualFaceCapacityDrop state +
          (nativeRestartStandingActionValuedArithmeticMaterial
            state).endpointResidualReadout := by
      linarith
    have quotientNonneg := div_nonneg sumNonneg chargePos.le
    linarith

def standingActionFrozenDyadicClockState
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {sourceCurrent : GeneratedWholeRestartRuntimeCurrent
      butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt sourceCurrent)
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    SourceGeneratedRootClockStateAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state where
  potential := standingActionFrozenDyadicFacePotential instruction state.1
  potential_nonneg :=
    standingActionFrozenDyadicFacePotential_nonneg instruction state.1

/-- Same-face dyadic payment generates an exact current-edge clock advance.
The source root supplies the target current; only the already-generated face
is frozen across this one retained-standing edge. -/
def sourceGeneratedRootClockAdvance_of_frozenDyadicPayment
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State)
    (edgePayment :
      state.1.physical.nextContact.time.1 * state.2.yCellCoreCharge ≤
        state.2.dyadicChildReadout
            state.1.physical.nextContact.physicalState -
          state.2.dyadicChildReadout
            state.1.physical.contact.physicalState) :
    SourceGeneratedRootClockAdvanceAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      state (standingActionFrozenDyadicClockState state.2 state)
      (standingActionFrozenDyadicClockState state.2
        ((standingActionWholeRestartMediumSource
          initialActionMaterial).successor state)) := by
  let faceGain :=
    state.2.dyadicChildReadout
        state.1.physical.nextContact.physicalState -
      state.2.dyadicChildReadout
        state.1.physical.contact.physicalState
  let faceWaste := faceGain / state.2.yCellCoreCharge -
    state.1.physical.nextContact.time.1
  let capacityDrop :=
    (standingPaidFaceCapacity state.1 state.2.dyadicChildModes -
      standingPaidFaceCapacity state.1.next state.2.dyadicChildModes) /
        state.2.yCellCoreCharge
  have faceWasteNonneg : 0 ≤ faceWaste := by
    dsimp only [faceWaste]
    apply sub_nonneg.mpr
    exact (le_div_iff₀ state.2.yCellCoreCharge_pos).2 (by
      simpa only [mul_comm] using edgePayment)
  have capacityDropNonneg : 0 ≤ capacityDrop := by
    dsimp only [capacityDrop]
    apply div_nonneg _ state.2.yCellCoreCharge_pos.le
    apply sub_nonneg.mpr
    unfold standingPaidFaceCapacity
    apply mul_le_mul_of_nonneg_left
    · exact nextContact_kineticMass_le state.1.physical
    · exact finiteModeKineticAmbientFactor_nonneg _
  exact
    { waste := faceWaste + capacityDrop
      waste_nonneg := add_nonneg faceWasteNonneg capacityDropNonneg
      settlement := by
        change standingActionFrozenDyadicFacePotential state.2 state.1 =
          state.1.physical.nextContact.time.1 +
            standingActionFrozenDyadicFacePotential state.2 state.1.next +
              (faceWaste + capacityDrop)
        unfold standingActionFrozenDyadicFacePotential
        dsimp only [faceGain, faceWaste, capacityDrop]
        rw [show state.1.next.physical.contact.physicalState =
          state.1.physical.nextContact.physicalState by rfl]
        field_simp [state.2.yCellCoreCharge_pos.ne']
        ring }

namespace SourceGeneratedStandingActionTotalEffectAt

def retainedActionClockSettlement?
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    {state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State}
    {outcome : NativeFluidMediumRootOperationalOutcomeAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state} :
    (total : SourceGeneratedStandingActionTotalEffectAt state outcome) →
      Option (SourceGeneratedRootClockSettlementAt
        (standingActionWholeRestartMediumSource initialActionMaterial)
        state (standingActionFrozenDyadicClockState state.2 state)
        (standingActionFrozenDyadicClockState state.2
          ((standingActionWholeRestartMediumSource
            initialActionMaterial).successor state)) outcome)
  | .actionIncidenceResidual _actionRooted actionCommutes =>
      some (.generatedResidual
        (sourceGeneratedRootClockAdvance_of_frozenDyadicPayment state
          ((nativeRestartStandingActionValuedArithmeticMaterial state
            ).clock_mul_yCellCoreCharge_le_faceReadoutGain_of_arithmeticExact
              actionCommutes)))
  | .actionIncidenceObstruction _actionRooted actionCommutes =>
      some (.obstructionAlternative
        (sourceGeneratedRootClockAdvance_of_frozenDyadicPayment state
          ((nativeRestartStandingActionValuedArithmeticMaterial state
            ).clock_mul_yCellCoreCharge_le_faceReadoutGain_of_arithmeticExact
              actionCommutes)))
  | .jointPayment _ _ => none
  | .standingPayment _ => none
  | .coupledResidual _ => none
  | .coupledObstruction _ => none

end SourceGeneratedStandingActionTotalEffectAt

/-- Total six-branch clock/lifecycle disposition on one reachable root edge.
The two coupled constructors do not freeze a failure: they carry the exact
standing residual expansion and its compiler-generated next normal form. -/
inductive SourceGeneratedStandingActionRunClockDispositionAt
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat) :
    NativeFluidMediumRootOperationalOutcomeAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      ((standingActionWholeRestartMediumSource initialActionMaterial
        ).stateAfter stage) → Type
  | settled
      {outcome}
      (settlement : SourceGeneratedRootClockSettlementAt
        (standingActionWholeRestartMediumSource initialActionMaterial)
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage)
        (standingActionMixedClockState
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter stage))
        (standingActionMixedClockState
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter (stage + 1))) outcome) :
      SourceGeneratedStandingActionRunClockDispositionAt
        initialActionMaterial stage outcome
  | generatedResidualAdvance
      {effect : NativeFluidMediumExactOperationalEffectAt
        (standingActionWholeRestartMediumSource initialActionMaterial)
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage)}
      {residual : GeneratedParallelResidualAt
        effect.effect effect.arithmeticMaterial}
      {expansion : (standingActionWholeRestartMediumSource
        initialActionMaterial).OperationalResidualExpansionAt
          effect.effect residual}
      {expansion_eq : expansion =
        (standingActionWholeRestartMediumSource initialActionMaterial
          ).generateOperationalResidualExpansionAt effect.effect residual}
      {payment : NativeFluidMediumResidualPaymentAt effect residual expansion}
      (actionResidual : GeneratedParallelResidualAt
        (nativeRestartStandingActionValuedArithmeticMaterial
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter stage))
        (nativeRestartStandingActionValuedArithmeticMaterial
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter stage)).actionArithmeticMaterial)
      (nextNormalForm : ParallelIncidenceNormalFormAt
        expansion.standingExpansion.nextMaterial
        expansion.standingExpansion.nextMaterial.arithmeticMaterial) :
      SourceGeneratedStandingActionRunClockDispositionAt
        initialActionMaterial stage
          (.generatedResidual effect residual expansion expansion_eq payment)
  | obstructionAdvance
      {obstruction : NativeFluidMediumOperationalObstructionAt
        (standingActionWholeRestartMediumSource initialActionMaterial)
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage)}
      {demand : SourceGeneratedU7DemandAt
        (nativeFluidMediumU7Producer
          (standingActionWholeRestartMediumSource initialActionMaterial))
        obstruction
        ((nativeFluidMediumU7Producer
          (standingActionWholeRestartMediumSource initialActionMaterial)
          ).generateDemand obstruction)}
      (actionResidual : GeneratedParallelResidualAt
        (nativeRestartStandingActionValuedArithmeticMaterial
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter stage))
        (nativeRestartStandingActionValuedArithmeticMaterial
          ((standingActionWholeRestartMediumSource initialActionMaterial
            ).stateAfter stage)).actionArithmeticMaterial)
      (nextNormalForm : ParallelIncidenceNormalFormAt
        obstruction.expansion.standingExpansion.nextMaterial
        obstruction.expansion.standingExpansion.nextMaterial.arithmeticMaterial) :
      SourceGeneratedStandingActionRunClockDispositionAt
        initialActionMaterial stage (.obstruction obstruction demand)

noncomputable def sourceGeneratedStandingActionRunClockDisposition
    {initial : GeneratedWholeRestartCurrent butterflyGainViscosity}
    (initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0))
    (stage : Nat) :
    SourceGeneratedStandingActionRunClockDispositionAt
      initialActionMaterial stage
      (nativeFluidMediumRootOperationalOutcomeAt
        (standingActionWholeRestartMediumSource initialActionMaterial)
        ((standingActionWholeRestartMediumSource initialActionMaterial
          ).stateAfter stage)) := by
  let state := (standingActionWholeRestartMediumSource
    initialActionMaterial).stateAfter stage
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state =
        outcome
  have total : SourceGeneratedStandingActionTotalEffectAt state outcome := by
    rw [← outcomeEq]
    exact sourceGeneratedStandingActionTotalEffect state
  cases total with
  | jointPayment actionRooted actionCommutes =>
      rename_i effect rooted rootCommutes
      exact .settled (.exactPayment
        (standingActionRootExactMixedClockAdvance initialActionMaterial stage
          effect rootCommutes))
  | standingPayment actionResidual =>
      rename_i effect rooted rootCommutes
      exact .settled (.exactPayment
        (standingActionRootExactMixedClockAdvance initialActionMaterial stage
          effect rootCommutes))
  | actionIncidenceResidual actionRooted actionCommutes =>
      rename_i effect rootResidual expansion expansionEq payment
      exact .settled (.generatedResidual
        (standingActionRootResidualActionExactMixedClockAdvance
          initialActionMaterial stage effect rootResidual actionCommutes))
  | actionIncidenceObstruction actionRooted actionCommutes =>
      rename_i obstruction demand
      exact .settled (.obstructionAlternative
        (standingActionRootResidualActionExactMixedClockAdvance
          initialActionMaterial stage obstruction.effect
            obstruction.residual actionCommutes))
  | coupledResidual actionResidual =>
      rename_i effect rootResidual expansion expansionEq payment
      exact .generatedResidualAdvance actionResidual
        expansion.standingExpansion.nextNormalForm
  | coupledObstruction actionResidual =>
      rename_i obstruction demand
      exact .obstructionAdvance actionResidual
        obstruction.expansion.standingExpansion.nextNormalForm

/-- Fixed source face potential read from the current root state.  This is a
physical valuation of the action-medium occurrence, not a future payment
table. -/
def standingActionFacePotential
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (modes : Finset IntegerWavevector)
    (charge : Real)
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) : Real :=
  standingPaidKineticCapacityPotential state.1 modes charge

theorem standingActionFacePotential_nonneg
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (charge : Real)
    (charge_pos : 0 < charge)
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    0 ≤ standingActionFacePotential modes charge state := by
  unfold standingActionFacePotential standingPaidKineticCapacityPotential
  exact div_nonneg
    (sub_nonneg.mpr (standingPaidFaceMass_le_capacity
      state.1 modes zeroNotMem)) charge_pos.le

def standingActionFaceClockState
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (charge : Real)
    (charge_pos : 0 < charge)
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State) :
    SourceGeneratedRootClockStateAt
      (standingActionWholeRestartMediumSource initialActionMaterial) state where
  potential := standingActionFacePotential modes charge state
  potential_nonneg := standingActionFacePotential_nonneg
    modes zeroNotMem charge charge_pos state

/-- A payment on the current source face generates the exact clock
settlement.  Crucially, no proof that the same face pays the next edge is an
input: the target is only the root-generated next potential. -/
def sourceGeneratedRootClockAdvance_of_facePayment
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
      (runRuntime initial 0)}
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (charge : Real)
    (charge_pos : 0 < charge)
    (state : (standingActionWholeRestartMediumSource
      initialActionMaterial).State)
    (edgePayment :
      state.1.physical.nextContact.time.1 * charge ≤
        finiteStateVorticityCoefficientEnstrophy modes
            state.1.physical.nextContact.physicalState -
          finiteStateVorticityCoefficientEnstrophy modes
            state.1.physical.contact.physicalState) :
    SourceGeneratedRootClockAdvanceAt
      (standingActionWholeRestartMediumSource initialActionMaterial)
      state
      (standingActionFaceClockState
        modes zeroNotMem charge charge_pos state)
      (standingActionFaceClockState
        modes zeroNotMem charge charge_pos
          ((standingActionWholeRestartMediumSource
            initialActionMaterial).successor state)) := by
  let massDropPayment :=
    (finiteStateVorticityCoefficientEnstrophy modes
          state.1.physical.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy modes
          state.1.physical.contact.physicalState) / charge -
      state.1.physical.nextContact.time.1
  let capacityDrop :=
    (standingPaidFaceCapacity state.1 modes -
      standingPaidFaceCapacity state.1.next modes) / charge
  have massDropPaymentNonneg : 0 ≤ massDropPayment := by
    dsimp only [massDropPayment]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ charge_pos).2
    simpa only [mul_comm] using edgePayment
  have capacityDropNonneg : 0 ≤ capacityDrop := by
    dsimp only [capacityDrop]
    apply div_nonneg _ charge_pos.le
    apply sub_nonneg.mpr
    unfold standingPaidFaceCapacity
    apply mul_le_mul_of_nonneg_left
    · change
        puncturedWholeVorticityKineticMass
            state.1.physical.nextContact.physicalState ≤
          puncturedWholeVorticityKineticMass
            state.1.physical.contact.physicalState
      exact nextContact_kineticMass_le state.1.physical
    · exact finiteModeKineticAmbientFactor_nonneg modes
  have faceMassNextEq :
      standingPaidFaceMass state.1.next modes =
        finiteStateVorticityCoefficientEnstrophy modes
          state.1.physical.nextContact.physicalState := by
    unfold standingPaidFaceMass
    unfold GeneratedWholeRestartRuntimeCurrent.next
    rw [next_contact]
    rfl
  exact
    { waste := massDropPayment + capacityDrop
      waste_nonneg := add_nonneg massDropPaymentNonneg capacityDropNonneg
      settlement := by
        change
          standingPaidKineticCapacityPotential state.1 modes charge =
            state.1.physical.nextContact.time.1 +
              standingPaidKineticCapacityPotential state.1.next modes charge +
                (massDropPayment + capacityDrop)
        unfold standingPaidKineticCapacityPotential
        rw [faceMassNextEq]
        unfold standingPaidFaceMass
        dsimp only [massDropPayment, capacityDrop]
        field_simp [charge_pos.ne']
        ring }

/-- Complete finite source program.  Its sole branch-sensitive field settles
the root compiler's current outcome.  The fixed root recursively supplies
the actual successor and the next action material. -/
structure SourceGeneratedStandingActionClockLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 1 where
  initialActionMaterial : SourceGeneratedActionMaterialInstructionAt
    (runRuntime initial 0)
  clockLaw : SourceGeneratedRootClockLaw
    (standingActionWholeRestartMediumSource initialActionMaterial)

namespace SourceGeneratedStandingActionClockLaw

theorem contactTime_summable
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (law : SourceGeneratedStandingActionClockLaw initial) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  have nextSummable := law.clockLaw.clock_summable
  have nextSummable' : Summable fun stage =>
      (run initial stage).nextContact.time.1 := by
    apply nextSummable.congr
    intro stage
    change
      ((standingActionWholeRestartMediumSource law.initialActionMaterial
        ).stateAfter stage).1.physical.nextContact.time.1 =
        (run initial stage).nextContact.time.1
    rw [standingActionWholeRestartMediumSource_stateAfter_current]
    rfl
  have shifted : Summable fun stage =>
      (run initial (stage + 1)).contact.time.1 := by
    simpa only [run_succ, next_contact] using nextSummable'
  exact (summable_nat_add_iff 1).mp shifted

end SourceGeneratedStandingActionClockLaw

/-! ## Exact sideband residual of the actual action -/

def sidebandPlusX (state : ComplexVorticityHilbertState) : Real :=
  (state plusWave 0).re

def sidebandPlusZ (state : ComplexVorticityHilbertState) : Real :=
  (state plusWave 2).re

def sidebandMinusY (state : ComplexVorticityHilbertState) : Real :=
  (state minusWave 0).re

def sidebandMinusW (state : ComplexVorticityHilbertState) : Real :=
  (state minusWave 2).re

def sidebandPlusXJet (state : ComplexVorticityHilbertState) : Real :=
  (classicalWholeNSVorticityTangent butterflyGainViscosity state
    plusWave 0).re

def sidebandPlusZJet (state : ComplexVorticityHilbertState) : Real :=
  (classicalWholeNSVorticityTangent butterflyGainViscosity state
    plusWave 2).re

def sidebandMinusYJet (state : ComplexVorticityHilbertState) : Real :=
  (classicalWholeNSVorticityTangent butterflyGainViscosity state
    minusWave 0).re

def sidebandMinusWJet (state : ComplexVorticityHilbertState) : Real :=
  (classicalWholeNSVorticityTangent butterflyGainViscosity state
    minusWave 2).re

def sidebandPlusXResidual (state : ComplexVorticityHilbertState) : Real :=
  sidebandPlusXJet state -
    (1 / 4 - (17 / 100) * sidebandPlusX state)

def sidebandPlusZResidual (state : ComplexVorticityHilbertState) : Real :=
  sidebandPlusZJet state -
    (-(15 / 4) - (17 / 100) * sidebandPlusZ state)

def sidebandMinusYResidual (state : ComplexVorticityHilbertState) : Real :=
  sidebandMinusYJet state -
    (-(1 / 4) - (17 / 100) * sidebandMinusY state)

def sidebandMinusWResidual (state : ComplexVorticityHilbertState) : Real :=
  sidebandMinusWJet state -
    (15 / 4 - (17 / 100) * sidebandMinusW state)

/-- Finite cell coordinates on one actual whole state. -/
structure ButterflyOrientedSidebandCellAt
    (state : ComplexVorticityHilbertState) : Prop where
  plusX_pos : 0 < sidebandPlusX state
  plusZ_neg : sidebandPlusZ state < 0
  minusY_neg : sidebandMinusY state < 0
  minusW_pos : 0 < sidebandMinusW state

/-- Exact quantitative responsibility left after the affine cell action is
removed from the actual whole tangent. -/
structure ButterflySidebandActionResidualEscrowAt
    (state : ComplexVorticityHilbertState) : Prop where
  plusX_lower : -(1 / 4 : Real) < sidebandPlusXResidual state
  plusZ_upper : sidebandPlusZResidual state < 15 / 4
  minusY_upper : sidebandMinusYResidual state < 1 / 4
  minusW_lower : -(15 / 4 : Real) < sidebandMinusWResidual state

/-- The four affine core margins and the same-state residual escrow give the
literal whole-NS inward signs on every oriented wall. -/
theorem actualSideband_walls_strictly_inward
    (state : ComplexVorticityHilbertState)
    (escrow : ButterflySidebandActionResidualEscrowAt state) :
    (sidebandPlusX state = 0 → 0 < sidebandPlusXJet state) ∧
      (sidebandPlusZ state = 0 → sidebandPlusZJet state < 0) ∧
      (sidebandMinusY state = 0 → sidebandMinusYJet state < 0) ∧
      (sidebandMinusW state = 0 → 0 < sidebandMinusWJet state) := by
  constructor
  · intro wall
    have bound := escrow.plusX_lower
    unfold sidebandPlusXResidual at bound
    rw [wall] at bound
    norm_num at bound
    linarith
  constructor
  · intro wall
    have bound := escrow.plusZ_upper
    unfold sidebandPlusZResidual at bound
    rw [wall] at bound
    norm_num at bound
    linarith
  constructor
  · intro wall
    have bound := escrow.minusY_upper
    unfold sidebandMinusYResidual at bound
    rw [wall] at bound
    norm_num at bound
    linarith
  · intro wall
    have bound := escrow.minusW_lower
    unfold sidebandMinusWResidual at bound
    rw [wall] at bound
    norm_num at bound
    linarith

def projectedSidebandPlusXCoreResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  (instruction.projectedTangent plusWave 0).re -
    (1 / 4 - (17 / 100) *
      sidebandPlusX current.physical.contact.physicalState)

def projectedSidebandPlusZCoreResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  (instruction.projectedTangent plusWave 2).re -
    (-(15 / 4) - (17 / 100) *
      sidebandPlusZ current.physical.contact.physicalState)

def projectedSidebandMinusYCoreResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  (instruction.projectedTangent minusWave 0).re -
    (-(1 / 4) - (17 / 100) *
      sidebandMinusY current.physical.contact.physicalState)

def projectedSidebandMinusWCoreResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Real :=
  (instruction.projectedTangent minusWave 2).re -
    (15 / 4 - (17 / 100) *
      sidebandMinusW current.physical.contact.physicalState)

private theorem actionCoordinate_commutes
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current)
    (wave : IntegerWavevector) (coordinate : Fin 3) :
    (classicalWholeNSVorticityTangent butterflyGainViscosity
        current.physical.contact.physicalState wave coordinate).re =
      (instruction.projectedTangent wave coordinate).re +
        (instruction.actionResidual wave coordinate).re := by
  have commuting := instruction.wholeTangent_eq_projected_add_residual
  have row := congrFun commuting wave
  have component := congrFun row coordinate
  change
    classicalWholeNSVorticityTangent butterflyGainViscosity
        current.physical.contact.physicalState wave coordinate =
      instruction.projectedTangent wave coordinate +
        instruction.actionResidual wave coordinate at component
  have realPart := congrArg Complex.re component
  simpa only [Complex.add_re] using realPart

/-- Direct D1/D2 splice: the actual affine-cell residual is exactly the
finite projected core mismatch plus the same instruction's whole action
residual. -/
theorem sidebandPlusXResidual_eq_projected_add_actionResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    sidebandPlusXResidual current.physical.contact.physicalState =
      projectedSidebandPlusXCoreResidual instruction +
        (instruction.actionResidual plusWave 0).re := by
  have realPart := actionCoordinate_commutes instruction plusWave 0
  unfold sidebandPlusXResidual sidebandPlusXJet
    projectedSidebandPlusXCoreResidual
  dsimp only at realPart ⊢
  linarith

theorem sidebandPlusZResidual_eq_projected_add_actionResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    sidebandPlusZResidual current.physical.contact.physicalState =
      projectedSidebandPlusZCoreResidual instruction +
        (instruction.actionResidual plusWave 2).re := by
  have realPart := actionCoordinate_commutes instruction plusWave 2
  unfold sidebandPlusZResidual sidebandPlusZJet
    projectedSidebandPlusZCoreResidual
  dsimp only at realPart ⊢
  linarith

theorem sidebandMinusYResidual_eq_projected_add_actionResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    sidebandMinusYResidual current.physical.contact.physicalState =
      projectedSidebandMinusYCoreResidual instruction +
        (instruction.actionResidual minusWave 0).re := by
  have realPart := actionCoordinate_commutes instruction minusWave 0
  unfold sidebandMinusYResidual sidebandMinusYJet
    projectedSidebandMinusYCoreResidual
  dsimp only at realPart ⊢
  linarith

theorem sidebandMinusWResidual_eq_projected_add_actionResidual
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) :
    sidebandMinusWResidual current.physical.contact.physicalState =
      projectedSidebandMinusWCoreResidual instruction +
        (instruction.actionResidual minusWave 2).re := by
  have realPart := actionCoordinate_commutes instruction minusWave 2
  unfold sidebandMinusWResidual sidebandMinusWJet
    projectedSidebandMinusWCoreResidual
  dsimp only at realPart ⊢
  linarith

/-- The one source-owned valuation of the action material.  Each field is
already the sum of finite core mismatch and whole action residual, so no
downstream caller can mix the two projections. -/
structure ButterflyActionMaterialEscrowAt
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    (instruction : SourceGeneratedActionMaterialInstructionAt current) : Prop where
  plusX_lower : -(1 / 4 : Real) <
    projectedSidebandPlusXCoreResidual instruction +
      (instruction.actionResidual plusWave 0).re
  plusZ_upper :
    projectedSidebandPlusZCoreResidual instruction +
        (instruction.actionResidual plusWave 2).re < 15 / 4
  minusY_upper :
    projectedSidebandMinusYCoreResidual instruction +
        (instruction.actionResidual minusWave 0).re < 1 / 4
  minusW_lower : -(15 / 4 : Real) <
    projectedSidebandMinusWCoreResidual instruction +
      (instruction.actionResidual minusWave 2).re

theorem ButterflyActionMaterialEscrowAt.toActualResidualEscrow
    {current : GeneratedWholeRestartRuntimeCurrent butterflyGainViscosity}
    {instruction : SourceGeneratedActionMaterialInstructionAt current}
    (escrow : ButterflyActionMaterialEscrowAt instruction) :
    ButterflySidebandActionResidualEscrowAt
      current.physical.contact.physicalState := by
  constructor
  · rw [sidebandPlusXResidual_eq_projected_add_actionResidual]
    exact escrow.plusX_lower
  · rw [sidebandPlusZResidual_eq_projected_add_actionResidual]
    exact escrow.plusZ_upper
  · rw [sidebandMinusYResidual_eq_projected_add_actionResidual]
    exact escrow.minusY_upper
  · rw [sidebandMinusWResidual_eq_projected_add_actionResidual]
    exact escrow.minusW_lower

/-! ## Exact source seed and the generated open medium cell -/

theorem stackedSeedTangent_eq_coneAction
    (wave : IntegerWavevector) :
    wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState wave =
      GaussianRatVector.toComplex
        (coneAction (1 / 4) (-(15 / 4)) (-(1 / 4)) (15 / 4) wave) := by
  calc
    wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff stackedSeedState wave =
        GaussianRatVector.toComplex
          (butterflyFirstStackRationalTangent (-1) wave) := by
      change
        wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            (butterflyFirstStackPhysicalState (-1)) wave = _
      unfold wholeLatticeVorticityFourierTangentAt
      rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
        butterflyFirstStackModes
        (butterflyFirstStackPhysicalState (-1))
        (butterflyFirstStackPhysicalState_supported (-1)) wave]
      exact (butterflyFirstStackRationalTangent_toComplex (-1) wave).symm
    _ = GaussianRatVector.toComplex
          (coneAction (1 / 4) (-(15 / 4))
            (-(1 / 4)) (15 / 4) wave) := by
      apply congrArg GaussianRatVector.toComplex
      unfold butterflyFirstStackRationalTangent coneAction
      rw [coneState_source_eq]

theorem stackedSeedState_eq_coneToComplex
    (wave : IntegerWavevector) :
    stackedSeedState wave = GaussianRatVector.toComplex
      (coneState (1 / 4) (-(15 / 4)) (-(1 / 4)) (15 / 4) wave) := by
  change butterflyFirstStackPhysicalState (-1) wave = _
  rw [coneState_source_eq]
  exact (butterflyFirstStackRationalState_toComplex (-1) wave).symm

theorem stackedSeed_sidebandCoordinates :
    sidebandPlusX stackedSeedState = 1 / 4 ∧
      sidebandPlusZ stackedSeedState = -(15 / 4) ∧
      sidebandMinusY stackedSeedState = -(1 / 4) ∧
      sidebandMinusW stackedSeedState = 15 / 4 := by
  constructor
  · unfold sidebandPlusX
    rw [stackedSeedState_eq_coneToComplex]
    simp [coneState, conePlusRow, plusWave, minusWave,
      realRow, realGaussian, GaussianRatVector.toComplex,
      GaussianRat.toComplex, Matrix.cons_val_zero]
  constructor
  · unfold sidebandPlusZ
    rw [stackedSeedState_eq_coneToComplex]
    simp [coneState, conePlusRow, plusWave, minusWave,
      realRow, realGaussian, GaussianRatVector.toComplex,
      GaussianRat.toComplex, Matrix.cons_val_two]
  constructor
  · unfold sidebandMinusY
    rw [stackedSeedState_eq_coneToComplex]
    simp [coneState, coneMinusRow, plusWave, minusWave,
      axisWave, pumpY,
      realRow, realGaussian, GaussianRatVector.toComplex,
      GaussianRat.toComplex, Matrix.cons_val_zero]
  · unfold sidebandMinusW
    rw [stackedSeedState_eq_coneToComplex]
    simp [coneState, coneMinusRow, plusWave, minusWave,
      axisWave, pumpY,
      realRow, realGaussian, GaussianRatVector.toComplex,
      GaussianRat.toComplex, Matrix.cons_val_two]

theorem stackedSeed_orientedSidebandCell :
    ButterflyOrientedSidebandCellAt stackedSeedState := by
  rcases stackedSeed_sidebandCoordinates with ⟨plusX, plusZ, minusY, minusW⟩
  constructor <;> simp [plusX, plusZ, minusY, minusW]

theorem stackedSeed_sidebandJets :
    sidebandPlusXJet stackedSeedState =
        1 / 4 - (17 / 100) * (1 / 4) ∧
      sidebandPlusZJet stackedSeedState =
        -(15 / 4) - (17 / 100) * (-(15 / 4)) ∧
      sidebandMinusYJet stackedSeedState =
        -(1 / 4) - (17 / 100) * (-(1 / 4)) ∧
      sidebandMinusWJet stackedSeedState =
        15 / 4 - (17 / 100) * (15 / 4) := by
  have plus := stackedSeedTangent_eq_coneAction plusWave
  have minus := stackedSeedTangent_eq_coneAction minusWave
  rw [coneAction_plus_eq] at plus
  rw [coneAction_minus_eq] at minus
  constructor
  · unfold sidebandPlusXJet
    have coordinate := congrFun plus 0
    have realPart := congrArg Complex.re coordinate
    change
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState plusWave 0).re = _
    simpa [conePlusActionRow, conePlusRow, realRow, realGaussian,
      GaussianRatVector.toComplex, GaussianRat.toComplex,
      Matrix.cons_val_zero] using realPart
  constructor
  · unfold sidebandPlusZJet
    have coordinate := congrFun plus 2
    have realPart := congrArg Complex.re coordinate
    change
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState plusWave 2).re = _
    simpa [conePlusActionRow, conePlusRow, realRow, realGaussian,
      GaussianRatVector.toComplex, GaussianRat.toComplex,
      Matrix.cons_val_two] using realPart
  constructor
  · unfold sidebandMinusYJet
    have coordinate := congrFun minus 0
    have realPart := congrArg Complex.re coordinate
    change
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState minusWave 0).re = _
    simpa [coneMinusActionRow, coneMinusRow, realRow, realGaussian,
      GaussianRatVector.toComplex, GaussianRat.toComplex,
      Matrix.cons_val_zero] using realPart
  · unfold sidebandMinusWJet
    have coordinate := congrFun minus 2
    have realPart := congrArg Complex.re coordinate
    change
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff stackedSeedState minusWave 2).re = _
    simpa [coneMinusActionRow, coneMinusRow, realRow, realGaussian,
      GaussianRatVector.toComplex, GaussianRat.toComplex,
      Matrix.cons_val_two] using realPart

theorem stackedSeed_sidebandResiduals_zero :
    sidebandPlusXResidual stackedSeedState = 0 ∧
      sidebandPlusZResidual stackedSeedState = 0 ∧
      sidebandMinusYResidual stackedSeedState = 0 ∧
      sidebandMinusWResidual stackedSeedState = 0 := by
  rcases stackedSeed_sidebandCoordinates with ⟨plusX, plusZ, minusY, minusW⟩
  rcases stackedSeed_sidebandJets with
    ⟨plusXJet, plusZJet, minusYJet, minusWJet⟩
  constructor
  · unfold sidebandPlusXResidual
    rw [plusX, plusXJet]
    ring
  constructor
  · unfold sidebandPlusZResidual
    rw [plusZ, plusZJet]
    ring
  constructor
  · unfold sidebandMinusYResidual
    rw [minusY, minusYJet]
    ring
  · unfold sidebandMinusWResidual
    rw [minusW, minusWJet]
    ring

theorem stackedSeed_actionResidualEscrow :
    ButterflySidebandActionResidualEscrowAt stackedSeedState := by
  rcases stackedSeed_sidebandResiduals_zero with
    ⟨plusX, plusZ, minusY, minusW⟩
  constructor <;> simp [plusX, plusZ, minusY, minusW]

/-! ## Concrete initial instruction -/

def stackedInitialActionMaterialInstruction :
    SourceGeneratedActionMaterialInstructionAt
      (runRuntime stackedShortCurrent 0) where
  floor := 1
  floor_pos := by norm_num
  radius := max
    (currentFullReceiptResolvedCaptureRadius stackedShortCurrent
      (currentFullReceiptScaleTolerance stackedShortCurrent 1 (by norm_num))) 8
  capture_le := le_max_left _ _
  cellScale := 4
  cellScale_two := by norm_num
  cellScale_four := by norm_num
  cellScale_le_radius := (by norm_num : 4 ≤ 8).trans (le_max_right _ _)

theorem stackedSidebandModes_subset_radiusFour :
    stackedSidebandModes ⊆ wholeRestartModes 4 := by
  intro wave waveMem
  simp only [stackedSidebandModes, plusSideband, minusSideband,
    Finset.mem_insert, Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl <;>
    decide

theorem stackedInitialPaidModes_subset_actionMaterial :
    stackedInitialPaidState.modes ⊆
      stackedInitialActionMaterialInstruction.modes := by
  exact stackedSidebandModes_subset_radiusFour.trans
    (wholeRestartModes_mono
      ((by norm_num : 4 ≤ 8).trans (le_max_right _ _)))

def stackedFirstChildFaceModes : Finset IntegerWavevector :=
  {butterflyFirstStackAxisEight,
    butterflyFirstStackAxisEightPlusY,
    butterflyFirstStackAxisEightMinusY}

theorem stackedFirstChildFaceModes_subset_radiusEight :
    stackedFirstChildFaceModes ⊆ wholeRestartModes 8 := by
  intro wave waveMem
  simp only [stackedFirstChildFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl | rfl <;> decide

theorem stackedFirstChildFaceModes_subset_initialActionMaterial :
    stackedFirstChildFaceModes ⊆
      stackedInitialActionMaterialInstruction.modes := by
  exact stackedFirstChildFaceModes_subset_radiusEight.trans
    (wholeRestartModes_mono (le_max_right _ _))

/-- The action-medium root seed now carries the complete first renewal face
as physical material, not merely the parent paying rows. -/
theorem stackedInitialActionMaterial_childFace_active :
    ∀ wave ∈ stackedFirstChildFaceModes,
      (runRuntime stackedShortCurrent 0).physical.contact.physicalState wave ≠
        0 := by
  intro wave waveMem
  change stackedShortCurrent.contact.physicalState wave ≠ 0
  simp only [stackedFirstChildFaceModes, Finset.mem_insert,
    Finset.mem_singleton] at waveMem
  rcases waveMem with rfl | rfl | rfl
  · exact stackedShortContact_axisEight_ne_zero
  · exact stackedShortContact_axisEightPlusY_ne_zero
  · exact stackedShortContact_axisEightMinusY_ne_zero

/-- Concrete authoritative root seed.  Its future action materials are
generated only by the root successor; no paid face is preinstalled. -/
def stackedStandingActionMediumSource : NativeFluidMediumSource
    butterflyGainViscosity :=
  standingActionWholeRestartMediumSource
    stackedInitialActionMaterialInstruction

def stackedInitialRootClockState : SourceGeneratedRootClockStateAt
    stackedStandingActionMediumSource
    stackedStandingActionMediumSource.initial :=
  standingActionFaceClockState stackedSidebandModes
    stackedSidebandCone.zeroNotMem (3998 / 1000) (by norm_num)
    stackedStandingActionMediumSource.initial

def stackedInitialNextRootClockState : SourceGeneratedRootClockStateAt
    stackedStandingActionMediumSource
    (stackedStandingActionMediumSource.successor
      stackedStandingActionMediumSource.initial) :=
  standingActionFaceClockState stackedSidebandModes
    stackedSidebandCone.zeroNotMem (3998 / 1000) (by norm_num)
    (stackedStandingActionMediumSource.successor
      stackedStandingActionMediumSource.initial)

/-- The initial butterfly edge pays its clock without committing the next
edge to a paid subtype. -/
def stackedInitialRootClockAdvance :
    SourceGeneratedRootClockAdvanceAt stackedStandingActionMediumSource
      stackedStandingActionMediumSource.initial
      stackedInitialRootClockState stackedInitialNextRootClockState := by
  apply sourceGeneratedRootClockAdvance_of_facePayment
    stackedSidebandModes stackedSidebandCone.zeroNotMem
      (3998 / 1000) (by norm_num)
  change
    (runRuntime stackedShortCurrent 0).physical.nextContact.time.1 *
          (3998 / 1000 : Real) ≤
      finiteStateVorticityCoefficientEnstrophy stackedSidebandModes
          (runRuntime stackedShortCurrent 0).physical.nextContact.physicalState -
        finiteStateVorticityCoefficientEnstrophy stackedSidebandModes
          (runRuntime stackedShortCurrent 0).physical.contact.physicalState
  exact stackedInitialEdgePayment

/-- First actual total-outcome splice.  Even if the raw standing valuation is
the root obstruction constructor, the same occurrence is settled by the
independently generated butterfly face payment.  No branch is supplied by a
caller. -/
def stackedInitialRootClockSettlement :
    SourceGeneratedRootClockSettlementAt stackedStandingActionMediumSource
      stackedStandingActionMediumSource.initial
      stackedInitialRootClockState
      stackedInitialNextRootClockState
      (nativeFluidMediumRootOperationalOutcomeAt
        stackedStandingActionMediumSource
        stackedStandingActionMediumSource.initial) := by
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt
      stackedStandingActionMediumSource
      stackedStandingActionMediumSource.initial = outcome
  cases outcome with
  | exactPayment effect rooted commutes =>
      exact .exactPayment stackedInitialRootClockAdvance
  | generatedResidual effect residual expansion expansion_eq payment =>
      exact .generatedResidual stackedInitialRootClockAdvance
  | obstruction obstruction demand =>
      exact .obstructionAlternative stackedInitialRootClockAdvance

/-- Exact remaining concrete source obligation after restoring total root
branching.  The local law settles paid and obstruction outcomes separately;
it contains no source-owned recurrence or next authority. -/
abbrev ButterflyStandingActionClockLaw :=
  SourceGeneratedStandingActionClockLaw concreteCounterexampleInitial

end
end ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
end NavierStokes
end SaturationMonoid
