import H0mework.NavierStokes.Galerkin.KineticCommonTimeExistence
import H0mework.NavierStokes.ShellGluing.NativeMacroWholeUnforcedPositiveTimeRestart
import H0mework.NavierStokes.InitialData.SourceOwnedLocalCompactnessBudget
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation
import H0mework.NavierStokes.WholeSpace.WholeStateSourceOwnedLocalBarrier

/-!
# Canonical whole-state restart replay

An actual positive-time whole restart state now generates the entire
punctured-cube Galerkin family from its own Fourier coefficients.  Every
finite trajectory is an actual unforced Galerkin orbit on one common
positive horizon selected from the whole state, its initial projections
converge strongly back to that exact state, and the common barrier bounds
every stage without a caller-selected cutoff or smallness knob.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay

open scoped Topology

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinNegativeSobolevTimeBudget
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticCommonTimeExistence
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedCompiler
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open
  ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalCompactnessBudget

noncomputable section

/-! ## Source-owned physical seed

The canonical whole-flow compiler never uses the receipt which happened to
produce its restart contact.  Its genuine input is the physical state written
at that contact together with the three source laws needed by the canonical
Galerkin projections.  Keeping that smaller input explicit lets a later
source-generated endpoint enter the same compiler without fabricating a prior
whole receipt.
-/

/-- Minimal source-owned datum consumed by the canonical whole-flow compiler.

The viscosity is an index so the same seed cannot silently migrate between
different physical generators.  No duration, cutoff, target path, branch, or
continuation witness is stored here. -/
class WholeRestartPhysicalSeed (ν : outParam Viscosity) (Seed : Type) where
  physicalState : Seed → ComplexVorticityHilbertState
  physicalState_zero : ∀ seed, physicalState seed 0 = 0
  transverse : ∀ seed, WholeStateTransverse (physicalState seed)
  reality : ∀ seed, FiniteStateFourierReality (physicalState seed)

/-- Versioned concrete seed for source producers which already generated the
whole state and its physical laws, but did not arrive through an earlier
`WholeContinuousMildSerrinReceipt`. -/
structure SourceOwnedWholeRestartPhysicalSeed (ν : Viscosity) where
  physicalState : ComplexVorticityHilbertState
  physicalState_zero : physicalState 0 = 0
  transverse : WholeStateTransverse physicalState
  reality : FiniteStateFourierReality physicalState

instance sourceOwnedWholeRestartPhysicalSeed_instance
    (ν : Viscosity) :
    WholeRestartPhysicalSeed ν (SourceOwnedWholeRestartPhysicalSeed ν) where
  physicalState := SourceOwnedWholeRestartPhysicalSeed.physicalState
  physicalState_zero := SourceOwnedWholeRestartPhysicalSeed.physicalState_zero
  transverse := SourceOwnedWholeRestartPhysicalSeed.transverse
  reality := SourceOwnedWholeRestartPhysicalSeed.reality

/-- Conservative instance: every historical positive restart contact exposes
exactly the same physical seed that the old compiler consumed. -/
instance generatedPositiveWholeRestartContact_physicalSeed
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime} :
    WholeRestartPhysicalSeed ν
      (GeneratedPositiveWholeRestartContact receipt) where
  physicalState := GeneratedPositiveWholeRestartContact.physicalState
  physicalState_zero :=
    GeneratedPositiveWholeRestartContact.physicalState_zero
  transverse := GeneratedPositiveWholeRestartContact.transverse
  reality := GeneratedPositiveWholeRestartContact.reality

/-- The exact whole state carried by a source-owned restart seed. -/
def wholeRestartPhysicalState
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (seed : Seed) : ComplexVorticityHilbertState :=
  WholeRestartPhysicalSeed.physicalState (ν := ν) seed

/-- Conservativity at the historical contact seam: the generic physical-seed
projection is definitionally the exact physical state carried by the actual
positive restart contact. -/
@[simp] theorem wholeRestartPhysicalState_generatedPositiveWholeRestartContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    wholeRestartPhysicalState contact = contact.physicalState := rfl

@[simp] theorem wholeRestartPhysicalState_zero
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (seed : Seed) :
    wholeRestartPhysicalState seed 0 = 0 :=
  WholeRestartPhysicalSeed.physicalState_zero (ν := ν) seed

theorem wholeRestartPhysicalTransverse
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (seed : Seed) :
    WholeStateTransverse (wholeRestartPhysicalState seed) :=
  WholeRestartPhysicalSeed.transverse (ν := ν) seed

theorem wholeRestartPhysicalReality
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (seed : Seed) :
    FiniteStateFourierReality (wholeRestartPhysicalState seed) :=
  WholeRestartPhysicalSeed.reality (ν := ν) seed

/-- The exact physical coefficient-enstrophy ceiling read from the actual
whole restart state.  It is retained as the conservative physical readout
of the quantized source ceiling below. -/
def wholeRestartRawCoefficientCeiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) : ℝ :=
  wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) + 1

/-- Native discrete level selected by the actual physical ceiling. -/
def wholeRestartCoefficientLevel
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) : ℕ :=
  Nat.ceil (wholeRestartRawCoefficientCeiling contact)

/-- The common barrier ceiling used by the whole restart producer.  Taking
the natural ceiling preserves the exact physical bound while ensuring that
a bounded physical trajectory can visit only finitely many generated
kernel cores. -/
def wholeRestartCoefficientCeiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) : ℝ :=
  wholeRestartCoefficientLevel contact

@[simp] theorem wholeRestartRawCoefficientCeiling_eq
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    wholeRestartRawCoefficientCeiling contact =
      wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) + 1 := rfl

/-- Conservativity: quantization never lowers the actual physical ceiling. -/
theorem wholeRestartRawCoefficientCeiling_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    wholeRestartRawCoefficientCeiling contact ≤
      wholeRestartCoefficientCeiling contact := by
  exact Nat.le_ceil (wholeRestartRawCoefficientCeiling contact)

/-- One positive horizon for the complete canonical projection family. -/
def wholeRestartDuration
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) : ℝ :=
  sourceOwnedWholeStateDuration ν
    (wholeRestartCoefficientCeiling contact)

theorem wholeRestartDuration_pos
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    0 < wholeRestartDuration contact :=
  sourceOwnedWholeStateDuration_pos ν
    (wholeRestartCoefficientCeiling contact)

/-- Canonical finite carrier at one generated radius. -/
def wholeRestartModes (radius : ℕ) : Finset IntegerWavevector :=
  puncturedIntegerWaveFrequencyCube radius

/-- Canonical projection of the actual whole restart state. -/
def wholeRestartInitialState
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (radius : ℕ) : ComplexVorticityHilbertState :=
  complexSharpSupportProjection
    (wholeRestartModes radius) (wholeRestartPhysicalState contact)

theorem wholeRestartInitialState_supported
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (radius : ℕ) :
    ∀ wave, wave ∉ wholeRestartModes radius →
      wholeRestartInitialState contact radius wave = 0 :=
  complexSharpSupportProjection_supported
    (wholeRestartModes radius) (wholeRestartPhysicalState contact)

theorem wholeRestartInitialState_transverse
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (radius : ℕ) :
    ∀ wave ∈ wholeRestartModes radius,
      complexWavevector wave ⬝ᵥ
          wholeRestartInitialState contact radius wave =
        0 :=
  complexSharpSupportProjection_transverse
    (wholeRestartModes radius) (wholeRestartPhysicalState contact) (wholeRestartPhysicalTransverse contact)

theorem wholeRestartInitialState_reality
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (radius : ℕ) :
    FiniteStateFourierReality
      (wholeRestartInitialState contact radius) :=
  complexSharpSupportProjection_reality
    (wholeRestartModes radius) (wholeRestartPhysicalState contact)
    (fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem)
    (wholeRestartPhysicalReality contact)

/-- One actual finite unforced orbit compiled from the canonical projection
of the whole restart state. -/
structure GeneratedWholeRestartCanonicalStage
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (radius : ℕ) where
  trajectory : ℝ → ComplexVorticityHilbertState
  initial :
    trajectory 0 = wholeRestartInitialState contact radius
  physical :
    ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
      HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (wholeRestartModes radius) ν.coeff (trajectory time))
          time ∧
        (∀ wave, wave ∉ wholeRestartModes radius →
          trajectory time wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ trajectory time wave = 0) ∧
        FiniteStateFourierReality (trajectory time)

/-- The finite trajectory is generated internally from the canonical
projection and the whole-state horizon. -/
noncomputable def generatedWholeRestartCanonicalStage
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (radius : ℕ) :
    GeneratedWholeRestartCanonicalStage contact radius := by
  let trajectoryResult :=
    exists_finitePhysicalTrajectory_on_Icc
      (wholeRestartModes radius)
      (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
      (fun _wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem)
      ν (wholeRestartInitialState contact radius)
      (wholeRestartInitialState_supported contact radius)
      (wholeRestartInitialState_transverse contact radius)
      (wholeRestartInitialState_reality contact radius)
      (wholeRestartDuration contact)
      (wholeRestartDuration_pos contact)
  let trajectory := Classical.choose trajectoryResult
  have trajectorySpec := Classical.choose_spec trajectoryResult
  exact
    { trajectory := trajectory
      initial := trajectorySpec.1
      physical := trajectorySpec.2 }

/-- The generated whole-state ceiling bounds every canonical finite initial
state, uniformly in radius. -/
theorem wholeRestartInitialState_enstrophy_add_one_le_ceiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed)
    (radius : ℕ) :
    finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (wholeRestartInitialState contact radius) + 1 ≤
      wholeRestartCoefficientCeiling contact := by
  unfold wholeRestartInitialState
  rw [finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
  apply le_trans _ (wholeRestartRawCoefficientCeiling_le contact)
  unfold wholeRestartRawCoefficientCeiling
  linarith [finiteStateVorticityCoefficientEnstrophy_le_wholeMass
    (wholeRestartModes radius) (wholeRestartPhysicalState contact)]

/-- Every actual canonical trajectory obeys the same source-generated local
barrier on the same physical interval. -/
theorem GeneratedWholeRestartCanonicalStage.uniformBarrier
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius) :
    ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
      finiteStateVorticityHalfEnstrophy
            (wholeRestartModes radius) (stage.trajectory time) ≤
          finiteStateVorticityHalfEnstrophy
              (wholeRestartModes radius) (stage.trajectory 0) +
            sourceOwnedWholeStateBarrierSlope ν
                (wholeRestartCoefficientCeiling contact) * time ∧
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) (stage.trajectory time) ≤
          wholeRestartCoefficientCeiling contact := by
  apply finiteStateVorticity_sourceOwnedWholeStateBarrier_on_Icc
    (wholeRestartModes radius)
    (fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem)
    ν (wholeRestartCoefficientCeiling contact) stage.trajectory
    (wholeRestartDuration contact)
  · rw [stage.initial]
    exact wholeRestartInitialState_enstrophy_add_one_le_ceiling
      contact radius
  · exact le_rfl
  · intro time timeMem
    exact (stage.physical time timeMem).1
  · intro time timeMem
    exact (stage.physical time timeMem).2.2.2
  · intro time timeMem wave waveMem
    exact (stage.physical time timeMem).2.2.1 wave

/-- The terminal coefficient mass of every canonical stage quantitatively
factors through the unweighted vorticity payment on the same prefix.  This
is the finite-stage commuting row later preserved by the whole-carrier
limit. -/
theorem GeneratedWholeRestartCanonicalStage.terminal_sub_one_mul_time_le_integral
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    time.1 *
        (finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) (stage.trajectory time.1) - 1) ≤
      ∫ actual in (0 : ℝ)..time.1,
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) (stage.trajectory actual) := by
  apply finiteStateVorticity_terminal_sub_one_mul_time_le_integral
    (wholeRestartModes radius)
    (fun _wave waveMem ↦
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem)
    ν (wholeRestartCoefficientCeiling contact) stage.trajectory
    (wholeRestartDuration contact)
  · rw [stage.initial]
    exact wholeRestartInitialState_enstrophy_add_one_le_ceiling
      contact radius
  · exact le_rfl
  · intro actual actualMem
    exact (stage.physical actual actualMem).1
  · intro actual actualMem
    exact (stage.physical actual actualMem).2.2.2
  · intro actual actualMem wave waveMem
    exact (stage.physical actual actualMem).2.2.1 wave
  · exact time.2

/-- The complete compactness ledger is uniform across the canonical replay:
pointwise coefficient mass, gradient time mass, Serrin velocity mass, and
negative-one tangent mass are all paid on the same generated horizon. -/
theorem GeneratedWholeRestartCanonicalStage.uniformCompactnessBudget
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius) :
    (∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) (stage.trajectory time) ≤
          wholeRestartCoefficientCeiling contact) ∧
      (3 * ν.coeff / 8) * (2 * Real.pi) ^ 2 *
            (∫ time in (0 : ℝ)..wholeRestartDuration contact,
              finiteStateVorticityEnstrophyMass
                (wholeRestartModes radius) (stage.trajectory time)) ≤
        finiteStateVorticityHalfEnstrophy
            (wholeRestartModes radius) (stage.trajectory 0) +
          sourceOwnedLocalQuadraticCoefficient ν
              (wholeRestartCoefficientCeiling contact) *
            wholeRestartCoefficientCeiling contact ^ 2 *
              wholeRestartDuration contact ∧
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVelocityMajorant
            (wholeRestartModes radius) (stage.trajectory time) ^ 2) ≤
        2 * sourceOwnedLocalCoreVelocityCoefficient ν
              (wholeRestartCoefficientCeiling contact) *
            wholeRestartCoefficientCeiling contact *
              wholeRestartDuration contact +
          2 * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν
              (wholeRestartCoefficientCeiling contact) *
            (∫ time in (0 : ℝ)..wholeRestartDuration contact,
              finiteStateVorticityEnstrophyMass
                (wholeRestartModes radius) (stage.trajectory time)) ∧
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVorticityNegativeOneMass
            (wholeRestartModes radius)
            (finiteStateVorticityGenerator
              (wholeRestartModes radius) ν.coeff
              (stage.trajectory time))) ≤
        8 * wholeRestartCoefficientCeiling contact *
            (∫ time in (0 : ℝ)..wholeRestartDuration contact,
              finiteStateVelocityMajorant
                (wholeRestartModes radius) (stage.trajectory time) ^ 2) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            (∫ time in (0 : ℝ)..wholeRestartDuration contact,
              finiteStateVorticityEnstrophyMass
                (wholeRestartModes radius) (stage.trajectory time)) := by
  apply
    finiteStateVorticity_sourceOwnedWholeStateCompactnessBudget_on_Icc
      (wholeRestartModes radius)
      (fun _wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem)
      ν (wholeRestartCoefficientCeiling contact) stage.trajectory
      (wholeRestartDuration contact)
      (wholeRestartDuration_pos contact).le
  · rw [stage.initial]
    exact wholeRestartInitialState_enstrophy_add_one_le_ceiling
      contact radius
  · exact le_rfl
  · intro time timeMem
    exact (stage.physical time timeMem).1
  · intro time timeMem
    exact (stage.physical time timeMem).2.2.2
  · intro time timeMem wave waveMem
    exact (stage.physical time timeMem).2.2.1 wave

/-! ## Uniform scalar ceilings for compactness -/

theorem wholeRestartCoefficientCeiling_pos
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    0 < wholeRestartCoefficientCeiling contact := by
  have rawPos : 0 < wholeRestartRawCoefficientCeiling contact := by
    unfold wholeRestartRawCoefficientCeiling wholeVorticityEuclideanMass
    have massNonneg :
        0 ≤ ∑' wave : IntegerWavevector,
          vorticityRowAmplitude (wholeRestartPhysicalState contact) wave ^ 2 :=
      tsum_nonneg fun wave => sq_nonneg _
    linarith
  have massNonneg :
      wholeRestartRawCoefficientCeiling contact ≤
        wholeRestartCoefficientCeiling contact :=
    wholeRestartRawCoefficientCeiling_le contact
  exact rawPos.trans_le massNonneg

def wholeRestartGradientCeiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) : ℝ :=
  let ceiling := wholeRestartCoefficientCeiling contact
  (ceiling / 2 +
      sourceOwnedLocalQuadraticCoefficient ν ceiling * ceiling ^ 2 *
        wholeRestartDuration contact) /
    ((3 * ν.coeff / 8) * (2 * Real.pi) ^ 2)

def wholeRestartVelocityCeiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) : ℝ :=
  let ceiling := wholeRestartCoefficientCeiling contact
  2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling * ceiling *
      wholeRestartDuration contact +
    2 * biotSavartSerrinConstant *
      sourceOwnedKernelTailTolerance ν ceiling *
      wholeRestartGradientCeiling contact

def wholeRestartNegativeOneCeiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) : ℝ :=
  8 * wholeRestartCoefficientCeiling contact *
      wholeRestartVelocityCeiling contact +
    2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
      wholeRestartGradientCeiling contact

theorem wholeRestartGradientCoefficient_pos
    (ν : Viscosity) :
    0 < (3 * ν.coeff / 8) * (2 * Real.pi) ^ 2 := by
  exact mul_pos
    (div_pos (mul_pos (by norm_num) ν.coeff_pos) (by norm_num))
    (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))

theorem wholeRestartGradientCeiling_nonneg
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    0 ≤ wholeRestartGradientCeiling contact := by
  unfold wholeRestartGradientCeiling
  apply div_nonneg
  · apply add_nonneg
    · exact div_nonneg (wholeRestartCoefficientCeiling_pos contact).le
        (by norm_num)
    · exact mul_nonneg
        (mul_nonneg
          (sourceOwnedLocalQuadraticCoefficient_nonneg ν _)
          (sq_nonneg _))
        (wholeRestartDuration_pos contact).le
  · exact (wholeRestartGradientCoefficient_pos ν).le

theorem wholeRestartVelocityCeiling_nonneg
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    0 ≤ wholeRestartVelocityCeiling contact := by
  unfold wholeRestartVelocityCeiling
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (sourceOwnedLocalCoreVelocityCoefficient_nonneg ν _))
        (wholeRestartCoefficientCeiling_pos contact).le)
      (wholeRestartDuration_pos contact).le)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        (sourceOwnedKernelTailTolerance_pos ν _).le)
      (wholeRestartGradientCeiling_nonneg contact))

theorem wholeRestartNegativeOneCeiling_nonneg
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    0 ≤ wholeRestartNegativeOneCeiling contact := by
  unfold wholeRestartNegativeOneCeiling
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (wholeRestartCoefficientCeiling_pos contact).le)
      (wholeRestartVelocityCeiling_nonneg contact))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (sq_nonneg _))
      (wholeRestartGradientCeiling_nonneg contact))

/-- Uniform unweighted compactness budget for one generated canonical
stage. -/
theorem GeneratedWholeRestartCanonicalStage.uniformScalarBudget
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {radius : ℕ}
    (stage : GeneratedWholeRestartCanonicalStage contact radius) :
    (∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) (stage.trajectory time) ≤
          wholeRestartCoefficientCeiling contact) ∧
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVorticityEnstrophyMass
            (wholeRestartModes radius) (stage.trajectory time)) ≤
        wholeRestartGradientCeiling contact ∧
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVelocityMajorant
            (wholeRestartModes radius) (stage.trajectory time) ^ 2) ≤
        wholeRestartVelocityCeiling contact ∧
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVorticityNegativeOneMass
            (wholeRestartModes radius)
            (finiteStateVorticityGenerator
              (wholeRestartModes radius) ν.coeff
              (stage.trajectory time))) ≤
        wholeRestartNegativeOneCeiling contact := by
  obtain ⟨enstrophy, gradientWeighted, velocityRaw, negativeRaw⟩ :=
    stage.uniformCompactnessBudget
  have initialHalfLe :
      finiteStateVorticityHalfEnstrophy
            (wholeRestartModes radius) (stage.trajectory 0) ≤
        wholeRestartCoefficientCeiling contact / 2 := by
    unfold finiteStateVorticityHalfEnstrophy
    have initialFits :
        finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes radius) (stage.trajectory 0) + 1 ≤
          wholeRestartCoefficientCeiling contact := by
      rw [stage.initial]
      exact wholeRestartInitialState_enstrophy_add_one_le_ceiling
        contact radius
    linarith
  have gradient :
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVorticityEnstrophyMass
            (wholeRestartModes radius) (stage.trajectory time)) ≤
        wholeRestartGradientCeiling contact := by
    unfold wholeRestartGradientCeiling
    apply (le_div_iff₀ (wholeRestartGradientCoefficient_pos ν)).2
    calc
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVorticityEnstrophyMass
            (wholeRestartModes radius) (stage.trajectory time)) *
            ((3 * ν.coeff / 8) * (2 * Real.pi) ^ 2) =
          ((3 * ν.coeff / 8) * (2 * Real.pi) ^ 2) *
            (∫ time in (0 : ℝ)..wholeRestartDuration contact,
              finiteStateVorticityEnstrophyMass
                (wholeRestartModes radius) (stage.trajectory time)) := by
        ring
      _ ≤
          finiteStateVorticityHalfEnstrophy
              (wholeRestartModes radius) (stage.trajectory 0) +
            sourceOwnedLocalQuadraticCoefficient ν
                (wholeRestartCoefficientCeiling contact) *
              wholeRestartCoefficientCeiling contact ^ 2 *
                wholeRestartDuration contact := gradientWeighted
      _ ≤
          wholeRestartCoefficientCeiling contact / 2 +
            sourceOwnedLocalQuadraticCoefficient ν
                (wholeRestartCoefficientCeiling contact) *
              wholeRestartCoefficientCeiling contact ^ 2 *
                wholeRestartDuration contact :=
        add_le_add initialHalfLe le_rfl
  have velocityCoefficientNonneg :
      0 ≤ 2 * biotSavartSerrinConstant *
        sourceOwnedKernelTailTolerance ν
          (wholeRestartCoefficientCeiling contact) :=
    mul_nonneg
      (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
      (sourceOwnedKernelTailTolerance_pos ν _).le
  have velocity :
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVelocityMajorant
            (wholeRestartModes radius) (stage.trajectory time) ^ 2) ≤
        wholeRestartVelocityCeiling contact := by
    refine velocityRaw.trans ?_
    unfold wholeRestartVelocityCeiling
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left gradient velocityCoefficientNonneg)
  have negativeVelocityCoefficientNonneg :
      0 ≤ 8 * wholeRestartCoefficientCeiling contact :=
    mul_nonneg (by norm_num)
      (wholeRestartCoefficientCeiling_pos contact).le
  have negativeGradientCoefficientNonneg :
      0 ≤ 2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have negative :
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
          finiteStateVorticityNegativeOneMass
            (wholeRestartModes radius)
            (finiteStateVorticityGenerator
              (wholeRestartModes radius) ν.coeff
              (stage.trajectory time))) ≤
        wholeRestartNegativeOneCeiling contact := by
    refine negativeRaw.trans ?_
    unfold wholeRestartNegativeOneCeiling
    exact add_le_add
      (mul_le_mul_of_nonneg_left velocity
        negativeVelocityCoefficientNonneg)
      (mul_le_mul_of_nonneg_left gradient
        negativeGradientCoefficientNonneg)
  exact ⟨enstrophy, gradient, velocity, negative⟩

/-- The canonical initial rows converge strongly to the exact actual whole
restart state; no finite cutoff remains in the limit. -/
theorem wholeRestartInitialState_tendsto
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    Tendsto (wholeRestartInitialState contact) atTop
      (𝓝 (wholeRestartPhysicalState contact)) := by
  exact
    complexSharpSupportProjection_puncturedFrequencyCube_tendsto
      (wholeRestartPhysicalState contact) (wholeRestartPhysicalState_zero contact)

/-- The complete source-generated canonical replay family. -/
structure GeneratedWholeRestartCanonicalReplay
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) where
  current :
    ∀ radius : ℕ,
      GeneratedWholeRestartCanonicalStage contact radius
  initial_tendsto :
    Tendsto (fun radius => (current radius).trajectory 0) atTop
      (𝓝 (wholeRestartPhysicalState contact))

noncomputable def generatedWholeRestartCanonicalReplay
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (contact : Seed) :
    GeneratedWholeRestartCanonicalReplay contact where
  current := generatedWholeRestartCanonicalStage contact
  initial_tendsto := by
    have initialEq :
        (fun radius =>
          (generatedWholeRestartCanonicalStage contact radius).trajectory 0) =
          wholeRestartInitialState contact := by
      funext radius
      exact (generatedWholeRestartCanonicalStage contact radius).initial
    rw [initialEq]
    exact wholeRestartInitialState_tendsto contact

/-- Authoritative native-contact producer.  The source occurrence itself
selects the whole restart state, the common horizon, and every canonical
unforced Galerkin orbit. -/
noncomputable def generatedNativeMacroWholeRestartCanonicalReplayAt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    GeneratedWholeRestartCanonicalReplay
      (generatedNativeMacroWholePositiveTimeRestartContactAt lineage index) :=
  generatedWholeRestartCanonicalReplay
    (generatedNativeMacroWholePositiveTimeRestartContactAt lineage index)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
end NavierStokes
end SaturationMonoid
