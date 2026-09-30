import H0mework.Realization.Arithmetic.Incidence
import H0mework.Foundation.Arithmetic.RootIncidence
import H0mework.NavierStokes.Restart.RealityClosure
import H0mework.NavierStokes.Restart.WholeMildAssembly
import H0mework.NavierStokes.Restart.CriticalDissipationLedger
import H0mework.NavierStokes.Energy.WholeTangentEnergyTransport
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness

/-!
# Generated whole restart as an actual mild/Serrin receipt

The canonical replay now compiles into one whole continuous unforced update
from the exact actual restart state.  Its strong limit, transverse nonlinear
state, Fourier reality, whole gradient budget, negative-one tangent, and
real-line row derivatives all come from the same generated replay.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin

open scoped ENNReal Topology

open Set Filter MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticIncidence
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticGeneration
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientWholeContinuousMildAssembly
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartRealityClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeMildAssembly
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact

noncomputable section

/-- The actual transverse nonlinear row, canonically extended by zero off
the generated physical interval. -/
def wholeRestartActualWaveNonlinearExtension
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  commonTimeZeroExtension (wholeRestartDuration contact)
    (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)

theorem wholeRestartActualWaveNonlinearExtension_intervalIntegrable
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (wholeRestartActualWaveNonlinearExtension closure wave)
      volume 0 (wholeRestartDuration contact) :=
  commonTimeZeroExtension_intervalIntegrable
    (wholeRestartDuration contact) (wholeRestartDuration_pos contact).le
    (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)

/-- The real-line integrating-factor path determined by the exact restart
initial row and generated transverse nonlinearity. -/
def wholeRestartActualWaveHeatDuhamelPath
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  heatDuhamelComplexCoordinatePath
    ((wholeRestartPhysicalState contact) wave)
    (wholeRestartActualWaveNonlinearExtension closure wave)
    (ν.coeff * integerWaveViscousMultiplier wave) 0

theorem wholeRestartWholePath_mild_identity
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    (wholeRestartWholeMildAssembly closure).wholePath time wave =
      fixedWaveHeatDuhamelValue
        (wholeRestartDuration contact) ν.coeff wave
        ((wholeRestartPhysicalState contact) wave)
        (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)
        time := by
  change
    assemblyWholeMildPath
        (wholeRestartWholeMildAssemblyInput closure) time wave = _
  rw [assemblyWholeMildPath_apply,
    assemblyWholeMildState_apply,
    assemblyMildCoefficient_eq_rowPath
      (wholeRestartWholeMildAssemblyInput closure)
      time wave waveNonzero]
  exact
    (wholeRestartWholeMildAssemblyInput
      closure).row_mild_identity wave waveNonzero time

theorem wholeRestartWholePath_wave_eq_actualWaveHeatDuhamelPath
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    (wholeRestartWholeMildAssembly closure).wholePath time wave =
      wholeRestartActualWaveHeatDuhamelPath closure wave time.1 := by
  have convertedIntegral :=
    commonTime_integral_Iic_eq_intervalIntegral
      (wholeRestartDuration contact) (wholeRestartDuration_pos contact).le time
      (fun earlier =>
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier) wave •
          wholeRestartActualWaveNonlinearExtension closure wave earlier)
  have convertedIntegral' :
      (∫ earlier in Iic time,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            transverseSpaceTimeNonlinearRow
              closure.transverseLimit wave earlier
          ∂(commonTimeMeasure (wholeRestartDuration contact))) =
        ∫ earlier in (0 : ℝ)..time.1,
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier) wave •
            wholeRestartActualWaveNonlinearExtension
              closure wave earlier := by
    rw [← convertedIntegral]
    apply integral_congr_ae
    filter_upwards with earlier
    rw [wholeRestartActualWaveNonlinearExtension,
      commonTimeZeroExtension_of_mem
        (wholeRestartDuration contact)
        (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)
        earlier.1 earlier.property]
  rw [wholeRestartWholePath_mild_identity
    closure wave waveNonzero time]
  unfold fixedWaveHeatDuhamelValue
  rw [convertedIntegral']
  unfold wholeRestartActualWaveHeatDuhamelPath
  rw [heatDuhamelComplexCoordinatePath_eq_heat_add_integral]
  unfold finiteStateVorticityHeatMultiplier
  simp only [sub_zero]

/-- The assembled whole path inherits the actual finite-stage kinetic
ledger almost everywhere on the same physical interval. -/
theorem wholeRestartWholePath_kineticMass_ae_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      puncturedWholeVorticityKineticMass
          ((wholeRestartWholeMildAssembly closure).wholePath time) ≤
        puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) := by
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      (wholeRestartWholeMildAssembly closure).wholePath
  filter_upwards [closure.kineticMass_ae_le, pathAE] with
    time kineticLe pathEq
  rw [wholeRestartWholeMildAssembly_toLp_eq closure] at pathEq
  simpa only [← pathEq] using kineticLe

private theorem commonTimeMeasure_eq_comap_volume
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

/-- Continuity upgrades the generated almost-everywhere kinetic ledger to
the actual assembled path at every physical time.  No exceptional endpoint
or externally supplied ceiling remains in the theorem mouth. -/
theorem wholeRestartWholePath_kineticMass_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    puncturedWholeVorticityKineticMass
        ((wholeRestartWholeMildAssembly closure).wholePath time) ≤
      puncturedWholeVorticityKineticMass
        (wholeRestartPhysicalState contact) := by
  let kineticCeiling :=
    puncturedWholeVorticityKineticMass
      (wholeRestartPhysicalState contact)
  let extendedKinetic : ℝ → ℝ :=
    fun actualTime =>
      puncturedWholeVorticityKineticMass
        ((wholeRestartWholeMildAssembly closure).wholePath
          (Set.projIcc
            (0 : ℝ) (wholeRestartDuration contact)
            (wholeRestartDuration_pos contact).le actualTime))
  let clippedKinetic : ℝ → ℝ :=
    fun actualTime => max (extendedKinetic actualTime) kineticCeiling
  have extendedContinuous : Continuous extendedKinetic :=
    continuous_puncturedWholeVorticityKineticMass.comp
      ((wholeRestartWholeMildAssembly closure).wholePath.continuous.comp
        continuous_projIcc)
  have clippedContinuous : Continuous clippedKinetic :=
    extendedContinuous.max continuous_const
  have kineticSubtypeAE :=
    wholeRestartWholePath_kineticMass_ae_le closure
  rw [commonTimeMeasure_eq_comap_volume] at kineticSubtypeAE
  have clippedKineticAE :
      clippedKinetic =ᵐ[
        volume.restrict
          (Icc (0 : ℝ) (wholeRestartDuration contact))]
        fun _ => kineticCeiling := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [kineticSubtypeAE] with currentTime kineticLe
    simp only [clippedKinetic, extendedKinetic,
      Set.projIcc_of_mem (wholeRestartDuration_pos contact).le
        currentTime.property, kineticCeiling, max_eq_right kineticLe]
  have clippedKineticOn :=
    Measure.eqOn_Icc_of_ae_eq
      (μ := volume)
      (wholeRestartDuration_pos contact).ne
      clippedKineticAE
      clippedContinuous.continuousOn
      continuousOn_const
  have clippedAtTime := clippedKineticOn time.property
  have projectedTimeEq :
      Set.projIcc
          (0 : ℝ) (wholeRestartDuration contact)
          (wholeRestartDuration_pos contact).le time.1 =
        time := by
    simpa only [Subtype.coe_eta] using
      (Set.projIcc_of_mem
        (wholeRestartDuration_pos contact).le time.property)
  dsimp only [clippedKinetic, extendedKinetic] at clippedAtTime
  rw [projectedTimeEq] at clippedAtTime
  have kineticLeCeiling :
      puncturedWholeVorticityKineticMass
          ((wholeRestartWholeMildAssembly closure).wholePath time) ≤
        kineticCeiling :=
    (le_max_left _ _).trans_eq clippedAtTime
  simpa only [kineticCeiling] using kineticLeCeiling

/-- The assembled whole path also retains the coefficient-enstrophy ceiling
generated by the exact contact from which the replay started. -/
theorem wholeRestartWholePath_coefficientMass_ae_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      wholeVorticityEuclideanMass
          ((wholeRestartWholeMildAssembly closure).wholePath time) ≤
        wholeRestartCoefficientCeiling contact := by
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      (wholeRestartWholeMildAssembly closure).wholePath
  filter_upwards [closure.coefficientMass_ae_le, pathAE] with
    time massLe pathEq
  rw [wholeRestartWholeMildAssembly_toLp_eq closure] at pathEq
  simpa only [← pathEq] using massLe

/-- The nonlinear-minus-viscous tangent of one assembled nonzero row. -/
def wholeRestartActualWaveTangent
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (_waveNonzero : wave ≠ 0) :
    Icc (0 : ℝ) (wholeRestartDuration contact) → ComplexCoordinateVector :=
  fun time =>
    transverseSpaceTimeNonlinearRow closure.transverseLimit wave time -
      (ν.coeff * integerWaveViscousMultiplier wave) •
        (wholeRestartWholeMildAssembly closure).wholePath time wave

theorem wholeRestartActualWaveHeatDuhamelPath_absolutelyContinuous
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector) :
    AbsolutelyContinuousOnInterval
      (wholeRestartActualWaveHeatDuhamelPath closure wave)
      0 (wholeRestartDuration contact) :=
  heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
    ((wholeRestartPhysicalState contact) wave)
    (ν.coeff * integerWaveViscousMultiplier wave) 0
    (wholeRestartActualWaveNonlinearExtension_intervalIntegrable closure wave)
    (by simp)

theorem wholeRestartActualWaveHeatDuhamelPath_ae_hasDerivAt
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ actual : ℝ,
      actual ∈ uIcc (0 : ℝ) (wholeRestartDuration contact) →
        HasDerivAt
          (wholeRestartActualWaveHeatDuhamelPath closure wave)
          (commonTimeZeroExtension (wholeRestartDuration contact)
            (wholeRestartActualWaveTangent closure wave waveNonzero) actual)
          actual := by
  have generated :=
    heatDuhamelComplexCoordinatePath_ae_hasDerivAt
      ((wholeRestartPhysicalState contact) wave)
      (ν.coeff * integerWaveViscousMultiplier wave) 0
      (wholeRestartActualWaveNonlinearExtension_intervalIntegrable closure wave)
      (by simp)
  filter_upwards [generated] with actual derivative
  intro actualMem
  have actualIcc :
      actual ∈ Icc (0 : ℝ) (wholeRestartDuration contact) := by
    simpa [uIcc_of_le (wholeRestartDuration_pos contact).le] using actualMem
  have pathEq :=
    wholeRestartWholePath_wave_eq_actualWaveHeatDuhamelPath
      closure wave waveNonzero ⟨actual, actualIcc⟩
  rw [commonTimeZeroExtension_of_mem
    (wholeRestartDuration contact)
    (wholeRestartActualWaveTangent closure wave waveNonzero)
    actual actualIcc]
  unfold wholeRestartActualWaveTangent
  rw [pathEq]
  rw [wholeRestartActualWaveNonlinearExtension,
    commonTimeZeroExtension_of_mem
      (wholeRestartDuration contact)
      (transverseSpaceTimeNonlinearRow closure.transverseLimit wave)
      actual actualIcc] at derivative
  simpa only [wholeRestartActualWaveHeatDuhamelPath,
    wholeRestartActualWaveNonlinearExtension] using derivative actualMem

/-- The complete weighted whole nonlinear-minus-viscous tangent. -/
noncomputable def wholeRestartWholeNegativeOneTangent
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    SpaceTimeState (wholeRestartDuration contact) :=
  wholeRestartNegativeOneForcing closure -
    wholeSpaceTimeViscousNegativeOneState
      ν.coeff closure.weakClosure.stateLimit closure.gradient_summable
      (wholePointwiseGradientDensity_ae_summable
        (wholeRestartDuration contact) closure.weakClosure.stateLimit
        closure.gradient_summable)

theorem wholeRestartWholeNegativeOneTangent_eq_unforced_ae
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      wholeRestartWholeNegativeOneTangent closure time =
        wholeSpaceTimeNonlinearNegativeOneFunction
            closure.transverseLimit time -
          wholeSpaceTimeViscousNegativeOneFunction
            ν.coeff closure.weakClosure.stateLimit time := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (wholeRestartNegativeOneForcing closure)
      (wholeSpaceTimeViscousNegativeOneState
        ν.coeff closure.weakClosure.stateLimit closure.gradient_summable
        (wholePointwiseGradientDensity_ae_summable
          (wholeRestartDuration contact) closure.weakClosure.stateLimit
          closure.gradient_summable)),
    wholeSpaceTimeNonlinearNegativeOneState_coeFn
      closure.transverseLimit
      (wholeRestartTransverseGradient_summable closure)
      (wholeRestartCoefficientCeiling_pos contact).le
      (wholeRestartTransverseCoefficientMass_ae_le closure),
    wholeSpaceTimeViscousNegativeOneState_coeFn
      ν.coeff closure.weakClosure.stateLimit closure.gradient_summable
      (wholePointwiseGradientDensity_ae_summable
        (wholeRestartDuration contact) closure.weakClosure.stateLimit
        closure.gradient_summable)] with
      time tangentEq nonlinearEq viscousEq
  have nonlinearEq' :
      wholeRestartNegativeOneForcing closure time =
        wholeSpaceTimeNonlinearNegativeOneFunction
          closure.transverseLimit time := by
    simpa only [wholeRestartNegativeOneForcing] using nonlinearEq
  rw [wholeRestartWholeNegativeOneTangent, tangentEq]
  change
    wholeRestartNegativeOneForcing closure time -
        wholeSpaceTimeViscousNegativeOneState
          ν.coeff closure.weakClosure.stateLimit closure.gradient_summable
          (wholePointwiseGradientDensity_ae_summable
            (wholeRestartDuration contact) closure.weakClosure.stateLimit
            closure.gradient_summable) time = _
  rw [nonlinearEq', viscousEq]

theorem wholeRestartActualWaveTangent_eq_wholeNegativeOneTangent_ae
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeRestartWholeNegativeOneTangent closure time) wave =
        wholeRestartActualWaveTangent closure wave waveNonzero time := by
  have pointwiseGradient :=
    wholePointwiseGradientDensity_ae_summable
      (wholeRestartDuration contact) closure.weakClosure.stateLimit
      closure.gradient_summable
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (wholeRestartNegativeOneForcing closure)
      (wholeSpaceTimeViscousNegativeOneState
        ν.coeff closure.weakClosure.stateLimit
        closure.gradient_summable pointwiseGradient),
    wholeRestartNegativeOneForcing_unweighted_row_ae
      closure wave waveNonzero,
    wholeSpaceTimeViscousNegativeOneState_unweighted_row_ae
      ν.coeff closure.weakClosure.stateLimit
      closure.gradient_summable pointwiseGradient wave,
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      (wholeRestartWholeMildAssembly closure).wholePath] with
      time tangentEq nonlinearEq viscousEq pathEq
  rw [wholeRestartWholeNegativeOneTangent, tangentEq]
  change
    (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
        ((wholeRestartNegativeOneForcing closure time) wave -
          (wholeSpaceTimeViscousNegativeOneState
            ν.coeff closure.weakClosure.stateLimit
            closure.gradient_summable pointwiseGradient time) wave) = _
  have nonlinearEqComplex :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeRestartNegativeOneForcing closure time) wave =
        transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave time := by
    calc
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeRestartNegativeOneForcing closure time) wave =
          (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
            (wholeRestartNegativeOneForcing closure time) wave := by
        ext coordinate
        simp [Complex.real_smul]
      _ = _ := nonlinearEq
  have viscousEqComplex :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeSpaceTimeViscousNegativeOneState
            ν.coeff closure.weakClosure.stateLimit
            closure.gradient_summable pointwiseGradient time) wave =
        (ν.coeff * integerWaveViscousMultiplier wave) •
          closure.weakClosure.stateLimit time wave := by
    calc
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (wholeSpaceTimeViscousNegativeOneState
            ν.coeff closure.weakClosure.stateLimit
            closure.gradient_summable pointwiseGradient time) wave =
          (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
            (wholeSpaceTimeViscousNegativeOneState
              ν.coeff closure.weakClosure.stateLimit
              closure.gradient_summable pointwiseGradient time) wave := by
        ext coordinate
        simp [Complex.real_smul]
      _ = _ := viscousEq
  rw [smul_sub, nonlinearEqComplex, viscousEqComplex]
  unfold wholeRestartActualWaveTangent
  rw [← wholeRestartWholeMildAssembly_toLp_eq closure, pathEq]

/-- The canonical replay closure generates one whole continuous
mild/Serrin receipt on its source-owned positive horizon. -/
noncomputable def wholeRestartWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    WholeContinuousMildSerrinReceipt
      ν (wholeRestartPhysicalState contact) (wholeRestartDuration contact) where
  requestedTimePos := wholeRestartDuration_pos contact
  stateLimit := closure.weakClosure.stateLimit
  transverseLimit := closure.transverseLimit
  stateLimit_eq_transverse := closure.inclusion_eq
  wholePath := (wholeRestartWholeMildAssembly closure).wholePath
  wholePath_toLp_eq_stateLimit :=
    wholeRestartWholeMildAssembly_toLp_eq closure
  wholePath_initial :=
    (wholeRestartWholeMildAssembly closure).wholePath_initial
  wholePath_zero_row := fun time => by
    change
      assemblyWholeMildPath
          (wholeRestartWholeMildAssemblyInput closure) time 0 = 0
    exact
      assemblyWholeMildPath_zero_row
        (wholeRestartWholeMildAssemblyInput closure) time
  transverse_fourierReality_ae :=
    wholeRestartTransverseLimit_fourierReality_ae closure
  gradient_summable := closure.gradient_summable
  wholeTangent := wholeRestartWholeNegativeOneTangent closure
  wholeTangent_eq_unforced_ae :=
    wholeRestartWholeNegativeOneTangent_eq_unforced_ae closure
  rowExtension wave _waveNonzero :=
    wholeRestartActualWaveHeatDuhamelPath closure wave
  rowExtension_on_interval wave waveNonzero time :=
    (wholeRestartWholePath_wave_eq_actualWaveHeatDuhamelPath
      closure wave waveNonzero time).symm
  rowTangent wave waveNonzero :=
    wholeRestartActualWaveTangent closure wave waveNonzero
  rowTangent_eq_unforced_ae wave _waveNonzero := by
    filter_upwards [
      transverseSpaceTimeNonlinearRow_coeFn
        closure.transverseLimit wave] with time nonlinearEq
    unfold wholeRestartActualWaveTangent
    rw [nonlinearEq]
    exact congrArg
      (fun nonlinear =>
        nonlinear -
          (ν.coeff * integerWaveViscousMultiplier wave) •
            (wholeRestartWholeMildAssembly closure).wholePath time wave)
      (wholeStateVorticityBilinearCoefficientAt_self
        (closure.transverseLimit time).1 wave).symm
  rowTangent_eq_wholeTangent_ae wave waveNonzero :=
    wholeRestartActualWaveTangent_eq_wholeNegativeOneTangent_ae
      closure wave waveNonzero
  rowExtension_absolutelyContinuous wave _waveNonzero :=
    wholeRestartActualWaveHeatDuhamelPath_absolutelyContinuous closure wave
  rowExtension_ae_hasDerivAt wave waveNonzero :=
    wholeRestartActualWaveHeatDuhamelPath_ae_hasDerivAt
      closure wave waveNonzero
  row_mild_identity wave waveNonzero time :=
    wholeRestartWholePath_mild_identity closure wave waveNonzero time

/-- Source-facing compiler from the actual canonical replay. -/
noncomputable def generatedWholeRestartWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    WholeContinuousMildSerrinReceipt
      ν (wholeRestartPhysicalState contact) (wholeRestartDuration contact) :=
  wholeRestartWholeContinuousMildSerrinReceipt
    (generatedWholeRestartCriticalClosure replay)

/-- Public source-facing whole-flow producer for any generated physical seed.

The seed itself fixes the initial whole state, its canonical Galerkin
family, and the positive source-owned horizon.  The caller supplies no
duration, cutoff, branch, target solution, continuation witness, or
coverage certificate. -/
noncomputable def
    generatedWholeRestartPhysicalSeedWholeContinuousMildSerrinReceipt
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    (seed : Seed) :
    WholeContinuousMildSerrinReceipt
      ν (wholeRestartPhysicalState seed) (wholeRestartDuration seed) :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt
    (generatedWholeRestartCanonicalReplay seed)

/-- Conservativity regression: on a historical positive restart contact,
the generic seed producer is definitionally the existing canonical replay
compiler. -/
@[simp] theorem
    generatedWholeRestartPhysicalSeedWholeContinuousMildSerrinReceipt_contact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    generatedWholeRestartPhysicalSeedWholeContinuousMildSerrinReceipt
        contact =
      generatedWholeRestartWholeContinuousMildSerrinReceipt
        (generatedWholeRestartCanonicalReplay contact) :=
  rfl

/-- The final source-generated whole receipt retains the quantitative
finite-observation modulus on every nonzero Fourier row. -/
theorem
    generatedWholeRestartWholeContinuousMildSerrinReceipt_fixedWave_increment_sq_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (first second : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    dist
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
          first wave)
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
          second wave) ^ 2 ≤
      dist first second *
        wholeRestartFiniteObservedHalfHolderEnergy replay {wave} := by
  let closure := generatedWholeRestartCriticalClosure replay
  change
    dist
        ((wholeRestartWholeMildAssembly closure).wholePath first wave)
        ((wholeRestartWholeMildAssembly closure).wholePath second wave) ^ 2 ≤
      dist first second *
        wholeRestartFiniteObservedHalfHolderEnergy replay {wave}
  exact
    wholeRestartWholeMildAssembly_fixedWave_increment_sq_le
      closure wave waveNonzero first second

/-- The generated next receipt retains the kinetic ledger of the exact
whole state from which its canonical replay started. -/
theorem generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticMass_ae_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      puncturedWholeVorticityKineticMass
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
            time) ≤
        puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) :=
  wholeRestartWholePath_kineticMass_ae_le
    (generatedWholeRestartCriticalClosure replay)

/-- The generated next receipt retains the source-owned coefficient ceiling
of the same exact canonical replay. -/
theorem generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      wholeVorticityEuclideanMass
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
            time) ≤
        wholeRestartCoefficientCeiling contact :=
  wholeRestartWholePath_coefficientMass_ae_le
    (generatedWholeRestartCriticalClosure replay)

/-- The generated receipt transports the exact finite Galerkin kinetic
ledger to the whole path: its physical kinetic mass plus the complete
unweighted vorticity payment accumulated before the same time is paid by
the exact restart state. -/
theorem generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_ae_le
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      puncturedWholeVorticityKineticMass
            ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
              time) +
          2 * nu.coeff *
            wholePrefixVorticityMass time
              (generatedWholeRestartWholeContinuousMildSerrinReceipt
                replay).stateLimit ≤
        puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) := by
  let closure := generatedWholeRestartCriticalClosure replay
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  have ledgerAE := criticalClosure_kineticDissipation_ae_le closure
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      nextReceipt.wholePath
  filter_upwards [ledgerAE, pathAE] with time ledgerLe pathEq
  have pathEqState :
      nextReceipt.wholePath time = nextReceipt.stateLimit time := by
    rw [← nextReceipt.wholePath_toLp_eq_stateLimit]
    exact pathEq.symm
  change
    puncturedWholeVorticityKineticMass (nextReceipt.stateLimit time) +
          2 * nu.coeff *
            wholePrefixVorticityMass time nextReceipt.stateLimit ≤
        puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) at ledgerLe
  rw [← pathEqState] at ledgerLe
  exact ledgerLe

/-- The generated whole path carries the internal half-critical exhaustion:
the actual source contact has already crossed the fixed threshold, or the
same positive-time endpoint pays the full whole-gradient dissipation. -/
theorem
    generatedWholeRestartWholeContinuousMildSerrinReceipt_halfCriticalAbsorption_disposition_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      0 < time.1 →
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2 <
            criticalEnstrophyLatticeConstant *
              wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) ∨
          wholeVorticityEuclideanMass
                ((generatedWholeRestartWholeContinuousMildSerrinReceipt
                  replay).wholePath time) +
              2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
                wholePrefixVorticityGradientMass time
                  (generatedWholeRestartWholeContinuousMildSerrinReceipt
                    replay).stateLimit ≤
            wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) := by
  let closure := generatedWholeRestartCriticalClosure replay
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  have dispositionAE :=
    criticalClosure_halfCriticalAbsorption_disposition_ae closure
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      nextReceipt.wholePath
  filter_upwards [dispositionAE, pathAE] with time disposition pathEq
  intro timePos
  rcases disposition timePos with crossed | payment
  · exact Or.inl crossed
  · right
    have pathEqState :
        nextReceipt.wholePath time = nextReceipt.stateLimit time := by
      rw [← nextReceipt.wholePath_toLp_eq_stateLimit]
      exact pathEq.symm
    change
      wholeVorticityEuclideanMass (nextReceipt.stateLimit time) +
            2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) nu *
              wholePrefixVorticityGradientMass time
                nextReceipt.stateLimit ≤
          wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) at payment
    rw [← pathEqState] at payment
    exact payment

/-- Actual quantized cells below one contact's physical raw ceiling.  Unlike
a bare `Fin level`, membership itself reads the source state's real-valued
mass; the `Fin (ceil ...)` presentation below is only its cardinal theorem. -/
def WholeRestartContactCellCarrierAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) : Type :=
  { cell : ℕ // (cell : ℝ) < wholeRestartRawCoefficientCeiling contact }

def WholeRestartContactCellCarrierAt.equivFin
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    WholeRestartContactCellCarrierAt contact ≃
      Fin (wholeRestartCoefficientLevel contact) where
  toFun := fun cell => ⟨cell.1, (Nat.lt_ceil).2 cell.2⟩
  invFun := fun cell => ⟨cell.1, (Nat.lt_ceil).1 cell.2⟩
  left_inv := fun cell => by cases cell; rfl
  right_inv := fun cell => by cases cell; rfl

noncomputable instance WholeRestartContactCellCarrierAt.instFintype
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    Fintype (WholeRestartContactCellCarrierAt contact) :=
  Fintype.ofEquiv (Fin (wholeRestartCoefficientLevel contact))
    (WholeRestartContactCellCarrierAt.equivFin contact).symm

@[simp] theorem WholeRestartContactCellCarrierAt.card
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    Fintype.card (WholeRestartContactCellCarrierAt contact) =
      wholeRestartCoefficientLevel contact := by
  rw [Fintype.card_congr
    (WholeRestartContactCellCarrierAt.equivFin contact)]
  exact Fintype.card_fin _

abbrev WholeRestartContactOnePaidCell := Fin 1

/-- Unary arithmetic history generated from the actual physical cell carrier.
The natural cardinal is only its final shadow. -/
def WholeRestartContactCellHistoryAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) : UnitHistory :=
  UnitHistory.generate (Fintype.card (WholeRestartContactCellCarrierAt contact))

/-- The paid unit is itself an actual one-cell history. -/
def WholeRestartContactOnePaidCellHistory : UnitHistory :=
  UnitHistory.generate (Fintype.card WholeRestartContactOnePaidCell)

@[simp] theorem WholeRestartContactCellHistoryAt_cardinalShadow
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    (contact : GeneratedPositiveWholeRestartContact receipt) :
    (WholeRestartContactCellHistoryAt contact).cardinalShadow =
      wholeRestartCoefficientLevel contact := by
  simp [WholeRestartContactCellHistoryAt]

@[simp] theorem WholeRestartContactOnePaidCellHistory_cardinalShadow :
    WholeRestartContactOnePaidCellHistory.cardinalShadow = 1 := by
  simp [WholeRestartContactOnePaidCellHistory,
    WholeRestartContactOnePaidCell]

/-- Arithmetic material of one physical restart edge.  The whole, retained
and paid histories are computed before normalization. -/
def wholeRestartRootArithmeticMaterialAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt
        replay)) :
    RootArithmeticMaterialAt where
  whole := WholeRestartContactCellHistoryAt nextContact
  left := WholeRestartContactCellHistoryAt contact
  right := WholeRestartContactOnePaidCellHistory

/-- Exact one-cell incidence between the two contacts of one native replay
edge.  No level equation is stored in this proposition. -/
def WholeRestartContactOneCellIncidenceAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)) : Prop :=
  ParallelIncidenceAt
    (WholeRestartContactCellCarrierAt nextContact)
    (WholeRestartContactCellCarrierAt contact)
    WholeRestartContactOnePaidCell

/-- Physical cell-debit row generated on the exact source replay and selected
target contact.  The constructor is private: source/target states and the
mass change are computed by the contact compiler, never supplied by a later
incidence or recurrence consumer. -/
structure GeneratedWholeRestartCellDebitAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)) : Type where
  private mk ::
  arithmeticMaterial : RootArithmeticMaterialAt
  sourcePhysicalState : ComplexVorticityHilbertState
  targetPhysicalState : ComplexVorticityHilbertState
  netEnstrophyDebit : ℝ
  arithmeticMaterial_eq :
    arithmeticMaterial = wholeRestartRootArithmeticMaterialAt nextContact
  sourcePhysicalState_eq :
    sourcePhysicalState = wholeRestartPhysicalState contact
  targetPhysicalState_eq :
    targetPhysicalState = nextContact.physicalState
  netEnstrophyDebit_eq :
    netEnstrophyDebit =
      wholeVorticityEuclideanMass targetPhysicalState -
        wholeVorticityEuclideanMass sourcePhysicalState

/-- Public semantic name: arithmetic histories and their real-valued NS
ledger are one source-generated material. -/
abbrev NativeRestartValuedArithmeticMaterialAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)) :=
  GeneratedWholeRestartCellDebitAt replay nextContact

private def generatedWholeRestartCellDebit
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)) :
    GeneratedWholeRestartCellDebitAt replay nextContact :=
  { sourcePhysicalState := wholeRestartPhysicalState contact
    arithmeticMaterial := wholeRestartRootArithmeticMaterialAt nextContact
    targetPhysicalState := nextContact.physicalState
    netEnstrophyDebit :=
      wholeVorticityEuclideanMass nextContact.physicalState -
        wholeVorticityEuclideanMass (wholeRestartPhysicalState contact)
    arithmeticMaterial_eq := rfl
    sourcePhysicalState_eq := rfl
    targetPhysicalState_eq := rfl
    netEnstrophyDebit_eq := rfl }

namespace GeneratedWholeRestartCellDebitAt

/-- Physical clock valuation of the same material occurrence. -/
def contactTime
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (_debit : GeneratedWholeRestartCellDebitAt replay nextContact) : ℝ :=
  nextContact.time.1

theorem contactTime_pos
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) :
    0 < debit.contactTime :=
  nextContact.time_pos

/-- The valued material's deterministic root normal form.  Its provenance is
the complete same-edge debit, so arithmetic and physical valuation cannot be
selected independently. -/
def parallelNormalForm
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) :
    ParallelIncidenceNormalFormAt debit debit.arithmeticMaterial :=
  normalizeParallel debit debit.arithmeticMaterial

/-- Exact one-cell arithmetic is the exact branch of the valued material,
before any cardinal or finite-carrier equivalence is read. -/
def ExactValuedOneCellAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) : Prop :=
  debit.arithmeticMaterial.whole =
    debit.arithmeticMaterial.left.parallel debit.arithmeticMaterial.right

/-- Typed residual generated by normalizing the same valued material. -/
abbrev GeneratedValuedResidualAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) :=
  GeneratedParallelResidualAt debit debit.arithmeticMaterial

def generatedResidualOfNotExact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact)
    (failed : ¬ ExactValuedOneCellAt debit) :
    GeneratedValuedResidualAt debit :=
  match debit.parallelNormalForm with
  | .exact _rooted exact => (failed exact).elim
  | .generatedResidual residual => residual

/-- Exact normal form reads out the old finite-carrier incidence.  This is a
compatibility theorem; it is not used to select the arithmetic branch. -/
theorem oneCellIncidenceOfExact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact)
    (exact : ExactValuedOneCellAt debit) :
    WholeRestartContactOneCellIncidenceAt replay nextContact := by
  have shadowEq := congrArg UnitHistory.cardinalShadow exact
  rw [debit.arithmeticMaterial_eq] at shadowEq
  have cardEq :
      Fintype.card (WholeRestartContactCellCarrierAt nextContact) =
        Fintype.card (WholeRestartContactCellCarrierAt contact) +
          Fintype.card WholeRestartContactOnePaidCell := by
    simpa [ExactValuedOneCellAt, wholeRestartRootArithmeticMaterialAt,
      WholeRestartContactCellHistoryAt,
      WholeRestartContactOnePaidCellHistory] using shadowEq
  exact ⟨Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sum] using cardEq)⟩

/-- The old physical carrier incidence conversely reads into the same root
normal form.  Kept only for compatibility adapters. -/
theorem exactOfOneCellIncidence
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact)
    (incidence : WholeRestartContactOneCellIncidenceAt replay nextContact) :
    ExactValuedOneCellAt debit := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  rw [debit.arithmeticMaterial_eq]
  have cardReadout := card_eq_add_of_parallel
    (WholeRestartContactCellCarrierAt nextContact)
    (WholeRestartContactCellCarrierAt contact)
    WholeRestartContactOnePaidCell incidence
  simpa [ExactValuedOneCellAt, wholeRestartRootArithmeticMaterialAt,
    WholeRestartContactCellHistoryAt,
    WholeRestartContactOnePaidCellHistory] using cardReadout

/-- `+1` is only the cardinal shadow of the exact root normal form. -/
theorem coefficientLevel_eq_add_one_of_exact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact)
    (exact : ExactValuedOneCellAt debit) :
    wholeRestartCoefficientLevel nextContact =
      wholeRestartCoefficientLevel contact + 1 := by
  have shadowEq := congrArg UnitHistory.cardinalShadow exact
  rw [debit.arithmeticMaterial_eq] at shadowEq
  simpa only [wholeRestartRootArithmeticMaterialAt,
    UnitHistory.cardinalShadow_parallel,
    WholeRestartContactCellHistoryAt_cardinalShadow,
    WholeRestartContactOnePaidCellHistory_cardinalShadow] using shadowEq

theorem exact_of_coefficientLevel_eq_add_one
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact)
    (levelEq : wholeRestartCoefficientLevel nextContact =
      wholeRestartCoefficientLevel contact + 1) :
    debit.ExactValuedOneCellAt := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  rw [debit.arithmeticMaterial_eq]
  simpa only [wholeRestartRootArithmeticMaterialAt,
    UnitHistory.cardinalShadow_parallel,
    WholeRestartContactCellHistoryAt_cardinalShadow,
    WholeRestartContactOnePaidCellHistory_cardinalShadow] using levelEq

theorem source_eq_receipt_initial
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) :
    (generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath
        ⟨0, ⟨le_rfl,
          (generatedWholeRestartWholeContinuousMildSerrinReceipt replay
            ).requestedTimePos.le⟩⟩ =
      debit.sourcePhysicalState :=
  (generatedWholeRestartWholeContinuousMildSerrinReceipt replay
    ).wholePath_initial.trans debit.sourcePhysicalState_eq.symm

theorem target_eq_receipt_terminal
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) :
    nextContact.prefixReceipt.wholePath
        ⟨nextContact.time.1, ⟨nextContact.time_pos.le, le_rfl⟩⟩ =
      debit.targetPhysicalState :=
  nextContact.prefixReceipt_terminal.trans debit.targetPhysicalState_eq.symm

/-- Exact one-cell incidence strictly increases the physical coefficient
mass on the same emitted debit row. -/
theorem netEnstrophyDebit_pos_of_incidence
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact)
    (incidence : WholeRestartContactOneCellIncidenceAt replay nextContact) :
    0 < debit.netEnstrophyDebit := by
  have cardReadout := card_eq_add_of_parallel
    (WholeRestartContactCellCarrierAt nextContact)
    (WholeRestartContactCellCarrierAt contact)
    WholeRestartContactOnePaidCell incidence
  have levelEq :
      wholeRestartCoefficientLevel nextContact =
        wholeRestartCoefficientLevel contact + 1 := by
    simpa only [WholeRestartContactCellCarrierAt.card,
      WholeRestartContactOnePaidCell, Fintype.card_fin] using cardReadout
  have sourceRawLe := wholeRestartRawCoefficientCeiling_le contact
  rw [wholeRestartRawCoefficientCeiling_eq] at sourceRawLe
  change
    wholeVorticityEuclideanMass contact.physicalState + 1 ≤
      (wholeRestartCoefficientLevel contact : ℝ) at sourceRawLe
  have sourceLevel_lt_targetLevel :
      wholeRestartCoefficientLevel contact <
        wholeRestartCoefficientLevel nextContact := by omega
  have sourceLevel_lt_targetRaw :
      (wholeRestartCoefficientLevel contact : ℝ) <
        wholeRestartRawCoefficientCeiling nextContact :=
    (Nat.lt_ceil).1 sourceLevel_lt_targetLevel
  rw [wholeRestartRawCoefficientCeiling_eq] at sourceLevel_lt_targetRaw
  change
    (wholeRestartCoefficientLevel contact : ℝ) <
      wholeVorticityEuclideanMass nextContact.physicalState + 1
    at sourceLevel_lt_targetRaw
  have sourceMass_lt_targetMass :
      wholeVorticityEuclideanMass contact.physicalState <
        wholeVorticityEuclideanMass nextContact.physicalState := by
    linarith
  rw [debit.netEnstrophyDebit_eq,
    debit.sourcePhysicalState_eq, debit.targetPhysicalState_eq]
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
  exact sub_pos.mpr sourceMass_lt_targetMass

end GeneratedWholeRestartCellDebitAt

/-! ## Source-first arithmetic event on the admissible time fibre -/

private theorem continuous_le_on_lateCommonTimes_of_ae_le
    {requestedTime ceiling : ℝ}
    (requestedTimePos : 0 < requestedTime)
    (value : Icc (0 : ℝ) requestedTime → ℝ)
    (valueContinuous : Continuous value)
    (valueAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime).restrict
          (lateCommonTimes requestedTime),
        value time ≤ ceiling) :
    ∀ time ∈ lateCommonTimes requestedTime, value time ≤ ceiling := by
  let extended : ℝ → ℝ := fun time =>
    value (projIcc 0 requestedTime requestedTimePos.le time)
  let clipped : ℝ → ℝ := fun time => min (extended time) ceiling
  have extendedContinuous : Continuous extended := by
    dsimp only [extended]
    exact valueContinuous.comp continuous_projIcc
  have clippedContinuous : Continuous clipped := by
    dsimp only [clipped]
    fun_prop
  rw [commonTimeMeasure_eq_comap_volume] at valueAE
  have valueImpAE :
      ∀ᵐ time ∂Measure.comap
          (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ) volume,
        time ∈ lateCommonTimes requestedTime → value time ≤ ceiling :=
    ae_imp_of_ae_restrict valueAE
  have extendedImpAE :
      ∀ᵐ time ∂volume.restrict (Icc (0 : ℝ) requestedTime),
        time ∈ Ioc (requestedTime / 2) requestedTime →
          extended time ≤ ceiling := by
    rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [valueImpAE] with time valueImp
    intro timeMem
    have timeLate : time ∈ lateCommonTimes requestedTime := by
      exact timeMem.1
    have valueLe := valueImp timeLate
    simpa only [extended,
      projIcc_of_mem requestedTimePos.le time.2] using valueLe
  have lateSubset :
      Ioc (requestedTime / 2) requestedTime ⊆
        Icc (0 : ℝ) requestedTime := by
    intro time timeMem
    exact ⟨(by linarith [timeMem.1, requestedTimePos]), timeMem.2⟩
  have extendedImpLateAE :
      ∀ᵐ time ∂volume.restrict (Ioc (requestedTime / 2) requestedTime),
        time ∈ Ioc (requestedTime / 2) requestedTime →
          extended time ≤ ceiling :=
    ae_restrict_of_ae_restrict_of_subset lateSubset extendedImpAE
  have extendedLateAE :
      ∀ᵐ time ∂volume.restrict (Ioc (requestedTime / 2) requestedTime),
        extended time ≤ ceiling := by
    filter_upwards [extendedImpLateAE,
      ae_restrict_mem measurableSet_Ioc] with time valueImp timeMem
    exact valueImp timeMem
  have extendedEqClippedAE :
      extended =ᵐ[volume.restrict (Ioc (requestedTime / 2) requestedTime)]
        clipped :=
    extendedLateAE.mono fun time valueLe => by
      dsimp only [clipped]
      rw [min_eq_left valueLe]
  have denseInterior :
      Ioc (requestedTime / 2) requestedTime ⊆
        closure (interior (Ioc (requestedTime / 2) requestedTime)) := by
    rw [interior_Ioc,
      closure_Ioo (ne_of_lt (by linarith [requestedTimePos]))]
    exact Ioc_subset_Icc_self
  have extendedEqClipped :
      EqOn extended clipped (Ioc (requestedTime / 2) requestedTime) :=
    MeasureTheory.Measure.eqOn_of_ae_eq extendedEqClippedAE
      extendedContinuous.continuousOn clippedContinuous.continuousOn
      denseInterior
  intro time timeLate
  have realTimeLate :
      time.1 ∈ Ioc (requestedTime / 2) requestedTime :=
    ⟨timeLate, time.2.2⟩
  have pointEq := extendedEqClipped realTimeLate
  dsimp only [extended, clipped] at pointEq
  rw [projIcc_of_mem requestedTimePos.le time.2] at pointEq
  rw [pointEq]
  exact min_le_right _ _

private theorem continuous_wholeVorticityEuclideanMass_for_restart :
    Continuous wholeVorticityEuclideanMass := by
  have functionalEq :
      wholeVorticityEuclideanMass =
        fun state : ComplexVorticityHilbertState =>
          ∑ coordinate : Coordinate,
            ‖wholeStateCoordinateSliceCLM coordinate state‖ ^ 2 := by
    funext state
    exact wholeVorticityEuclideanMass_eq_coordinateSlices state
  rw [functionalEq]
  fun_prop

/-- Complete coefficient-mass debit of the fixed replay terminal.  This is
computed before any good-time representative is selected. -/
def generatedWholeRestartTerminalNetEnstrophyDebit
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) : ℝ :=
  wholeVorticityEuclideanMass
      ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
        ).wholePath
          ⟨wholeRestartDuration contact,
            ⟨(wholeRestartDuration_pos contact).le, le_rfl⟩⟩) -
    wholeVorticityEuclideanMass (wholeRestartPhysicalState contact)

/-- One admissible late time of the generated replay, carrying every
physical row previously used by the contact chooser. -/
structure GeneratedWholeRestartGoodContactTimeAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) : Prop where
  time_pos : 0 < time.1
  time_half_lt : wholeRestartDuration contact / 2 < time.1
  gradient_summable :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
            ).wholePath time wave)
  transverse : WholeStateTransverse
    ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
      ).wholePath time)
  reality : FiniteStateFourierReality
    ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
      ).wholePath time)
  kineticMass_le :
    puncturedWholeVorticityKineticMass
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
          ).wholePath time) ≤
      puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact)
  coefficientMass_le :
    wholeVorticityEuclideanMass
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
          ).wholePath time) ≤
      wholeRestartCoefficientCeiling contact
  kineticDissipation_le :
    puncturedWholeVorticityKineticMass
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
            ).wholePath time) +
        2 * ν.coeff *
          wholePrefixVorticityMass time
            (generatedWholeRestartWholeContinuousMildSerrinReceipt
              replay).stateLimit ≤
      puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact)
  halfCriticalDisposition :
    (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) ∨
      wholeVorticityEuclideanMass
            ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
              ).wholePath time) +
          2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
            wholePrefixVorticityGradientMass time
              (generatedWholeRestartWholeContinuousMildSerrinReceipt
                replay).stateLimit ≤
        wholeVorticityEuclideanMass (wholeRestartPhysicalState contact)

/-- A good-time occurrence packages the actual time with its source proof. -/
structure GeneratedWholeRestartGoodContactAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) : Type where
  time : Icc (0 : ℝ) (wholeRestartDuration contact)
  good : GeneratedWholeRestartGoodContactTimeAt replay time

def GeneratedWholeRestartGoodContactAt.contact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (candidate : GeneratedWholeRestartGoodContactAt replay) :
    GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay) where
  time := candidate.time
  time_pos := candidate.good.time_pos
  time_half_lt := candidate.good.time_half_lt
  gradient_summable := candidate.good.gradient_summable
  transverse := candidate.good.transverse
  reality := candidate.good.reality

/-- Exact arithmetic normal form is tested on the valued material of a fully
admissible good-time occurrence, before any endpoint is selected. -/
def GeneratedWholeRestartGoodContactAt.OneCell
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (candidate : GeneratedWholeRestartGoodContactAt replay) : Prop :=
  (generatedWholeRestartCellDebit replay candidate.contact).ExactValuedOneCellAt

theorem GeneratedWholeRestartGoodContactAt.coefficientLevel_eq_add_one_of_oneCell
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (candidate : GeneratedWholeRestartGoodContactAt replay)
    (exact : candidate.OneCell) :
    wholeRestartCoefficientLevel candidate.contact =
      wholeRestartCoefficientLevel contact + 1 :=
  (generatedWholeRestartCellDebit replay candidate.contact
    ).coefficientLevel_eq_add_one_of_exact exact

theorem GeneratedWholeRestartGoodContactAt.oneCell_of_coefficientLevel_eq_add_one
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (candidate : GeneratedWholeRestartGoodContactAt replay)
    (levelEq : wholeRestartCoefficientLevel candidate.contact =
      wholeRestartCoefficientLevel contact + 1) :
    candidate.OneCell :=
  (generatedWholeRestartCellDebit replay candidate.contact
    ).exact_of_coefficientLevel_eq_add_one levelEq

/-- On one admissible good-time occurrence, the arithmetic incidence is
exactly the physical path crossing the current contact's upper cell wall.
The coefficient ceiling already carried by `good` rules out upward skips. -/
theorem GeneratedWholeRestartGoodContactAt.oneCell_iff_mass_crosses_sourceCellWall
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (candidate : GeneratedWholeRestartGoodContactAt replay) :
    candidate.OneCell ↔
      (wholeRestartCoefficientLevel contact : ℝ) - 1 <
        wholeVorticityEuclideanMass candidate.contact.physicalState := by
  constructor
  · intro exact
    have levelEq :
        wholeRestartCoefficientLevel candidate.contact =
          wholeRestartCoefficientLevel contact + 1 := by
      exact
        (generatedWholeRestartCellDebit replay candidate.contact
          ).coefficientLevel_eq_add_one_of_exact exact
    have sourceLevel_lt_targetLevel :
        wholeRestartCoefficientLevel contact <
          wholeRestartCoefficientLevel candidate.contact := by omega
    have sourceLevel_lt_targetRaw :
        (wholeRestartCoefficientLevel contact : ℝ) <
          wholeRestartRawCoefficientCeiling candidate.contact :=
      (Nat.lt_ceil).1 sourceLevel_lt_targetLevel
    rw [wholeRestartRawCoefficientCeiling_eq] at sourceLevel_lt_targetRaw
    change
      (wholeRestartCoefficientLevel contact : ℝ) <
        wholeVorticityEuclideanMass candidate.contact.physicalState + 1
      at sourceLevel_lt_targetRaw
    linarith
  · intro crossed
    have coefficientMassLe :
        wholeVorticityEuclideanMass candidate.contact.physicalState ≤
          wholeRestartCoefficientCeiling contact := by
      exact candidate.good.coefficientMass_le
    have rawLe :
        wholeRestartRawCoefficientCeiling candidate.contact ≤
          ((wholeRestartCoefficientLevel contact + 1 : ℕ) : ℝ) := by
      rw [wholeRestartRawCoefficientCeiling_eq]
      calc
        wholeVorticityEuclideanMass candidate.contact.physicalState + 1 ≤
            wholeRestartCoefficientCeiling contact + 1 := by
          linarith
        _ = ((wholeRestartCoefficientLevel contact + 1 : ℕ) : ℝ) := by
          simp [wholeRestartCoefficientCeiling]
    have targetLevel_le_sourceSucc :
        wholeRestartCoefficientLevel candidate.contact ≤
          wholeRestartCoefficientLevel contact + 1 := Nat.ceil_le.mpr rawLe
    have sourceLevel_lt_targetRaw :
        (wholeRestartCoefficientLevel contact : ℝ) <
          wholeRestartRawCoefficientCeiling candidate.contact := by
      rw [wholeRestartRawCoefficientCeiling_eq]
      change
        (wholeRestartCoefficientLevel contact : ℝ) <
          wholeVorticityEuclideanMass candidate.contact.physicalState + 1
      linarith
    have sourceLevel_lt_targetLevel :
        wholeRestartCoefficientLevel contact <
          wholeRestartCoefficientLevel candidate.contact :=
      (Nat.lt_ceil).2 sourceLevel_lt_targetRaw
    have levelEq :
        wholeRestartCoefficientLevel candidate.contact =
          wholeRestartCoefficientLevel contact + 1 := by omega
    change
      (generatedWholeRestartCellDebit replay candidate.contact
        ).ExactValuedOneCellAt
    apply UnitHistory.eq_of_cardinalShadow_eq
    rw [(generatedWholeRestartCellDebit replay
      candidate.contact).arithmeticMaterial_eq]
    simpa only [wholeRestartRootArithmeticMaterialAt,
      UnitHistory.cardinalShadow_parallel,
      WholeRestartContactCellHistoryAt_cardinalShadow,
      WholeRestartContactOnePaidCellHistory_cardinalShadow] using levelEq

/-- Source-owned persistent branch.  When the fixed terminal pays positive
coefficient mass, the selected admissible representative retains more than
half of that debit.  Otherwise the same branch records the exact nonpositive
terminal disposition. -/
structure GeneratedWholeRestartPersistentSettlementAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) : Type where
  private mk ::
  candidate : GeneratedWholeRestartGoodContactAt replay
  noCrossing : ∀ later : GeneratedWholeRestartGoodContactAt replay,
    (generatedWholeRestartCellDebit replay
      later.contact).GeneratedValuedResidualAt
  retainedTerminalDebit :
    (0 < generatedWholeRestartTerminalNetEnstrophyDebit replay ∧
      generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
        wholeVorticityEuclideanMass candidate.contact.physicalState -
          wholeVorticityEuclideanMass
            (wholeRestartPhysicalState contact)) ∨
      generatedWholeRestartTerminalNetEnstrophyDebit replay ≤ 0

/-- Exact failure of the one-cell incidence on the same debit occurrence. -/
structure GeneratedWholeRestartRetainedCellResidualAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)) : Type where
  private mk ::
  debit : GeneratedWholeRestartCellDebitAt replay nextContact
  normalResidual : debit.GeneratedValuedResidualAt
  noGoodTimeResidual :
    ∀ candidate : GeneratedWholeRestartGoodContactAt replay,
      (generatedWholeRestartCellDebit replay
        candidate.contact).GeneratedValuedResidualAt
  retainedTerminalDebit :
    (0 < generatedWholeRestartTerminalNetEnstrophyDebit replay ∧
      generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
        debit.netEnstrophyDebit) ∨
      generatedWholeRestartTerminalNetEnstrophyDebit replay ≤ 0
  targetLevel_le_sourceLevel :
    wholeRestartCoefficientLevel nextContact ≤
      wholeRestartCoefficientLevel contact
  targetMass_le_sourceCellWall :
    wholeVorticityEuclideanMass nextContact.physicalState ≤
      (wholeRestartCoefficientLevel contact : ℝ) - 1
  cellDeficit : ℝ
  cellDeficit_eq :
    cellDeficit =
      (wholeRestartCoefficientLevel contact : ℝ) - 1 -
        wholeVorticityEuclideanMass nextContact.physicalState
  cellDeficit_nonneg : 0 ≤ cellDeficit

namespace GeneratedWholeRestartRetainedCellResidualAt

/-- A persistent arithmetic event is a uniform physical wall bound over the
entire admissible good-time fibre, not failure at one opaque endpoint. -/
theorem goodContact_mass_le_sourceCellWall
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (residual : GeneratedWholeRestartRetainedCellResidualAt nextContact)
    (candidate : GeneratedWholeRestartGoodContactAt replay) :
    wholeVorticityEuclideanMass candidate.contact.physicalState ≤
      (wholeRestartCoefficientLevel contact : ℝ) - 1 := by
  apply le_of_not_gt
  intro crossed
  exact (residual.noGoodTimeResidual candidate).mismatch
    ((candidate.oneCell_iff_mass_crosses_sourceCellWall).2 crossed)

/-- Positive fixed-terminal mass payment survives the persistent selector
with a strict factor-two reserve on the actual emitted debit. -/
theorem netEnstrophyDebit_gt_half_terminal
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (residual : GeneratedWholeRestartRetainedCellResidualAt nextContact)
    (terminalPositive :
      0 < generatedWholeRestartTerminalNetEnstrophyDebit replay) :
    generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
      residual.debit.netEnstrophyDebit := by
  rcases residual.retainedTerminalDebit with retained | nonpositive
  · exact retained.2
  · exact (not_lt_of_ge nonpositive terminalPositive).elim

/-- Exact commuting row between the retained cell deficit and the physical
mass debit emitted on the same contact edge. -/
theorem cellDeficit_eq_sourceGap_sub_netEnstrophyDebit
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (residual : GeneratedWholeRestartRetainedCellResidualAt nextContact) :
    residual.cellDeficit =
      ((wholeRestartCoefficientLevel contact : ℝ) - 1 -
          wholeVorticityEuclideanMass residual.debit.sourcePhysicalState) -
        residual.debit.netEnstrophyDebit := by
  rw [residual.cellDeficit_eq, residual.debit.netEnstrophyDebit_eq,
    residual.debit.sourcePhysicalState_eq,
    residual.debit.targetPhysicalState_eq]
  ring

end GeneratedWholeRestartRetainedCellResidualAt

/-- Total evolution-sensitive cell effect generated by one exact contact
edge.  There is no `unknown` branch and no caller-supplied selector. -/
inductive GeneratedWholeRestartCellEffectAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)) : Type
  | oneCell
      (debit : GeneratedWholeRestartCellDebitAt replay nextContact)
      (exact : debit.ExactValuedOneCellAt)
  | retainedResidual
      (residual : GeneratedWholeRestartRetainedCellResidualAt nextContact)

/-- The physical debit is present in both exhaustive emitter branches. -/
def GeneratedWholeRestartCellEffectAt.debit
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (effect : GeneratedWholeRestartCellEffectAt nextContact) :
    GeneratedWholeRestartCellDebitAt replay nextContact :=
  match effect with
  | .oneCell debit _incidence => debit
  | .retainedResidual residual => residual.debit

/-- Source-level arithmetic event.  The crossing branch chooses only from
the good-time incidence fibre.  The persistent branch carries a proof that
the entire admissible fibre has no one-cell incidence. -/
inductive GeneratedWholeRestartArithmeticEventAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) : Type
  | crossing
      (candidate : GeneratedWholeRestartGoodContactAt replay)
      (incidence : candidate.OneCell)
      (retainedTerminalDebit :
        (0 < generatedWholeRestartTerminalNetEnstrophyDebit replay ∧
          generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
            wholeVorticityEuclideanMass candidate.contact.physicalState -
              wholeVorticityEuclideanMass
                (wholeRestartPhysicalState contact)) ∨
          generatedWholeRestartTerminalNetEnstrophyDebit replay ≤ 0)
  | persistent
      (settlement : GeneratedWholeRestartPersistentSettlementAt replay)

def GeneratedWholeRestartArithmeticEventAt.candidate
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact} :
    GeneratedWholeRestartArithmeticEventAt replay →
      GeneratedWholeRestartGoodContactAt replay
  | .crossing candidate _incidence _retainedTerminalDebit => candidate
  | .persistent settlement => settlement.candidate

abbrev GeneratedWholeRestartArithmeticEventAt.nextContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (event : GeneratedWholeRestartArithmeticEventAt replay) :=
  event.candidate.contact

private def generatedWholeRestartRetainedCellResidual
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (settlement : GeneratedWholeRestartPersistentSettlementAt replay) :
    GeneratedWholeRestartRetainedCellResidualAt
      settlement.candidate.contact := by
  let candidate := settlement.candidate
  let noCrossing := settlement.noCrossing
  let nextContact := candidate.contact
  let debit := generatedWholeRestartCellDebit replay nextContact
  let normalResidual := noCrossing candidate
  have notExact : ¬ candidate.OneCell := normalResidual.mismatch
  have coefficientMass_le :
      wholeVorticityEuclideanMass nextContact.physicalState ≤
        wholeRestartCoefficientCeiling contact :=
    candidate.good.coefficientMass_le
  have rawLe :
      wholeRestartRawCoefficientCeiling nextContact ≤
        ((wholeRestartCoefficientLevel contact + 1 : ℕ) : ℝ) := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    calc
      wholeVorticityEuclideanMass nextContact.physicalState + 1 ≤
          wholeRestartCoefficientCeiling contact + 1 := by linarith
      _ = ((wholeRestartCoefficientLevel contact + 1 : ℕ) : ℝ) := by
        simp [wholeRestartCoefficientCeiling]
  have targetLevel_le_succ :
      wholeRestartCoefficientLevel nextContact ≤
        wholeRestartCoefficientLevel contact + 1 := Nat.ceil_le.mpr rawLe
  have targetLevel_ne_succ :
      wholeRestartCoefficientLevel nextContact ≠
        wholeRestartCoefficientLevel contact + 1 := by
    intro levelEq
    apply notExact
    change debit.ExactValuedOneCellAt
    apply UnitHistory.eq_of_cardinalShadow_eq
    rw [debit.arithmeticMaterial_eq]
    simpa only [wholeRestartRootArithmeticMaterialAt,
      UnitHistory.cardinalShadow_parallel,
      WholeRestartContactCellHistoryAt_cardinalShadow,
      WholeRestartContactOnePaidCellHistory_cardinalShadow] using levelEq
  have targetLevel_le_source :
      wholeRestartCoefficientLevel nextContact ≤
        wholeRestartCoefficientLevel contact := by omega
  have targetRawLeLevel := wholeRestartRawCoefficientCeiling_le nextContact
  have targetMass_le_sourceCellWall :
      wholeVorticityEuclideanMass nextContact.physicalState ≤
        (wholeRestartCoefficientLevel contact : ℝ) - 1 := by
    have targetLevelCast_le :
        (wholeRestartCoefficientLevel nextContact : ℝ) ≤
          (wholeRestartCoefficientLevel contact : ℝ) := by
      exact_mod_cast targetLevel_le_source
    change
      wholeVorticityEuclideanMass nextContact.physicalState + 1 ≤
        (wholeRestartCoefficientLevel nextContact : ℝ) at targetRawLeLevel
    linarith
  let cellDeficit :=
    (wholeRestartCoefficientLevel contact : ℝ) - 1 -
      wholeVorticityEuclideanMass nextContact.physicalState
  have retainedTerminalDebit :
      (0 < generatedWholeRestartTerminalNetEnstrophyDebit replay ∧
        generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
          debit.netEnstrophyDebit) ∨
        generatedWholeRestartTerminalNetEnstrophyDebit replay ≤ 0 := by
    rcases settlement.retainedTerminalDebit with paid | nonpositive
    · left
      refine ⟨paid.1, ?_⟩
      rw [debit.netEnstrophyDebit_eq,
        debit.sourcePhysicalState_eq, debit.targetPhysicalState_eq]
      exact paid.2
    · exact Or.inr nonpositive
  exact
    { debit := debit
      normalResidual := normalResidual
      noGoodTimeResidual := noCrossing
      retainedTerminalDebit := retainedTerminalDebit
      targetLevel_le_sourceLevel := targetLevel_le_source
      targetMass_le_sourceCellWall := targetMass_le_sourceCellWall
      cellDeficit := cellDeficit
      cellDeficit_eq := rfl
      cellDeficit_nonneg := sub_nonneg.mpr targetMass_le_sourceCellWall }

def GeneratedWholeRestartArithmeticEventAt.cellEffect
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (event : GeneratedWholeRestartArithmeticEventAt replay) :
    GeneratedWholeRestartCellEffectAt event.nextContact :=
  match event with
  | .crossing candidate incidence _retainedTerminalDebit =>
      .oneCell (generatedWholeRestartCellDebit replay candidate.contact)
        incidence
  | .persistent settlement =>
      .retainedResidual
        (generatedWholeRestartRetainedCellResidual
          replay settlement)

/-- A source-selected contact on the generated next receipt together with
all physical ledgers and the total cell effect produced by the same
finite-to-whole limit. -/
structure GeneratedWholeRestartKineticContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) where
  private mk ::
  arithmeticEvent : GeneratedWholeRestartArithmeticEventAt replay
  goodFibreAE :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)).restrict
        (lateCommonTimes (wholeRestartDuration contact)),
      GeneratedWholeRestartGoodContactTimeAt replay time

abbrev GeneratedWholeRestartKineticContact.nextContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay) :=
  generated.arithmeticEvent.nextContact

theorem GeneratedWholeRestartKineticContact.kineticMass_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay) :
    puncturedWholeVorticityKineticMass generated.nextContact.physicalState ≤
      puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) :=
  generated.arithmeticEvent.candidate.good.kineticMass_le

theorem GeneratedWholeRestartKineticContact.coefficientMass_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay) :
    wholeVorticityEuclideanMass generated.nextContact.physicalState ≤
      wholeRestartCoefficientCeiling contact :=
  generated.arithmeticEvent.candidate.good.coefficientMass_le

theorem GeneratedWholeRestartKineticContact.kineticDissipation_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay) :
    puncturedWholeVorticityKineticMass generated.nextContact.physicalState +
        2 * ν.coeff *
          wholePrefixVorticityMass generated.nextContact.time
            (generatedWholeRestartWholeContinuousMildSerrinReceipt
              replay).stateLimit ≤
      puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) :=
  generated.arithmeticEvent.candidate.good.kineticDissipation_le

theorem GeneratedWholeRestartKineticContact.halfCriticalDisposition
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay) :
    (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) ∨
      wholeVorticityEuclideanMass generated.nextContact.physicalState +
          2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
            wholePrefixVorticityGradientMass generated.nextContact.time
              (generatedWholeRestartWholeContinuousMildSerrinReceipt
                replay).stateLimit ≤
        wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) :=
  generated.arithmeticEvent.candidate.good.halfCriticalDisposition

abbrev GeneratedWholeRestartKineticContact.cellEffect
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay) :=
  generated.arithmeticEvent.cellEffect

/-- Both arithmetic branches select their representative inside the same
factor-two terminal-payment fibre.  Thus the emitted contact, rather than a
separate witness, retains more than half of every positive fixed-terminal
debit. -/
theorem GeneratedWholeRestartKineticContact.cellEffect_debit_gt_half_terminal_of_terminalDebit_pos
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (terminalPositive :
      0 < generatedWholeRestartTerminalNetEnstrophyDebit replay) :
    generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
      generated.cellEffect.debit.netEnstrophyDebit := by
  rcases generated with ⟨event, _goodFibreAE⟩
  cases event with
  | crossing candidate _incidence retainedTerminalDebit =>
      rcases retainedTerminalDebit with paid | nonpositive
      · change generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
          (generatedWholeRestartCellDebit replay
            candidate.contact).netEnstrophyDebit
        rw [(generatedWholeRestartCellDebit replay
          candidate.contact).netEnstrophyDebit_eq,
          (generatedWholeRestartCellDebit replay
            candidate.contact).sourcePhysicalState_eq,
          (generatedWholeRestartCellDebit replay
            candidate.contact).targetPhysicalState_eq]
        exact paid.2
      · exact (not_lt_of_ge nonpositive terminalPositive).elim
  | persistent settlement =>
      let residual :=
        generatedWholeRestartRetainedCellResidual replay settlement
      exact residual.netEnstrophyDebit_gt_half_terminal terminalPositive

/-- Positive complete terminal mass payment always produces a strictly
positive debit on the actual emitted contact. -/
theorem GeneratedWholeRestartKineticContact.cellEffect_debit_pos_of_terminalDebit_pos
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (terminalPositive :
      0 < generatedWholeRestartTerminalNetEnstrophyDebit replay) :
    0 < generated.cellEffect.debit.netEnstrophyDebit :=
  (half_pos terminalPositive).trans
    (generated.cellEffect_debit_gt_half_terminal_of_terminalDebit_pos
      terminalPositive)

/-- Exact hybrid progress generated by a positive fixed terminal debit:
the emitter either crosses one whole coefficient cell, or stays at the same
level while retaining more than half of that terminal mass payment. -/
theorem GeneratedWholeRestartKineticContact.levelAdvance_or_retainedPayment_of_terminalDebit_pos
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (terminalPositive :
      0 < generatedWholeRestartTerminalNetEnstrophyDebit replay) :
    wholeRestartCoefficientLevel generated.nextContact =
        wholeRestartCoefficientLevel contact + 1 ∨
      (wholeRestartCoefficientLevel generated.nextContact =
          wholeRestartCoefficientLevel contact ∧
        generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
          generated.cellEffect.debit.netEnstrophyDebit) := by
  rcases generated with ⟨event, _goodFibreAE⟩
  cases event with
  | crossing candidate incidence _retainedTerminalDebit =>
      left
      change wholeRestartCoefficientLevel candidate.contact =
        wholeRestartCoefficientLevel contact + 1
      exact (generatedWholeRestartCellDebit replay candidate.contact
        ).coefficientLevel_eq_add_one_of_exact incidence
  | persistent settlement =>
      right
      let residual :=
        generatedWholeRestartRetainedCellResidual replay settlement
      have retained :
          generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
            residual.debit.netEnstrophyDebit :=
        residual.netEnstrophyDebit_gt_half_terminal terminalPositive
      have debitPos : 0 < residual.debit.netEnstrophyDebit :=
        (half_pos terminalPositive).trans retained
      have sourceMass_lt_targetMass :
          wholeVorticityEuclideanMass
                (wholeRestartPhysicalState contact) <
            wholeVorticityEuclideanMass
              settlement.candidate.contact.physicalState := by
        rw [residual.debit.netEnstrophyDebit_eq,
          residual.debit.sourcePhysicalState_eq,
          residual.debit.targetPhysicalState_eq] at debitPos
        exact sub_pos.mp debitPos
      simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
        at sourceMass_lt_targetMass
      have sourceRaw_le_targetRaw :
          wholeRestartRawCoefficientCeiling contact ≤
            wholeRestartRawCoefficientCeiling
              settlement.candidate.contact := by
        rw [wholeRestartRawCoefficientCeiling_eq,
          wholeRestartRawCoefficientCeiling_eq]
        change
          wholeVorticityEuclideanMass contact.physicalState + 1 ≤
            wholeVorticityEuclideanMass
              settlement.candidate.contact.physicalState + 1
        gcongr
        exact sourceMass_lt_targetMass.le
      have sourceLevel_le_targetLevel :
          wholeRestartCoefficientLevel contact ≤
            wholeRestartCoefficientLevel
              settlement.candidate.contact :=
        Nat.ceil_mono sourceRaw_le_targetRaw
      change
        (wholeRestartCoefficientLevel settlement.candidate.contact =
            wholeRestartCoefficientLevel contact ∧
          generatedWholeRestartTerminalNetEnstrophyDebit replay / 2 <
            residual.debit.netEnstrophyDebit)
      exact
        ⟨le_antisymm residual.targetLevel_le_sourceLevel
            sourceLevel_le_targetLevel,
          retained⟩

/-- If the emitted event is persistent, its full-fibre certificate and the
source-generated conull good-time row yield an almost-everywhere physical
wall bound on the entire late interval. -/
theorem GeneratedWholeRestartKineticContact.goodFibre_mass_le_sourceCellWall_ae_of_retainedResidual
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (residual : GeneratedWholeRestartRetainedCellResidualAt
      generated.nextContact)
    (_effectEq : generated.cellEffect = .retainedResidual residual) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)).restrict
        (lateCommonTimes (wholeRestartDuration contact)),
      wholeVorticityEuclideanMass
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
            ).wholePath time) ≤
        (wholeRestartCoefficientLevel contact : ℝ) - 1 := by
  filter_upwards [generated.goodFibreAE] with time good
  exact residual.goodContact_mass_le_sourceCellWall ⟨time, good⟩

/-- Continuity removes the conull presentation: persistent means every
actual time in the late half of this exact receipt stays below the source
cell wall. -/
theorem GeneratedWholeRestartKineticContact.latePath_mass_le_sourceCellWall_of_retainedResidual
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (residual : GeneratedWholeRestartRetainedCellResidualAt
      generated.nextContact)
    (effectEq : generated.cellEffect = .retainedResidual residual)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact))
    (timeLate : time ∈ lateCommonTimes (wholeRestartDuration contact)) :
    wholeVorticityEuclideanMass
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
            ).wholePath time) ≤
        (wholeRestartCoefficientLevel contact : ℝ) - 1 := by
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  apply continuous_le_on_lateCommonTimes_of_ae_le
    (wholeRestartDuration_pos contact)
    (fun actual => wholeVorticityEuclideanMass
      (nextReceipt.wholePath actual))
  · have massContinuous : Continuous wholeVorticityEuclideanMass := by
      have functionalEq :
          wholeVorticityEuclideanMass =
            fun state : ComplexVorticityHilbertState =>
              ∑ coordinate : Coordinate,
                ‖wholeStateCoordinateSliceCLM coordinate state‖ ^ 2 := by
        funext state
        exact wholeVorticityEuclideanMass_eq_coordinateSlices state
      rw [functionalEq]
      fun_prop
    exact massContinuous.comp nextReceipt.wholePath.continuous
  · simpa only [nextReceipt] using
      generated.goodFibre_mass_le_sourceCellWall_ae_of_retainedResidual
        residual effectEq
  · exact timeLate

theorem GeneratedWholeRestartKineticContact.cellEffect_oneCell_of_incidence
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (incidence : WholeRestartContactOneCellIncidenceAt replay
      generated.nextContact) :
    ∃ (debit : GeneratedWholeRestartCellDebitAt replay generated.nextContact)
        (exact : debit.ExactValuedOneCellAt),
      generated.cellEffect = .oneCell debit exact := by
  rcases generated with ⟨event, _goodFibreAE⟩
  cases event with
  | crossing candidate actualIncidence _retainedTerminalDebit =>
      exact
        ⟨generatedWholeRestartCellDebit replay candidate.contact,
          actualIncidence, rfl⟩
  | persistent settlement =>
      let residual := generatedWholeRestartRetainedCellResidual replay settlement
      exact (residual.normalResidual.mismatch
        (residual.debit.exactOfOneCellIncidence incidence)).elim

/-- A source proof that the admissible fibre contains a one-cell occurrence
forces the compiler's own selected event into the crossing branch.  The
emitted representative need not be the witness supplied to this theorem. -/
theorem GeneratedWholeRestartKineticContact.cellEffect_oneCell_of_goodContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (candidate : GeneratedWholeRestartGoodContactAt replay)
    (incidence : candidate.OneCell) :
    ∃ (debit : GeneratedWholeRestartCellDebitAt replay
          generated.nextContact)
        (exact : debit.ExactValuedOneCellAt),
      generated.cellEffect = .oneCell debit exact := by
  rcases generated with ⟨event, _goodFibreAE⟩
  cases event with
  | crossing selected selectedIncidence _retainedTerminalDebit =>
      exact
        ⟨generatedWholeRestartCellDebit replay selected.contact,
          selectedIncidence, rfl⟩
  | persistent settlement =>
      exact ((settlement.noCrossing candidate).mismatch incidence).elim

/-- A physical crossing at the fixed terminal point of the complete replay
forces a positive-measure late crossing neighbourhood.  The conull good row
therefore makes the compiler choose its own one-cell occurrence; no theorem
must identify the emitted contact with the terminal point. -/
theorem GeneratedWholeRestartKineticContact.cellEffect_oneCell_of_terminal_mass_crosses
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (generated : GeneratedWholeRestartKineticContact replay)
    (terminalCrossing :
      (wholeRestartCoefficientLevel contact : ℝ) - 1 <
        wholeVorticityEuclideanMass
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay
            ).wholePath
              ⟨wholeRestartDuration contact,
                ⟨(wholeRestartDuration_pos contact).le, le_rfl⟩⟩)) :
    ∃ (debit : GeneratedWholeRestartCellDebitAt replay
          generated.nextContact)
        (exact : debit.ExactValuedOneCellAt),
      generated.cellEffect = .oneCell debit exact := by
  generalize effectEq : generated.cellEffect = effect
  cases effect with
  | oneCell debit incidence =>
      exact ⟨debit, incidence, rfl⟩
  | retainedResidual residual =>
      have terminalLate :
          (⟨wholeRestartDuration contact,
              ⟨(wholeRestartDuration_pos contact).le, le_rfl⟩⟩ :
            Icc (0 : ℝ) (wholeRestartDuration contact)) ∈
            lateCommonTimes (wholeRestartDuration contact) := by
        change wholeRestartDuration contact / 2 <
          wholeRestartDuration contact
        linarith [wholeRestartDuration_pos contact]
      have terminalLe :=
        generated.latePath_mass_le_sourceCellWall_of_retainedResidual
          residual effectEq
          ⟨wholeRestartDuration contact,
            ⟨(wholeRestartDuration_pos contact).le, le_rfl⟩⟩
          terminalLate
      exact (not_lt_of_ge terminalLe terminalCrossing).elim

/-- The generated whole receipt internally selects a late positive contact
that simultaneously carries gradient, physical invariants, the actual
kinetic ledger, and the same replay's coefficient ceiling.  No contact time,
target state, cutoff, or energy bound is accepted from a caller. -/
noncomputable def generatedWholeRestartKineticContact
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    {receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    GeneratedWholeRestartKineticContact replay := by
  let nextReceipt :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt replay
  let μ := commonTimeMeasure (wholeRestartDuration contact)
  let late := lateCommonTimes (wholeRestartDuration contact)
  have statePathAE :
      ∀ᵐ time ∂μ,
        nextReceipt.stateLimit time = nextReceipt.wholePath time := by
    have pathAE :=
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞)) (μ := μ) ℂ nextReceipt.wholePath
    filter_upwards [pathAE] with time pathEq
    rw [nextReceipt.wholePath_toLp_eq_stateLimit] at pathEq
    exact pathEq
  have gradientAE :
      ∀ᵐ time ∂μ,
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (nextReceipt.wholePath time wave) := by
    filter_upwards [
      wholePointwiseGradientDensity_ae_summable
        (wholeRestartDuration contact) nextReceipt.stateLimit
        nextReceipt.gradient_summable,
      statePathAE] with time gradient stateEq
    simpa only [stateEq] using gradient
  have kineticAE :
      ∀ᵐ time ∂μ,
        puncturedWholeVorticityKineticMass
            (nextReceipt.wholePath time) ≤
          puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) := by
    simpa only [nextReceipt] using
      generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticMass_ae_le
        replay
  have coefficientAE :
      ∀ᵐ time ∂μ,
        wholeVorticityEuclideanMass
            (nextReceipt.wholePath time) ≤
          wholeRestartCoefficientCeiling contact := by
    simpa only [nextReceipt] using
      generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
        replay
  have kineticDissipationAE :
      ∀ᵐ time ∂μ,
        puncturedWholeVorticityKineticMass
              (nextReceipt.wholePath time) +
            2 * ν.coeff *
              wholePrefixVorticityMass time nextReceipt.stateLimit ≤
          puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) := by
    simpa only [nextReceipt] using
      generatedWholeRestartWholeContinuousMildSerrinReceipt_kineticDissipation_ae_le
        replay
  have criticalDissipationAE :
      ∀ᵐ time ∂μ,
        0 < time.1 →
          ((1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
              criticalEnstrophyLatticeConstant *
                wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) ∨
            wholeVorticityEuclideanMass
                  (nextReceipt.wholePath time) +
                2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                  wholePrefixVorticityGradientMass time
                    nextReceipt.stateLimit ≤
              wholeVorticityEuclideanMass (wholeRestartPhysicalState contact)) := by
    simpa only [nextReceipt] using
      generatedWholeRestartWholeContinuousMildSerrinReceipt_halfCriticalAbsorption_disposition_ae
        replay
  have goodAE :
      ∀ᵐ time ∂μ,
        (Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (nextReceipt.wholePath time wave)) ∧
        WholeStateTransverse (nextReceipt.wholePath time) ∧
        FiniteStateFourierReality (nextReceipt.wholePath time) ∧
        puncturedWholeVorticityKineticMass
            (nextReceipt.wholePath time) ≤
            puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) ∧
        wholeVorticityEuclideanMass
            (nextReceipt.wholePath time) ≤
            wholeRestartCoefficientCeiling contact ∧
        puncturedWholeVorticityKineticMass
              (nextReceipt.wholePath time) +
            2 * ν.coeff *
              wholePrefixVorticityMass time nextReceipt.stateLimit ≤
          puncturedWholeVorticityKineticMass (wholeRestartPhysicalState contact) ∧
        (0 < time.1 →
          ((1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
              criticalEnstrophyLatticeConstant *
                wholeVorticityEuclideanMass (wholeRestartPhysicalState contact) ∨
            wholeVorticityEuclideanMass
                  (nextReceipt.wholePath time) +
                2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
                  wholePrefixVorticityGradientMass time
                    nextReceipt.stateLimit ≤
              wholeVorticityEuclideanMass (wholeRestartPhysicalState contact))) := by
    filter_upwards [gradientAE, nextReceipt.wholePath_eq_transverse_ae,
      nextReceipt.transverse_fourierReality_ae, kineticAE,
      coefficientAE, kineticDissipationAE, criticalDissipationAE] with
        time gradient pathEq reality kineticLe coefficientLe dissipationLe
          criticalDissipation
    have transverse := (nextReceipt.transverseLimit time).2
    change WholeStateTransverse
      ((nextReceipt.transverseLimit time).1) at transverse
    exact
      ⟨gradient, by simpa only [pathEq] using transverse,
        by simpa only [pathEq] using reality, kineticLe, coefficientLe,
        dissipationLe, criticalDissipation⟩
  have lateMeasure : 0 < μ late := by
    exact commonTimeMeasure_lateCommonTimes_pos
      (wholeRestartDuration contact) nextReceipt.requestedTimePos
  have restrictedNe : μ.restrict late ≠ 0 := by
    intro restrictedZero
    have univEq := congrArg
      (fun measure : Measure
          (Icc (0 : ℝ) (wholeRestartDuration contact)) =>
        measure Set.univ) restrictedZero
    simp at univEq
    exact lateMeasure.ne' univEq
  letI : NeZero (μ.restrict late) := ⟨restrictedNe⟩
  have goodRestricted := ae_restrict_of_ae (s := late) goodAE
  have lateRestricted :
      ∀ᵐ time ∂μ.restrict late, time ∈ late :=
    ae_restrict_mem
      (lateCommonTimes_measurable (wholeRestartDuration contact))
  have goodFibreAE :
      ∀ᵐ time ∂μ.restrict late,
        GeneratedWholeRestartGoodContactTimeAt replay time := by
    filter_upwards [goodRestricted, lateRestricted] with time timeSpec lateMem
    have timeHalf : wholeRestartDuration contact / 2 < time.1 := by
      simpa only [late, lateCommonTimes, Set.mem_ofPred_eq] using lateMem
    have timePos : 0 < time.1 := by
      linarith [nextReceipt.requestedTimePos, timeHalf]
    exact
      { time_pos := timePos
        time_half_lt := timeHalf
        gradient_summable := timeSpec.1
        transverse := timeSpec.2.1
        reality := timeSpec.2.2.1
        kineticMass_le := timeSpec.2.2.2.1
        coefficientMass_le := timeSpec.2.2.2.2.1
        kineticDissipation_le := timeSpec.2.2.2.2.2.1
        halfCriticalDisposition := timeSpec.2.2.2.2.2.2 timePos }
  have ordinaryGood : Nonempty (GeneratedWholeRestartGoodContactAt replay) := by
    rcases goodFibreAE.exists with ⟨time, good⟩
    exact ⟨⟨time, good⟩⟩
  classical
  let terminalDebit :=
    generatedWholeRestartTerminalNetEnstrophyDebit replay
  have retainedExistsOfPositive (terminalPositive : 0 < terminalDebit) :
      ∃ candidate : GeneratedWholeRestartGoodContactAt replay,
        terminalDebit / 2 <
          wholeVorticityEuclideanMass candidate.contact.physicalState -
            wholeVorticityEuclideanMass
              (wholeRestartPhysicalState contact) := by
    by_contra noRetained
    have everyGoodLe :
        ∀ candidate : GeneratedWholeRestartGoodContactAt replay,
          wholeVorticityEuclideanMass candidate.contact.physicalState -
                wholeVorticityEuclideanMass
                  (wholeRestartPhysicalState contact) ≤
              terminalDebit / 2 := by
      intro candidate
      exact le_of_not_gt fun retained =>
        noRetained ⟨candidate, retained⟩
    have lateMassAE :
        ∀ᵐ time ∂μ.restrict late,
          wholeVorticityEuclideanMass (nextReceipt.wholePath time) ≤
            wholeVorticityEuclideanMass
                (wholeRestartPhysicalState contact) +
              terminalDebit / 2 := by
      filter_upwards [goodFibreAE] with time good
      have bounded := everyGoodLe
        (⟨time, good⟩ : GeneratedWholeRestartGoodContactAt replay)
      change
        wholeVorticityEuclideanMass (nextReceipt.wholePath time) -
            wholeVorticityEuclideanMass
              (wholeRestartPhysicalState contact) ≤
          terminalDebit / 2 at bounded
      linarith
    let terminal : Icc (0 : ℝ) (wholeRestartDuration contact) :=
      ⟨wholeRestartDuration contact,
        ⟨(wholeRestartDuration_pos contact).le, le_rfl⟩⟩
    have terminalLate : terminal ∈ late := by
      change wholeRestartDuration contact / 2 <
        wholeRestartDuration contact
      linarith [wholeRestartDuration_pos contact]
    have terminalLe :=
      continuous_le_on_lateCommonTimes_of_ae_le
        (wholeRestartDuration_pos contact)
        (fun time => wholeVorticityEuclideanMass
          (nextReceipt.wholePath time))
        (continuous_wholeVorticityEuclideanMass_for_restart.comp
          nextReceipt.wholePath.continuous)
        lateMassAE terminal terminalLate
    have terminalDebitEq :
        terminalDebit =
          wholeVorticityEuclideanMass
              (nextReceipt.wholePath terminal) -
            wholeVorticityEuclideanMass
              (wholeRestartPhysicalState contact) := rfl
    rw [terminalDebitEq] at terminalPositive terminalLe
    linarith
  by_cases crossing :
      ∃ candidate : GeneratedWholeRestartGoodContactAt replay,
        candidate.OneCell
  · by_cases terminalPositive : 0 < terminalDebit
    · let retainedExists := retainedExistsOfPositive terminalPositive
      let retainedCandidate := Classical.choose retainedExists
      have retained := Classical.choose_spec retainedExists
      by_cases retainedCrosses : retainedCandidate.OneCell
      · exact
          { arithmeticEvent := .crossing retainedCandidate retainedCrosses
              (Or.inl ⟨terminalPositive, retained⟩)
            goodFibreAE := goodFibreAE }
      · let candidate := Classical.choose crossing
        have incidence : candidate.OneCell := Classical.choose_spec crossing
        have retainedMassLe :
            wholeVorticityEuclideanMass
                retainedCandidate.contact.physicalState ≤
              (wholeRestartCoefficientLevel contact : ℝ) - 1 := by
          apply le_of_not_gt
          intro retainedMassCrosses
          exact retainedCrosses
            ((retainedCandidate.oneCell_iff_mass_crosses_sourceCellWall).2
              retainedMassCrosses)
        have candidateMassGt :
            (wholeRestartCoefficientLevel contact : ℝ) - 1 <
              wholeVorticityEuclideanMass candidate.contact.physicalState :=
          (candidate.oneCell_iff_mass_crosses_sourceCellWall).1 incidence
        have candidateRetained :
            terminalDebit / 2 <
              wholeVorticityEuclideanMass candidate.contact.physicalState -
                wholeVorticityEuclideanMass
                  (wholeRestartPhysicalState contact) := by
          linarith
        exact
          { arithmeticEvent := .crossing candidate incidence
              (Or.inl ⟨terminalPositive, candidateRetained⟩)
            goodFibreAE := goodFibreAE }
    · let candidate := Classical.choose crossing
      have incidence : candidate.OneCell := Classical.choose_spec crossing
      exact
        { arithmeticEvent := .crossing candidate incidence
            (Or.inr (le_of_not_gt terminalPositive))
          goodFibreAE := goodFibreAE }
  · have noCrossing :
        ∀ later : GeneratedWholeRestartGoodContactAt replay,
          (generatedWholeRestartCellDebit replay
            later.contact).GeneratedValuedResidualAt := by
      intro later
      exact (generatedWholeRestartCellDebit replay
        later.contact).generatedResidualOfNotExact
          (fun exact => crossing ⟨later, exact⟩)
    by_cases terminalPositive : 0 < terminalDebit
    · have retainedExists := retainedExistsOfPositive terminalPositive
      let candidate := Classical.choose retainedExists
      have retained := Classical.choose_spec retainedExists
      exact
        { arithmeticEvent := .persistent
            { candidate := candidate
              noCrossing := noCrossing
              retainedTerminalDebit := by
                change
                  (0 < terminalDebit ∧ terminalDebit / 2 <
                    wholeVorticityEuclideanMass
                        candidate.contact.physicalState -
                      wholeVorticityEuclideanMass
                        (wholeRestartPhysicalState contact)) ∨
                    terminalDebit ≤ 0
                exact Or.inl ⟨terminalPositive, retained⟩ }
          goodFibreAE := goodFibreAE }
    · let candidate := Classical.choice ordinaryGood
      exact
        { arithmeticEvent := .persistent
            { candidate := candidate
              noCrossing := noCrossing
              retainedTerminalDebit := by
                change
                  (0 < terminalDebit ∧ terminalDebit / 2 <
                    wholeVorticityEuclideanMass
                        candidate.contact.physicalState -
                      wholeVorticityEuclideanMass
                        (wholeRestartPhysicalState contact)) ∨
                    terminalDebit ≤ 0
                exact Or.inr (le_of_not_gt terminalPositive) }
          goodFibreAE := goodFibreAE }

/-- Authoritative native-contact compiler: an actual macro contact generates
its next whole unforced positive-time receipt without a caller-selected
target, horizon, cutoff, branch, or continuation witness. -/
noncomputable def
    generatedNativeMacroWholeRestartWholeContinuousMildSerrinReceiptAt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    WholeContinuousMildSerrinReceipt
      ν
      (generatedNativeMacroWholePositiveTimeRestartContactAt
        lineage index).physicalState
      (wholeRestartDuration
        (generatedNativeMacroWholePositiveTimeRestartContactAt
          lineage index)) :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt
    (generatedNativeMacroWholeRestartCanonicalReplayAt lineage index)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
end NavierStokes
end SaturationMonoid
