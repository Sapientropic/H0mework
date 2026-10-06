import H0mework.Arithmetic.RiemannRuntime.PairedOmegaQuarterScaleRadialCurrent
import H0mework.Arithmetic.SonineSource.ClozelSeededIntegralGraphOrbitAction
import H0mework.Arithmetic.SonineSource.ClozelModifiedWeakFEGraphSource

/-!
# Projection of the emitted quarter boundary through the WeakFE source state

The fixed-root runtime already emits the integral update
`delta 1 - delta q`.  The source-generated modified WeakFE unit state now
supplies a faithful dependent graph face of that same update.  Its paired
Riesz read is exactly the previously retained radial incidence coordinate.
No new event, free comparator, or vanishing premise is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockEndpointFixedCoordinateReadback
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open Character.GlobalCoPoissonCurrent
open InverseZeroFibre
open QRich
open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation
open scoped InnerProductSpace

noncomputable section

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial :
  ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))

def selectedSourceModifiedUnitIntegralGraphOrbit :
    IntegralScaleCarrier →ₗ[ℤ]
      SelectedCoPoissonMuntzGraphCokernel observation nontrivial :=
  seededIntegralGraphOrbit
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (selectedSourceModifiedUnitQuarterTest observation nontrivial)

def reversalSourceModifiedUnitIntegralGraphOrbit :
    IntegralScaleCarrier →ₗ[ℤ]
      ReversalCoPoissonMuntzGraphCokernel observation nontrivial :=
  seededIntegralGraphOrbit
    (reversalCoPoissonMuntzParameter observation)
    (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
    (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    (reversalSourceModifiedUnitQuarterTest observation nontrivial)

def selectedSourceModifiedUnitBoundaryClass :
    SelectedCoPoissonMuntzGraphCokernel observation nontrivial :=
  selectedSourceModifiedUnitIntegralGraphOrbit observation nontrivial
    stageZeroQuarterIntegralBoundary

def reversalSourceModifiedUnitBoundaryClass :
    ReversalCoPoissonMuntzGraphCokernel observation nontrivial :=
  reversalSourceModifiedUnitIntegralGraphOrbit observation nontrivial
    stageZeroQuarterIntegralBoundary

/-- This is literally a dependent-face projection of the integral value of
the already emitted fixed-root source-boundary row. -/
theorem runtimeQuarterSourceBoundary_selectedModifiedUnit_projection :
    selectedSourceModifiedUnitIntegralGraphOrbit observation nontrivial
        (runtimeJointIntegralFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterSourceBoundary))) =
      selectedSourceModifiedUnitBoundaryClass observation nontrivial := by
  rw [runtimeQuarterSourceBoundary_integral_readback]
  rfl

theorem runtimeQuarterSourceBoundary_reversalModifiedUnit_projection :
    reversalSourceModifiedUnitIntegralGraphOrbit observation nontrivial
        (runtimeJointIntegralFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterSourceBoundary))) =
      reversalSourceModifiedUnitBoundaryClass observation nontrivial := by
  rw [runtimeQuarterSourceBoundary_integral_readback]
  rfl

theorem selectedSourceModifiedUnitBoundaryClass_source :
    selectedSourceModifiedUnitBoundaryClass observation nontrivial =
      coPoissonMuntzGraphSourceMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (selectedSourceModifiedUnitQuarterTest observation nontrivial -
          quarterDilationTestAction
            (selectedCoPoissonMuntzParameter observation)
            stageZeroSqrtScale stageZeroSqrtScale_pos
            (selectedSourceModifiedUnitQuarterTest observation nontrivial)) := by
  unfold selectedSourceModifiedUnitBoundaryClass
    selectedSourceModifiedUnitIntegralGraphOrbit
  rw [stageZeroQuarterIntegralBoundary_eq_delta_sub_delta, map_sub,
    seededIntegralGraphOrbit_delta, seededIntegralGraphOrbit_delta]
  have oneScale : scaleSquare (1 : Units NNReal) = 1 := by
    simp [scaleSquare, scaleValue]
  have oneAction :
      quarterDilationTestAction
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare (1 : Units NNReal)) (scaleSquare_pos 1)
          (selectedSourceModifiedUnitQuarterTest observation nontrivial) =
        selectedSourceModifiedUnitQuarterTest observation nontrivial := by
    simpa only [oneScale, LinearMap.id_apply] using LinearMap.congr_fun
      (quarterDilationTestAction_one
        (selectedCoPoissonMuntzParameter observation))
      (selectedSourceModifiedUnitQuarterTest observation nontrivial)
  have quarterAction :
      quarterDilationTestAction
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare stageZeroQuarterScaleUnit)
          (scaleSquare_pos stageZeroQuarterScaleUnit)
          (selectedSourceModifiedUnitQuarterTest observation nontrivial) =
        quarterDilationTestAction
          (selectedCoPoissonMuntzParameter observation)
          stageZeroSqrtScale stageZeroSqrtScale_pos
          (selectedSourceModifiedUnitQuarterTest observation nontrivial) := by
    simp only [stageZeroQuarterScaleUnit_square]
  rw [oneAction, quarterAction, map_sub]

theorem reversalSourceModifiedUnitBoundaryClass_source :
    reversalSourceModifiedUnitBoundaryClass observation nontrivial =
      coPoissonMuntzGraphSourceMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (reversalSourceModifiedUnitQuarterTest observation nontrivial -
          quarterDilationTestAction
            (reversalCoPoissonMuntzParameter observation)
            stageZeroSqrtScale stageZeroSqrtScale_pos
            (reversalSourceModifiedUnitQuarterTest observation nontrivial)) := by
  unfold reversalSourceModifiedUnitBoundaryClass
    reversalSourceModifiedUnitIntegralGraphOrbit
  rw [stageZeroQuarterIntegralBoundary_eq_delta_sub_delta, map_sub,
    seededIntegralGraphOrbit_delta, seededIntegralGraphOrbit_delta]
  have oneScale : scaleSquare (1 : Units NNReal) = 1 := by
    simp [scaleSquare, scaleValue]
  have oneAction :
      quarterDilationTestAction
          (reversalCoPoissonMuntzParameter observation)
          (scaleSquare (1 : Units NNReal)) (scaleSquare_pos 1)
          (reversalSourceModifiedUnitQuarterTest observation nontrivial) =
        reversalSourceModifiedUnitQuarterTest observation nontrivial := by
    simpa only [oneScale, LinearMap.id_apply] using LinearMap.congr_fun
      (quarterDilationTestAction_one
        (reversalCoPoissonMuntzParameter observation))
      (reversalSourceModifiedUnitQuarterTest observation nontrivial)
  have quarterAction :
      quarterDilationTestAction
          (reversalCoPoissonMuntzParameter observation)
          (scaleSquare stageZeroQuarterScaleUnit)
          (scaleSquare_pos stageZeroQuarterScaleUnit)
          (reversalSourceModifiedUnitQuarterTest observation nontrivial) =
        quarterDilationTestAction
          (reversalCoPoissonMuntzParameter observation)
          stageZeroSqrtScale stageZeroSqrtScale_pos
          (reversalSourceModifiedUnitQuarterTest observation nontrivial) := by
    simp only [stageZeroQuarterScaleUnit_square]
  rw [oneAction, quarterAction, map_sub]

theorem selectedSourceModifiedUnitBoundaryClass_riesz :
    ⟪ selectedCoPoissonMuntzRieszVector observation nontrivial,
      selectedSourceModifiedUnitBoundaryClass observation nontrivial⟫_ℂ =
      1 - selectedStageZeroRawRieszTarget observation nontrivial := by
  rw [selectedSourceModifiedUnitBoundaryClass_source,
    selectedCoPoissonMuntzRieszVector_source_readback, map_sub,
    selectedSourceModifiedUnitQuarterTest_functional_one]
  have eigen := LinearMap.congr_fun
    (quarterDilationFunctional_eigenlaw
      (selectedCoPoissonMuntzParameter observation)
      stageZeroSqrtScale stageZeroSqrtScale_pos)
    (selectedSourceModifiedUnitQuarterTest observation nontrivial)
  change quarterMellinL2Functional
      (selectedCoPoissonMuntzParameter observation)
      (quarterDilationTestAction
        (selectedCoPoissonMuntzParameter observation)
        stageZeroSqrtScale stageZeroSqrtScale_pos
        (selectedSourceModifiedUnitQuarterTest observation nontrivial)) =
    quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation) stageZeroSqrtScale •
      quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation)
        (selectedSourceModifiedUnitQuarterTest observation nontrivial) at eigen
  rw [eigen, selectedSourceModifiedUnitQuarterTest_functional_one]
  simp only [smul_eq_mul, mul_one]
  unfold selectedStageZeroRawRieszTarget
  rw [occurrence_selectedDilationTrace_eq_character]
  rfl

theorem reversalSourceModifiedUnitBoundaryClass_riesz :
    ⟪ reversalCoPoissonMuntzRieszVector observation nontrivial,
      reversalSourceModifiedUnitBoundaryClass observation nontrivial⟫_ℂ =
      1 - reversalStageZeroRawRieszTarget observation nontrivial := by
  rw [reversalSourceModifiedUnitBoundaryClass_source,
    reversalCoPoissonMuntzRieszVector_source_readback, map_sub,
    reversalSourceModifiedUnitQuarterTest_functional_one]
  have eigen := LinearMap.congr_fun
    (quarterDilationFunctional_eigenlaw
      (reversalCoPoissonMuntzParameter observation)
      stageZeroSqrtScale stageZeroSqrtScale_pos)
    (reversalSourceModifiedUnitQuarterTest observation nontrivial)
  change quarterMellinL2Functional
      (reversalCoPoissonMuntzParameter observation)
      (quarterDilationTestAction
        (reversalCoPoissonMuntzParameter observation)
        stageZeroSqrtScale stageZeroSqrtScale_pos
        (reversalSourceModifiedUnitQuarterTest observation nontrivial)) =
    quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation) stageZeroSqrtScale •
      quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation)
        (reversalSourceModifiedUnitQuarterTest observation nontrivial) at eigen
  rw [eigen, reversalSourceModifiedUnitQuarterTest_functional_one]
  simp only [smul_eq_mul, mul_one]
  unfold reversalStageZeroRawRieszTarget
  rw [occurrence_reversalDilationTrace_eq_character]
  rfl

/-- Paired detector of the two source-boundary projections.  This is the
existing root update seen through the source-generated WeakFE state. -/
def sourceModifiedUnitBoundaryIncidence : ℂ :=
  ⟪ reversalCoPoissonMuntzRieszVector observation nontrivial,
      reversalSourceModifiedUnitBoundaryClass observation nontrivial⟫_ℂ -
    star (⟪ selectedCoPoissonMuntzRieszVector observation nontrivial,
      selectedSourceModifiedUnitBoundaryClass observation nontrivial⟫_ℂ)

theorem sourceModifiedUnitBoundaryIncidence_eq_rawRieszResidual :
    sourceModifiedUnitBoundaryIncidence observation nontrivial =
      star (selectedStageZeroRawRieszTarget observation nontrivial) -
        reversalStageZeroRawRieszTarget observation nontrivial := by
  rw [sourceModifiedUnitBoundaryIncidence,
    selectedSourceModifiedUnitBoundaryClass_riesz,
    reversalSourceModifiedUnitBoundaryClass_riesz]
  simp

/-- Faithful radial measurement reconstructed from the two source-boundary
reads.  Unlike the complex incidence above, it forgets only phase. -/
def sourceModifiedUnitBoundaryTargetModulusImbalance : ℝ :=
  ‖1 - ⟪ selectedCoPoissonMuntzRieszVector observation nontrivial,
      selectedSourceModifiedUnitBoundaryClass observation nontrivial⟫_ℂ‖ -
    ‖1 - ⟪ reversalCoPoissonMuntzRieszVector observation nontrivial,
      reversalSourceModifiedUnitBoundaryClass observation nontrivial⟫_ℂ‖

theorem sourceModifiedUnitBoundaryTargetModulusImbalance_eq_radialCurrent :
    sourceModifiedUnitBoundaryTargetModulusImbalance observation nontrivial =
      stageZeroRawRadialCurrent observation nontrivial := by
  rw [sourceModifiedUnitBoundaryTargetModulusImbalance,
    selectedSourceModifiedUnitBoundaryClass_riesz,
    reversalSourceModifiedUnitBoundaryClass_riesz]
  unfold stageZeroRawRadialCurrent
  ring_nf

/-- The source-generated projection and the already installed fixed-root
retained row expose one and the same radial current. -/
theorem sourceModifiedUnitBoundaryTargetModulusImbalance_eq_runtime :
    sourceModifiedUnitBoundaryTargetModulusImbalance observation nontrivial =
      retainedTargetModulusImbalance
        (runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterRetained))) := by
  rw [sourceModifiedUnitBoundaryTargetModulusImbalance_eq_radialCurrent,
    runtimeQuarterRetained_modulusImbalance_eq_stageZeroRawRadialCurrent]

theorem sourceModifiedUnitBoundaryTargetModulusImbalance_eq_zero_iff_separator_zero
    (characterStage stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    sourceModifiedUnitBoundaryTargetModulusImbalance
          observation nontrivial = 0 ↔
      branchNormalizedQRichSeparator
          (mathlibLeftRegressionComponent observation) stage row = 0 := by
  rw [sourceModifiedUnitBoundaryTargetModulusImbalance_eq_runtime,
    runtimeQuarterModulusImbalance_eq_zero_iff_separator_zero
      observation nontrivial characterStage stage row]

end
end IntegralGraphJointAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
