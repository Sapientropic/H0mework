import H0mework.NavierStokes.KineticRestart.KineticVelocityWholeCarrierMorphism
import H0mework.NavierStokes.MacroRuntime.GlobalStrongInterfaceObstruction
import H0mework.Realization.Residual.Process

/-!
# Global physical residual transport at a whole-restart accumulation interface

The kinetic endpoint atom already lives on an actual source-selected
subsequence, while the global macro runtime already owns the corresponding
unforced physical velocity path.  This module forms the residual before any
finite Fourier quotient:

```text
global path at the selected pre-interface contact
  - global path at the exact accumulation interface.
```

Literal shift along the source-selected contacts is its native keep/update.
The residual converges weakly to zero, its square norm converges to the
generated endpoint atom, and it is definitionally the same residual whether
read in the local macro chart or in the stabilized global path.

No endpoint, subsequence, cutoff, defect branch, continuity witness, strong
limit, or tail-settlement certificate is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Filter Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## The physical endpoint residual on the actual selected contacts -/

/-- Complete physical-velocity residual of one source-selected contact
against the physical endpoint generated on the same refined lineage. -/
def wholeRestartEndpointVelocityResidual
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : WholeRestartVelocityEndpointState :=
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).family.endpointReceipt
  wholeRestartContactVelocityState initial (receipt.subsequence index) -
    receipt.velocityEndpoint

/-- The concrete weighted Biot--Savart morphism carries the source-aligned
kinetic residual to the complete physical residual at the identical actual
selected contact. -/
theorem wholeRestartKineticToVelocityCLM_alignedResidual
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartKineticToVelocityCLM
        (wholeRestartEndpointAlignedKineticResidual
          initial elapsedBounded index) =
      wholeRestartEndpointVelocityResidual
        initial elapsedBounded index := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).family.endpointReceipt
  change
    wholeRestartKineticToVelocityCLM
        (wholeRestartContactKineticState
            initial (receipt.subsequence index) -
          receipt.kineticReceipt.endpoint) =
      wholeRestartContactVelocityState
          initial (receipt.subsequence index) -
        receipt.velocityEndpoint
  rw [map_sub, wholeRestartKineticToVelocityCLM_contact,
    wholeRestartKineticToVelocityCLM_endpoint receipt]

/-- Future complete physical residuals beginning at one selected contact. -/
abbrev WholeRestartEndpointVelocityResidualTail :=
  ℕ → WholeRestartVelocityEndpointState

/-- Forget the current selected contact and retain its generated future. -/
def wholeRestartEndpointVelocityResidualTailKeep :
    WholeRestartEndpointVelocityResidualTail →ₗ[ℂ]
      WholeRestartEndpointVelocityResidualTail where
  toFun residual offset := residual (offset + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual future physical residual tail on the selected source lineage. -/
def wholeRestartEndpointVelocityResidualTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : WholeRestartEndpointVelocityResidualTail :=
  fun offset =>
    wholeRestartEndpointVelocityResidual
      initial elapsedBounded (index + offset)

/-- The aligned kinetic residual tail on the same refined endpoint
occurrences used by the physical compiler. -/
def wholeRestartEndpointAlignedKineticResidualTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : WholeRestartKineticEndpointResidualTail :=
  fun offset =>
    wholeRestartEndpointAlignedKineticResidual
      initial elapsedBounded (index + offset)

/-- Pointwise lift of the concrete weighted Biot--Savart morphism to future
residual tails. -/
def wholeRestartKineticToVelocityResidualTail
    (residual : WholeRestartKineticEndpointResidualTail) :
    WholeRestartEndpointVelocityResidualTail :=
  fun offset => wholeRestartKineticToVelocityCLM (residual offset)

/-- The concrete whole-carrier morphism commutes with the two literal shift
keeps on arbitrary residual tails. -/
theorem wholeRestartKineticToVelocityResidualTail_keep_commutes
    (residual : WholeRestartKineticEndpointResidualTail) :
    wholeRestartKineticToVelocityResidualTail
        (wholeRestartKineticEndpointResidualTailKeep residual) =
      wholeRestartEndpointVelocityResidualTailKeep
        (wholeRestartKineticToVelocityResidualTail residual) := by
  rfl

/-- Consequently the uniquely forced traces commute with the same concrete
whole-carrier morphism. -/
theorem wholeRestartKineticToVelocityResidualTail_trace_commutes
    (residual : WholeRestartKineticEndpointResidualTail) :
    wholeRestartKineticToVelocityResidualTail
        (linearResidualTrace
          wholeRestartKineticEndpointResidualTailKeep residual) =
      linearResidualTrace
        wholeRestartEndpointVelocityResidualTailKeep
        (wholeRestartKineticToVelocityResidualTail residual) := by
  funext offset
  exact map_sub wholeRestartKineticToVelocityCLM _ _

/-- On the generated refined source lineage, the entire future kinetic
residual tail maps to the actual physical endpoint residual tail. -/
theorem wholeRestartKineticToVelocityResidualTail_aligned
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartKineticToVelocityResidualTail
        (wholeRestartEndpointAlignedKineticResidualTail
          initial elapsedBounded index) =
      wholeRestartEndpointVelocityResidualTail
        initial elapsedBounded index := by
  funext offset
  exact wholeRestartKineticToVelocityCLM_alignedResidual
    initial elapsedBounded (index + offset)

/-- The physical endpoint residual follows literal shift along the
source-selected actual contact lineage. -/
def generatedWholeRestartEndpointVelocityResidualEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    EffectiveResidualProcess
      ℂ WholeRestartEndpointVelocityResidualTail ℕ where
  target := 0
  keep := wholeRestartEndpointVelocityResidualTailKeep
  residual := wholeRestartEndpointVelocityResidualTail
    initial elapsedBounded
  update := fun index => index + 1
  residual_transport_law := by
    intro index
    funext offset
    simp only [wholeRestartEndpointVelocityResidualTail,
      wholeRestartEndpointVelocityResidualTailKeep,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    omega

/-- Whole-carrier commuting square for the next selected actual contact. -/
theorem wholeRestartEndpointVelocityResidual_transport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartEndpointVelocityResidualTail
        initial elapsedBounded (index + 1) =
      wholeRestartEndpointVelocityResidualTailKeep
        (wholeRestartEndpointVelocityResidualTail
          initial elapsedBounded index) :=
  (generatedWholeRestartEndpointVelocityResidualEffectiveProcess
    initial elapsedBounded).residual_transport_law index

/-- The physical residual converges weakly to zero on the complete velocity
carrier before any finite Fourier observation. -/
theorem wholeRestartEndpointVelocityResidual_weak_tendsto_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (test : WholeRestartVelocityEndpointState) :
    Tendsto
      (fun index =>
        inner ℂ
          (wholeRestartEndpointVelocityResidual
            initial elapsedBounded index)
          test)
      atTop (nhds 0) := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).family.endpointReceipt
  have weak := receipt.velocity_weak_tendsto_shared test
  have shifted := weak.sub_const
    (inner ℂ receipt.velocityEndpoint test)
  convert shifted using 1
  · funext index
    rw [wholeRestartEndpointVelocityResidual, inner_sub_left]
  · simp

/-- Every fixed physical Fourier coordinate of the complete residual tends
to zero; the possible atom is therefore a simultaneous whole-tail effect. -/
theorem wholeRestartEndpointVelocityResidual_coordinate_tendsto_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    Tendsto
      (fun index =>
        wholeRestartEndpointVelocityResidual
          initial elapsedBounded index wave coordinate)
      atTop (nhds 0) := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).family.endpointReceipt
  change
    Tendsto
      (fun index =>
        (wholeRestartContactVelocityState initial
            (receipt.subsequence index) -
          receipt.velocityEndpoint) wave coordinate)
      atTop (nhds 0)
  have rowTendsto :=
    velocityWeakTendsto_coordinate
      (fun index =>
        wholeRestartContactVelocityState initial
          (receipt.subsequence index))
      receipt.velocityEndpoint receipt.velocity_weak_tendsto_shared
      wave coordinate
  have shifted := rowTendsto.sub_const
    (receipt.velocityEndpoint wave coordinate)
  convert shifted using 1
  · funext index
    rfl
  · simp

/-- The square norm of the actual physical residual converges exactly to the
same generated kinetic endpoint defect. -/
theorem wholeRestartEndpointVelocityResidual_norm_sq_tendsto_defect
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let receipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt
    Tendsto
      (fun index =>
        ‖wholeRestartEndpointVelocityResidual
          initial elapsedBounded index‖ ^ 2)
      atTop
      (nhds
        (wholeRestartKineticWeakEndpointDefect
          initial receipt.kineticReceipt.endpoint)) := by
  dsimp only
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).family.endpointReceipt
  have normSqTendsto :
      Tendsto
        (fun index =>
          ‖wholeRestartContactVelocityState
            initial (receipt.subsequence index)‖ ^ 2)
        atTop
        (nhds (wholeRestartKineticMassLimit initial)) := by
    have massTendsto :
        Tendsto
          (fun index =>
            wholeRestartContactKineticMass
              initial (receipt.subsequence index))
          atTop
          (nhds (wholeRestartKineticMassLimit initial)) := by
      simpa only [
        GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.subsequence,
        Function.comp_def] using
      receipt.kineticReceipt.mass_tendsto.comp
        receipt.velocitySubsubsequence_strictMono.tendsto_atTop
    convert massTendsto using 1
    funext index
    rw [wholeRestartContactKineticMass,
      wholeRestartContactVelocityState_norm_sq,
      wholeRestartContactKineticState,
      puncturedWholeVorticityKineticEuclideanState_norm_sq]
  have weakRealTendsto :
      Tendsto
        (fun index =>
          (inner ℂ
            (wholeRestartContactVelocityState
              initial (receipt.subsequence index))
            receipt.velocityEndpoint).re)
        atTop
        (nhds (‖receipt.velocityEndpoint‖ ^ 2)) := by
    have evaluated :=
      (Complex.continuous_re.tendsto
        (inner ℂ receipt.velocityEndpoint receipt.velocityEndpoint)).comp
          (receipt.velocity_weak_tendsto_shared receipt.velocityEndpoint)
    change
      Tendsto
        (fun index =>
          (inner ℂ
            (wholeRestartContactVelocityState
              initial (receipt.subsequence index))
            receipt.velocityEndpoint).re)
        atTop
        (nhds
          ((inner ℂ
            receipt.velocityEndpoint receipt.velocityEndpoint).re))
        at evaluated
    have endpointInnerEq :
        (inner ℂ
          receipt.velocityEndpoint receipt.velocityEndpoint).re =
            ‖receipt.velocityEndpoint‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) receipt.velocityEndpoint
    rw [endpointInnerEq] at evaluated
    exact evaluated
  have expanded :
      Tendsto
        (fun index =>
          ‖wholeRestartContactVelocityState
              initial (receipt.subsequence index)‖ ^ 2 -
            2 *
              (inner ℂ
                (wholeRestartContactVelocityState
                  initial (receipt.subsequence index))
                receipt.velocityEndpoint).re +
              ‖receipt.velocityEndpoint‖ ^ 2)
        atTop
        (nhds
          (wholeRestartKineticMassLimit initial -
            2 * ‖receipt.velocityEndpoint‖ ^ 2 +
              ‖receipt.velocityEndpoint‖ ^ 2)) :=
    (normSqTendsto.sub (weakRealTendsto.const_mul 2)).add_const
      (‖receipt.velocityEndpoint‖ ^ 2)
  convert expanded using 1
  · funext index
    exact norm_sub_sq (𝕜 := ℂ)
      (wholeRestartContactVelocityState
        initial (receipt.subsequence index)) receipt.velocityEndpoint
  · rw [wholeRestartVelocityWeakEndpoint_norm_sq_eq_kineticEndpoint
      receipt]
    unfold wholeRestartKineticWeakEndpointDefect
    simp only [receipt]
    congr 1
    ring

/-! ## Exact realization on one macro stage and on the global path -/

namespace GeneratedWholeRestartEndpointMacroStep

/-- The local physical-stage residual at the selected contact is literally
the complete residual generated above. -/
theorem physicalStage_selectedContact_sub_accumulation
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (index : ℕ) :
    step.physicalStage (step.physicalStageSelectedContactTime index) -
        step.physicalStage step.physicalStageAccumulation =
      wholeRestartEndpointVelocityResidual
        current step.elapsedBounded index := by
  rw [step.physicalStage_selectedContactTime,
    step.physicalStage_accumulation]
  rfl

/-- The local physical-stage residual carries exactly the stage's generated
kinetic-energy atom in its limiting square norm. -/
theorem physicalStage_selectedContactResidual_norm_sq_tendsto_energyAtom
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Tendsto
      (fun index =>
        ‖step.physicalStage
              (step.physicalStageSelectedContactTime index) -
            step.physicalStage step.physicalStageAccumulation‖ ^ 2)
      atTop (nhds step.physicalStageKineticEnergyAtom) := by
  simp_rw [step.physicalStage_selectedContact_sub_accumulation]
  rw [step.physicalStageKineticEnergyAtom_eq_defect]
  exact
    wholeRestartEndpointVelocityResidual_norm_sq_tendsto_defect
      step.elapsedBounded

end GeneratedWholeRestartEndpointMacroStep

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- Absolute time of one source-selected pre-interface contact inside a
generated global macro stage. -/
def globalStageSelectedContactTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) : ℝ :=
  lineage.macroClock stage +
    (lineage.step stage).physicalStageSelectedContactTime index

/-- The generated selected contact times converge to the exact global
accumulation interface from the actual stage chart. -/
theorem globalStageSelectedContactTime_tendsto_accumulation
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    Tendsto
      (lineage.globalStageSelectedContactTime stage)
      atTop
      (nhds (lineage.globalStageAccumulationTime stage)) := by
  let step := lineage.step stage
  change
    Tendsto
      (fun index =>
        lineage.macroClock stage +
          ((step.physicalStageSelectedContactTime index :
            Icc (0 : ℝ) step.clockAdvance) : ℝ))
      atTop
      (nhds
        (lineage.macroClock stage +
          ((step.physicalStageAccumulation :
            Icc (0 : ℝ) step.clockAdvance) : ℝ)))
  have localTendsto :
      Tendsto
        (fun index =>
          ((step.physicalStageSelectedContactTime index :
            Icc (0 : ℝ) step.clockAdvance) : ℝ))
        atTop
        (nhds ((step.physicalStageAccumulation :
          Icc (0 : ℝ) step.clockAdvance) : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      step.physicalStageSelectedContactTime_tendsto_accumulation
  exact tendsto_const_nhds.add localTendsto

/-- Complete whole-velocity residual read directly from the stabilized
global physical path at one generated accumulation interface. -/
def globalStagePhysicalResidual
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) : WholeRestartVelocityEndpointState :=
  lineage.globalAbsoluteVelocityTrajectory
      (lineage.globalStageSelectedContactTime stage index) -
    lineage.globalAbsoluteVelocityTrajectory
      (lineage.globalStageAccumulationTime stage)

/-- The global residual is definitionally the same physical residual as in
the exact local macro chart and the source-selected contact lineage. -/
theorem globalStagePhysicalResidual_eq_endpointVelocityResidual
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    lineage.globalStagePhysicalResidual stage index =
      wholeRestartEndpointVelocityResidual
        (lineage.current stage)
        (lineage.step stage).elapsedBounded index := by
  change
    lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock stage +
            ((lineage.step stage).physicalStageSelectedContactTime index).1) -
        lineage.globalAbsoluteVelocityTrajectory
          (lineage.macroClock stage +
            ((lineage.step stage).physicalStageAccumulation).1) =
      wholeRestartEndpointVelocityResidual
        (lineage.current stage)
        (lineage.step stage).elapsedBounded index
  rw [lineage.globalAbsoluteVelocityTrajectory_eq_stage
      stage
      ((lineage.step stage).physicalStageSelectedContactTime index),
    lineage.globalAbsoluteVelocityTrajectory_eq_stage
      stage (lineage.step stage).physicalStageAccumulation,
    (lineage.step stage).physicalStage_selectedContact_sub_accumulation]

/-- Exact same-event commuting theorem: the global physical path difference
is the concrete weighted Biot--Savart image of the source-aligned kinetic
residual, occurrence by occurrence. -/
theorem globalStagePhysicalResidual_eq_kineticImage
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    lineage.globalStagePhysicalResidual stage index =
      wholeRestartKineticToVelocityCLM
        (wholeRestartEndpointAlignedKineticResidual
          (lineage.current stage)
          (lineage.step stage).elapsedBounded index) := by
  rw [lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual,
    wholeRestartKineticToVelocityCLM_alignedResidual]

/-- Future global physical residuals beginning at one selected contact. -/
def globalStagePhysicalResidualTail
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) : WholeRestartEndpointVelocityResidualTail :=
  fun offset =>
    lineage.globalStagePhysicalResidual stage (index + offset)

/-- The full global interface residual tail is the concrete image of the
source-aligned kinetic tail before any Fourier-coordinate quotient. -/
theorem globalStagePhysicalResidualTail_eq_kineticImage
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage index : ℕ) :
    globalStagePhysicalResidualTail lineage stage index =
      wholeRestartKineticToVelocityResidualTail
        (wholeRestartEndpointAlignedKineticResidualTail
          (lineage.current stage)
          (lineage.step stage).elapsedBounded index) := by
  funext offset
  exact lineage.globalStagePhysicalResidual_eq_kineticImage
    stage (index + offset)

/-- The actual global-path interface residual inherits the same native shift
process; this is the whole-carrier commuting square at the global join. -/
def generatedGlobalStagePhysicalResidualEffectiveProcess
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    EffectiveResidualProcess
      ℂ WholeRestartEndpointVelocityResidualTail ℕ where
  target := 0
  keep := wholeRestartEndpointVelocityResidualTailKeep
  residual := globalStagePhysicalResidualTail lineage stage
  update := fun index => index + 1
  residual_transport_law := by
    intro index
    funext offset
    simp only [globalStagePhysicalResidualTail,
      wholeRestartEndpointVelocityResidualTailKeep,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    omega

/-- Every fixed coordinate of the exact global interface residual tends to
zero on the source-selected actual contacts. -/
theorem globalStagePhysicalResidual_coordinate_tendsto_zero
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ)
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    Tendsto
      (fun index =>
        lineage.globalStagePhysicalResidual
          stage index wave coordinate)
      atTop (nhds 0) := by
  simp_rw [lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual]
  exact
    wholeRestartEndpointVelocityResidual_coordinate_tendsto_zero
      (lineage.step stage).elapsedBounded wave coordinate

/-- The exact global physical interface residual has limiting square mass
equal to the source-generated kinetic defect at that same stage. -/
theorem globalStagePhysicalResidual_norm_sq_tendsto_stageDefect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    Tendsto
      (fun index =>
        ‖lineage.globalStagePhysicalResidual stage index‖ ^ 2)
      atTop
      (nhds (infiniteEndpointMacroStageKineticDefect lineage stage)) := by
  simp_rw [lineage.globalStagePhysicalResidual_eq_endpointVelocityResidual]
  simpa only [infiniteEndpointMacroStageKineticDefect] using
    wholeRestartEndpointVelocityResidual_norm_sq_tendsto_defect
      (lineage.step stage).elapsedBounded

/-- A positive stage atom remains quantitatively present in every
sufficiently late complete global physical residual, although each fixed
coordinate tends to zero. -/
theorem globalStagePhysicalResidual_eventually_gt_half_stageDefect
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ)
    (defectPositive :
      0 < infiniteEndpointMacroStageKineticDefect lineage stage) :
    ∀ᶠ index : ℕ in atTop,
      infiniteEndpointMacroStageKineticDefect lineage stage / 2 <
        ‖lineage.globalStagePhysicalResidual stage index‖ ^ 2 := by
  exact
    (lineage.globalStagePhysicalResidual_norm_sq_tendsto_stageDefect stage)
      (eventually_gt_nhds (by linarith))

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
