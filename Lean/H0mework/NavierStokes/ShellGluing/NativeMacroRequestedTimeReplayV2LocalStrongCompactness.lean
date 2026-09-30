import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalFiniteObservedCompactness
import H0mework.NavierStokes.GeneratedPaths.StrongSpaceTimeSubsequence
import H0mework.NavierStokes.Galerkin.CriticalHighFrequencyTail

/-!
# Whole-carrier strong compactness of the local V2 replay

The source-owned local gradient ledger makes the high-frequency tail of
every actual V2 Galerkin stage uniformly small in the genuine
`L²([0,T]; ℓ²)` carrier.  Combined with the finite-observation compactness
of the same trajectories, this gives a strongly convergent subsequence of
the residual-driven replay without a critical-smallness branch.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalStrongCompactness

open scoped ENNReal Topology Interval

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalHighFrequencyTail
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalFiniteObservedCompactness

noncomputable section

def localReplayV2WholeTrajectory
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (index : ℕ)
    (time : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    ComplexVorticityHilbertState :=
  (replay.current index).trajectory time.1

theorem localReplayV2WholeTrajectory_continuous
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (index : ℕ) :
    Continuous (localReplayV2WholeTrajectory replay index) := by
  rw [continuous_iff_continuousAt]
  intro time
  exact
    ((replay.current index).physical time.1 time.2).1.continuousAt.comp
      continuousAt_subtype_val

def localReplayV2WholeBoundedPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (index : ℕ) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
      ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact
    ⟨localReplayV2WholeTrajectory replay index,
      localReplayV2WholeTrajectory_continuous replay index⟩

def localReplayV2SpaceTimePath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (index : ℕ) :
    SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
  BoundedContinuousFunction.toLp 2
    (commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)) ℂ
    (localReplayV2WholeBoundedPath replay index)

def localReplayV2SpaceTimePathFamily
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
    Set (SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage)) :=
  Set.range fun index : ℕ => localReplayV2SpaceTimePath replay index

def projectedLocalReplayV2SpaceTimePath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
  observedPathToSpaceTime
    (sourceOwnedLocalReplayV2Duration lineage) observed
    (localReplayV2FiniteObservedBoundedPath replay observed index)

def compactLocalReplayV2ObservedSpaceTimeSet
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector) :
    Set (SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage)) :=
  observedPathToSpaceTime
      (sourceOwnedLocalReplayV2Duration lineage) observed ''
    closure (localReplayV2FiniteObservedPathFamily replay observed)

theorem compactLocalReplayV2ObservedSpaceTimeSet_isCompact
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector) :
    IsCompact (compactLocalReplayV2ObservedSpaceTimeSet replay observed) :=
  (localReplayV2FiniteObservedPathFamily_isCompact_closure
    replay observed).image
      (observedPathToSpaceTime
        (sourceOwnedLocalReplayV2Duration lineage) observed).continuous

theorem projectedLocalReplayV2SpaceTimePath_mem_compactObserved
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    projectedLocalReplayV2SpaceTimePath replay observed index ∈
      compactLocalReplayV2ObservedSpaceTimeSet replay observed := by
  refine ⟨localReplayV2FiniteObservedBoundedPath replay observed index,
    subset_closure ⟨index, rfl⟩, rfl⟩

theorem localReplayV2SpaceTime_sub_projection_coeFn_ae
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
      (localReplayV2SpaceTimePath replay index -
          projectedLocalReplayV2SpaceTimePath replay observed index) time =
        localReplayV2WholeTrajectory replay index time -
          complexSharpSupportProjection observed
            (localReplayV2WholeTrajectory replay index time) := by
  have wholeAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage))
      ℂ (localReplayV2WholeBoundedPath replay index)
  have projectionAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage))
      ℂ
      ((finiteObservedEmbedding observed).compLeftContinuousBounded
        (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
        (localReplayV2FiniteObservedBoundedPath replay observed index))
  have subAE :=
    MeasureTheory.Lp.coeFn_sub
      (localReplayV2SpaceTimePath replay index)
      (projectedLocalReplayV2SpaceTimePath replay observed index)
  filter_upwards [subAE, wholeAE, projectionAE] with
    time subEq wholeEq projectionEq
  rw [subEq]
  change
    (localReplayV2SpaceTimePath replay index) time -
        (projectedLocalReplayV2SpaceTimePath replay observed index) time = _
  change
    ((BoundedContinuousFunction.toLp 2
      (commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)) ℂ)
      (localReplayV2WholeBoundedPath replay index)) time -
        ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)) ℂ)
          ((finiteObservedEmbedding observed).compLeftContinuousBounded
            (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
            (localReplayV2FiniteObservedBoundedPath
              replay observed index))) time = _
  rw [wholeEq, projectionEq]
  change
    localReplayV2WholeTrajectory replay index time -
        finiteObservedEmbedding observed
          (finiteObservedCoefficientState observed
            (localReplayV2WholeTrajectory replay index time)) = _
  rw [finiteObservedEmbedding_finiteObservedCoefficientState]

theorem localReplayV2_projection_norm_sq_eq_intervalIntegral
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    ‖localReplayV2SpaceTimePath replay index -
        projectedLocalReplayV2SpaceTimePath replay observed index‖ ^ 2 =
      ∫ time in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
        ‖(replay.current index).trajectory time -
            complexSharpSupportProjection observed
              ((replay.current index).trajectory time)‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  calc
    (∫ time,
        ‖(localReplayV2SpaceTimePath replay index -
            projectedLocalReplayV2SpaceTimePath replay observed index)
              time‖ ^ 2
        ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage))) =
      ∫ time,
        ‖localReplayV2WholeTrajectory replay index time -
          complexSharpSupportProjection observed
            (localReplayV2WholeTrajectory replay index time)‖ ^ 2
        ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)) := by
      apply integral_congr_ae
      filter_upwards [
        localReplayV2SpaceTime_sub_projection_coeFn_ae
          replay observed index] with time pointwiseEq
      rw [pointwiseEq]
    _ =
      ∫ time in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
        ‖(replay.current index).trajectory time -
            complexSharpSupportProjection observed
              ((replay.current index).trajectory time)‖ ^ 2 := by
      simpa [localReplayV2WholeTrajectory] using
        (commonTime_integral_eq_intervalIntegral
          (sourceOwnedLocalReplayV2Duration lineage) durationPos.le
          (fun time =>
            ‖(replay.current index).trajectory time -
              complexSharpSupportProjection observed
                ((replay.current index).trajectory time)‖ ^ 2))

theorem localReplayV2_projection_norm_sq_le_tail_integral
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (radius : ℕ)
    (index : ℕ) :
    ‖localReplayV2SpaceTimePath replay index -
        projectedLocalReplayV2SpaceTimePath replay
          (lowFrequencyCube radius) index‖ ^ 2 ≤
      ∫ time in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
        finiteStateVorticityHighFrequencyTailMass
          (replay.current index).modes ((radius : ℝ) ^ 2)
          ((replay.current index).trajectory time) := by
  rw [localReplayV2_projection_norm_sq_eq_intervalIntegral]
  let stage := replay.current index
  have differenceContinuous :
      ContinuousOn
        (fun time =>
          ‖stage.trajectory time -
            complexSharpSupportProjection (lowFrequencyCube radius)
              (stage.trajectory time)‖ ^ 2)
        (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) := by
    let difference : ℝ → ℝ := fun time =>
      ‖stage.trajectory time -
        complexSharpSupportProjection (lowFrequencyCube radius)
          (stage.trajectory time)‖
    have trajectoryContinuous :
        ContinuousOn stage.trajectory
          (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :=
      HasDerivAt.continuousOn fun time timeMem =>
        (stage.physical time timeMem).1
    have projectionContinuous :
        ContinuousOn
          (fun time =>
            sharpSupportProjectionCLM (lowFrequencyCube radius)
              (stage.trajectory time))
          (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) := by
      exact
        (sharpSupportProjectionCLM
          (lowFrequencyCube radius)).continuous.comp_continuousOn
            trajectoryContinuous
    have differenceBaseContinuous :
        ContinuousOn difference
          (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) := by
      intro time timeMem
      simpa only [difference, Pi.sub_apply,
        sharpSupportProjectionCLM_apply] using
          ((trajectoryContinuous time timeMem).sub
            (projectionContinuous time timeMem)).norm
    have functionEq :
        (fun time =>
          ‖stage.trajectory time -
            complexSharpSupportProjection (lowFrequencyCube radius)
              (stage.trajectory time)‖ ^ 2) =
          difference ^ 2 := by
      funext time
      rfl
    rw [functionEq]
    exact differenceBaseContinuous.pow 2
  have differenceIntegrable :
      IntervalIntegrable
        (fun time =>
          ‖stage.trajectory time -
            complexSharpSupportProjection (lowFrequencyCube radius)
              (stage.trajectory time)‖ ^ 2)
        volume 0 (sourceOwnedLocalReplayV2Duration lineage) :=
    ContinuousOn.intervalIntegrable_of_Icc durationPos.le
      differenceContinuous
  have tailContinuous :
      ContinuousOn
        (fun time =>
          finiteStateVorticityHighFrequencyTailMass stage.modes
            ((radius : ℝ) ^ 2) (stage.trajectory time))
        (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) := by
    intro time timeMem
    exact
      (finiteStateVorticityHighFrequencyTailMass_continuousAt_of_hasDerivAt
        stage.modes ((radius : ℝ) ^ 2) stage.trajectory time
        (finiteStateVorticityGenerator
          stage.modes ν.coeff (stage.trajectory time))
        (stage.physical time timeMem).1).continuousWithinAt
  have tailIntegrable :
      IntervalIntegrable
        (fun time =>
          finiteStateVorticityHighFrequencyTailMass stage.modes
            ((radius : ℝ) ^ 2) (stage.trajectory time))
        volume 0 (sourceOwnedLocalReplayV2Duration lineage) :=
    ContinuousOn.intervalIntegrable_of_Icc durationPos.le tailContinuous
  apply intervalIntegral.integral_mono_on
    durationPos.le differenceIntegrable tailIntegrable
  intro time timeMem
  exact norm_sub_lowFrequencyCubeProjection_sq_le_tail
    radius stage.modes (stage.trajectory time)
    (stage.physical time timeMem).2.1

theorem localReplayV2_projection_norm_sq_le_uniformTail
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (radius : ℕ)
    (radiusPos : 0 < radius)
    (index : ℕ) :
    ‖localReplayV2SpaceTimePath replay index -
        projectedLocalReplayV2SpaceTimePath replay
          (lowFrequencyCube radius) index‖ ^ 2 ≤
      sourceOwnedLocalReplayV2GradientCeiling lineage /
        (radius : ℝ) ^ 2 := by
  let stage := replay.current index
  have thresholdPos : 0 < (radius : ℝ) ^ 2 := by positivity
  have thresholdTail :=
    threshold_mul_integral_highFrequencyTailMass_le_integral_enstrophyMass
      stage.modes ν.coeff ((radius : ℝ) ^ 2) stage.trajectory
      0 (sourceOwnedLocalReplayV2Duration lineage) durationPos.le
      (fun time timeMem => (stage.physical time timeMem).1)
  have gradient :=
    (requestedTimeReplayV2Stage_uniformLocalCompactnessBudget stage).2.1
  have tailLe :
      (∫ time in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
        finiteStateVorticityHighFrequencyTailMass stage.modes
          ((radius : ℝ) ^ 2) (stage.trajectory time)) ≤
        sourceOwnedLocalReplayV2GradientCeiling lineage /
          (radius : ℝ) ^ 2 := by
    apply (le_div_iff₀ thresholdPos).2
    simpa [mul_comm] using thresholdTail.trans gradient
  exact
    (localReplayV2_projection_norm_sq_le_tail_integral
      replay radius index).trans (by simpa [stage] using tailLe)

theorem exists_lowFrequencyCube_localReplayV2_uniformly_close
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (ε : ℝ)
    (εPos : 0 < ε) :
    ∃ radius : ℕ, 0 < radius ∧
      ∀ index : ℕ,
        dist (localReplayV2SpaceTimePath replay index)
          (projectedLocalReplayV2SpaceTimePath replay
            (lowFrequencyCube radius) index) < ε := by
  let numerator := sourceOwnedLocalReplayV2GradientCeiling lineage
  have numeratorNonneg : 0 ≤ numerator :=
    sourceOwnedLocalReplayV2GradientCeiling_nonneg lineage
  have εSqPos : 0 < ε ^ 2 := sq_pos_of_pos εPos
  obtain ⟨radius, radiusGt⟩ := exists_nat_gt (numerator / ε ^ 2)
  have ratioNonneg : 0 ≤ numerator / ε ^ 2 :=
    div_nonneg numeratorNonneg εSqPos.le
  have radiusRealPos : 0 < (radius : ℝ) := ratioNonneg.trans_lt radiusGt
  have radiusPos : 0 < radius := by exact_mod_cast radiusRealPos
  have radiusLeSquare : (radius : ℝ) ≤ (radius : ℝ) ^ 2 := by
    have radiusOneLe : (1 : ℝ) ≤ radius := by exact_mod_cast radiusPos
    nlinarith
  have numeratorLtRadius : numerator < (radius : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ εSqPos).1 radiusGt
  have ratioLt : numerator / (radius : ℝ) ^ 2 < ε ^ 2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos radiusRealPos)).2
    calc
      numerator < (radius : ℝ) * ε ^ 2 := numeratorLtRadius
      _ ≤ (radius : ℝ) ^ 2 * ε ^ 2 :=
        mul_le_mul_of_nonneg_right radiusLeSquare εSqPos.le
      _ = ε ^ 2 * (radius : ℝ) ^ 2 := by ring
  refine ⟨radius, radiusPos, ?_⟩
  intro index
  rw [dist_eq_norm]
  have normSqLe :=
    localReplayV2_projection_norm_sq_le_uniformTail
      replay radius radiusPos index
  have normSqLt :
      ‖localReplayV2SpaceTimePath replay index -
          projectedLocalReplayV2SpaceTimePath replay
            (lowFrequencyCube radius) index‖ ^ 2 < ε ^ 2 :=
    normSqLe.trans_lt (by simpa [numerator] using ratioLt)
  nlinarith [norm_nonneg
    (localReplayV2SpaceTimePath replay index -
      projectedLocalReplayV2SpaceTimePath replay
        (lowFrequencyCube radius) index)]

theorem localReplayV2SpaceTimePathFamily_totallyBounded
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
    TotallyBounded (localReplayV2SpaceTimePathFamily replay) := by
  rw [Metric.totallyBounded_iff]
  intro ε εPos
  have halfεPos : 0 < ε / 2 := by linarith
  obtain ⟨radius, radiusPos, uniformlyClose⟩ :=
    exists_lowFrequencyCube_localReplayV2_uniformly_close
      replay (ε / 2) halfεPos
  let compactSet :=
    compactLocalReplayV2ObservedSpaceTimeSet replay
      (lowFrequencyCube radius)
  have compactSetCompact : IsCompact compactSet :=
    compactLocalReplayV2ObservedSpaceTimeSet_isCompact
      replay (lowFrequencyCube radius)
  obtain ⟨centers, centersFinite, centersCover⟩ :=
    (Metric.totallyBounded_iff.mp compactSetCompact.totallyBounded)
      (ε / 2) halfεPos
  refine ⟨centers, centersFinite, ?_⟩
  intro member memberMem
  rcases memberMem with ⟨index, rfl⟩
  let projection := projectedLocalReplayV2SpaceTimePath replay
    (lowFrequencyCube radius) index
  have projectionMem : projection ∈ compactSet :=
    projectedLocalReplayV2SpaceTimePath_mem_compactObserved
      replay (lowFrequencyCube radius) index
  rcases Set.mem_iUnion.mp (centersCover projectionMem) with
    ⟨center, centerCover⟩
  rcases Set.mem_iUnion.mp centerCover with
    ⟨centerMem, projectionInBall⟩
  refine Set.mem_iUnion.mpr ⟨center, ?_⟩
  refine Set.mem_iUnion.mpr ⟨centerMem, ?_⟩
  rw [Metric.mem_ball] at projectionInBall ⊢
  calc
    dist (localReplayV2SpaceTimePath replay index) center ≤
      dist (localReplayV2SpaceTimePath replay index) projection +
        dist projection center := dist_triangle _ _ _
    _ < ε := by
      have memberClose := uniformlyClose index
      dsimp [projection] at memberClose projectionInBall ⊢
      linarith

theorem localReplayV2SpaceTimePathFamily_isCompact_closure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
    IsCompact (closure (localReplayV2SpaceTimePathFamily replay)) :=
  (localReplayV2SpaceTimePathFamily_totallyBounded replay).closure
    |>.isCompact_of_isClosed isClosed_closure

/-- The actual residual-driven replay itself has a common strongly
convergent whole-carrier subsequence. -/
theorem exists_localReplayV2SpaceTime_strong_subsequence
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
    ∃ limit : SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage),
      limit ∈ closure (localReplayV2SpaceTimePathFamily replay) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
          (fun index =>
            localReplayV2SpaceTimePath replay (subsequence index))
          atTop (𝓝 limit) ∧
        ∀ wave : IntegerWavevector,
          Tendsto
            (fun index =>
              fixedWaveSpaceTimeRestriction
                (sourceOwnedLocalReplayV2Duration lineage) wave
                (localReplayV2SpaceTimePath replay (subsequence index)))
            atTop
            (𝓝 (fixedWaveSpaceTimeRestriction
              (sourceOwnedLocalReplayV2Duration lineage) wave limit)) := by
  have sequenceMem (index : ℕ) :
      localReplayV2SpaceTimePath replay index ∈
        closure (localReplayV2SpaceTimePathFamily replay) :=
    subset_closure ⟨index, rfl⟩
  obtain ⟨limit, limitMem, subsequence, subsequenceMono, wholeTendsto⟩ :=
    (localReplayV2SpaceTimePathFamily_isCompact_closure replay).tendsto_subseq
      sequenceMem
  refine ⟨limit, limitMem, subsequence, subsequenceMono, ?_, ?_⟩
  · simpa [Function.comp_def] using wholeTendsto
  · intro wave
    exact
      ((fixedWaveSpaceTimeRestriction
        (sourceOwnedLocalReplayV2Duration lineage) wave).continuous.tendsto
          limit).comp (by simpa [Function.comp_def] using wholeTendsto)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalStrongCompactness
end NavierStokes
end SaturationMonoid
