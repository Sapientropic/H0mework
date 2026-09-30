import H0mework.NavierStokes.Restart.FiniteObservedCompactness
import H0mework.NavierStokes.GeneratedPaths.StrongSpaceTimeSubsequence
import H0mework.NavierStokes.Galerkin.CriticalHighFrequencyTail

/-!
# Whole-carrier strong compactness of the generated whole restart replay

The common gradient ledger makes every high-frequency tail uniformly small
in the genuine `L²_t ℓ²_x` carrier.  Together with finite-observation
compactness, this produces a strongly convergent subsequence of the actual
canonical whole-state restart replay.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness

open scoped ENNReal Topology Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalHighFrequencyTail
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

def wholeRestartWholeTrajectory
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (index : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    ComplexVorticityHilbertState :=
  (replay.current index).trajectory time.1

theorem wholeRestartWholeTrajectory_continuous
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (index : ℕ) :
    Continuous (wholeRestartWholeTrajectory replay index) := by
  rw [continuous_iff_continuousAt]
  intro time
  exact
    ((replay.current index).physical time.1 time.2).1.continuousAt.comp
      continuousAt_subtype_val

def wholeRestartWholeBoundedPath
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (index : ℕ) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) (wholeRestartDuration contact))
      ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact
    ⟨wholeRestartWholeTrajectory replay index,
      wholeRestartWholeTrajectory_continuous replay index⟩

def wholeRestartSpaceTimePath
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (index : ℕ) :
    SpaceTimeState (wholeRestartDuration contact) :=
  BoundedContinuousFunction.toLp 2
    (commonTimeMeasure (wholeRestartDuration contact)) ℂ
    (wholeRestartWholeBoundedPath replay index)

def wholeRestartSpaceTimePathFamily
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    Set (SpaceTimeState (wholeRestartDuration contact)) :=
  Set.range fun index : ℕ => wholeRestartSpaceTimePath replay index

def projectedWholeRestartSpaceTimePath
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    SpaceTimeState (wholeRestartDuration contact) :=
  observedPathToSpaceTime
    (wholeRestartDuration contact) observed
    (wholeRestartFiniteObservedBoundedPath replay observed index)

def compactWholeRestartObservedSpaceTimeSet
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) :
    Set (SpaceTimeState (wholeRestartDuration contact)) :=
  observedPathToSpaceTime (wholeRestartDuration contact) observed ''
    closure (wholeRestartFiniteObservedPathFamily replay observed)

theorem compactWholeRestartObservedSpaceTimeSet_isCompact
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) :
    IsCompact (compactWholeRestartObservedSpaceTimeSet replay observed) :=
  (wholeRestartFiniteObservedPathFamily_isCompact_closure replay observed).image
    (observedPathToSpaceTime
      (wholeRestartDuration contact) observed).continuous

theorem projectedWholeRestartSpaceTimePath_mem_compactObserved
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    projectedWholeRestartSpaceTimePath replay observed index ∈
      compactWholeRestartObservedSpaceTimeSet replay observed := by
  refine ⟨wholeRestartFiniteObservedBoundedPath replay observed index,
    subset_closure ⟨index, rfl⟩, rfl⟩

theorem wholeRestartSpaceTime_sub_projection_coeFn_ae
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      (wholeRestartSpaceTimePath replay index -
          projectedWholeRestartSpaceTimePath replay observed index) time =
        wholeRestartWholeTrajectory replay index time -
          complexSharpSupportProjection observed
            (wholeRestartWholeTrajectory replay index time) := by
  have wholeAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      (wholeRestartWholeBoundedPath replay index)
  have projectionAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
      ((finiteObservedEmbedding observed).compLeftContinuousBounded
        (Icc (0 : ℝ) (wholeRestartDuration contact))
        (wholeRestartFiniteObservedBoundedPath replay observed index))
  have subAE :=
    MeasureTheory.Lp.coeFn_sub
      (wholeRestartSpaceTimePath replay index)
      (projectedWholeRestartSpaceTimePath replay observed index)
  filter_upwards [subAE, wholeAE, projectionAE] with
    time subEq wholeEq projectionEq
  rw [subEq]
  change
    (wholeRestartSpaceTimePath replay index) time -
        (projectedWholeRestartSpaceTimePath replay observed index) time = _
  change
    ((BoundedContinuousFunction.toLp 2
      (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
      (wholeRestartWholeBoundedPath replay index)) time -
        ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
          ((finiteObservedEmbedding observed).compLeftContinuousBounded
            (Icc (0 : ℝ) (wholeRestartDuration contact))
            (wholeRestartFiniteObservedBoundedPath
              replay observed index))) time = _
  rw [wholeEq, projectionEq]
  change
    wholeRestartWholeTrajectory replay index time -
        finiteObservedEmbedding observed
          (finiteObservedCoefficientState observed
            (wholeRestartWholeTrajectory replay index time)) = _
  rw [finiteObservedEmbedding_finiteObservedCoefficientState]

theorem wholeRestart_projection_norm_sq_eq_intervalIntegral
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    ‖wholeRestartSpaceTimePath replay index -
        projectedWholeRestartSpaceTimePath replay observed index‖ ^ 2 =
      ∫ time in (0 : ℝ)..wholeRestartDuration contact,
        ‖(replay.current index).trajectory time -
            complexSharpSupportProjection observed
              ((replay.current index).trajectory time)‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  calc
    (∫ time,
        ‖(wholeRestartSpaceTimePath replay index -
            projectedWholeRestartSpaceTimePath replay observed index)
              time‖ ^ 2
        ∂(commonTimeMeasure (wholeRestartDuration contact))) =
      ∫ time,
        ‖wholeRestartWholeTrajectory replay index time -
          complexSharpSupportProjection observed
            (wholeRestartWholeTrajectory replay index time)‖ ^ 2
        ∂(commonTimeMeasure (wholeRestartDuration contact)) := by
      apply integral_congr_ae
      filter_upwards [
        wholeRestartSpaceTime_sub_projection_coeFn_ae
          replay observed index] with time pointwiseEq
      rw [pointwiseEq]
    _ =
      ∫ time in (0 : ℝ)..wholeRestartDuration contact,
        ‖(replay.current index).trajectory time -
            complexSharpSupportProjection observed
              ((replay.current index).trajectory time)‖ ^ 2 := by
      simpa [wholeRestartWholeTrajectory] using
        (commonTime_integral_eq_intervalIntegral
          (wholeRestartDuration contact)
          (wholeRestartDuration_pos contact).le
          (fun time =>
            ‖(replay.current index).trajectory time -
              complexSharpSupportProjection observed
                ((replay.current index).trajectory time)‖ ^ 2))

theorem wholeRestart_projection_norm_sq_le_tail_integral
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (radius : ℕ)
    (index : ℕ) :
    ‖wholeRestartSpaceTimePath replay index -
        projectedWholeRestartSpaceTimePath replay
          (lowFrequencyCube radius) index‖ ^ 2 ≤
      ∫ time in (0 : ℝ)..wholeRestartDuration contact,
        finiteStateVorticityHighFrequencyTailMass
          (wholeRestartModes index) ((radius : ℝ) ^ 2)
          ((replay.current index).trajectory time) := by
  rw [wholeRestart_projection_norm_sq_eq_intervalIntegral]
  let stage := replay.current index
  have differenceContinuous :
      ContinuousOn
        (fun time =>
          ‖stage.trajectory time -
            complexSharpSupportProjection (lowFrequencyCube radius)
              (stage.trajectory time)‖ ^ 2)
        (Icc (0 : ℝ) (wholeRestartDuration contact)) := by
    let difference : ℝ → ℝ := fun time =>
      ‖stage.trajectory time -
        complexSharpSupportProjection (lowFrequencyCube radius)
          (stage.trajectory time)‖
    have trajectoryContinuous :
        ContinuousOn stage.trajectory
          (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
      HasDerivAt.continuousOn fun time timeMem =>
        (stage.physical time timeMem).1
    have projectionContinuous :
        ContinuousOn
          (fun time =>
            sharpSupportProjectionCLM (lowFrequencyCube radius)
              (stage.trajectory time))
          (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
      (sharpSupportProjectionCLM
        (lowFrequencyCube radius)).continuous.comp_continuousOn
          trajectoryContinuous
    have differenceBaseContinuous :
        ContinuousOn difference
          (Icc (0 : ℝ) (wholeRestartDuration contact)) := by
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
        volume 0 (wholeRestartDuration contact) :=
    ContinuousOn.intervalIntegrable_of_Icc
      (wholeRestartDuration_pos contact).le differenceContinuous
  have tailContinuous :
      ContinuousOn
        (fun time =>
          finiteStateVorticityHighFrequencyTailMass
            (wholeRestartModes index) ((radius : ℝ) ^ 2)
            (stage.trajectory time))
        (Icc (0 : ℝ) (wholeRestartDuration contact)) := by
    intro time timeMem
    exact
      (finiteStateVorticityHighFrequencyTailMass_continuousAt_of_hasDerivAt
        (wholeRestartModes index) ((radius : ℝ) ^ 2)
        stage.trajectory time
        (finiteStateVorticityGenerator
          (wholeRestartModes index) ν.coeff (stage.trajectory time))
        (stage.physical time timeMem).1).continuousWithinAt
  have tailIntegrable :
      IntervalIntegrable
        (fun time =>
          finiteStateVorticityHighFrequencyTailMass
            (wholeRestartModes index) ((radius : ℝ) ^ 2)
            (stage.trajectory time))
        volume 0 (wholeRestartDuration contact) :=
    ContinuousOn.intervalIntegrable_of_Icc
      (wholeRestartDuration_pos contact).le tailContinuous
  apply intervalIntegral.integral_mono_on
    (wholeRestartDuration_pos contact).le
    differenceIntegrable tailIntegrable
  intro time timeMem
  exact norm_sub_lowFrequencyCubeProjection_sq_le_tail
    radius (wholeRestartModes index) (stage.trajectory time)
    (stage.physical time timeMem).2.1

theorem wholeRestart_projection_norm_sq_le_uniformTail
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (radius : ℕ)
    (radiusPos : 0 < radius)
    (index : ℕ) :
    ‖wholeRestartSpaceTimePath replay index -
        projectedWholeRestartSpaceTimePath replay
          (lowFrequencyCube radius) index‖ ^ 2 ≤
      wholeRestartGradientCeiling contact / (radius : ℝ) ^ 2 := by
  let stage := replay.current index
  have thresholdPos : 0 < (radius : ℝ) ^ 2 := by positivity
  have thresholdTail :=
    threshold_mul_integral_highFrequencyTailMass_le_integral_enstrophyMass
      (wholeRestartModes index) ν.coeff ((radius : ℝ) ^ 2)
      stage.trajectory 0 (wholeRestartDuration contact)
      (wholeRestartDuration_pos contact).le
      (fun time timeMem => (stage.physical time timeMem).1)
  have gradient := (stage.uniformScalarBudget).2.1
  have tailLe :
      (∫ time in (0 : ℝ)..wholeRestartDuration contact,
        finiteStateVorticityHighFrequencyTailMass
          (wholeRestartModes index) ((radius : ℝ) ^ 2)
          (stage.trajectory time)) ≤
        wholeRestartGradientCeiling contact / (radius : ℝ) ^ 2 := by
    apply (le_div_iff₀ thresholdPos).2
    simpa [mul_comm] using thresholdTail.trans gradient
  exact
    (wholeRestart_projection_norm_sq_le_tail_integral
      replay radius index).trans (by simpa [stage] using tailLe)

theorem exists_lowFrequencyCube_wholeRestart_uniformly_close
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (ε : ℝ)
    (εPos : 0 < ε) :
    ∃ radius : ℕ, 0 < radius ∧
      ∀ index : ℕ,
        dist (wholeRestartSpaceTimePath replay index)
          (projectedWholeRestartSpaceTimePath replay
            (lowFrequencyCube radius) index) < ε := by
  let numerator := wholeRestartGradientCeiling contact
  have numeratorNonneg : 0 ≤ numerator :=
    wholeRestartGradientCeiling_nonneg contact
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
    wholeRestart_projection_norm_sq_le_uniformTail
      replay radius radiusPos index
  have normSqLt :
      ‖wholeRestartSpaceTimePath replay index -
          projectedWholeRestartSpaceTimePath replay
            (lowFrequencyCube radius) index‖ ^ 2 < ε ^ 2 :=
    normSqLe.trans_lt (by simpa [numerator] using ratioLt)
  nlinarith [norm_nonneg
    (wholeRestartSpaceTimePath replay index -
      projectedWholeRestartSpaceTimePath replay
        (lowFrequencyCube radius) index)]

theorem wholeRestartSpaceTimePathFamily_totallyBounded
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    TotallyBounded (wholeRestartSpaceTimePathFamily replay) := by
  rw [Metric.totallyBounded_iff]
  intro ε εPos
  have halfεPos : 0 < ε / 2 := by linarith
  obtain ⟨radius, radiusPos, uniformlyClose⟩ :=
    exists_lowFrequencyCube_wholeRestart_uniformly_close
      replay (ε / 2) halfεPos
  let compactSet :=
    compactWholeRestartObservedSpaceTimeSet replay
      (lowFrequencyCube radius)
  have compactSetCompact : IsCompact compactSet :=
    compactWholeRestartObservedSpaceTimeSet_isCompact
      replay (lowFrequencyCube radius)
  obtain ⟨centers, centersFinite, centersCover⟩ :=
    (Metric.totallyBounded_iff.mp compactSetCompact.totallyBounded)
      (ε / 2) halfεPos
  refine ⟨centers, centersFinite, ?_⟩
  intro member memberMem
  rcases memberMem with ⟨index, rfl⟩
  let projection := projectedWholeRestartSpaceTimePath replay
    (lowFrequencyCube radius) index
  have projectionMem : projection ∈ compactSet :=
    projectedWholeRestartSpaceTimePath_mem_compactObserved
      replay (lowFrequencyCube radius) index
  rcases Set.mem_iUnion.mp (centersCover projectionMem) with
    ⟨center, centerCover⟩
  rcases Set.mem_iUnion.mp centerCover with
    ⟨centerMem, projectionInBall⟩
  refine Set.mem_iUnion.mpr ⟨center, ?_⟩
  refine Set.mem_iUnion.mpr ⟨centerMem, ?_⟩
  rw [Metric.mem_ball] at projectionInBall ⊢
  calc
    dist (wholeRestartSpaceTimePath replay index) center ≤
      dist (wholeRestartSpaceTimePath replay index) projection +
        dist projection center := dist_triangle _ _ _
    _ < ε := by
      have memberClose := uniformlyClose index
      dsimp [projection] at memberClose projectionInBall ⊢
      linarith

theorem wholeRestartSpaceTimePathFamily_isCompact_closure
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    IsCompact (closure (wholeRestartSpaceTimePathFamily replay)) :=
  (wholeRestartSpaceTimePathFamily_totallyBounded replay).closure
    |>.isCompact_of_isClosed isClosed_closure

/-- The actual canonical restart replay has one common strongly convergent
whole-carrier subsequence, with the same subsequence converging on every
fixed Fourier row. -/
theorem exists_wholeRestartSpaceTime_strong_subsequence
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    ∃ limit : SpaceTimeState (wholeRestartDuration contact),
      limit ∈ closure (wholeRestartSpaceTimePathFamily replay) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
          (fun index =>
            wholeRestartSpaceTimePath replay (subsequence index))
          atTop (𝓝 limit) ∧
        ∀ wave : IntegerWavevector,
          Tendsto
            (fun index =>
              fixedWaveSpaceTimeRestriction
                (wholeRestartDuration contact) wave
                (wholeRestartSpaceTimePath replay (subsequence index)))
            atTop
            (𝓝 (fixedWaveSpaceTimeRestriction
              (wholeRestartDuration contact) wave limit)) := by
  have sequenceMem (index : ℕ) :
      wholeRestartSpaceTimePath replay index ∈
        closure (wholeRestartSpaceTimePathFamily replay) :=
    subset_closure ⟨index, rfl⟩
  obtain ⟨limit, limitMem, subsequence, subsequenceMono, wholeTendsto⟩ :=
    (wholeRestartSpaceTimePathFamily_isCompact_closure replay).tendsto_subseq
      sequenceMem
  refine ⟨limit, limitMem, subsequence, subsequenceMono, ?_, ?_⟩
  · simpa [Function.comp_def] using wholeTendsto
  · intro wave
    exact
      ((fixedWaveSpaceTimeRestriction
        (wholeRestartDuration contact) wave).continuous.tendsto
          limit).comp (by simpa [Function.comp_def] using wholeTendsto)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness
end NavierStokes
end SaturationMonoid
