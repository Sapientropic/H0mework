import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Holder
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalBudget
import H0mework.NavierStokes.GeneratedPaths.FiniteObservedCompactness

/-!
# Finite-observation compactness of the local V2 replay

The unconditional residual-driven V2 runtime supplies one actual Galerkin
orbit at every support-refinement stage.  On the source-generated local
horizon, the common coefficient and negative-Sobolev budgets give a single
Arzela--Ascoli modulus for the complete infinite replay.

No critical-smallness margin, cutoff, subsequence, or target limit is a
premise.  This is the finite-observation half of the whole-flow compiler.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalFiniteObservedCompactness

open scoped BigOperators ENNReal NNReal Topology Interval

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinNegativeSobolevTimeBudget
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinTimeEquicontinuity
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget

noncomputable section

def localReplayV2FiniteObservedTrajectory
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (time : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    FiniteObservedCoefficientState observed :=
  finiteObservedCoefficientState observed
    ((replay.current index).trajectory time.1)

theorem localReplayV2FiniteObservedTrajectory_continuous
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    Continuous
      (localReplayV2FiniteObservedTrajectory replay observed index) := by
  apply continuous_pi
  intro wave
  rw [continuous_iff_continuousAt]
  intro time
  have evolves := ((replay.current index).physical time.1 time.2).1
  exact
    (complexVorticityTrajectoryWave_hasDerivAt
      (replay.current index).trajectory time.1
      (finiteStateVorticityGenerator
        (replay.current index).modes ν.coeff
        ((replay.current index).trajectory time.1))
      wave.1 evolves).continuousAt.comp continuousAt_subtype_val

def localReplayV2FiniteObservedBoundedPath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
      (FiniteObservedCoefficientState observed) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨localReplayV2FiniteObservedTrajectory replay observed index,
      localReplayV2FiniteObservedTrajectory_continuous
        replay observed index⟩

theorem localReplayV2FiniteObservedTrajectory_norm_le_ceiling
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (time : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    ‖localReplayV2FiniteObservedTrajectory replay observed index time‖ ≤
      Real.sqrt (sourceOwnedLocalReplayV2EnstrophyCeiling lineage) := by
  let stage := replay.current index
  have currentEnstrophyLe :=
    (requestedTimeReplayV2Stage_uniformLocalCompactnessBudget stage).1
      time.1 time.2
  have ambientSqLe :
      ‖stage.trajectory time.1‖ ^ 2 ≤
        finiteStateVorticityCoefficientEnstrophy
          stage.modes (stage.trajectory time.1) :=
    complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      stage.modes (stage.trajectory time.1)
      (stage.physical time.1 time.2).2.1
  have ceilingNonneg :
      0 ≤ sourceOwnedLocalReplayV2EnstrophyCeiling lineage :=
    (sourceOwnedLocalEnstrophyCeiling_pos _ _).le
  have ambientNormLe :
      ‖stage.trajectory time.1‖ ≤
        Real.sqrt (sourceOwnedLocalReplayV2EnstrophyCeiling lineage) :=
    (Real.le_sqrt (norm_nonneg _) ceilingNonneg).2
      (ambientSqLe.trans currentEnstrophyLe)
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro wave
  exact
    (lp.norm_apply_le_norm (by norm_num)
      (stage.trajectory time.1) wave.1).trans ambientNormLe

def localReplayV2FiniteObservedHalfHolderEnergy
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (observed : Finset IntegerWavevector) : ℝ :=
  finiteObservedMultiplierMass observed *
    sourceOwnedLocalReplayV2NegativeOneCeiling lineage

theorem localReplayV2FiniteObservedHalfHolderEnergy_nonneg
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (observed : Finset IntegerWavevector) :
    0 ≤ localReplayV2FiniteObservedHalfHolderEnergy lineage observed :=
  mul_nonneg
    (finiteObservedMultiplierMass_nonneg observed)
    (sourceOwnedLocalReplayV2NegativeOneCeiling_nonneg lineage)

def localReplayV2FiniteObservedHalfHolderConstant
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (observed : Finset IntegerWavevector) : NNReal :=
  ⟨Real.sqrt
      (localReplayV2FiniteObservedHalfHolderEnergy lineage observed),
    Real.sqrt_nonneg _⟩

private theorem activeObservedMultiplier_le
    (observed modes : Finset IntegerWavevector) :
    (∑ wave ∈ observed.filter (fun wave => wave ∈ modes),
        integerWaveViscousMultiplier wave) ≤
      finiteObservedMultiplierMass observed := by
  unfold finiteObservedMultiplierMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro wave waveMem
    exact (Finset.mem_filter.mp waveMem).1
  · intro wave waveNotMem waveMem
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)

private theorem localReplayV2_negativeOneMass_interval_le_ceiling
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (index : ℕ)
    (a b : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
    (hab : a.1 ≤ b.1) :
    (∫ t in a.1..b.1,
      finiteStateVorticityNegativeOneMass
        (replay.current index).modes
        (finiteStateVorticityGenerator
          (replay.current index).modes ν.coeff
          ((replay.current index).trajectory t))) ≤
      sourceOwnedLocalReplayV2NegativeOneCeiling lineage := by
  let stage := replay.current index
  let mass : ℝ → ℝ := fun t =>
    finiteStateVorticityNegativeOneMass stage.modes
      (finiteStateVorticityGenerator
        stage.modes ν.coeff (stage.trajectory t))
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage),
        HasDerivAt stage.trajectory
          (finiteStateVorticityGenerator
            stage.modes ν.coeff (stage.trajectory t)) t := by
    intro t tMem
    exact (stage.physical t tMem).1
  have massContinuous :
      ContinuousOn mass
        (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :=
    finiteGalerkinGeneratorNegativeOneMass_continuousOn
      stage.modes ν.coeff stage.trajectory 0
      (sourceOwnedLocalReplayV2Duration lineage) evolves
  have massIntegrable :
      IntervalIntegrable mass volume 0
        (sourceOwnedLocalReplayV2Duration lineage) :=
    ContinuousOn.intervalIntegrable_of_Icc durationPos.le massContinuous
  have localLeFull :
      (∫ t in a.1..b.1, mass t) ≤
        ∫ t in (0 : ℝ)..sourceOwnedLocalReplayV2Duration lineage,
          mass t := by
    apply intervalIntegral.integral_mono_interval
    · exact a.2.1
    · exact hab
    · exact b.2.2
    · exact Filter.Eventually.of_forall fun t =>
        finiteStateVorticityNegativeOneMass_nonneg _ _
    · exact massIntegrable
  exact localLeFull.trans (by
    simpa [mass, stage] using
      (requestedTimeReplayV2Stage_uniformLocalCompactnessBudget
        stage).2.2.2)

private theorem localReplayV2FiniteObservedTrajectory_ordered_increment_sq_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (a b : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
    (hab : a.1 ≤ b.1) :
    dist
        (localReplayV2FiniteObservedTrajectory replay observed index a)
        (localReplayV2FiniteObservedTrajectory replay observed index b) ^ 2 ≤
      (b.1 - a.1) *
        localReplayV2FiniteObservedHalfHolderEnergy lineage observed := by
  let stage := replay.current index
  let activeObserved := observed.filter (fun wave => wave ∈ stage.modes)
  have activeSubset : activeObserved ⊆ stage.modes := by
    intro wave waveMem
    exact (Finset.mem_filter.mp waveMem).2
  have activeZeroFree : ∀ wave ∈ activeObserved, wave ≠ 0 := by
    intro wave waveMem waveZero
    subst wave
    exact stage.zero_not_mem (activeSubset waveMem)
  have evolves :
      ∀ t ∈ Icc a.1 b.1,
        HasDerivAt stage.trajectory
          (finiteStateVorticityGenerator
            stage.modes ν.coeff (stage.trajectory t)) t := by
    intro t tMem
    exact (stage.physical t
      ⟨a.2.1.trans tMem.1, tMem.2.trans b.2.2⟩).1
  have summedIncrementLe :=
    finiteGalerkinFiniteInventory_timeIncrement_sq_le_negativeOneMass
      stage.modes activeObserved activeSubset activeZeroFree
      ν.coeff stage.trajectory a.1 b.1 hab evolves
  have observedNormSqLe :
      dist
          (localReplayV2FiniteObservedTrajectory replay observed index a)
          (localReplayV2FiniteObservedTrajectory replay observed index b) ^ 2 ≤
        ∑ wave ∈ activeObserved,
          ‖stage.trajectory b.1 wave - stage.trajectory a.1 wave‖ ^ 2 := by
    let incrementMass :=
      ∑ wave ∈ activeObserved,
        ‖stage.trajectory b.1 wave - stage.trajectory a.1 wave‖ ^ 2
    have incrementMassNonneg : 0 ≤ incrementMass :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have coordinateSqLe :
        ∀ wave : {wave : IntegerWavevector // wave ∈ observed},
          ‖stage.trajectory a.1 wave.1 - stage.trajectory b.1 wave.1‖ ^ 2 ≤
            incrementMass := by
      intro wave
      by_cases waveMem : wave.1 ∈ stage.modes
      · have activeMem : wave.1 ∈ activeObserved :=
          Finset.mem_filter.mpr ⟨wave.2, waveMem⟩
        simpa [incrementMass, norm_sub_rev] using
          (Finset.single_le_sum
            (fun later _ => sq_nonneg
              ‖stage.trajectory b.1 later - stage.trajectory a.1 later‖)
            activeMem)
      · have aZero := (stage.physical a.1 a.2).2.1 wave.1 waveMem
        have bZero := (stage.physical b.1 b.2).2.1 wave.1 waveMem
        simp [aZero, bZero, incrementMassNonneg]
    have normLeSqrt :
        ‖localReplayV2FiniteObservedTrajectory replay observed index a -
            localReplayV2FiniteObservedTrajectory replay observed index b‖ ≤
          Real.sqrt incrementMass := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
      intro wave
      exact (Real.le_sqrt (norm_nonneg _) incrementMassNonneg).2
        (coordinateSqLe wave)
    rw [dist_eq_norm]
    calc
      ‖localReplayV2FiniteObservedTrajectory replay observed index a -
          localReplayV2FiniteObservedTrajectory replay observed index b‖ ^ 2 ≤
        (Real.sqrt incrementMass) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 normLeSqrt
      _ = incrementMass := Real.sq_sqrt incrementMassNonneg
  have localBudgetLe :=
    localReplayV2_negativeOneMass_interval_le_ceiling
      replay index a b hab
  have activeMultiplierLe :
      (∑ wave ∈ activeObserved, integerWaveViscousMultiplier wave) ≤
        finiteObservedMultiplierMass observed := by
    simpa [activeObserved] using
      activeObservedMultiplier_le observed stage.modes
  have intervalNonneg :
      0 ≤ ∫ t in a.1..b.1,
        finiteStateVorticityNegativeOneMass stage.modes
          (finiteStateVorticityGenerator
            stage.modes ν.coeff (stage.trajectory t)) := by
    apply intervalIntegral.integral_nonneg hab
    intro t tMem
    exact finiteStateVorticityNegativeOneMass_nonneg _ _
  have intervalLengthNonneg : 0 ≤ b.1 - a.1 := sub_nonneg.mpr hab
  calc
    dist
        (localReplayV2FiniteObservedTrajectory replay observed index a)
        (localReplayV2FiniteObservedTrajectory replay observed index b) ^ 2 ≤
      (∑ wave ∈ activeObserved,
        ‖stage.trajectory b.1 wave - stage.trajectory a.1 wave‖ ^ 2) :=
      observedNormSqLe
    _ ≤
      (b.1 - a.1) *
        (∑ wave ∈ activeObserved, integerWaveViscousMultiplier wave) *
        ∫ t in a.1..b.1,
          finiteStateVorticityNegativeOneMass stage.modes
            (finiteStateVorticityGenerator
              stage.modes ν.coeff (stage.trajectory t)) := summedIncrementLe
    _ ≤
      (b.1 - a.1) * finiteObservedMultiplierMass observed *
        sourceOwnedLocalReplayV2NegativeOneCeiling lineage := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          activeMultiplierLe intervalLengthNonneg)
        localBudgetLe intervalNonneg
        (mul_nonneg intervalLengthNonneg
          (finiteObservedMultiplierMass_nonneg observed))
    _ =
      (b.1 - a.1) *
        localReplayV2FiniteObservedHalfHolderEnergy lineage observed := by
      simp [localReplayV2FiniteObservedHalfHolderEnergy, mul_assoc]

theorem localReplayV2FiniteObservedTrajectory_increment_sq_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (first second :
      Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    dist
        (localReplayV2FiniteObservedTrajectory replay observed index first)
        (localReplayV2FiniteObservedTrajectory replay observed index second) ^ 2 ≤
      dist first second *
        localReplayV2FiniteObservedHalfHolderEnergy lineage observed := by
  by_cases order : first.1 ≤ second.1
  · have ordered :=
      localReplayV2FiniteObservedTrajectory_ordered_increment_sq_le
        replay observed index first second order
    have distanceEq : dist first second = second.1 - first.1 := by
      rw [Subtype.dist_eq, Real.dist_eq]
      rw [abs_of_nonpos (sub_nonpos.mpr order)]
      ring
    simpa only [distanceEq] using ordered
  · have reverseOrder : second.1 ≤ first.1 := le_of_not_ge order
    have ordered :=
      localReplayV2FiniteObservedTrajectory_ordered_increment_sq_le
        replay observed index second first reverseOrder
    have distanceEq : dist first second = first.1 - second.1 := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact abs_of_nonneg (sub_nonneg.mpr reverseOrder)
    rw [distanceEq]
    simpa only [dist_comm] using ordered

theorem localReplayV2FiniteObservedTrajectory_halfHolder_dist
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (first second :
      Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    dist
        (localReplayV2FiniteObservedTrajectory replay observed index first)
        (localReplayV2FiniteObservedTrajectory replay observed index second) ≤
      (localReplayV2FiniteObservedHalfHolderConstant lineage observed : ℝ) *
        dist first second ^ (1 / 2 : ℝ) := by
  let energy :=
    localReplayV2FiniteObservedHalfHolderEnergy lineage observed
  have energyNonneg : 0 ≤ energy :=
    localReplayV2FiniteObservedHalfHolderEnergy_nonneg lineage observed
  have productNonneg : 0 ≤ dist first second * energy :=
    mul_nonneg dist_nonneg energyNonneg
  have squareLe :
      dist
          (localReplayV2FiniteObservedTrajectory replay observed index first)
          (localReplayV2FiniteObservedTrajectory replay observed index second) ^ 2 ≤
        dist first second * energy := by
    simpa [energy] using
      localReplayV2FiniteObservedTrajectory_increment_sq_le
        replay observed index first second
  have distanceLeSqrt :=
    (Real.le_sqrt dist_nonneg productNonneg).2 squareLe
  calc
    dist
        (localReplayV2FiniteObservedTrajectory replay observed index first)
        (localReplayV2FiniteObservedTrajectory replay observed index second) ≤
      Real.sqrt (dist first second * energy) := distanceLeSqrt
    _ = Real.sqrt energy * Real.sqrt (dist first second) := by
      rw [mul_comm]
      exact Real.sqrt_mul energyNonneg _
    _ =
      (localReplayV2FiniteObservedHalfHolderConstant lineage observed : ℝ) *
        dist first second ^ (1 / 2 : ℝ) := by
      change Real.sqrt energy * Real.sqrt (dist first second) =
        Real.sqrt energy * dist first second ^ (1 / 2 : ℝ)
      simp only [Real.sqrt_eq_rpow]

def localReplayV2FiniteObservedPathFamily
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector) :
    Set
      (BoundedContinuousFunction
        (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
        (FiniteObservedCoefficientState observed)) :=
  Set.range fun index : ℕ =>
    localReplayV2FiniteObservedBoundedPath replay observed index

theorem localReplayV2FiniteObservedPathFamily_equicontinuous
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector) :
    Equicontinuous
      (fun member : localReplayV2FiniteObservedPathFamily replay observed =>
        (member.1 :
          Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage) →
            FiniteObservedCoefficientState observed)) := by
  let holderConstant : ℝ :=
    localReplayV2FiniteObservedHalfHolderConstant lineage observed
  let modulus : ℝ → ℝ := fun radius => holderConstant * Real.sqrt |radius|
  have modulusContinuous : Continuous modulus :=
    continuous_const.mul (Real.continuous_sqrt.comp continuous_abs)
  have modulusTendsToZero : Tendsto modulus (𝓝 0) (𝓝 0) := by
    have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
    have modulusZero : modulus 0 = 0 := by simp [modulus]
    nth_rewrite 2 [← modulusZero]
    exact atZero
  apply Metric.equicontinuous_of_continuity_modulus
    modulus modulusTendsToZero
  intro first second member
  rcases member with ⟨function, ⟨index, functionEq⟩⟩
  subst function
  change
    dist
        (localReplayV2FiniteObservedTrajectory replay observed index first)
        (localReplayV2FiniteObservedTrajectory replay observed index second) ≤
      modulus (dist first second)
  calc
    _ ≤
      (localReplayV2FiniteObservedHalfHolderConstant lineage observed : ℝ) *
        dist first second ^ (1 / 2 : ℝ) :=
      localReplayV2FiniteObservedTrajectory_halfHolder_dist
        replay observed index first second
    _ = modulus (dist first second) := by
      simp [modulus, holderConstant, abs_of_nonneg dist_nonneg,
        Real.sqrt_eq_rpow]

/-- The complete V2 finite-observation family has compact uniform closure
on the source-generated local horizon. -/
theorem localReplayV2FiniteObservedPathFamily_isCompact_closure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (observed : Finset IntegerWavevector) :
    IsCompact (closure
      (localReplayV2FiniteObservedPathFamily replay observed)) := by
  let coefficientBall : Set (FiniteObservedCoefficientState observed) :=
    Metric.closedBall 0
      (Real.sqrt (sourceOwnedLocalReplayV2EnstrophyCeiling lineage))
  apply BoundedContinuousFunction.arzela_ascoli
    coefficientBall (isCompact_closedBall _ _)
  · intro function time functionMem
    rcases functionMem with ⟨index, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact localReplayV2FiniteObservedTrajectory_norm_le_ceiling
      replay observed index time
  · exact localReplayV2FiniteObservedPathFamily_equicontinuous
      replay observed

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalFiniteObservedCompactness
end NavierStokes
end SaturationMonoid
