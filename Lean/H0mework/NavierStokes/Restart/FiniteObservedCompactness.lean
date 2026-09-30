import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Holder
import H0mework.NavierStokes.GeneratedPaths.FiniteObservedCompactness
import H0mework.NavierStokes.Restart.CanonicalReplay

/-!
# Finite-observation compactness of the generated whole restart replay

The canonical whole-state replay supplies one actual unforced Galerkin orbit
at every punctured-cube radius and a single source-generated compactness
budget for the complete family.  Every fixed finite Fourier observation
therefore has compact uniform closure on the common physical horizon.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteObservedCompactness

open scoped BigOperators ENNReal NNReal Topology Interval

open Set Filter MeasureTheory
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
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

def wholeRestartFiniteObservedTrajectory
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    FiniteObservedCoefficientState observed :=
  finiteObservedCoefficientState observed
    ((replay.current index).trajectory time.1)

theorem wholeRestartFiniteObservedTrajectory_continuous
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    Continuous
      (wholeRestartFiniteObservedTrajectory replay observed index) := by
  apply continuous_pi
  intro wave
  rw [continuous_iff_continuousAt]
  intro time
  have evolves := ((replay.current index).physical time.1 time.2).1
  exact
    (complexVorticityTrajectoryWave_hasDerivAt
      (replay.current index).trajectory time.1
      (finiteStateVorticityGenerator
        (wholeRestartModes index) ν.coeff
        ((replay.current index).trajectory time.1))
      wave.1 evolves).continuousAt.comp continuousAt_subtype_val

def wholeRestartFiniteObservedBoundedPath
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) (wholeRestartDuration contact))
      (FiniteObservedCoefficientState observed) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨wholeRestartFiniteObservedTrajectory replay observed index,
      wholeRestartFiniteObservedTrajectory_continuous
        replay observed index⟩

theorem wholeRestartFiniteObservedTrajectory_norm_le_ceiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    ‖wholeRestartFiniteObservedTrajectory replay observed index time‖ ≤
      Real.sqrt (wholeRestartCoefficientCeiling contact) := by
  let stage := replay.current index
  have currentEnstrophyLe :=
    (stage.uniformScalarBudget).1 time.1 time.2
  have ambientSqLe :
      ‖stage.trajectory time.1‖ ^ 2 ≤
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes index) (stage.trajectory time.1) :=
    complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      (wholeRestartModes index) (stage.trajectory time.1)
      (stage.physical time.1 time.2).2.1
  have ambientNormLe :
      ‖stage.trajectory time.1‖ ≤
        Real.sqrt (wholeRestartCoefficientCeiling contact) :=
    (Real.le_sqrt (norm_nonneg _)
      (wholeRestartCoefficientCeiling_pos contact).le).2
      (ambientSqLe.trans currentEnstrophyLe)
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro wave
  exact
    (lp.norm_apply_le_norm (by norm_num)
      (stage.trajectory time.1) wave.1).trans ambientNormLe

def wholeRestartFiniteObservedHalfHolderEnergy
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (_replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) : ℝ :=
  finiteObservedMultiplierMass observed *
    wholeRestartNegativeOneCeiling contact

theorem wholeRestartFiniteObservedHalfHolderEnergy_nonneg
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) :
    0 ≤ wholeRestartFiniteObservedHalfHolderEnergy replay observed :=
  mul_nonneg
    (finiteObservedMultiplierMass_nonneg observed)
    (wholeRestartNegativeOneCeiling_nonneg contact)

def wholeRestartFiniteObservedHalfHolderConstant
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) : NNReal :=
  ⟨Real.sqrt
      (wholeRestartFiniteObservedHalfHolderEnergy replay observed),
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

private theorem wholeRestart_negativeOneMass_interval_le_ceiling
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (index : ℕ)
    (a b : Icc (0 : ℝ) (wholeRestartDuration contact))
    (hab : a.1 ≤ b.1) :
    (∫ t in a.1..b.1,
      finiteStateVorticityNegativeOneMass
        (wholeRestartModes index)
        (finiteStateVorticityGenerator
          (wholeRestartModes index) ν.coeff
          ((replay.current index).trajectory t))) ≤
      wholeRestartNegativeOneCeiling contact := by
  let stage := replay.current index
  let mass : ℝ → ℝ := fun t =>
    finiteStateVorticityNegativeOneMass (wholeRestartModes index)
      (finiteStateVorticityGenerator
        (wholeRestartModes index) ν.coeff (stage.trajectory t))
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
        HasDerivAt stage.trajectory
          (finiteStateVorticityGenerator
            (wholeRestartModes index) ν.coeff (stage.trajectory t)) t := by
    intro t tMem
    exact (stage.physical t tMem).1
  have massContinuous :
      ContinuousOn mass (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
    finiteGalerkinGeneratorNegativeOneMass_continuousOn
      (wholeRestartModes index) ν.coeff stage.trajectory 0
      (wholeRestartDuration contact) evolves
  have massIntegrable :
      IntervalIntegrable mass volume 0 (wholeRestartDuration contact) :=
    ContinuousOn.intervalIntegrable_of_Icc
      (wholeRestartDuration_pos contact).le massContinuous
  have localLeFull :
      (∫ t in a.1..b.1, mass t) ≤
        ∫ t in (0 : ℝ)..wholeRestartDuration contact, mass t := by
    apply intervalIntegral.integral_mono_interval
    · exact a.2.1
    · exact hab
    · exact b.2.2
    · exact Filter.Eventually.of_forall fun t =>
        finiteStateVorticityNegativeOneMass_nonneg _ _
    · exact massIntegrable
  exact localLeFull.trans (by
    simpa [mass, stage] using (stage.uniformScalarBudget).2.2.2)

private theorem wholeRestartFiniteObservedTrajectory_ordered_increment_sq_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (a b : Icc (0 : ℝ) (wholeRestartDuration contact))
    (hab : a.1 ≤ b.1) :
    dist
        (wholeRestartFiniteObservedTrajectory replay observed index a)
        (wholeRestartFiniteObservedTrajectory replay observed index b) ^ 2 ≤
      (b.1 - a.1) *
        wholeRestartFiniteObservedHalfHolderEnergy replay observed := by
  let stage := replay.current index
  let modes := wholeRestartModes index
  let activeObserved := observed.filter (fun wave => wave ∈ modes)
  have activeSubset : activeObserved ⊆ modes := by
    intro wave waveMem
    exact (Finset.mem_filter.mp waveMem).2
  have activeZeroFree : ∀ wave ∈ activeObserved, wave ≠ 0 := by
    intro wave waveMem waveZero
    subst wave
    exact (zero_not_mem_puncturedIntegerWaveFrequencyCube index)
      (activeSubset waveMem)
  have evolves :
      ∀ t ∈ Icc a.1 b.1,
        HasDerivAt stage.trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (stage.trajectory t)) t := by
    intro t tMem
    exact (stage.physical t
      ⟨a.2.1.trans tMem.1, tMem.2.trans b.2.2⟩).1
  have summedIncrementLe :=
    finiteGalerkinFiniteInventory_timeIncrement_sq_le_negativeOneMass
      modes activeObserved activeSubset activeZeroFree
      ν.coeff stage.trajectory a.1 b.1 hab evolves
  have observedNormSqLe :
      dist
          (wholeRestartFiniteObservedTrajectory replay observed index a)
          (wholeRestartFiniteObservedTrajectory replay observed index b) ^ 2 ≤
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
      by_cases waveMem : wave.1 ∈ modes
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
        ‖wholeRestartFiniteObservedTrajectory replay observed index a -
            wholeRestartFiniteObservedTrajectory replay observed index b‖ ≤
          Real.sqrt incrementMass := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
      intro wave
      exact (Real.le_sqrt (norm_nonneg _) incrementMassNonneg).2
        (coordinateSqLe wave)
    rw [dist_eq_norm]
    calc
      ‖wholeRestartFiniteObservedTrajectory replay observed index a -
          wholeRestartFiniteObservedTrajectory replay observed index b‖ ^ 2 ≤
        (Real.sqrt incrementMass) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 normLeSqrt
      _ = incrementMass := Real.sq_sqrt incrementMassNonneg
  have localBudgetLe :=
    wholeRestart_negativeOneMass_interval_le_ceiling
      replay index a b hab
  have activeMultiplierLe :
      (∑ wave ∈ activeObserved, integerWaveViscousMultiplier wave) ≤
        finiteObservedMultiplierMass observed := by
    simpa [activeObserved, modes] using
      activeObservedMultiplier_le observed modes
  have intervalNonneg :
      0 ≤ ∫ t in a.1..b.1,
        finiteStateVorticityNegativeOneMass modes
          (finiteStateVorticityGenerator
            modes ν.coeff (stage.trajectory t)) := by
    apply intervalIntegral.integral_nonneg hab
    intro t tMem
    exact finiteStateVorticityNegativeOneMass_nonneg _ _
  have intervalLengthNonneg : 0 ≤ b.1 - a.1 := sub_nonneg.mpr hab
  calc
    dist
        (wholeRestartFiniteObservedTrajectory replay observed index a)
        (wholeRestartFiniteObservedTrajectory replay observed index b) ^ 2 ≤
      (∑ wave ∈ activeObserved,
        ‖stage.trajectory b.1 wave - stage.trajectory a.1 wave‖ ^ 2) :=
      observedNormSqLe
    _ ≤
      (b.1 - a.1) *
        (∑ wave ∈ activeObserved, integerWaveViscousMultiplier wave) *
        ∫ t in a.1..b.1,
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν.coeff (stage.trajectory t)) := summedIncrementLe
    _ ≤
      (b.1 - a.1) * finiteObservedMultiplierMass observed *
        wholeRestartNegativeOneCeiling contact := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          activeMultiplierLe intervalLengthNonneg)
        localBudgetLe intervalNonneg
        (mul_nonneg intervalLengthNonneg
          (finiteObservedMultiplierMass_nonneg observed))
    _ =
      (b.1 - a.1) *
        wholeRestartFiniteObservedHalfHolderEnergy replay observed := by
      simp [wholeRestartFiniteObservedHalfHolderEnergy, mul_assoc]

theorem wholeRestartFiniteObservedTrajectory_increment_sq_le
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (first second : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    dist
        (wholeRestartFiniteObservedTrajectory replay observed index first)
        (wholeRestartFiniteObservedTrajectory replay observed index second) ^ 2 ≤
      dist first second *
        wholeRestartFiniteObservedHalfHolderEnergy replay observed := by
  by_cases order : first.1 ≤ second.1
  · have ordered :=
      wholeRestartFiniteObservedTrajectory_ordered_increment_sq_le
        replay observed index first second order
    have distanceEq : dist first second = second.1 - first.1 := by
      rw [Subtype.dist_eq, Real.dist_eq]
      rw [abs_of_nonpos (sub_nonpos.mpr order)]
      ring
    simpa only [distanceEq] using ordered
  · have reverseOrder : second.1 ≤ first.1 := le_of_not_ge order
    have ordered :=
      wholeRestartFiniteObservedTrajectory_ordered_increment_sq_le
        replay observed index second first reverseOrder
    have distanceEq : dist first second = first.1 - second.1 := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact abs_of_nonneg (sub_nonneg.mpr reverseOrder)
    rw [distanceEq]
    simpa only [dist_comm] using ordered

theorem wholeRestartFiniteObservedTrajectory_halfHolder_dist
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector)
    (index : ℕ)
    (first second : Icc (0 : ℝ) (wholeRestartDuration contact)) :
    dist
        (wholeRestartFiniteObservedTrajectory replay observed index first)
        (wholeRestartFiniteObservedTrajectory replay observed index second) ≤
      (wholeRestartFiniteObservedHalfHolderConstant replay observed : ℝ) *
        dist first second ^ (1 / 2 : ℝ) := by
  let energy := wholeRestartFiniteObservedHalfHolderEnergy replay observed
  have energyNonneg : 0 ≤ energy :=
    wholeRestartFiniteObservedHalfHolderEnergy_nonneg replay observed
  have productNonneg : 0 ≤ dist first second * energy :=
    mul_nonneg dist_nonneg energyNonneg
  have squareLe :
      dist
          (wholeRestartFiniteObservedTrajectory replay observed index first)
          (wholeRestartFiniteObservedTrajectory replay observed index second) ^ 2 ≤
        dist first second * energy := by
    simpa [energy] using
      wholeRestartFiniteObservedTrajectory_increment_sq_le
        replay observed index first second
  have distanceLeSqrt :=
    (Real.le_sqrt dist_nonneg productNonneg).2 squareLe
  calc
    dist
        (wholeRestartFiniteObservedTrajectory replay observed index first)
        (wholeRestartFiniteObservedTrajectory replay observed index second) ≤
      Real.sqrt (dist first second * energy) := distanceLeSqrt
    _ = Real.sqrt energy * Real.sqrt (dist first second) := by
      rw [mul_comm]
      exact Real.sqrt_mul energyNonneg _
    _ =
      (wholeRestartFiniteObservedHalfHolderConstant replay observed : ℝ) *
        dist first second ^ (1 / 2 : ℝ) := by
      change Real.sqrt energy * Real.sqrt (dist first second) =
        Real.sqrt energy * dist first second ^ (1 / 2 : ℝ)
      simp only [Real.sqrt_eq_rpow]

def wholeRestartFiniteObservedPathFamily
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) :
    Set
      (BoundedContinuousFunction
        (Icc (0 : ℝ) (wholeRestartDuration contact))
        (FiniteObservedCoefficientState observed)) :=
  Set.range fun index : ℕ =>
    wholeRestartFiniteObservedBoundedPath replay observed index

theorem wholeRestartFiniteObservedPathFamily_equicontinuous
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) :
    Equicontinuous
      (fun member :
          wholeRestartFiniteObservedPathFamily replay observed =>
        (member.1 :
          Icc (0 : ℝ) (wholeRestartDuration contact) →
            FiniteObservedCoefficientState observed)) := by
  let holderConstant : ℝ :=
    wholeRestartFiniteObservedHalfHolderConstant replay observed
  let modulus : ℝ → ℝ := fun radius =>
    holderConstant * Real.sqrt |radius|
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
        (wholeRestartFiniteObservedTrajectory
          replay observed index first)
        (wholeRestartFiniteObservedTrajectory
          replay observed index second) ≤
      modulus (dist first second)
  calc
    dist
        (wholeRestartFiniteObservedTrajectory
          replay observed index first)
        (wholeRestartFiniteObservedTrajectory
          replay observed index second) ≤
      (wholeRestartFiniteObservedHalfHolderConstant replay observed : ℝ) *
        dist first second ^ (1 / 2 : ℝ) :=
      wholeRestartFiniteObservedTrajectory_halfHolder_dist
        replay observed index first second
    _ = modulus (dist first second) := by
      simp [modulus, holderConstant, abs_of_nonneg dist_nonneg,
        Real.sqrt_eq_rpow]

/-- Every fixed finite observation of the complete actual restart replay
has compact uniform closure. -/
theorem wholeRestartFiniteObservedPathFamily_isCompact_closure
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (observed : Finset IntegerWavevector) :
    IsCompact (closure
      (wholeRestartFiniteObservedPathFamily replay observed)) := by
  let coefficientBall : Set (FiniteObservedCoefficientState observed) :=
    Metric.closedBall 0
      (Real.sqrt (wholeRestartCoefficientCeiling contact))
  apply BoundedContinuousFunction.arzela_ascoli
    coefficientBall (isCompact_closedBall _ _)
  · intro function time functionMem
    rcases functionMem with ⟨index, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact wholeRestartFiniteObservedTrajectory_norm_le_ceiling
      replay observed index time
  · exact wholeRestartFiniteObservedPathFamily_equicontinuous
      replay observed

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteObservedCompactness
end NavierStokes
end SaturationMonoid
