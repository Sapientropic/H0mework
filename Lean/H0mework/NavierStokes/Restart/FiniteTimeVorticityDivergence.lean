import H0mework.NavierStokes.Restart.FiniteTimeObstruction
import H0mework.NavierStokes.Restart.NonlinearRegenerationRateObstruction
import H0mework.NavierStokes.Restart.NonlinearRegenerationCascade
import H0mework.NavierStokes.Restart.VelocityWeakEndpoint

/-!
# Tailwise vorticity divergence at a finite whole-restart accumulation

Bounded accumulated physical time makes the actual source-owned contact
durations summable.  Since every contact is selected in the late half of its
own generated whole-flow horizon, all source horizons tend to zero.  Their
reciprocal barrier slopes therefore tend to infinity.

The barrier is not an independent analytic certificate: it is computed from
the quantized coefficient ceiling of the same actual contact.  Below any fixed
physical vorticity bound only finitely many generated kernel cores can occur,
so the corresponding barrier slopes share one finite source-generated bound.
Consequently the complete physical vorticity mass tends to infinity along the
entire native tail, not merely along an externally selected subsequence.

In particular every cofinal endpoint subsequence already used by the velocity
weak endpoint inherits this divergence.  No cutoff, subsequence, mass bound,
target solution, continuation witness, or blow-up branch enters the producer
mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open
  ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationRateObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint

noncomputable section

/-! ## Collapse of every actual local horizon -/

/-- Bounded elapsed time makes the actual current-contact durations summable.
The existing next-contact theorem already pays the tail; the initial contact
is the only extra finite term. -/
theorem elapsedTime_bddAbove_forces_contactTime_summable
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Summable fun index => (run initial index).contact.time.1 := by
  have tailSummable :
      Summable fun index => (run initial (index + 1)).contact.time.1 := by
    change Summable fun index => (run initial index).nextContact.time.1
    exact
      elapsedTime_bddAbove_forces_nextContactDuration_summable
        initial elapsedBounded
  exact
    (summable_nat_add_iff
      (f := fun index => (run initial index).contact.time.1) 1).mp
        tailSummable

/-- Every actual source contact time tends to zero on a bounded elapsed
write-chain. -/
theorem tendsto_contactTime_zero_of_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun index => (run initial index).contact.time.1)
      atTop (nhds 0) :=
  (elapsedTime_bddAbove_forces_contactTime_summable
    initial elapsedBounded).tendsto_atTop_zero

/-- The source-generated whole-flow horizons themselves tend to zero.  This
uses the late-half contact law of the same actual receipt, not a caller-chosen
restart time. -/
theorem tendsto_wholeRestartDuration_zero_of_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun index => (run initial index).duration)
      atTop (nhds 0) := by
  refine squeeze_zero'
    (f := fun index => (run initial index).duration)
    (g := fun index => 2 * (run initial index).contact.time.1)
    ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun index =>
      (run initial index).receipt.requestedTimePos.le
  · exact Filter.Eventually.of_forall fun index => by
      linarith [run_contact_time_half_duration_lt initial index]
  · simpa using
      (tendsto_contactTime_zero_of_elapsedTime_bddAbove
        initial elapsedBounded).const_mul 2

/-- The exact source horizon generated from each actual contact tends to
zero as well.  This is the duration of the next native current, so the first
possibly differently constructed seed duration plays no role. -/
theorem tendsto_wholeRestartGeneratedHorizon_zero_of_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto
      (fun index => (run initial (index + 1)).duration)
      atTop (nhds 0) := by
  refine squeeze_zero'
    (f := fun index => (run initial (index + 1)).duration)
    (g := fun index =>
      2 * (run initial (index + 1)).contact.time.1)
    ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun index =>
      (run initial (index + 1)).receipt.requestedTimePos.le
  · exact Filter.Eventually.of_forall fun index => by
      have late := run_contact_time_half_duration_lt initial (index + 1)
      linarith
  · have shiftedContactTendsto :
        Tendsto
          (fun index => (run initial (index + 1)).contact.time.1)
          atTop (nhds 0) :=
      (summable_nat_add_iff
        (f := fun index => (run initial index).contact.time.1) 1).mpr
          (elapsedTime_bddAbove_forces_contactTime_summable
            initial elapsedBounded)
        |>.tendsto_atTop_zero
    simpa only [mul_zero] using shiftedContactTendsto.const_mul 2

/-! ## Reciprocal source barrier and finite-level exclusion -/

/-- Collapse of every generated horizon is exactly divergence of the actual
reciprocal source barrier. -/
theorem tendsto_restartBarrierSlope_atTop_of_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto (restartBarrierSlope initial) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro bound
  let target := max bound 0 + 1
  have targetPos : 0 < target := by
    dsimp only [target]
    linarith [le_max_right bound 0]
  let small := 1 / (2 * target)
  have smallPos : 0 < small := by
    exact one_div_pos.mpr (mul_pos (by norm_num) targetPos)
  have durationSmall :
      ∀ᶠ index in atTop,
        (run initial (index + 1)).duration < small :=
    (tendsto_order.1
      (tendsto_wholeRestartGeneratedHorizon_zero_of_elapsedTime_bddAbove
        initial elapsedBounded)).2 small smallPos
  filter_upwards [durationSmall] with index indexSmall
  have nextDurationEq :
      (run initial (index + 1)).duration =
        wholeRestartDuration (run initial index).contact := by
    rw [run_succ, GeneratedWholeRestartCurrent.next_duration]
  rw [nextDurationEq] at indexSmall
  have slopePos : 0 < restartBarrierSlope initial index :=
    restartBarrierSlope_pos initial index
  have reciprocalLt :
      1 / (2 * restartBarrierSlope initial index) <
        1 / (2 * target) := by
    simpa only [wholeRestartDuration, sourceOwnedWholeStateDuration,
      restartBarrierSlope, restartCoefficientCeiling, small] using
      indexSmall
  have targetLtSlope : target < restartBarrierSlope initial index := by
    have doubled :
        2 * target < 2 * restartBarrierSlope initial index :=
      lt_of_one_div_lt_one_div
        (mul_pos (by norm_num) slopePos) reciprocalLt
    linarith
  exact (le_max_left bound 0).trans
    ((lt_add_one (max bound 0)).le.trans targetLtSlope.le)

/-- Below one supplied physical mass level, the source can visit only the
finitely many quantized kernel cores up to the corresponding natural ceiling;
their exact barrier slopes therefore satisfy this internally computed bound.
This is a pointwise implication, not a boundedness premise on the run. -/
theorem restartBarrierSlope_le_generatedBound_of_physicalMass_le
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ)
    (physicalBound : ℝ)
    (massLe :
      restartPhysicalVorticityMass initial index ≤ physicalBound) :
    let levelBound := Nat.ceil (max (physicalBound + 1) 0)
    let coefficientBound :=
      ∑ level ∈ Finset.range (levelBound + 1),
        sourceOwnedLocalQuadraticCoefficient nu (level : ℝ)
    restartBarrierSlope initial index ≤
      coefficientBound * (levelBound : ℝ) ^ 2 + 1 := by
  dsimp only
  let level :=
    wholeRestartCoefficientLevel (run initial index).contact
  let levelBound := Nat.ceil (max (physicalBound + 1) 0)
  let coefficientBound :=
    ∑ later ∈ Finset.range (levelBound + 1),
      sourceOwnedLocalQuadraticCoefficient nu (later : ℝ)
  have rawLe :
      wholeRestartRawCoefficientCeiling (run initial index).contact ≤
        max (physicalBound + 1) 0 := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    have massAddLe :
        restartPhysicalVorticityMass initial index + 1 ≤
          physicalBound + 1 := by
      linarith
    exact massAddLe.trans (le_max_left (physicalBound + 1) 0)
  have levelLe : level ≤ levelBound := by
    exact Nat.ceil_mono rawLe
  have levelMem : level ∈ Finset.range (levelBound + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le levelLe)
  have coefficientLe :
      sourceOwnedLocalQuadraticCoefficient nu (level : ℝ) ≤
        coefficientBound := by
    exact Finset.single_le_sum
      (f := fun later : ℕ =>
        sourceOwnedLocalQuadraticCoefficient nu (later : ℝ))
      (s := Finset.range (levelBound + 1))
      (fun later laterMem =>
        sourceOwnedLocalQuadraticCoefficient_nonneg nu (later : ℝ))
      levelMem
  have levelCastLe : (level : ℝ) ≤ levelBound := by
    exact_mod_cast levelLe
  have coefficientNonneg :
      0 ≤ sourceOwnedLocalQuadraticCoefficient nu (level : ℝ) :=
    sourceOwnedLocalQuadraticCoefficient_nonneg nu (level : ℝ)
  have coefficientBoundNonneg : 0 ≤ coefficientBound := by
    exact Finset.sum_nonneg fun later laterMem =>
      sourceOwnedLocalQuadraticCoefficient_nonneg nu (later : ℝ)
  have squareLe : (level : ℝ) ^ 2 ≤ (levelBound : ℝ) ^ 2 := by
    exact
      (sq_le_sq₀ (Nat.cast_nonneg level) (Nat.cast_nonneg levelBound)).2
        levelCastLe
  have productLe :
      sourceOwnedLocalQuadraticCoefficient nu (level : ℝ) *
          (level : ℝ) ^ 2 ≤
        coefficientBound * (levelBound : ℝ) ^ 2 := by
    exact mul_le_mul coefficientLe squareLe
      (sq_nonneg _) coefficientBoundNonneg
  have plusLe :
      sourceOwnedLocalQuadraticCoefficient nu (level : ℝ) *
            (level : ℝ) ^ 2 + 1 ≤
        coefficientBound * (levelBound : ℝ) ^ 2 + 1 := by
    linarith
  simpa only [restartBarrierSlope, restartQuadraticCoefficient,
    restartCoefficientCeiling, wholeRestartCoefficientCeiling,
    sourceOwnedWholeStateBarrierSlope, level, coefficientBound,
    levelBound] using plusLe

/-! ## Tailwise physical vorticity divergence -/

/-- Main strengthening of the finite-time obstruction: physical vorticity
mass tends to infinity along the entire actual native tail.  Thus every
cofinal source subsequence, rather than merely some selected indices, carries
the critical obstruction. -/
theorem tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    Tendsto (restartPhysicalVorticityMass initial) atTop atTop := by
  have barrierTendsto :=
    tendsto_restartBarrierSlope_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded
  apply Filter.tendsto_atTop.2
  intro physicalBound
  let levelBound := Nat.ceil (max (physicalBound + 1) 0)
  let coefficientBound :=
    ∑ level ∈ Finset.range (levelBound + 1),
      sourceOwnedLocalQuadraticCoefficient nu (level : ℝ)
  let barrierBound := coefficientBound * (levelBound : ℝ) ^ 2 + 1
  have barrierEventually :
      ∀ᶠ index in atTop,
        barrierBound + 1 ≤ restartBarrierSlope initial index :=
    Filter.tendsto_atTop.1 barrierTendsto (barrierBound + 1)
  filter_upwards [barrierEventually] with index barrierLarge
  have massNotLe :
      ¬ restartPhysicalVorticityMass initial index ≤ physicalBound := by
    intro massLe
    have barrierLe :=
      restartBarrierSlope_le_generatedBound_of_physicalMass_le
        initial index physicalBound massLe
    change restartBarrierSlope initial index ≤ barrierBound at barrierLe
    linarith
  exact (lt_of_not_ge massNotLe).le

/-- The exact endpoint subsequence used by the source-generated physical
velocity weak endpoint inherits the whole-tail vorticity divergence.  No
second endpoint or blow-up subsequence is selected. -/
theorem sourceGeneratedVelocityEndpoint_vorticityMass_tendsto_atTop
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let endpoint :=
      generatedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded
    Tendsto
      (fun index =>
        restartPhysicalVorticityMass
          initial (endpoint.subsequence index))
      atTop atTop := by
  dsimp only
  let endpoint :=
    generatedWholeRestartVelocityWeakEndpointAtAccumulation
      initial elapsedBounded
  exact
    (tendsto_restartPhysicalVorticityMass_atTop_of_elapsedTime_bddAbove
      initial elapsedBounded).comp
        endpoint.subsequence_strictMono.tendsto_atTop

/-- Divergent physical-vorticity mass excludes a strong whole-vorticity landing of the original
actual contact process.  This theorem belongs to the finite native run itself; boundary-world and
endpoint-macro presentations may consume it but do not own its authority. -/
theorem vorticityMass_tendsto_atTop_excludes_strongContactLanding
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (vorticityDiverges :
      Tendsto (restartPhysicalVorticityMass initial) atTop atTop) :
    ∀ candidate : ComplexVorticityHilbertState,
      ¬ Tendsto
          (fun index => (run initial index).contact.physicalState)
          atTop (nhds candidate) := by
  intro candidate contactTendsto
  have statesBounded :
      Bornology.IsBounded
        (Set.range fun index =>
          (run initial index).contact.physicalState) :=
    Metric.isBounded_range_of_tendsto _ contactTendsto
  obtain ⟨upper, upperBound⟩ := statesBounded.exists_norm_le
  have contactNormBounded :
      BddAbove
        (Set.range fun index =>
          ‖(run initial index).contact.physicalState‖) := by
    refine ⟨upper, ?_⟩
    rintro _ ⟨index, rfl⟩
    exact upperBound _ ⟨index, rfl⟩
  exact
    (Filter.not_bddAbove_of_tendsto_atTop vorticityDiverges)
      (restartPhysicalVorticityMass_bddAbove_of_contact_norm_bddAbove
        initial contactNormBounded)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence
end NavierStokes
end SaturationMonoid
