import H0mework.NavierStokes.Restart.NonlinearRegenerationCascade

/-!
# Quadratic rate obstruction for nonlinear restart regeneration

Finite accumulated physical time makes the actual restart durations
summable.  The preceding cascade theorem makes the norms of the same-edge
nonlinear Duhamel regenerations nonsummable.  Discrete Hölder therefore
forces divergence of the source-owned quadratic rate

```text
‖nonlinear regeneration on edge i‖² / physical duration i.
```

This is a quadratic physical-time obstruction on the actual native run;
neither a caller-chosen partition nor a persistence modulus appears.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationRateObstruction

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade

noncomputable section

/-- Bounded source-generated elapsed time makes the actual durations of the
next-contact receipts summable.  This is the same source-owned time carried
by `wholeRestartNonlinearRegenerationState` at each index. -/
theorem elapsedTime_bddAbove_forces_nextContactDuration_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))) :
    Summable fun index =>
      (run initial index).nextContact.time.1 := by
  rcases elapsedBounded with ⟨upper, upperBound⟩
  have contactSummable :
      Summable fun index =>
        (run initial index).contact.time.1 := by
    apply summable_of_sum_le
    · intro index
      exact (run initial index).contact.time_pos.le
    · intro indices
      obtain ⟨length, indicesSubset⟩ :=
        Finset.exists_nat_subset_range indices
      calc
        (∑ index ∈ indices,
            (run initial index).contact.time.1) ≤
            ∑ index ∈ Finset.range length,
              (run initial index).contact.time.1 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            indicesSubset
            (fun index indexMem indexNotMem =>
              (run initial index).contact.time_pos.le)
        _ = elapsedTime initial length := by
          rw [elapsedTime_eq_sum_contactTime]
        _ ≤ upper := upperBound ⟨length, rfl⟩
  have shifted := contactSummable.comp_injective Nat.succ_injective
  apply shifted.congr
  intro index
  rfl

/-- Quadratic nonlinear regeneration rate on one source-owned physical
restart window.  Its denominator is strictly positive by construction. -/
def wholeRestartNonlinearRegenerationRateSquare
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  wholeRestartNonlinearRegenerationNorm initial index ^ 2 /
    (run initial index).nextContact.time.1

theorem wholeRestartNonlinearRegenerationRateSquare_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartNonlinearRegenerationRateSquare initial index := by
  exact div_nonneg (sq_nonneg _)
    (run initial index).nextContact.time_pos.le

private theorem regenerationNorm_summable_of_duration_and_rate_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (durationSummable :
      Summable fun index =>
        (run initial index).nextContact.time.1)
    (rateSummable :
      Summable
        (wholeRestartNonlinearRegenerationRateSquare initial)) :
    Summable
      (wholeRestartNonlinearRegenerationNorm initial) := by
  let durationRoot : ℕ → ℝ := fun index =>
    Real.sqrt (run initial index).nextContact.time.1
  let normalizedRegeneration : ℕ → ℝ := fun index =>
    wholeRestartNonlinearRegenerationNorm initial index /
      Real.sqrt (run initial index).nextContact.time.1
  have durationRootNonneg :
      ∀ index, 0 ≤ durationRoot index := fun index =>
    Real.sqrt_nonneg _
  have normalizedRegenerationNonneg :
      ∀ index, 0 ≤ normalizedRegeneration index := by
    intro index
    exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have durationRootSquareSummable :
      Summable fun index => durationRoot index ^ (2 : ℝ) := by
    apply durationSummable.congr
    intro index
    dsimp [durationRoot]
    rw [Real.rpow_two,
      Real.sq_sqrt (run initial index).nextContact.time_pos.le]
  have normalizedRegenerationSquareSummable :
      Summable fun index =>
        normalizedRegeneration index ^ (2 : ℝ) := by
    apply rateSummable.congr
    intro index
    dsimp [normalizedRegeneration,
      wholeRestartNonlinearRegenerationRateSquare]
    rw [Real.rpow_two, div_pow,
      Real.sq_sqrt (run initial index).nextContact.time_pos.le]
  have productSummable :
      Summable fun index =>
        durationRoot index * normalizedRegeneration index :=
    Real.summable_mul_of_Lp_Lq_of_nonneg
      Real.HolderConjugate.two_two
      durationRootNonneg normalizedRegenerationNonneg
      durationRootSquareSummable
      normalizedRegenerationSquareSummable
  apply productSummable.congr
  intro index
  dsimp [durationRoot, normalizedRegeneration]
  field_simp [ne_of_gt
    (Real.sqrt_pos.2 (run initial index).nextContact.time_pos)]

/-- Main quadratic hard-gate reduction.  Finite physical-time accumulation
forces the actual nonlinear Duhamel regeneration rate squares to be
nonsummable. -/
theorem elapsedTime_bddAbove_forces_nonlinearRegenerationRateSquare_not_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))) :
    ¬ Summable
      (wholeRestartNonlinearRegenerationRateSquare initial) := by
  intro rateSummable
  have durationSummable :=
    elapsedTime_bddAbove_forces_nextContactDuration_summable
      initial elapsedBounded
  have regenerationSummable :=
    regenerationNorm_summable_of_duration_and_rate_summable
      initial durationSummable rateSummable
  exact
    (elapsedTime_bddAbove_forces_nonlinearRegenerationNorm_not_summable
      initial elapsedBounded) regenerationSummable

/-- Premise-free exhaustion: the native whole-flow time axis is unbounded,
or the same run generates a nonsummable quadratic nonlinear-regeneration
rate. -/
theorem elapsedTime_unbounded_or_nonlinearRegenerationRateSquare_not_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ¬ BddAbove (Set.range (elapsedTime initial)) ∨
      ¬ Summable
        (wholeRestartNonlinearRegenerationRateSquare initial) := by
  by_cases elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))
  · exact Or.inr
      (elapsedTime_bddAbove_forces_nonlinearRegenerationRateSquare_not_summable
        initial elapsedBounded)
  · exact Or.inl elapsedBounded

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationRateObstruction
end NavierStokes
end SaturationMonoid
