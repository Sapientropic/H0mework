import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Source.Division
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Source.Lift
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.GeneratorResolventOperator

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Division
open Complex MeasureTheory Set Filter Function
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open SourceGeneratedComplexFeaturePerfectification
open scoped InnerProductSpace Topology
noncomputable section

def rawAction {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re) : BurnolL2 →L[ℂ] BurnolL2 :=
  burnolDirectRightResolventCLM (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)

def rawIterate {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re) (k : Nat) : BurnolL2 →L[ℂ] BurnolL2 :=
  (rawAction observation rightHalf)^k

theorem state_raw {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat) :
    quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k) =
      (2:ℂ) • rawIterate observation rightHalf k (burnolCompactAdditiveL2 source) := by
  have rq : 1/4 < (selectedCoPoissonMuntzParameter observation).re := by
    change 1/4 < (observation.coordinate/2).re
    rw [Complex.div_re]; norm_num; linarith
  induction k with
  | zero => simpa only [rawIterate, pow_zero, one_apply_eq_self] using
      state_zero_raw observation nontrivial source
  | succ k ih =>
      rw [state_succ, quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct _ rq, ih]
      change rawAction observation rightHalf ((2:ℂ) • _) = _
      rw [map_smul]
      simp only [rawIterate, pow_succ', mul_apply_eq_comp]

def fourierRead {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re) : BurnolL2 →L[ℂ] ℂ :=
  (burnolCompletedMellinEvaluator (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)).comp
    ((evenFaceFourier burnolUnscaledCommonGapRadius).toContinuousLinearMap.comp
      burnolEvenAmbientProjection)

theorem compact_raw_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (atMost : k ≤ generatedRiemannXiZeroOrder owner observation.coordinate) :
    rawIterate observation rightHalf k (burnolCompactAdditiveL2 source) ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  have h := compact_physical observation nontrivial rightHalf source k atMost
  rw [state_raw observation nontrivial rightHalf source k] at h
  have scaled := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).smul_mem (2:ℂ)⁻¹ h
  rw [inv_smul_smul₀ (by norm_num : (2:ℂ) ≠ 0)] at scaled
  exact scaled

theorem compact_raw_fourier_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (before : k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    fourierRead observation rightHalf
      (rawIterate observation rightHalf k (burnolCompactAdditiveL2 source)) = 0 := by
  have physical := compact_physical observation nontrivial rightHalf source k (Nat.le_of_lt before)
  have h := compact_fourier_zero_of_physical observation nontrivial rightHalf source k before physical
  have projection := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k), physical⟩ : BurnolPaAmbientCarrier)
  change burnolEvenAmbientProjection _ = _ at projection
  have full : fourierRead observation rightHalf
      (quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
        (state observation nontrivial source k)) = 0 := by
    unfold fourierRead
    simp only [ContinuousLinearMap.comp_apply, projection]
    exact h
  rw [state_raw observation nontrivial rightHalf source k, map_smul, smul_eq_mul] at full
  exact (mul_eq_zero.mp full).resolve_left (by norm_num)

private theorem generator_raw {index : BurnolCompactCoPoissonGeneratorIndex} :
    ∃ source : burnolCompactAnnulusSource,
      (burnolCompactCoPoissonGenerator index : BurnolL2) = burnolCompactAdditiveL2 source := by
  rcases index with ⟨source, parity⟩
  fin_cases parity
  · exact ⟨source, rfl⟩
  · refine ⟨burnolCompactTateReciprocalSource source, ?_⟩
    change fourierL2 (burnolCompactAdditiveL2 source) = _
    exact burnolCompactFourierL2_eq_reciprocalL2 source

private theorem pa_le_closed {closed : ClosedSubmodule ℂ BurnolPaAmbientCarrier}
    (generators : ∀ index, burnolCompactCoPoissonGenerator index ∈ closed) :
    burnolCompactCoPoissonClosedRange.toSubmodule ≤ closed.toSubmodule := by
  change (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure ≤ _
  apply Submodule.topologicalClosure_minimal _ _ closed.isClosed
  rintro value ⟨source, rfl⟩
  induction source using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using closed.zero_mem
  | add left right leftLaw rightLaw =>
      simpa only [map_add] using closed.add_mem leftLaw rightLaw
  | single index coefficient =>
      rw [burnolCompactCoPoissonLanding_single]
      exact closed.smul_mem coefficient (generators index)

theorem whole_pa_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (k : Nat) (atMost : k ≤ generatedRiemannXiZeroOrder owner observation.coordinate)
    (value : BurnolPaAmbientCarrier) (member : value ∈ burnolCompactCoPoissonClosedRange) :
    rawIterate observation rightHalf k (value : BurnolL2) ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let closed : ClosedSubmodule ℂ BurnolPaAmbientCarrier :=
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).comap
      ((rawIterate observation rightHalf k).comp
        (Submodule.subtypeL (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule))
  apply (pa_le_closed (closed := closed) ?_) member
  intro index
  obtain ⟨source, same⟩ := generator_raw (index := index)
  change rawIterate observation rightHalf k (burnolCompactCoPoissonGenerator index : BurnolL2) ∈
    evenBurnolClosedFace burnolUnscaledCommonGapRadius
  rw [same]
  exact compact_raw_physical observation nontrivial rightHalf source k atMost

theorem whole_pa_fourier_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (k : Nat) (before : k < generatedRiemannXiZeroOrder owner observation.coordinate)
    (value : BurnolPaAmbientCarrier) (member : value ∈ burnolCompactCoPoissonClosedRange) :
    fourierRead observation rightHalf (rawIterate observation rightHalf k (value : BurnolL2)) = 0 := by
  let closed : ClosedSubmodule ℂ BurnolPaAmbientCarrier :=
    (⊥ : ClosedSubmodule ℂ ℂ).comap
      ((fourierRead observation rightHalf).comp ((rawIterate observation rightHalf k).comp
        (Submodule.subtypeL (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)))
  have h : value ∈ closed := (pa_le_closed (closed := closed) (by
    intro index
    obtain ⟨source, same⟩ := generator_raw (index := index)
    change fourierRead observation rightHalf
      (rawIterate observation rightHalf k (burnolCompactCoPoissonGenerator index : BurnolL2)) ∈
      (⊥ : ClosedSubmodule ℂ ℂ)
    rw [same]
    simpa only [ClosedSubmodule.mem_bot] using
      compact_raw_fourier_zero observation nontrivial rightHalf source k before)) member
  exact h

theorem actual_comb_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (n k : Nat) (atMost : k ≤ generatedRiemannXiZeroOrder owner observation.coordinate) :
    rawIterate observation rightHalf k (burnolPaCombApproximation n : BurnolL2) ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius :=
  whole_pa_physical observation nontrivial rightHalf k atMost
    (burnolPaCombApproximation n) (burnolPaCombApproximation_mem n)

theorem actual_comb_fourier_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (n k : Nat) (before : k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    fourierRead observation rightHalf (rawIterate observation rightHalf k (burnolPaCombApproximation n : BurnolL2)) = 0 :=
  whole_pa_fourier_zero observation nontrivial rightHalf k before
    (burnolPaCombApproximation n) (burnolPaCombApproximation_mem n)

theorem actual_comb_iterate_readback {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re) (n k : Nat) :
    quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (quarterFeatureCompletionRightResolventIterate (selectedCoPoissonMuntzParameter observation) k
        (CombSource.actualCombLift n (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))) =
      rawIterate observation rightHalf k (burnolPaCombApproximation n : BurnolL2) := by
  induction k with
  | zero =>
      simpa only [quarterFeatureCompletionRightResolventIterate, rawIterate, pow_zero,
        one_apply_eq_self] using (CombSource.actualCombLift_readback n
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
  | succ k ih =>
      have rq : 1/4 < (selectedCoPoissonMuntzParameter observation).re := by
        change 1/4 < (observation.coordinate/2).re
        rw [Complex.div_re]; norm_num; linarith
      change quarterMellinFeatureCompletionEvenAdditive _
        (quarterFeatureCompletionRightResolvent _ _) = _
      rw [quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct _ rq, ih]
      change rawAction observation rightHalf _ = _
      simp only [rawIterate, pow_succ', mul_apply_eq_comp]

theorem actual_full_jordan_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re) (n k : Nat)
    (atMost : k ≤ generatedRiemannXiZeroOrder owner observation.coordinate) :
    quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (quarterFeatureCompletionRightResolventIterate (selectedCoPoissonMuntzParameter observation) k
        (CombSource.actualCombLift n (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))) ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  rw [actual_comb_iterate_readback observation nontrivial rightHalf n k]
  exact actual_comb_physical observation nontrivial rightHalf n k atMost

theorem actual_full_jordan_fourier_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re) (n k : Nat)
    (before : k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    burnolCompletedMellinEvaluator (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
      (evenFaceFourier burnolUnscaledCommonGapRadius
        ⟨quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
          (quarterFeatureCompletionRightResolventIterate (selectedCoPoissonMuntzParameter observation) k
            (CombSource.actualCombLift n (selectedCoPoissonMuntzParameter observation)
              (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
              (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))),
          actual_full_jordan_physical observation nontrivial rightHalf n k (Nat.le_of_lt before)⟩) = 0 := by
  let value : BurnolPaAmbientCarrier := ⟨_, actual_full_jordan_physical observation nontrivial rightHalf n k (Nat.le_of_lt before)⟩
  have h : fourierRead observation rightHalf (value : BurnolL2) = 0 := by
    dsimp only [value]
    rw [actual_comb_iterate_readback observation nontrivial rightHalf n k]
    exact actual_comb_fourier_zero observation nontrivial rightHalf n k before
  unfold fourierRead at h
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [show burnolEvenAmbientProjection (value : BurnolL2) = value from
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value] at h
  exact h


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Division
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
