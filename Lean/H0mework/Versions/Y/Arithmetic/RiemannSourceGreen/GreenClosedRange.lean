import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.CompactEnergy

/-! Continuity extends the signed source Green identity to every point of the original Pa closed range. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private def compactLinear : burnolCompactAnnulusSource →ₗ[ℂ] BurnolPaAmbientCarrier where
  toFun := burnolCompactAdditivePhysicalState
  map_add' a b := by
    apply Subtype.ext
    change burnolCompactAdditiveL2 (a + b) = burnolCompactAdditiveL2 a + burnolCompactAdditiveL2 b
    simp_rw [← compactQuarterMellinAdditiveEvenRechart_eq (3 / 8) (by norm_num) (by norm_num)]
    change quarterMellinAdditiveEvenRechartLinear (3 / 8)
        (coPoissonQuarterMellinConvergentMap (3 / 8) (by norm_num) (by norm_num) (a.1 + b.1)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c a := by
    apply Subtype.ext
    change burnolCompactAdditiveL2 (c • a) = c • burnolCompactAdditiveL2 a
    simp_rw [← compactQuarterMellinAdditiveEvenRechart_eq (3 / 8) (by norm_num) (by norm_num)]
    change quarterMellinAdditiveEvenRechartLinear (3 / 8)
        (coPoissonQuarterMellinConvergentMap (3 / 8) (by norm_num) (by norm_num) (c • a.1)) = _
    rw [map_smul, map_smul]
    rfl

private theorem pa_in_compact_closure (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    p ∈ (LinearMap.range compactLinear).topologicalClosure := by
  have generator (i : BurnolCompactCoPoissonGeneratorIndex) :
      burnolCompactCoPoissonGenerator i ∈ LinearMap.range compactLinear := by
    rcases i with ⟨source, parity⟩
    fin_cases parity
    · exact ⟨source, rfl⟩
    · refine ⟨burnolCompactTateReciprocalSource source, ?_⟩
      apply Subtype.ext
      exact (burnolCompactFourierL2_eq_reciprocalL2 source).symm
  have lands (input : BurnolCompactCoPoissonLinearSource) :
      burnolCompactCoPoissonLanding input ∈ LinearMap.range compactLinear := by
    induction input using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (LinearMap.range compactLinear).zero_mem
    | add left right hl hr =>
      rw [map_add]
      exact (LinearMap.range compactLinear).add_mem hl hr
    | single i c =>
      rw [burnolCompactCoPoissonLanding_single]
      exact (LinearMap.range compactLinear).smul_mem c (generator i)
  have included : LinearMap.range burnolCompactCoPoissonLanding ≤
      (LinearMap.range compactLinear).topologicalClosure := by
    rintro _ ⟨input, rfl⟩
    exact (LinearMap.range compactLinear).le_topologicalClosure (lands input)
  exact (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    included (LinearMap.range compactLinear).isClosed_topologicalClosure inside

theorem burnolPaSourceGreen (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    let psi := burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate ⟨p, inside⟩));
    -4 * (inner ℂ psi (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))).re =
      (2 * coordinate.value.re - 1) * ‖psi‖ ^ 2 +
        (1 / 2 : ℝ) * ‖((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
          burnolPaResolventSourceCoefficient coordinate p‖ ^ 2 := by
  let project := burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto
  let corrected : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    (burnolTateReciprocalL2.comp burnolMobiusSourceL2).comp ((burnolPaSourceCorrection coordinate).comp project)
  let original : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    burnolTateReciprocalL2.comp burnolMobiusSourceL2
  let left : BurnolPaAmbientCarrier → ℝ := fun v => -4 * (inner ℂ (corrected v) (original v)).re
  let right : BurnolPaAmbientCarrier → ℝ := fun v =>
    (2 * coordinate.value.re - 1) * ‖corrected v‖ ^ 2 +
      (1 / 2 : ℝ) * ‖((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
        burnolPaResolventSourceCoefficient coordinate v‖ ^ 2
  have leftContinuous : Continuous left := by
    exact (Complex.continuous_re.comp (corrected.continuous.inner original.continuous)).const_mul _
  have rightContinuous : Continuous right := by
    exact ((corrected.continuous.norm.pow 2).const_mul _).add
      ((((burnolPaResolventSourceCoefficient coordinate).continuous.const_mul _).norm.pow 2).const_mul _)
  have onCompact (source : burnolCompactAnnulusSource) :
      left (burnolCompactAdditivePhysicalState source) = right (burnolCompactAdditivePhysicalState source) := by
    have compactInside : burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange := by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))
    have projectRead : project (burnolCompactAdditivePhysicalState source) =
        ⟨burnolCompactAdditivePhysicalState source, compactInside⟩ :=
      burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self
        ⟨burnolCompactAdditivePhysicalState source, compactInside⟩
    dsimp only [left, right, corrected, original, ContinuousLinearMap.comp_apply]
    rw [projectRead]
    exact burnolCompactPaSourceGreen coordinate source
  have closes : closure (Set.range compactLinear) ⊆ {v | left v = right v} :=
    closure_minimal (by rintro _ ⟨source, rfl⟩; exact onCompact source)
      (isClosed_eq leftContinuous rightContinuous)
  have atP : left p = right p := closes (pa_in_compact_closure p inside)
  have projectRead : project p = ⟨p, inside⟩ :=
    burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨p, inside⟩
  dsimp only [left, right, corrected, original, ContinuousLinearMap.comp_apply] at atP
  rw [projectRead] at atP
  exact atP

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
