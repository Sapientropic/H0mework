import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.Linearity
import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.GreenClosedRange

/-! Finite Volterra contacts generated directly from the original Pa inverse source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

/-- The finite contact is a bounded readout of the actual Tate-recovered source. -/
def burnolPaSourceContact (coordinate : BurnolCompletedMellinCoordinate)
    (t : ℝ) (positive : 0 < t) : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  (-(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1)) •
    ((burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf -
      burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf).comp
        (burnolTateReciprocalL2.comp burnolMobiusSourceL2))

theorem burnolPaSourceContact_eq_integral (coordinate : BurnolCompletedMellinCoordinate)
    (t : ℝ) (positive : 0 < t) (upper : t ≤ 4) (p : BurnolPaAmbientCarrier) :
    burnolPaSourceContact coordinate t positive p =
      -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
        ∫ u : ℝ in t..4, (u : ℂ) ^ (-coordinate.value) *
          burnolTateReciprocalL2 (burnolMobiusSourceL2 p) u := by
  simp only [burnolPaSourceContact, smul_apply,
    ContinuousLinearMap.comp_apply, sub_apply, smul_eq_mul,
    burnolRadiusMellinTailEvaluator_eq_integral]
  rw [intervalIntegral.integral_Ioi_sub_Ioi
    (burnolRadiusMellinWeight_integrableOn_tail t positive coordinate.value
      coordinate.rightHalf (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) upper]

theorem burnolPaSourceContact_compact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    burnolPaSourceContact coordinate t (lt_of_lt_of_le (by norm_num) inside.1)
      (burnolCompactAdditivePhysicalState source) =
        (1 / 2 : ℂ) * burnolFirstSourceCoefficient coordinate source t := by
  rw [burnolPaSourceContact_eq_integral coordinate t _ inside.2, burnolCompactPa_tate_source]
  have same :
      (∫ u : ℝ in t..4, burnolFirstSourceDensity coordinate source u) =
      (2 : ℂ) * ∫ u : ℝ in t..4,
        (u : ℂ) ^ (-coordinate.value) * source.1.toLp 2 volume u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [source.1.coeFn_toLp 2 volume] with u read hu
    have interval : t < u ∧ u ≤ 4 := by simpa only [uIoc_of_le inside.2, mem_Ioc] using hu
    unfold burnolFirstSourceDensity
    rw [max_eq_right (show (1 / 8 : ℝ) ≤ u by linarith [inside.1]), read]
    ring
  unfold burnolFirstSourceCoefficient
  rw [max_eq_right (show (1 / 8 : ℝ) ≤ t by linarith [inside.1]), same]
  ring

theorem burnolPaSourceContact_outer (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) :
    burnolPaSourceContact coordinate 4 (by norm_num) p = 0 := by
  rw [burnolPaSourceContact_eq_integral coordinate 4 (by norm_num) le_rfl]
  simp


private theorem pa_in_compact_closure (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    p ∈ (LinearMap.range burnolCompactAdditivePhysicalLinear).topologicalClosure := by
  have generator (i : BurnolCompactCoPoissonGeneratorIndex) :
      burnolCompactCoPoissonGenerator i ∈ LinearMap.range burnolCompactAdditivePhysicalLinear := by
    rcases i with ⟨source, parity⟩
    fin_cases parity
    · exact ⟨source, rfl⟩
    · refine ⟨burnolCompactTateReciprocalSource source, ?_⟩
      apply Subtype.ext
      exact (burnolCompactFourierL2_eq_reciprocalL2 source).symm
  have lands (input : BurnolCompactCoPoissonLinearSource) :
      burnolCompactCoPoissonLanding input ∈ LinearMap.range burnolCompactAdditivePhysicalLinear := by
    induction input using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (LinearMap.range burnolCompactAdditivePhysicalLinear).zero_mem
    | add left right hl hr =>
      rw [map_add]
      exact (LinearMap.range burnolCompactAdditivePhysicalLinear).add_mem hl hr
    | single i c =>
      rw [burnolCompactCoPoissonLanding_single]
      exact (LinearMap.range burnolCompactAdditivePhysicalLinear).smul_mem c (generator i)
  have included : LinearMap.range burnolCompactCoPoissonLanding ≤
      (LinearMap.range burnolCompactAdditivePhysicalLinear).topologicalClosure := by
    rintro _ ⟨input, rfl⟩
    exact (LinearMap.range burnolCompactAdditivePhysicalLinear).le_topologicalClosure (lands input)
  exact (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    included (LinearMap.range burnolCompactAdditivePhysicalLinear).isClosed_topologicalClosure inside

/-- The inner contact is forced by the same source Mellin coefficient on the full original Pa. -/
theorem burnolPaSourceContact_inner (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolPaSourceContact coordinate (1 / 4) (by norm_num) p =
      -((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
        burnolPaResolventSourceCoefficient coordinate p := by
  let left := burnolPaSourceContact coordinate (1 / 4) (by norm_num)
  let right := -((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) •
    burnolPaResolventSourceCoefficient coordinate
  have onCompact (source : burnolCompactAnnulusSource) :
      left (burnolCompactAdditivePhysicalState source) =
        right (burnolCompactAdditivePhysicalState source) := by
    simp only [left, right, smul_apply, smul_eq_mul]
    rw [burnolPaSourceContact_compact coordinate source (by constructor <;> norm_num),
      burnolCompactSourceGreen_endpoint coordinate source]
    ring
  have closes : closure (Set.range burnolCompactAdditivePhysicalLinear) ⊆ {v | left v = right v} :=
    closure_minimal (by rintro _ ⟨source, rfl⟩; exact onCompact source)
      (isClosed_eq left.continuous right.continuous)
  exact closes (pa_in_compact_closure p inside)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
