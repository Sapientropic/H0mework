import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.EulerFibre

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPhysical
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped Topology ENNReal

open private centreLimit half_centre_strong from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit

local notation "q₀" => (1/4 : ℝ)
local notation "r₀" => (q₀/2)
local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection
local notation "Y" => countedNormalizedField
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "s₀" => fun c => star (BurnolCompletedMellinCoordinate.value c)
local notation "scale" => fun c (n : Nat) =>
  (Real.log ((n+2 : Nat) : ℝ) : ℂ)*((n+2 : Nat) : ℂ)^(-s₀ c)
local notation "whole" => fun c => floorFromResponses c+riemannZeta (s₀ c) • elementarySource c
local notation "delta" => fun c (n : Nat) => whole c-compensated c (n+2)
local notation "S'" => TemperedDistribution ℝ ℂ

/-- The original compact projection uses just the centre's complete mass.
The exterior keeps the literal original Hilbert projection. -/
def physicalProjectionFromCentre : (L¹ × BurnolL2) →L[ℂ] BurnolPaAmbientCarrier :=
  ((L1.integralCLM' ℂ (μ := (volume : Measure ℝ))).smulRight
      ((2 : ℂ) • P ConstantDual.seed)).comp (ContinuousLinearMap.fst ℂ L¹ BurnolL2) +
    burnolEvenAmbientProjection.comp (ContinuousLinearMap.snd ℂ L¹ BurnolL2)

/-- An actual physical cutoff gives the integrable centre and Hilbert exterior. -/
def splitAtPhysicalCutoff (radius : ℝ) (value : BurnolL2) : L¹ × BurnolL2 :=
  let centre := originalPhysicalCutoff radius value
  ((originalPhysicalCutoff_integrable radius value).toL1 (centre : ℝ → ℂ), value-centre)

private theorem cutoff_inside_quarter (radius : ℝ) (inside : radius ≤ q₀) (value : BurnolL2) :
    originalPhysicalCutoff q₀ (originalPhysicalCutoff radius value) = originalPhysicalCutoff radius value := by
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn q₀ (originalPhysicalCutoff radius value),
    originalPhysicalCutoff_coeFn radius value] with x large small
  rw [large]
  by_cases member : x ∈ symmetricInterval q₀
  · rw [indicator_of_mem member]
  · have missing : x ∉ symmetricInterval radius := fun h => member (abs_le.mp ((abs_le.mpr h).trans inside))
    rw [indicator_of_notMem member, small, indicator_of_notMem missing]

/-- The continuous centre and exterior consumer recovers the original
projection at every actual cutoff inside its constant gap. -/
theorem original_physical_projection_from_split (radius : ℝ) (inside : radius ≤ q₀)
    (value : BurnolL2) :
    physicalProjectionFromCentre (splitAtPhysicalCutoff radius value) = P value := by
  let centre := originalPhysicalCutoff radius value
  let integrableCentre := (originalPhysicalCutoff_integrable radius value).toL1 (centre : ℝ → ℂ)
  have support : burnolQuarterZeroExtension (burnolQuarterRestriction centre) = centre :=
    cutoff_inside_quarter radius inside value
  have compact := actual_compact_projection (burnolQuarterRestriction centre)
  rw [support, Constructor.mean_integral] at compact
  have mean : (∫ x : ℝ in symmetricInterval q₀, (burnolQuarterRestriction centre) x) =
      ∫ x : ℝ, centre x := by
    calc
      _ = ∫ x in symmetricInterval q₀, centre x :=
        integral_congr_ae (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q₀) centre)
      _ = _ := by
        rw [← integral_indicator (measurableSet_symmetricInterval q₀)]
        have cut := originalPhysicalCutoff_coeFn q₀ centre
        change (burnolQuarterZeroExtension (burnolQuarterRestriction centre) : ℝ → ℂ) =ᵐ[volume] _ at cut
        rw [support] at cut
        exact integral_congr_ae cut.symm
  have valueIntegral : L1.integralCLM' ℂ integrableCentre = ∫ x : ℝ, centre x := by
    rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
    exact integral_congr_ae (originalPhysicalCutoff_integrable radius value).coeFn_toL1
  change (L1.integralCLM' ℂ integrableCentre) • ((2 : ℂ) • P ConstantDual.seed)+P (value-centre) = P value
  rw [valueIntegral, smul_smul, mul_comm (∫ x : ℝ, centre x) (2 : ℂ)]
  change ((2 : ℂ)*(∫ x : ℝ, centre x)) • P (burnolQuarterZeroExtension (intervalConstant q₀))+
    P (value-centre) = _
  rw [← mean, ← compact, map_sub]
  abel

/-- The complete mixed field uses the paid original centre and exterior at
the same cutoff, including when the whole field is outside L². -/
def countedHomogeneousSplit (c : BurnolCompletedMellinCoordinate) : L¹ × BurnolL2 :=
  (centreLimit c, (-(1/2 : ℂ)) • burnolRadiusNormalizedUnitTail (barC c) r₀ (by norm_num))

theorem actual_counted_mixed_source_graph (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => ((((scale c n)⁻¹ • delta c n : BurnolL2) : S'),
      splitAtPhysicalCutoff r₀ (Y c n))) atTop (𝓝 (0, countedHomogeneousSplit c)) := by
  have source := (actual_counted_weak_euler_fibre c).fst_nhds
  exact source.prodMk_nhds ((half_centre_strong c).prodMk_nhds (actual_normalized_counted_half_exterior c))

/-- The continuous extension on the actual mixed field computes the original K. -/
theorem actual_homogeneous_physical_projection (c : BurnolCompletedMellinCoordinate) :
    physicalProjectionFromCentre (countedHomogeneousSplit c) = K c := by
  have field := (actual_counted_mixed_source_graph c).snd_nhds
  have calculated := (physicalProjectionFromCentre.continuous.tendsto (countedHomogeneousSplit c)).comp field
  apply tendsto_nhds_unique (calculated.congr' (Eventually.of_forall fun n =>
    original_physical_projection_from_split r₀ (by norm_num) (Y c n)))
  simpa only [countedNormalizedField, map_smul] using actual_scaled_counted_physical_limit c

local instance splitPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance splitCompactRangeComplete : CompleteSpace burnolCompactCoPoissonClosedRange.toSubmodule :=
  IsComplete.completeSpace_coe burnolCompactCoPoissonClosedRange.isClosed.isComplete

/-- The original infinite Pa projection consumes the same mixed limit. -/
theorem actual_homogeneous_pa_projection (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto
      (physicalProjectionFromCentre (countedHomogeneousSplit c)) = 0 := by
  rw [actual_homogeneous_physical_projection]
  exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero)

/-- The original physical read recovers the coefficient on the actual
homogeneous line at the exact original zero. -/
theorem actual_homogeneous_coefficient_recovery (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (a b : ℂ) :
    physicalProjectionFromCentre (a • countedHomogeneousSplit c) =
      physicalProjectionFromCentre (b • countedHomogeneousSplit c) ↔ a = b := by
  rw [map_smul, map_smul, actual_homogeneous_physical_projection]
  refine ⟨fun equal => ?_, fun equal => by rw [equal]⟩
  have live := (burnolZeroPaRieszState_ne_zero_iff_evaluator_ne_zero c zero).2
    (burnolCompletedMellinEvaluator_nonzero_at_zero c zero)
  have physicalNonzero : K c ≠ 0 := fun gone => live (Subtype.ext gone)
  have difference : (a-b) • K c = 0 := by rw [sub_smul, equal, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp difference).resolve_right physicalNonzero)

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
