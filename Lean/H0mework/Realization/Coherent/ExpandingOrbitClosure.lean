import H0mework.Realization.Coherent.OrbitClosedDefectPort

/-!
# Expanding graph orbit: algebraic residual and topological admission

Let an actual integral feature land in an energy/measurement graph.  Suppose
one source-generated power orbit has bounded energy and measurement
`character ^ n`, with `‖character‖ > 1`.  Inverse-character normalization
then gives explicit points in the complexified range converging to every
vertical state with the chosen measurement.

If the literal integral feature also has energy-kernel contained in its
measurement-kernel, a nonzero vertical state is outside the algebraic
integral range but inside its complexified closure.  This is the exact
representation/compression residual; no classifier or target-zero premise
is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedExpandingGraphOrbitClosure

open SourceGeneratedIntegralCoherentCompletion
open SourceGeneratedIntegralOrbitClosedDefectPort
open scoped TensorProduct

noncomputable section

universe l h

def expandingRangeApproximant
    {L : Type l} [AddCommGroup L]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : L →ₗ[ℤ] WithLp 2 (H × ℂ))
    (event : ℕ → L) (character measurement : ℂ) (stage : ℕ) :
    WithLp 2 (H × ℂ) :=
  (measurement * character⁻¹ ^ stage) • feature (event stage)

theorem expandingRangeApproximant_mem_range
    {L : Type l} [AddCommGroup L]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : L →ₗ[ℤ] WithLp 2 (H × ℂ))
    (event : ℕ → L) (character measurement : ℂ) (stage : ℕ) :
    expandingRangeApproximant feature event character measurement stage ∈
      LinearMap.range (complexifiedFeature feature) := by
  refine ⟨(measurement * character⁻¹ ^ stage) ⊗ₜ[ℤ] event stage, ?_⟩
  simp [expandingRangeApproximant]

theorem expandingRangeApproximant_tendsto
    {L : Type l} [AddCommGroup L]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : L →ₗ[ℤ] WithLp 2 (H × ℂ))
    (event : ℕ → L) (character : ℂ)
    (state : WithLp 2 (H × ℂ))
    (energy_zero : state.fst = 0)
    (expanding : 1 < ‖character‖)
    (energy_norm : ∀ stage,
      ‖(feature (event stage)).fst‖ = ‖(feature (event 0)).fst‖)
    (measurement_pow : ∀ stage,
      (feature (event stage)).snd = character ^ stage) :
    Filter.Tendsto
      (expandingRangeApproximant feature event character state.snd)
      Filter.atTop (nhds state) := by
  have character_ne : character ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one expanding))
  have inverse_norm_lt_one : ‖character⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ expanding
  have scalar_norm_tendsto :
      Filter.Tendsto (fun stage : ℕ => ‖character⁻¹‖ ^ stage)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (norm_nonneg _) inverse_norm_lt_one
  have energy_tendsto :
      Filter.Tendsto
        (fun stage =>
          (expandingRangeApproximant
            feature event character state.snd stage).fst)
        Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have scaled := scalar_norm_tendsto.const_mul
      (‖state.snd‖ * ‖(feature (event 0)).fst‖)
    simpa only [mul_zero] using scaled.congr'
      (Filter.Eventually.of_forall fun stage => by
        simp only [expandingRangeApproximant, WithLp.smul_fst,
          norm_smul, norm_mul, norm_pow]
        rw [energy_norm stage]
        ring)
  have measurement_eq (stage : ℕ) :
      (expandingRangeApproximant
        feature event character state.snd stage).snd = state.snd := by
    simp only [expandingRangeApproximant, WithLp.smul_snd, smul_eq_mul,
      measurement_pow]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ character_ne,
      one_pow, mul_one]
  have measurement_tendsto :
      Filter.Tendsto
        (fun stage =>
          (expandingRangeApproximant
            feature event character state.snd stage).snd)
        Filter.atTop (nhds state.snd) := by
    simpa only [measurement_eq] using tendsto_const_nhds
  apply ((WithLp.homeomorphProd 2 H ℂ).isInducing.tendsto_nhds_iff).mpr
  change Filter.Tendsto
    (fun stage =>
      ((expandingRangeApproximant
          feature event character state.snd stage).fst,
        (expandingRangeApproximant
          feature event character state.snd stage).snd))
    Filter.atTop (nhds (state.fst, state.snd))
  simpa [energy_zero] using
    energy_tendsto.prodMk_nhds measurement_tendsto

theorem measurementOnly_mem_orbitClosedRange_of_expandingOrbit
    {L : Type l} [AddCommGroup L]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : L →ₗ[ℤ] WithLp 2 (H × ℂ))
    (event : ℕ → L) (character : ℂ)
    (state : WithLp 2 (H × ℂ))
    (energy_zero : state.fst = 0)
    (expanding : 1 < ‖character‖)
    (energy_norm : ∀ stage,
      ‖(feature (event stage)).fst‖ = ‖(feature (event 0)).fst‖)
    (measurement_pow : ∀ stage,
      (feature (event stage)).snd = character ^ stage) :
    state ∈ orbitClosedRange feature := by
  apply (orbitClosedRange feature).isClosed.mem_of_tendsto
    (expandingRangeApproximant_tendsto feature event character state
      energy_zero expanding energy_norm measurement_pow)
  exact Filter.Eventually.of_forall fun stage =>
    subset_closure (expandingRangeApproximant_mem_range
      feature event character state.snd stage)

theorem measurementOnly_not_mem_integralRange_of_kernel
    {L : Type l} [AddCommGroup L]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : L →ₗ[ℤ] WithLp 2 (H × ℂ))
    (state : WithLp 2 (H × ℂ))
    (energy_zero : state.fst = 0) (measurement_ne_zero : state.snd ≠ 0)
    (kernel : ∀ event : L, (feature event).fst = 0 →
      (feature event).snd = 0) :
    state ∉ LinearMap.range feature := by
  rintro ⟨event, readback⟩
  have eventEnergy : (feature event).fst = 0 := by
    calc
      (feature event).fst = state.fst :=
        congrArg (fun value : WithLp 2 (H × ℂ) => value.fst) readback
      _ = 0 := energy_zero
  apply measurement_ne_zero
  calc
    state.snd = (feature event).snd :=
      congrArg (fun value : WithLp 2 (H × ℂ) => value.snd) readback.symm
    _ = 0 := kernel event eventEnergy

theorem measurementOnly_not_mem_complexRange_of_kernel
    {C : Type l} [AddCommGroup C] [Module ℂ C]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : C →ₗ[ℂ] WithLp 2 (H × ℂ))
    (state : WithLp 2 (H × ℂ))
    (energy_zero : state.fst = 0) (measurement_ne_zero : state.snd ≠ 0)
    (kernel : ∀ source : C, (feature source).fst = 0 →
      (feature source).snd = 0) :
    state ∉ LinearMap.range feature := by
  rintro ⟨source, readback⟩
  have sourceEnergy : (feature source).fst = 0 := by
    calc
      (feature source).fst = state.fst :=
        congrArg (fun value : WithLp 2 (H × ℂ) => value.fst) readback
      _ = 0 := energy_zero
  apply measurement_ne_zero
  calc
    state.snd = (feature source).snd :=
      congrArg (fun value : WithLp 2 (H × ℂ) => value.snd) readback.symm
    _ = 0 := kernel source sourceEnergy

theorem measurementOnly_algebraicResidual_and_closedAdmission
    {L : Type l} [AddCommGroup L]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : L →ₗ[ℤ] WithLp 2 (H × ℂ))
    (event : ℕ → L) (character : ℂ)
    (state : WithLp 2 (H × ℂ))
    (energy_zero : state.fst = 0) (measurement_ne_zero : state.snd ≠ 0)
    (kernel : ∀ source : L, (feature source).fst = 0 →
      (feature source).snd = 0)
    (expanding : 1 < ‖character‖)
    (energy_norm : ∀ stage,
      ‖(feature (event stage)).fst‖ = ‖(feature (event 0)).fst‖)
    (measurement_pow : ∀ stage,
      (feature (event stage)).snd = character ^ stage) :
    state ∉ LinearMap.range feature ∧ state ∈ orbitClosedRange feature :=
  ⟨measurementOnly_not_mem_integralRange_of_kernel
      feature state energy_zero measurement_ne_zero kernel,
    measurementOnly_mem_orbitClosedRange_of_expandingOrbit
      feature event character state energy_zero expanding
      energy_norm measurement_pow⟩

theorem measurementOnly_complexResidual_and_closedAdmission
    {L : Type l} [AddCommGroup L]
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : L →ₗ[ℤ] WithLp 2 (H × ℂ))
    (event : ℕ → L) (character : ℂ)
    (state : WithLp 2 (H × ℂ))
    (energy_zero : state.fst = 0) (measurement_ne_zero : state.snd ≠ 0)
    (kernel : ∀ source : ComplexifiedCarrier L,
      (complexifiedFeature feature source).fst = 0 →
      (complexifiedFeature feature source).snd = 0)
    (expanding : 1 < ‖character‖)
    (energy_norm : ∀ stage,
      ‖(feature (event stage)).fst‖ = ‖(feature (event 0)).fst‖)
    (measurement_pow : ∀ stage,
      (feature (event stage)).snd = character ^ stage) :
    state ∉ LinearMap.range (complexifiedFeature feature) ∧
      state ∈ orbitClosedRange feature :=
  ⟨measurementOnly_not_mem_complexRange_of_kernel
      (complexifiedFeature feature) state energy_zero measurement_ne_zero kernel,
    measurementOnly_mem_orbitClosedRange_of_expandingOrbit
      feature event character state energy_zero expanding
      energy_norm measurement_pow⟩

end

end SourceGeneratedExpandingGraphOrbitClosure
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
