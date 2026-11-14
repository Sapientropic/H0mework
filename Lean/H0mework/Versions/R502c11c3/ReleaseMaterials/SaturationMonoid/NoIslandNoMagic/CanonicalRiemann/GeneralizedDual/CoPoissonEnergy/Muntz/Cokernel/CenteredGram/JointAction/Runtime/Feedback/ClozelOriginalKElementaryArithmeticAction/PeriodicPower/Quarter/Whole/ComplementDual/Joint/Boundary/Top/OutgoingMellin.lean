import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.CountingMellin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.UnitSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.OutgoingMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.CountingMellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open OriginalUnitMellinSource.Resolvent
open scoped Topology InnerProductSpace
open private actual_tate_mellin from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.UnitSource
open private power_measurable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "T" => burnolTateReciprocalL2
local notation "V" => sourceVolterraResolvent

/-- The full outgoing action, before every quarter cut, reads its genuine Mellin scalar. -/
theorem actual_outgoing_mellin (c d : BurnolCompletedMellinCoordinate) (v : BurnolL2) (m : ℂ)
    (between : d.value.re < c.value.re) (source : HasMellin (v : ℝ → ℂ) (1 - d.value) m) :
    HasMellin (V c v : ℝ → ℂ) (1 - d.value) (2 / (d.value - c.value) * m) := by
  have first := actual_tate_mellin v (1 - d.value) m source
  rw [sub_sub_cancel] at first
  have acted := actual_R_mellin c (T v) d.value m first between
  have last := actual_tate_mellin (burnolDirectRightResolvent (c.value / 2) (T v)) d.value _ acted
  exact last

/-- The original native cotest keeps its zeta factor at every actual outgoing order. -/
theorem actual_native_outgoing_mellin (c d : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (j : ℕ) (between : d.value.re < c.value.re) :
    HasMellin (nativeOutgoingCotest c j : ℝ → ℂ) (1 - d.value)
      ((2 / (d.value - c.value))^j * riemannZeta d.value *
        burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2)) := by
  have source : HasMellin (((V c)^j) (pairedCotestForward c) : ℝ → ℂ) (1 - d.value)
      ((2 / (d.value - c.value))^j * riemannZeta d.value *
        burnolAmbientCompletedMellinEvaluator d (physicalCotest c : BurnolL2)) := by
    induction j with
    | zero => simpa only [pow_zero, one_apply_eq_self, one_mul] using actual_counted_cotest_mellin c d zero
    | succ j previous =>
      have next := actual_outgoing_mellin c d (((V c)^j) (pairedCotestForward c)) _ between previous
      rw [pow_succ', mul_apply_eq_comp]
      convert next using 1
      rw [pow_succ]
      ring
  rw [actual_native_outgoing_cotest c j]
  exact source

/-- A real right approach uses two honest source moments to dominate the entire positive axis. -/
theorem actual_mellin_right_continuity (v : BurnolL2) (z : ℂ) (radius : ℝ)
    (left : MellinConvergent (v : ℝ → ℂ) z)
    (right : MellinConvergent (v : ℝ → ℂ) (z + (radius : ℂ))) :
    ContinuousWithinAt (fun t : ℝ => mellin (v : ℝ → ℂ) (z + (t : ℂ))) (Icc 0 radius) 0 := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let integrand := fun (t : ℝ) (x : ℝ) => (x : ℂ) ^ (z + (t : ℂ) - 1) * v x
  let bound := fun x : ℝ => ‖(x : ℂ) ^ (z - 1) * v x‖ +
    ‖(x : ℂ) ^ (z + (radius : ℂ) - 1) * v x‖
  have measured : ∀ᶠ t : ℝ in 𝓝[Icc 0 radius] 0, AEStronglyMeasurable (integrand t) μ := by
    apply Eventually.of_forall
    intro t
    exact (((power_measurable (z + (t : ℂ) - 1)).mul (Lp.stronglyMeasurable v).measurable).aestronglyMeasurable).restrict
  have bounded : ∀ᶠ t : ℝ in 𝓝[Icc 0 radius] 0, ∀ᵐ x : ℝ ∂μ, ‖integrand t x‖ ≤ bound x := by
    filter_upwards [self_mem_nhdsWithin] with t inside
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x xPositive
    dsimp only [integrand, bound]
    by_cases large : 1 ≤ x
    · apply le_add_of_nonneg_of_le (norm_nonneg _)
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos xPositive]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le large
      simp only [sub_re, add_re, ofReal_re, one_re]
      linarith [inside.2]
    · apply le_add_of_le_of_nonneg _ (norm_nonneg _)
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos xPositive]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_ge xPositive (le_of_not_ge large)
      simp only [sub_re, add_re, ofReal_re, one_re]
      linarith [inside.1]
  have budget : Integrable bound μ := left.norm.add right.norm
  have regular : ∀ᵐ x : ℝ ∂μ, ContinuousWithinAt (fun t : ℝ => integrand t x) (Icc 0 radius) 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x xPositive
    have power : ContinuousAt (fun u : ℂ => (x : ℂ)^u) (z + (0 : ℂ) - 1) :=
      ((hasDerivAt_id (z + (0 : ℂ) - 1)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr xPositive.ne'))).continuousAt
    have input : ContinuousAt (fun t : ℝ => z + (t : ℂ) - 1) 0 := by fun_prop
    have phase : ContinuousAt (fun t : ℝ => (x : ℂ) ^ (z + (t : ℂ) - 1)) 0 :=
      power.comp (f := fun t : ℝ => z + (t : ℂ) - 1) (x := (0 : ℝ)) input
    exact (phase.mul_const (v x)).continuousWithinAt
  have generated := continuousWithinAt_of_dominated measured bounded budget regular
  change ContinuousWithinAt (fun t : ℝ => ∫ x : ℝ, integrand t x ∂μ) (Icc 0 radius) 0
  exact generated

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Top.OutgoingMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
