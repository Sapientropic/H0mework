import H0mework.Probability.Source.MomentMoment
import H0mework.Fock.SourceHistoryClock.GraphGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceVectorMoment

open scoped InnerProductSpace
noncomputable section
universe u
variable {ι : Type u} [Fintype ι] (p : PMF ι)

def massMap : SourceJointClockGraph.Carrier →ₗ[ℂ] ℂ :=
  (SourceMassCompletion.massRead.comp SourceJointClockGraph.joint).toLinearMap

def massClockCovariance (value : ι → SourceJointClockGraph.Carrier) : ℝ :=
  ∑ i, (p i).toReal * (inner ℂ
    (SourceJointClockGraph.clock (value i - mean p value)) (massMap (value i - mean p value))).re

theorem mean_action (value : ι → SourceJointClockGraph.Carrier) :
    mean p (SourceJointClockGraph.action ∘ value) = SourceJointClockGraph.action (mean p value) :=
  mean_map p SourceJointClockGraph.action.toLinearMap value

theorem variance_action (value : ι → SourceJointClockGraph.Carrier) :
    variance p (SourceJointClockGraph.action ∘ value) = variance p value +
      variance p (massMap ∘ value) + 2 * massClockCovariance p value := by
  calc
    variance p (SourceJointClockGraph.action ∘ value) =
        ∑ i, (p i).toReal * ‖SourceJointClockGraph.action (value i - mean p value)‖ ^ 2 := by
      simp only [variance, error, Function.comp_apply, mean_action, map_sub]
    _ = (∑ i, (p i).toReal * ‖value i - mean p value‖ ^ 2) +
        (∑ i, (p i).toReal * ‖massMap (value i - mean p value)‖ ^ 2) +
        2 * massClockCovariance p value := by
      simp only [SourceJointClockGraph.action_energy, massClockCovariance,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (p i).toReal * (‖value i - mean p value‖ ^ 2 +
        ‖massMap (value i - mean p value)‖ ^ 2 +
        2 * (inner ℂ (SourceJointClockGraph.clock (value i - mean p value))
          (massMap (value i - mean p value))).re) = _
      ring
    _ = variance p value + variance p (massMap ∘ value) + 2 * massClockCovariance p value := by
      simp only [variance, error, mean_map, Function.comp_apply, map_sub]

theorem mean_const (constant : SourceJointClockGraph.Carrier) : mean p (fun _ : ι => constant) = constant := by
  rw [mean, ← Finset.sum_smul, weights, one_smul]

theorem mass_const (value : ι → SourceJointClockGraph.Carrier) (constant : ℂ)
    (source : ∀ i, massMap (value i) = constant) : massMap (mean p value) = constant := by
  rw [← mean_map]
  simp only [mean, Function.comp_apply, source, ← Finset.sum_smul, weights, one_smul]

theorem constant_mass_variance (value : ι → SourceJointClockGraph.Carrier) (constant : ℂ)
    (source : ∀ i, massMap (value i) = constant) :
    variance p (SourceJointClockGraph.action ∘ value) = variance p value := by
  rw [variance_action]
  have mass : variance p (massMap ∘ value) = 0 := by
    simp only [variance, error, mean_map, mass_const p value constant source, Function.comp_apply,
      source, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
  have cross : massClockCovariance p value = 0 := by
    simp only [massClockCovariance, map_sub, mass_const p value constant source, source,
      sub_self, inner_zero_right, Complex.zero_re, mul_zero, Finset.sum_const_zero]
  rw [mass, cross]
  ring

end
end SourceVectorMoment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
