import H0mework.Physics.Source.SourceBridgeNoGo
import Mathlib.Topology.Algebra.Order.Archimedean
import H0mework.Physics.MotherProgrammesFormation.Dyadic

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContactFlow

open StageNineSourceBridgeNoGo
open DyadicFormation

noncomputable section

theorem flow_ext (first last : ComplexUnitaryOneParameterFlow)
    (same : first.evolve = last.evolve) : first = last := by
  cases first
  cases last
  cases same
  rfl

theorem flow_neg (flow : ComplexUnitaryOneParameterFlow) (time : ℝ) :
    flow.evolve (-time) = (flow.evolve time)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← flow.evolve_add, neg_add_cancel, flow.evolve_zero]

/-- Arbitrarily fine generated samples determine the entire continuous action.
The additive equalizer also retains every integer multiple of each sample. -/
theorem flow_eq_of_dyadic (first last : ComplexUnitaryOneParameterFlow)
    (samples : ∀ depth : ℕ, first.evolve (1 / 2 ^ depth) = last.evolve (1 / 2 ^ depth)) :
    first = last := by
  let agreement : AddSubgroup ℝ :=
    { carrier := {time | first.evolve time = last.evolve time}
      zero_mem' := first.evolve_zero.trans last.evolve_zero.symm
      add_mem' := by
        intro a b ha hb
        change first.evolve (a+b) = last.evolve (a+b)
        rw [first.evolve_add, last.evolve_add, ha, hb]
      neg_mem' := by
        intro a ha
        change first.evolve (-a) = last.evolve (-a)
        rw [flow_neg, flow_neg, ha] }
  have dense : Dense (agreement : Set ℝ) := by
    apply agreement.dense_of_not_isolated_zero
    intro epsilon positive
    obtain ⟨depth, large⟩ := pow_unbounded_of_one_lt (1 / epsilon) (show (1 : ℝ) < 2 by norm_num)
    refine ⟨1 / 2 ^ depth, samples depth, by positivity, ?_⟩
    apply (div_lt_iff₀ (show (0 : ℝ) < 2 ^ depth by positivity)).mpr
    have := (div_lt_iff₀ positive).mp large
    nlinarith
  apply flow_ext
  exact Continuous.ext_on dense first.continuous_evolve last.continuous_evolve
    (fun _ present => present)

/-- Local primitive contact laws, independent of the reference physical source. -/
structure Primitive (flow : ComplexUnitaryOneParameterFlow) : Prop where
  involution : flow.evolve 1 ^ 2 = 1
  effective : flow.evolve 1 ≠ 1
  oriented : ∀ depth : ℕ, 0 ≤ (flow.evolve (1 / 2 ^ depth) : ℂ).im

theorem flow_dyadic_square (flow : ComplexUnitaryOneParameterFlow) (depth : ℕ) :
    flow.evolve (1 / 2 ^ (depth + 1)) ^ 2 = flow.evolve (1 / 2 ^ depth) := by
  rw [pow_two, ← flow.evolve_add]
  congr 1
  rw [pow_succ]
  field_simp
  ring

theorem primitive_samples (flow : ComplexUnitaryOneParameterFlow) (law : Primitive flow)
    (depth : ℕ) : flow.evolve (1 / 2 ^ depth) = generatedAt (flow.evolve 1) depth := by
  induction depth with
  | zero => simp [generatedAt]
  | succ depth previous =>
    apply step_unique (generatedAt (flow.evolve 1) depth)
      (at_upper _ (primitive_upper _ law.involution law.effective) depth)
    · exact (flow_dyadic_square flow depth).trans previous
    · exact law.oriented (depth + 1)

/-- The continuous readout extends the recursively formed complement trajectory. -/
def generatedFlow : ComplexUnitaryOneParameterFlow where
  evolve := fun time => Circle.exp (Complex.arg (-1 : ℂ) * time)
  evolve_zero := by simp
  evolve_add := by intro a b; rw [mul_add, Circle.exp_add]
  continuous_evolve := Circle.exp.continuous.comp (continuous_const.mul continuous_id)

theorem generatedFlow_samples (depth : ℕ) :
    generatedFlow.evolve (1 / 2 ^ depth) = generatedAt (-1) depth := by
  rw [primitive_normalForm (-1) (by ext; simp) (by intro same; have := congrArg (fun z : Circle => (z : ℂ)) same; norm_num at this)]
  simp [generatedFlow, div_eq_mul_inv]

theorem generatedFlow_primitive : Primitive generatedFlow where
  involution := by
    change Circle.exp (Complex.arg (-1 : ℂ) * 1) ^ 2 = 1
    simp only [Complex.arg_neg_one, mul_one]
    rw [← Circle.exp_natCast_mul]
    exact Circle.exp_two_pi
  effective := by simpa [generatedFlow] using Circle.exp_pi_ne_one
  oriented := by
    intro depth
    rw [generatedFlow_samples]
    exact at_im_nonneg (-1) (by simpa [Upper] using Real.pi_pos) depth

theorem primitive_flow (flow : ComplexUnitaryOneParameterFlow) (law : Primitive flow) :
    flow = generatedFlow := by
  apply flow_eq_of_dyadic
  intro depth
  rw [primitive_samples flow law depth,
    primitive_eq_neg_one _ law.involution law.effective, generatedFlow_samples]

theorem continuous_action_formed : ∃! flow : ComplexUnitaryOneParameterFlow, Primitive flow :=
  ⟨generatedFlow, generatedFlow_primitive, primitive_flow⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContactFlow
