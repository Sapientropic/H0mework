import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ExactOrder
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageLimit
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology

def stripEnvelope (w:ℂ) (x:ℝ):ℂ:=
  (Ioc (0:ℝ) 1).indicator (fun t:ℝ=>(t:ℂ)^(w-1)) x+
  (Ioi (1:ℝ)).indicator (fun t:ℝ=>(t:ℂ)^(w-2)) x

theorem actual_strip_envelope_integrable (w:ℂ) (positive:0<w.re) (below:w.re<1):
    Integrable (stripEnvelope w):=by
  have head:IntegrableOn (fun t:ℝ=>(t:ℂ)^(w-1)) (Ioc (0:ℝ) 1):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num:(0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_cpow' (by simp only [sub_re,one_re];linarith))
  have tail:IntegrableOn (fun t:ℝ=>(t:ℂ)^(w-2)) (Ioi (1:ℝ)):=
    integrableOn_Ioi_cpow_of_lt (by norm_num;linarith) one_pos
  exact (head.integrable_indicator measurableSet_Ioc).add
    (tail.integrable_indicator measurableSet_Ioi)

theorem actual_strip_weight_bound (w:ℂ) (C:ℝ) (f:ℝ→ℂ) (x:ℝ) (positive:0<x)
    (head:x≤1→‖f x‖≤C) (tail:1<x→‖f x‖≤C/x):
    ‖(x:ℂ)^(w-1)*f x‖≤C*‖stripEnvelope w x‖:=by
  by_cases small:x≤1
  · rw [stripEnvelope,indicator_of_mem (show x∈Ioc (0:ℝ) 1 from ⟨positive,small⟩),
      indicator_of_notMem (show x∉Ioi (1:ℝ) from not_lt.mpr small),add_zero,norm_mul]
    exact (mul_le_mul_of_nonneg_left (head small) (norm_nonneg _)).trans_eq (mul_comm _ _)
  · have large:1<x:=lt_of_not_ge small
    rw [stripEnvelope,indicator_of_notMem (show x∉Ioc (0:ℝ) 1 from fun member=>small member.2),
      indicator_of_mem (show x∈Ioi (1:ℝ) from large),zero_add,norm_mul]
    have power:(x:ℂ)^(w-1)=(x:ℂ)^(w-2)*(x:ℂ):=by
      calc
        _=(x:ℂ)^((w-2)+1):=by congr 1;ring
        _=(x:ℂ)^(w-2)*(x:ℂ)^(1:ℂ):=Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')
        _=_:=by rw [Complex.cpow_one]
    rw [power,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    calc
      _≤(‖(x:ℂ)^(w-2)‖*x)*(C/x):=
        mul_le_mul_of_nonneg_left (tail large) (by positivity)
      _=C*‖(x:ℂ)^(w-2)‖:=by field_simp

/-- The common source tail is consumed as an actual Mellin integral limit on the open strip. -/
theorem actual_image_mellin_limit (images:ℕ→ℝ→ℂ) (image:ℝ→ℂ) (C:ℝ)
    (measurable:∀N,Measurable (images N))
    (head:∀N x,0<x→x≤1→‖images N x‖≤C)
    (tail:∀N x,1<x→‖images N x‖≤C/x)
    (pointwise:∀x,0<x→Tendsto (fun N:ℕ=>images N x) atTop (𝓝 (image x)))
    (w:ℂ) (positive:0<w.re) (below:w.re<1):
    Tendsto (fun N:ℕ=>mellin (images N) w) atTop (𝓝 (mellin image w)):=by
  unfold mellin
  simp only [smul_eq_mul]
  apply tendsto_integral_of_dominated_convergence (fun x:ℝ=>C*‖stripEnvelope w x‖)
  · intro N
    have regular:ContinuousOn (fun x:ℝ=>(x:ℂ)^(w-1)) (Ioi (0:ℝ)):=by
      intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x (w-1) (Or.inr (ne_of_gt hx))).continuousWithinAt
    exact (regular.aestronglyMeasurable measurableSet_Ioi).mul (measurable N).aestronglyMeasurable.restrict
  · exact (((actual_strip_envelope_integrable w positive below).norm).const_mul C).integrableOn
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact actual_strip_weight_bound w C (images N) x hx (head N x hx) (tail N x)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (pointwise x hx).const_mul _

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageLimit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
