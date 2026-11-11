import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.AmbientSource
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitMellin.ContinuitySource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)

/-- Original ambient read is continuous in its legal coordinate, by the actual L2 tail budget. -/
theorem actual_ambient_mellin_tendsto {ι:Type*} {l:Filter ι} [l.IsCountablyGenerated]
    (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) (probe:ι→BurnolCompletedMellinCoordinate)
    (near:Tendsto (fun t=>(probe t).value) l (𝓝 c.value)):
    Tendsto (fun t=>burnolAmbientCompletedMellinEvaluator (probe t) v) l
      (𝓝 (burnolAmbientCompletedMellinEvaluator c v)):=by
  let a:ℝ:=(c.value.re+1/2)/2
  have aHalf:1/2<a:=by unfold a;linarith [c.rightHalf]
  have aBelow:a<c.value.re:=by unfold a;linarith [c.rightHalf]
  have eventuallyLower:∀ᶠ t in l,a<(probe t).value.re:=
    (Complex.continuous_re.tendsto c.value |>.comp near).eventually (Ioi_mem_nhds aBelow)
  let bound:ℝ→ℝ:=fun x=>‖(x:ℂ)^(-(a:ℂ))*v x‖+‖(x:ℂ)^(-1:ℂ)*v x‖
  have budget:IntegrableOn bound (Ioi q):=
    (burnolRadiusMellinWeight_integrableOn_tail q (by norm_num) (a:ℂ) aHalf v).norm.add
      (burnolRadiusMellinWeight_integrableOn_tail q (by norm_num) 1 (by norm_num) v).norm
  have measured:∀ᶠ t in l,AEStronglyMeasurable (fun x:ℝ=>(x:ℂ)^(-(probe t).value)*v x)
      (volume.restrict (Ioi q)):=Eventually.of_forall (fun t=>
    (burnolRadiusMellinWeight_integrableOn_tail q (by norm_num) (probe t).value (probe t).rightHalf v).aestronglyMeasurable)
  have dominates:∀ᶠ t in l,∀ᵐ x:ℝ ∂volume.restrict (Ioi q),
      ‖(x:ℂ)^(-(probe t).value)*v x‖≤bound x:=by
    filter_upwards [eventuallyLower] with t lower
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x inside
    have positive:0<x:=lt_trans (by norm_num:(0:ℝ)<q) inside
    have atA:‖(x:ℂ)^(-(probe t).value)*v x‖≤‖(x:ℂ)^(-(a:ℂ))*v x‖+
        ‖(x:ℂ)^(-1:ℂ)*v x‖:=by
      by_cases above:1≤x
      · have power:x^(-(probe t).value.re)≤x^(-a):=
          Real.rpow_le_rpow_of_exponent_le above (by linarith)
        have lhs:‖(x:ℂ)^(-(probe t).value)*v x‖≤‖(x:ℂ)^(-(a:ℂ))*v x‖:=by
          simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos positive,Complex.neg_re,Complex.ofReal_re]
          exact mul_le_mul_of_nonneg_right power (norm_nonneg _)
        exact lhs.trans (le_add_of_nonneg_right (norm_nonneg _))
      · have power:x^(-(probe t).value.re)≤x^(-1:ℝ):=
          Real.rpow_le_rpow_of_exponent_ge positive (by linarith) (by linarith [(probe t).belowOne])
        have lhs:‖(x:ℂ)^(-(probe t).value)*v x‖≤‖(x:ℂ)^(-1:ℂ)*v x‖:=by
          simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos positive,Complex.neg_re,Complex.one_re]
          exact mul_le_mul_of_nonneg_right power (norm_nonneg _)
        exact lhs.trans (le_add_of_nonneg_left (norm_nonneg _))
    exact atA
  have pointwise:∀ᵐ x:ℝ ∂volume.restrict (Ioi q),
      Tendsto (fun t=>(x:ℂ)^(-(probe t).value)*v x) l (𝓝 ((x:ℂ)^(-c.value)*v x)):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x inside
    have positive:0<x:=lt_trans (by norm_num:(0:ℝ)<q) inside
    exact ((continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr positive.ne')).tendsto.comp near.neg).mul_const _
  have tail:=tendsto_integral_filter_of_dominated_convergence bound measured dominates budget pointwise
  have gap:Tendsto (fun t=>burnolRadiusMellinGapMoment q (probe t).value) l
      (𝓝 (burnolRadiusMellinGapMoment q c.value)):=by
    have exponent:Tendsto (fun t=>(1:ℂ)-(probe t).value) l (𝓝 (1-c.value)):=tendsto_const_nhds.sub near
    have numerator:=(continuousAt_const_cpow (by norm_num:(q:ℂ)≠0)).tendsto.comp exponent
    have nonzero:1-c.value≠0:=by
      intro zero
      have realPart:=congrArg Complex.re zero
      simp only [sub_re,one_re,zero_re] at realPart
      linarith [c.belowOne]
    exact numerator.div exponent nonzero
  have sum:=(gap.mul_const (burnolAmbientGapCoefficient q v)).add tail
  change Tendsto (fun t=>burnolRadiusMellinGapMoment q (probe t).value*burnolAmbientGapCoefficient q v+
      burnolRadiusMellinTailEvaluator q (by norm_num) (probe t).value (probe t).rightHalf v) l
    (𝓝 (burnolRadiusMellinGapMoment q c.value*burnolAmbientGapCoefficient q v+
      burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf v))
  simp_rw [burnolRadiusMellinTailEvaluator_eq_integral]
  exact sum

end OriginalKFiniteOrderRelease.UnitMellin.ContinuitySource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
