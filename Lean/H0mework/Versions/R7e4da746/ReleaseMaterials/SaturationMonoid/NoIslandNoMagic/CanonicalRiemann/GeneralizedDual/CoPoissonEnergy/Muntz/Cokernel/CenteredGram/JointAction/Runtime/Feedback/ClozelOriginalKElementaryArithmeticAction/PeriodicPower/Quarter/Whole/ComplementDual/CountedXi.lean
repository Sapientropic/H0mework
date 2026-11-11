import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Whole

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open scoped Topology InnerProductSpace
open private logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.AnalyticComplementDivisionJet
open private bare_nonzero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
local notation "owner"=>ActualAnalyticOwner
local notation "order"=>generatedRiemannXiZeroOrder owner
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum owner

private theorem source_strip (c:BurnolCompletedMellinCoordinate):
    ∀ᶠz:ℂ in 𝓝 (star c.value),0<z.re ∧ z.re<1:=by
  have realRead:(star c.value).re=c.value.re:=by simp only [star_def,conj_re]
  exact ((continuous_re.tendsto (star c.value)).eventually
    (Ioi_mem_nhds (by rw [realRead];linarith [c.rightHalf]))).and
    ((continuous_re.tendsto (star c.value)).eventually
      (Iio_mem_nhds (by rw [realRead];exact c.belowOne)))

private theorem original_factor (c:BurnolCompletedMellinCoordinate) (z:ℂ)
    (positive:0<z.re) (below:z.re<1):
    riemannZeta z=(z-star c.value)^(order c.value)*bare (star c.value) z:=by
  have source:=generatedRiemannZeta_zero_factorization owner (star c.value) z
    (ne_of_apply_ne Complex.re (by simpa only [zero_re] using positive.ne'))
    (ne_of_apply_ne Complex.re (by simpa only [one_re] using below.ne))
    (Gammaℝ_ne_zero_of_re_pos positive)
  rw [OriginalUnitXiConjugateOrderSource.actual_original_Xi_order_conjugate c] at source
  simpa only [generatedRiemannZeta_eq_mathlib,smul_eq_mul] using source

def countComplement (c:BurnolCompletedMellinCoordinate) (z:ℂ):ℂ:=
  bare (star c.value) z*poleFreeSource c z

theorem actual_complement_analytic (c:BurnolCompletedMellinCoordinate):
    AnalyticAt ℂ (countComplement c) (star c.value):=by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [source_strip c] with z inside
  exact (divisionJet_differentiableAt_generatedRiemannBareZeroLocalizedSpectrum owner
    (star c.value) z inside.1 inside.2).mul (actual_polefree_differentiable c z inside.1)

theorem actual_complement_at_source (c:BurnolCompletedMellinCoordinate):
    countComplement c (star c.value)=bare (star c.value) (star c.value)/2:=by
  rw [countComplement,actual_polefree_at_source]
  ring

/-- The true integer-grid source loses exactly the one pole of the original dual seed. -/
theorem actual_original_order_factor (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (z:ℂ) (positive:0<z.re) (below:z.re<1) (apart:z≠star c.value):
    mellin (fullFloorRaw c) z=(z-star c.value)^(order c.value-1)*countComplement c z:=by
  have mpositive:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0<order c.value at mpositive
  have source:=actual_counting_pole_cleared_source c zero z positive
    (ne_of_apply_ne Complex.re (by simpa only [one_re] using below.ne))
  rw [original_factor c z positive below] at source
  have power:(z-star c.value)^(order c.value)=
      (z-star c.value)*(z-star c.value)^(order c.value-1):=by
    conv_lhs=>rw [show order c.value=(order c.value-1)+1 by omega]
    rw [pow_succ,mul_comm]
  rw [power] at source
  apply mul_left_cancel₀ (sub_ne_zero.mpr apart)
  simpa only [countComplement,mul_assoc] using source

theorem actual_original_order_germ (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    mellin (fullFloorRaw c)=ᶠ[𝓝 (star c.value)]
      (fun z:ℂ=>(z-star c.value)^(order c.value-1)*countComplement c z):=by
  have positive:0<(star c.value).re:=by simp only [star_def,conj_re];linarith [c.rightHalf]
  have continuous:ContinuousAt (mellin (fullFloorRaw c)) (star c.value):=by
    simpa only [logSource_zero] using (actual_floor_log_derivative c zero 0 _ positive).continuousAt
  apply (continuous.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (((continuousAt_id.sub continuousAt_const).pow _).mul (actual_complement_analytic c).continuousAt)).mp
  filter_upwards [(source_strip c).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with z inside apart
  exact actual_original_order_factor c zero z inside.1 inside.2 apart

theorem actual_count_leading_limit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Tendsto (fun z:ℂ=>mellin (fullFloorRaw c) z/(z-star c.value)^(order c.value-1))
      (𝓝[≠](star c.value)) (𝓝 (bare (star c.value) (star c.value)/2)):=by
  have limit:Tendsto (countComplement c) (𝓝[≠](star c.value))
      (𝓝 (countComplement c (star c.value))):=
    (actual_complement_analytic c).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [actual_complement_at_source] at limit
  apply limit.congr'
  filter_upwards [(source_strip c).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with z inside apart
  rw [actual_original_order_factor c zero z inside.1 inside.2 apart]
  exact (mul_div_cancel_left₀ (countComplement c z)
    (pow_ne_zero _ (sub_ne_zero.mpr apart))).symm

private theorem factor_jet (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (before:j≤order c.value-1):
    iteratedDeriv j (mellin (fullFloorRaw c)) (star c.value)=
      if j=order c.value-1 then ((order c.value-1).factorial:ℂ)*countComplement c (star c.value) else 0:=by
  classical
  rw [(actual_original_order_germ c zero).iteratedDeriv_eq j,
    iteratedDeriv_fun_mul (by fun_prop) (actual_complement_analytic c).contDiffAt]
  have power (i:ℕ):iteratedDeriv i
      (fun z:ℂ=>(z-star c.value)^(order c.value-1)) (star c.value)=
      if i=order c.value-1 then ((order c.value-1).factorial:ℂ) else 0:=by
    rw [iteratedDeriv_comp_sub_const i (fun z:ℂ=>z^(order c.value-1)) (star c.value)]
    dsimp only
    rw [sub_self,iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp only [Nat.cast_zero]
  simp_rw [power]
  by_cases top:j=order c.value-1
  · subst j
    rw [if_pos rfl,Finset.sum_eq_single (order c.value-1)]
    · simp only [if_true,Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero]
    · intro i member different
      rw [if_neg different,mul_zero,zero_mul]
    · intro absent
      exact (absent (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg top]
    apply Finset.sum_eq_zero
    intro i member
    have earlier:i<order c.value-1:=by
      have:=Finset.mem_range.mp member
      omega
    rw [if_neg earlier.ne,mul_zero,zero_mul]

/-- All actual low Mellin/log moments are generated by the same original Xi order. -/
theorem actual_count_lower_jet (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (before:j<order c.value-1):
    iteratedDeriv j (mellin (fullFloorRaw c)) (star c.value)=0:=by
  rw [factor_jet c zero j before.le,if_neg before.ne]

theorem actual_count_top_jet (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    iteratedDeriv (order c.value-1) (mellin (fullFloorRaw c)) (star c.value)=
      ((order c.value-1).factorial:ℂ)*bare (star c.value) (star c.value)/2:=by
  rw [factor_jet c zero _ le_rfl,if_pos rfl,actual_complement_at_source]
  ring

theorem actual_count_leading_nonzero (c:BurnolCompletedMellinCoordinate):
    bare (star c.value) (star c.value)/2≠0:=by
  let conjugate:BurnolCompletedMellinCoordinate:=
    ⟨star c.value,by simpa only [star_def,conj_re] using c.rightHalf,
      by simpa only [star_def,conj_re] using c.belowOne⟩
  exact div_ne_zero (bare_nonzero conjugate) (by norm_num)

/-- The opposite residues come from the two actual arithmetic sources, before any projection. -/
theorem actual_joint_leading_cancellation (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Tendsto (fun z:ℂ=>(mellin (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting.wholeCountedRaw c) z+
      mellin (fullFloorRaw c) z)/(z-star c.value)^(order c.value-1))
      (𝓝[≠](star c.value)) (𝓝 0):=by
  have source:=(OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Whole.actual_whole_Xi_leading_limit c zero).add
    (actual_count_leading_limit c zero)
  simpa only [←add_div,neg_div,neg_add_cancel] using source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
