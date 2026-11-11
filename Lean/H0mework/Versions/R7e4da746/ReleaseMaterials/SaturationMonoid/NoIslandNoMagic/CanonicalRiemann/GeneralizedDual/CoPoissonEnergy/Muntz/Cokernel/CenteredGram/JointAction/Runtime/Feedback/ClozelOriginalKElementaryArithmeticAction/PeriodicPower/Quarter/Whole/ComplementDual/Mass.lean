import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mass
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.PowerPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open scoped Topology InnerProductSpace
open private logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private ordinary_log_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin
open private even_half_integral from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceRaw
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Rq" => burnolQuarterRestriction
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

theorem actual_polefree_at_one_zero (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):poleFreeSource c 1=0:=by
  have source:=actual_counting_one_sub_source c zero 1 (by norm_num)
  simpa only [sub_self,zero_mul,riemannZeta₁_one,one_mul] using source.symm

/-- The zeta pole at one pays the actual counting mass through the original inverse source. -/
theorem actual_mellin_mass_finite_part (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    mellin (fullFloorRaw c) 1=deriv (poleFreeSource c) 1/(1-star c.value):=by
  have dM:HasDerivAt (mellin (fullFloorRaw c))
      (mellin (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source.logSource (fullFloorRaw c) 1) 1) 1:=by
    simpa only [logSource_zero] using actual_floor_log_derivative c zero 0 1 (by norm_num)
  have idD:HasDerivAt (fun z:ℂ=>z) 1 1:=hasDerivAt_id 1
  have left:=((idD.sub_const 1).mul (idD.sub_const (star c.value))).mul dM
  have right:=differentiable_riemannZeta₁.differentiableAt.hasDerivAt.mul
    (actual_polefree_differentiable c 1 (by norm_num)).hasDerivAt
  have same:(fun z:ℂ=>(z-1)*(z-star c.value)*mellin (fullFloorRaw c) z)=ᶠ[𝓝 (1:ℂ)]
      (fun z:ℂ=>riemannZeta₁ z*poleFreeSource c z):=by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
      (by norm_num : (0:ℝ)<(1:ℂ).re)] with z positive
    exact actual_counting_one_sub_source c zero z positive
  have derived:=same.deriv_eq
  change deriv (((fun z:ℂ=>z-1)*(fun z:ℂ=>z-star c.value))*mellin (fullFloorRaw c)) 1=
    deriv (riemannZeta₁*poleFreeSource c) 1 at derived
  rw [left.deriv,right.deriv] at derived
  have nonzero:1-star c.value≠0:=by
    intro equal
    have real:=congrArg Complex.re equal
    simp only [sub_re,one_re,star_def,conj_re,zero_re] at real
    linarith [c.belowOne]
  apply (eq_div_iff nonzero).mpr
  simpa only [Pi.mul_apply,sub_self,mul_zero,zero_add,one_mul,zero_mul,add_zero,
    riemannZeta₁_one,actual_polefree_at_one_zero c zero,mul_comm] using derived

private theorem positive_mass (c:BurnolCompletedMellinCoordinate):
    mellin (fullFloorRaw c) 1=∫x:ℝ in Ioc (0:ℝ) q,fullFloorRaw c x:=by
  have source:=ordinary_log_read c 0 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)] at source
  simpa only [logSource_zero,sub_self,Complex.cpow_zero,pow_zero,one_mul,mul_one] using source

private theorem quarter_integrable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):Integrable (fullFloorRaw c) μq:=
  ((Lp.memLp (Rq (fullFloorValue c zero))).integrable (by norm_num)).congr (actual_floor_quarter_raw c zero)

theorem actual_quarter_mean_finite_part (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    burnolQuarterMeanCoefficient (Rq (fullFloorValue c zero))=
      4*deriv (poleFreeSource c) 1/(1-star c.value):=by
  rw [Constructor.mean_integral,integral_congr_ae (actual_floor_quarter_raw c zero),
    even_half_integral _ (quarter_integrable c zero) (actual_floor_even c.value c.belowOne),
    ←positive_mass,actual_mellin_mass_finite_part c zero]
  ring

theorem actual_whole_mass_finite_part (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    (∫x:ℝ,fullFloorRaw c x)=2*deriv (poleFreeSource c) 1/(1-star c.value):=by
  have compact:(symmetricInterval q).indicator (fullFloorRaw c)=fullFloorRaw c:=by
    funext x
    by_cases inside:x∈symmetricInterval q
    · exact indicator_of_mem inside _
    · rw [indicator_of_notMem inside]
      exact (actual_floor_outer_zero c.value c.belowOne x
        (lt_of_not_ge (fun bound=>inside (abs_le.mp bound)))).symm
  calc
    _=∫x:ℝ in symmetricInterval q,fullFloorRaw c x:=by
      conv_lhs=>rw [←compact]
      exact integral_indicator (measurableSet_symmetricInterval q)
    _=2*deriv (poleFreeSource c) 1/(1-star c.value):=by
      rw [even_half_integral _ (quarter_integrable c zero) (actual_floor_even c.value c.belowOne),
        ←positive_mass,actual_mellin_mass_finite_part c zero]
      ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mass
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
