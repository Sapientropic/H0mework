import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.ComplementFirstCell

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TopUnit
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
open OriginalUnitXiConjugateOrderSource
open scoped Topology
open private bare_factor bare_analytic from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "owner"=>ActualAnalyticOwner
local notation "order"=>generatedRiemannXiZeroOrder owner
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum owner

/-- The original owner generates both bare values through the same conjugate zeta occurrence. -/
theorem actual_bare_conjugate (c:BurnolCompletedMellinCoordinate):
    bare (star c.value) (star c.value)=star (bare c.value c.value):=by
  have near:Tendsto (fun z:ℂ=>star z) (𝓝 (star c.value)) (𝓝 c.value):=by
    simpa only [star_star] using continuous_star.tendsto (star c.value)
  have reflected:riemannZeta=ᶠ[𝓝 (star c.value)]
      fun z:ℂ=>(z-star c.value)^order c.value*star (bare c.value (star z)):=by
    filter_upwards [near.eventually (bare_factor c)] with z field
    have source:=congrArg (starRingEnd ℂ) field
    rw [show riemannZeta (star z)=star (riemannZeta z) from riemannZeta_conj z] at source
    simpa only [starRingEnd_apply,star_star,star_mul,star_pow,star_sub,smul_eq_mul,mul_comm] using source
  have direct:riemannZeta=ᶠ[𝓝 (star c.value)]
      fun z:ℂ=>(z-star c.value)^order c.value*bare (star c.value) z:=by
    have source:=bare_factor (barC c)
    simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate,
      actual_original_Xi_order_conjugate c,smul_eq_mul] using source
  have equal:(fun z:ℂ=>bare (star c.value) z)=ᶠ[𝓝[≠](star c.value)]
      (fun z:ℂ=>star (bare c.value (star z))):=by
    filter_upwards [(direct.and reflected).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with z pair apart
    have different:z≠star c.value:=by simpa only [mem_compl_iff,mem_singleton_iff] using apart
    exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr different)) (pair.1.symm.trans pair.2)
  have left:Tendsto (fun z:ℂ=>bare (star c.value) z) (𝓝[≠](star c.value))
      (𝓝 (bare (star c.value) (star c.value))):=
    (bare_analytic (barC c)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have right:Tendsto (fun z:ℂ=>star (bare c.value (star z))) (𝓝[≠](star c.value))
      (𝓝 (star (bare c.value c.value))):=
    (((bare_analytic c).continuousAt.tendsto.comp near).star).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique left (right.congr' equal.symm)

/-- The original Fourier top read pays its own gamma factors before the conjugate bare value is read. -/
theorem actual_original_top_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    star (burnolAnalyticComplementExpectedPhysicalFourierRead owner (burnolPaZeroObservation c zero))=
      ((2:ℂ)^order c.value/2)*bare (star c.value) (star c.value):=by
  rw [burnolAnalyticComplementExpectedPhysicalFourierRead_eq (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero),star_mul,star_div₀,star_pow,star_ofNat]
  change star (bare c.value c.value)*((2:ℂ)^order c.value/2)=_
  rw [←actual_bare_conjugate c]
  ring

/-- The two original top-order fees agree by source jets and conjugacy, without a target equality input. -/
theorem actual_count_top_matches_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ((2:ℂ)^order c.value/((order c.value-1).factorial:ℂ))*
      iteratedDeriv (order c.value-1) (mellin (fullFloorRaw c)) (star c.value)=
        star (burnolAnalyticComplementExpectedPhysicalFourierRead owner (burnolPaZeroObservation c zero)):=by
  rw [actual_count_top_jet c zero,actual_original_top_unit c zero]
  have nonzero:((order c.value-1).factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero _
  field_simp [nonzero]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TopUnit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
