import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.UnitResponse.Resolvent.ParameterJet

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction
open scoped Topology
local notation "q" => (1/4 : ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def coefficient (s : ℂ) : ℂ := s*(q : ℂ)^(-s)/(2*(1-s))

def freeUnit (s : ℂ) (value : BurnolL2) : BurnolL2 :=
  coefficient s • (value-((1-s)/2) • burnolDirectRightResolvent (s/2) value)

private theorem not_one (c : BurnolCompletedMellinCoordinate) : c.value≠1 := by
  intro same
  have source := c.belowOne
  rw [same] at source
  norm_num at source

theorem actual_free_unit (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    unitResolventSource c value=freeUnit (star c.value) value := by
  have nonzero : 1-star c.value≠0 := by
    apply sub_ne_zero.mpr
    intro same
    apply not_one c
    have back := congrArg star same
    simpa only [star_one,star_star] using back.symm
  have gap := GapEuler.gapMean_primitive q (by norm_num) c
  have scalar : star c.value*GapEuler.gapMean q c=coefficient (star c.value) := by
    unfold coefficient
    apply (eq_div_iff (mul_ne_zero (by norm_num) nonzero)).mpr
    linear_combination 2*star c.value*gap
  rw [unitResolventSource,freeUnit,scalar]
  rfl

/-- The same original inverse source supplies a free analytic field before any zero observation. -/
theorem free_unit_analytic (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    AnalyticAt ℂ (fun s=>freeUnit s value) c.value := by
  have power : AnalyticAt ℂ (fun s : ℂ=>(q : ℂ)^(-s)) c.value :=
    ((differentiable_id.neg).const_cpow (.inl (by norm_num : (q : ℂ)≠0))).analyticAt _
  have scalar : AnalyticAt ℂ coefficient c.value :=
    (analyticAt_id.mul power).div (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (not_one c).symm))
  have rate : AnalyticAt ℂ (fun s : ℂ=>(1-s)/2) c.value :=
    (analyticAt_const.sub analyticAt_id).div_const
  exact scalar.smul (analyticAt_const.sub
    (rate.smul (OriginalRResolventParameterJet.parameter_analytic c value)))

def bRead : BurnolL2 →L[ℂ] M :=
  burnolMeanZeroBlockInverse.comp
    (burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto.comp
      (burnolQuarterRestriction.comp fourierL2.toContinuousLinearEquiv.toContinuousLinearMap))

def bModel (s : ℂ) : M := bRead (freeUnit s ConstantDual.seed)

theorem actual_original_B_model (c : BurnolCompletedMellinCoordinate) :
    burnolRieszSingleFourierSource c=bModel (star c.value) := by
  rw [bModel,←actual_free_unit,elementary_unit_resolvent]
  rfl

theorem original_B_model_analytic (c : BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ bModel c.value := by
  exact (bRead.analyticAt _).comp (free_unit_analytic c ConstantDual.seed)

theorem original_reverse_free_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ=>DualSource.source N (elementarySource c)) atTop
      (𝓝 (freeUnit (star c.value) ConstantDual.value)) := by
  have model : unitResolventSource c = fun value=>freeUnit (star c.value) value :=
    funext (actual_free_unit c)
  have regular : Continuous (unitResolventSource c) := by
    unfold unitResolventSource OriginalKSourceResolventReconstruction.sourceResolvent
    let reflected := OriginalPrimitiveRankBalance.conjugateCoordinate c
    change Continuous (fun value : BurnolL2=>
      (star c.value*GapEuler.gapMean q c) •
        (value-((1-star c.value)/2) • burnolDirectRightResolventCLM reflected value))
    fun_prop
  have source := (regular.tendsto ConstantDual.value).comp ConstantDual.original_tendsto
  rw [model] at source
  apply source.congr'
  filter_upwards with N
  rw [unit_resolvent_finite,actual_free_unit]
  rfl

end OriginalKElementaryArithmeticAction.FreeParameter.Riesz
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
