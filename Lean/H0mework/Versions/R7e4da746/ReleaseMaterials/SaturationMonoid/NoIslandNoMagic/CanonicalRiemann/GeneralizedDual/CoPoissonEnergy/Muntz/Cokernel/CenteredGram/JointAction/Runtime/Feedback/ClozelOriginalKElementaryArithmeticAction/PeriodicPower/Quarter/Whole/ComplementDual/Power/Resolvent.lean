import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.UnitResponse.Resolvent.ParameterJet

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Resolvent
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
open scoped Topology InnerProductSpace
open private actual_direct_R_positive_kernel from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource
open private actual_R_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
local notation "q"=>(1/4:ℝ)
local notation "Rq"=>burnolQuarterRestriction
local notation "E"=>burnolQuarterZeroExtension
local notation "Cq"=>intervalConstant q
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner

def exterior:BurnolL2→L[ℂ]BurnolL2:=
  ContinuousLinearMap.id ℂ BurnolL2-burnolQuarterRestriction.adjoint.comp Rq

theorem actual_exterior_apply (value:BurnolL2):exterior value=value-E (Rq value):=rfl

private theorem exterior_raw (value:BurnolL2) (raw:ℝ→ℂ)
    (read:(value:ℝ→ℂ)=ᵐ[volume]raw):
    (exterior value:ℝ→ℂ)=ᵐ[volume](fun x=>if |x|≤q then 0 else raw x):=by
  have localRead:∀ᵐx:ℝ ∂volume,x∈symmetricInterval q→Rq value x=value x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
      (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value)
  filter_upwards [Lp.coeFn_sub value (E (Rq value)),burnolQuarterZeroExtension_coe (Rq value),
    localRead,read] with x subtraction extension restriction actual
  change (value-E (Rq value)) x=_
  rw [subtraction,Pi.sub_apply,extension]
  by_cases inside:|x|≤q
  · rw [if_pos inside,indicator_of_mem (show x∈symmetricInterval q from abs_le.mp inside),
      restriction (abs_le.mp inside),sub_self]
  · rw [if_neg inside,indicator_of_notMem
      (show x∉symmetricInterval q from fun member=>inside (abs_le.mpr member)),sub_zero,actual]

private theorem even_of_raw (value:BurnolL2) (raw:ℝ→ℂ)
    (read:(value:ℝ→ℂ)=ᵐ[volume]raw) (even:∀x,raw (-x)=raw x):reflectL2 value=value:=by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving,
    negMeasurePreserving.quasiMeasurePreserving.ae read,read] with x reflected negative actual
  change reflectL2 value x=value (-x) at reflected
  rw [reflected,negative,actual,even]

theorem actual_count_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    reflectL2 (fullFloorValue c zero)=fullFloorValue c zero:=
  even_of_raw _ _ (actual_full_floor_raw c zero) (actual_floor_even c.value c.belowOne)

private theorem box_even:reflectL2 ConstantDual.seed=ConstantDual.seed:=
  even_of_raw _ _ ConstantDual.seed_coeFn (fun x=>by simp only [ConstantDual.seedRaw,abs_neg])

def prefixRaw (d:BurnolCompletedMellinCoordinate) (raw:ℝ→ℂ) (x:ℝ):ℂ:=
  -2*((|x|:ℝ):ℂ)^(-d.value)*(∫u:ℝ in (0:ℝ)..|x|,(u:ℂ)^(d.value-1)*raw u)

/-- The original inward R has this whole even kernel without a constant-gap hypothesis. -/
theorem actual_R_raw (d:BurnolCompletedMellinCoordinate) (value:BurnolL2) (raw:ℝ→ℂ)
    (read:(value:ℝ→ℂ)=ᵐ[volume]raw) (even:reflectL2 value=value):
    (burnolDirectRightResolvent (d.value/2) value:ℝ→ℂ)=ᵐ[volume]prefixRaw d raw:=by
  let acted:=burnolDirectRightResolvent (d.value/2) value
  have positive:=actual_direct_R_positive_kernel d value raw read
  have actedEven:reflectL2 acted=acted:=(actual_R_reflect d value).trans (congrArg _ even)
  filter_upwards [positive,negMeasurePreserving.quasiMeasurePreserving.ae positive,
    Lp.coeFn_compMeasurePreserving acted negMeasurePreserving,volume.ae_ne (0:ℝ)]
    with x first second reflected nonzero
  have reflectedRead:acted x=acted (-x):=by
    change reflectL2 acted x=acted (-x) at reflected
    rwa [actedEven] at reflected
  change acted x=prefixRaw d raw x
  by_cases pos:0<x
  · simpa only [prefixRaw,abs_of_pos pos] using first pos
  · have negpos:0< -x:=by
      have negative:x<0:=lt_of_le_of_ne (le_of_not_gt pos) nonzero
      linarith
    rw [reflectedRead]
    simpa only [prefixRaw,abs_of_neg (by linarith:x<0)] using second negpos

private theorem compact_prefix (raw:ℝ→ℂ) (outside:∀x:ℝ,q < |x| → raw x=0)
    (z:ℂ) (x:ℝ) (large:q≤x):
    (∫u:ℝ in (0:ℝ)..x,(u:ℂ)^(z-1)*raw u)=mellin raw z:=by
  have positive:0<x:=lt_of_lt_of_le (by norm_num:q>0) large
  rw [intervalIntegral.integral_of_le positive.le,mellin,
    ←integral_indicator measurableSet_Ioc,←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases pos:0<u
  · by_cases before:u≤x
    · simp only [indicator_of_mem (show u∈Ioc 0 x from ⟨pos,before⟩),
        indicator_of_mem (show u∈Ioi 0 from pos),smul_eq_mul]
    · have outer:q < |u|:=by rw [abs_of_pos pos];linarith
      rw [indicator_of_notMem (show u∉Ioc 0 x from fun h=>before h.2),
        indicator_of_mem (show u∈Ioi 0 from pos),outside u outer,smul_zero]
  · rw [indicator_of_notMem (show u∉Ioc 0 x from fun h=>pos h.1),
      indicator_of_notMem (show u∉Ioi 0 from pos)]

private theorem box_mellin (d:BurnolCompletedMellinCoordinate):
    mellin ConstantDual.seedRaw d.value=(q:ℂ)^d.value/d.value:=by
  have parameter:d.value≠0:=by intro eq;have:=d.rightHalf;rw [eq] at this;norm_num at this
  rw [←compact_prefix ConstantDual.seedRaw
    (fun x beyond=>by rw [ConstantDual.seedRaw,if_neg (not_le.mpr beyond)]) d.value q le_rfl]
  have source:(∫u:ℝ in (0:ℝ)..q,(u:ℂ)^(d.value-1)*ConstantDual.seedRaw u)=
      ∫u:ℝ in (0:ℝ)..q,(u:ℂ)^(d.value-1):=by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u inside
    dsimp only
    rw [ConstantDual.seedRaw,if_pos (by rw [abs_of_pos inside.1];exact inside.2.le),mul_one]
  rw [source,integral_cpow (Or.inl (by simp only [sub_re,one_re];linarith [d.rightHalf]))]
  simp only [sub_add_cancel,Complex.ofReal_zero,Complex.zero_cpow parameter,sub_zero]

def exteriorCoefficient (c:BurnolCompletedMellinCoordinate) (z:ℂ):ℂ:=
  z*(q:ℂ)^(-z)*mellin (fullFloorRaw c) z

/-- Two actual compact inputs share the same full exterior R carrier at every free parameter. -/
theorem actual_exterior_resolvent (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    exterior (burnolDirectRightResolvent (d.value/2) (fullFloorValue c zero))=
      exteriorCoefficient c d.value • exterior (burnolDirectRightResolvent (d.value/2) ConstantDual.seed):=by
  let left:=burnolDirectRightResolvent (d.value/2) (fullFloorValue c zero)
  let right:=burnolDirectRightResolvent (d.value/2) ConstantDual.seed
  have leftRead:=exterior_raw left _
    (actual_R_raw d _ _ (actual_full_floor_raw c zero) (actual_count_even c zero))
  have rightRead:=exterior_raw right _ (actual_R_raw d _ _ ConstantDual.seed_coeFn box_even)
  have parameter:d.value≠0:=by intro eq;have:=d.rightHalf;rw [eq] at this;norm_num at this
  have phase:(q:ℂ)^(-d.value)*(q:ℂ)^d.value=1:=by
    rw [←Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0),neg_add_cancel,Complex.cpow_zero]
  apply Lp.ext
  filter_upwards [leftRead,rightRead,Lp.coeFn_smul (exteriorCoefficient c d.value) (exterior right)]
    with x leftAt rightAt scalar
  change exterior left x=(exteriorCoefficient c d.value • exterior right) x
  rw [leftAt,scalar,Pi.smul_apply,rightAt,smul_eq_mul]
  by_cases inside:|x|≤q
  · simp only [if_pos inside,mul_zero]
  · simp only [if_neg inside]
    rw [prefixRaw,prefixRaw,
      compact_prefix (fullFloorRaw c) (actual_floor_outer_zero c.value c.belowOne)
        d.value |x| (le_of_not_ge inside),
      compact_prefix ConstantDual.seedRaw
        (fun u beyond=>by rw [ConstantDual.seedRaw,if_neg (not_le.mpr beyond)])
        d.value |x| (le_of_not_ge inside),box_mellin,exteriorCoefficient]
    calc
      _=(-2*((|x|:ℝ):ℂ)^(-d.value)*mellin (fullFloorRaw c) d.value)*
          ((q:ℂ)^(-d.value)*(q:ℂ)^d.value):=by rw [phase,mul_one]
      _=_:=by field_simp [parameter]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
