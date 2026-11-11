import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Read
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Read
open scoped Topology ENNReal InnerProductSpace
open private translated_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Read
local notation "F" => fourierL2
local notation "q" => (1/4:ℝ)
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local notation "CircleL2" => Lp ℂ 2 (AddCircle.haarAddCircle (T:=(1:ℝ)))
local notation "window" => Icc (-(1/2):ℝ) (1/2:ℝ)

def aliasRawTerm (c : BurnolCompletedMellinCoordinate) (k : ℤ) (x : ℝ) : ℂ :=
  if k=0 then 0 else resolvedFourierRaw c (x+k)

def aliasRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ := ∑' k:ℤ,aliasRawTerm c k x
def periodicRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  resolvedFourierRaw c x+aliasRaw c x-resolvedRaw c 0

theorem actual_resolved_continuousAt (c : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero:x≠0) :
    ContinuousAt (resolvedFourierRaw c) x := by
  exact (ForcingWhole.raw_continuousAt c nonzero).sub
    (continuousAt_const.mul (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant q)).continuousAt)

private theorem shifted_distance (x : ℝ) (inside:x∈window) (k : ℤ) (nonzero:k≠0) :
    (1/2:ℝ)*|(k:ℝ)|≤|x+k| := by
  have bound : |x|≤(1/2:ℝ):=abs_le.mpr inside
  have one : (1:ℝ)≤|(k:ℝ)|:=by exact_mod_cast Int.one_le_abs nonzero
  have triangle:=abs_add_le (x+k) (-x)
  rw [abs_neg,show x+(k:ℝ)+ -x=(k:ℝ) by ring] at triangle
  linarith

theorem actual_alias_uniform_bound (c : BurnolCompletedMellinCoordinate) (k : ℤ)
    (x : ℝ) (inside:x∈window) : ‖aliasRawTerm c k x‖≤4*tailBound c/(k:ℝ)^2 := by
  by_cases zero:k=0
  · subst k
    simp [aliasRawTerm]
  · rw [aliasRawTerm,if_neg zero]
    have distance:=shifted_distance x inside k zero
    have kpos : 0 < |(k:ℝ)| := abs_pos.mpr (by exact_mod_cast zero)
    have xpos : 0 < |x+k| := lt_of_lt_of_le (by positivity) distance
    apply (actual_resolved_fourier_bound c _ (abs_pos.mp xpos)).trans
    have squared : (k:ℝ)^2≤4*|x+k|^2 := by nlinarith [sq_abs (k:ℝ)]
    have denominator : (0:ℝ)<(k:ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast zero)
    apply (div_le_div_iff₀ (sq_pos_of_pos xpos) denominator).mpr
    nlinarith [mul_le_mul_of_nonneg_left squared (tailBound_nonnegative c)]

theorem actual_alias_raw_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (aliasRaw c) window := by
  have major:Summable (fun k:ℤ=>4*tailBound c/(k:ℝ)^2) := by
    simpa only [div_eq_mul_inv,one_mul] using
      (Real.summable_one_div_int_pow.mpr (by decide:1<2)).mul_left (4*tailBound c)
  apply continuousOn_tsum _ major (actual_alias_uniform_bound c)
  intro k
  by_cases zero:k=0
  · subst k
    have source : aliasRawTerm c 0=(fun _:ℝ=>(0:ℂ)) := by funext x; simp [aliasRawTerm]
    rw [source]
    exact continuousOn_const
  · intro x inside
    have distance:=shifted_distance x inside k zero
    have kpos : 0 < |(k:ℝ)| := abs_pos.mpr (by exact_mod_cast zero)
    have xpos : 0 < |x+k| := lt_of_lt_of_le (by positivity) distance
    have continuousShift : ContinuousAt (fun t:ℝ=>resolvedFourierRaw c (t+k)) x :=
      ContinuousAt.comp (g:=resolvedFourierRaw c) (f:=fun t:ℝ=>t+k)
        (actual_resolved_continuousAt c (x+k) (abs_pos.mp xpos))
        (continuous_id.add continuous_const).continuousAt
    have source : aliasRawTerm c k=(fun t:ℝ=>resolvedFourierRaw c (t+k)) := by
      funext t
      rw [aliasRawTerm,if_neg zero]
    rw [source]
    exact continuousShift.continuousWithinAt

/-- The actual periodic source has a continuous representative at every nonzero point of this cell. -/
theorem actual_periodic_raw_continuousAt (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (lower:-(1/2:ℝ)<x) (upper:x<1/2) (nonzero:x≠0) : ContinuousAt (periodicRaw c) x := by
  exact ((actual_resolved_continuousAt c x nonzero).add
    ((actual_alias_raw_continuous c).continuousAt (Icc_mem_nhds lower upper))).sub continuousAt_const

private theorem alias_piece_raw (c : BurnolCompletedMellinCoordinate) (k : ℤ) :
    (aliasPiece c k:AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle]
      fun x=>aliasRawTerm c k (representative x) := by
  by_cases zero:k=0
  · subst k
    simp only [aliasPiece,aliasRawTerm,ite_true]
    exact Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle
  · simpa only [aliasPiece,aliasRawTerm,if_neg zero] using translated_raw c k

theorem actual_alias_raw (c : BurnolCompletedMellinCoordinate) :
    (aliasValue c:AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle] fun x=>aliasRaw c (representative x) := by
  have summation:=Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr (aliasPiece_summable_norm c))
  have all : ∀ᵐx∂AddCircle.haarAddCircle,∀k:ℤ,aliasPiece c k x=aliasRawTerm c k (representative x) :=
    ae_all_iff.mpr (alias_piece_raw c)
  filter_upwards [summation,all] with x sum read
  change (∑'k:ℤ,aliasPiece c k) x=_
  rw [sum]
  exact tsum_congr (read)

private theorem basis_zero_raw :
    ((_root_.fourierBasis (T:=(1:ℝ)) 0):AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle] fun _=>1 := by
  have source:=(_root_.coeFn_fourierLp (T:=(1:ℝ)) 2 (0:ℤ)).trans
    (Eventually.of_forall (fun _=>_root_.fourier_zero))
  simpa only [_root_.coe_fourierBasis] using source

/-- This is the original W as an a.e. field, not an evaluation of an arbitrary L² representative. -/
theorem actual_periodic_raw (c : BurnolCompletedMellinCoordinate) :
    (periodicPower c:AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle]
      fun x=>periodicRaw c (representative x) := by
  have center:=translated_raw c 0
  rw [translated_zero] at center
  simp only [Int.cast_zero,add_zero] at center
  have period : (periodizedValue c:AddCircle (1:ℝ)→ℂ)=ᵐ[AddCircle.haarAddCircle]
      fun x=>resolvedFourierRaw c (representative x)+aliasRaw c (representative x) := by
    filter_upwards [Lp.coeFn_add (circleMap (F (resolvedSource c))) (aliasValue c),center,actual_alias_raw c]
      with x addition first second
    change (circleMap (F (resolvedSource c))+aliasValue c:CircleL2) x=_
    rw [addition,Pi.add_apply,first,second]
  rw [actual_periodized_source] at period
  filter_upwards [period,Lp.coeFn_add (periodicPower c) (resolvedRaw c 0 • _root_.fourierBasis (T:=(1:ℝ)) 0),
    Lp.coeFn_smul (resolvedRaw c 0) (_root_.fourierBasis (T:=(1:ℝ)) 0),basis_zero_raw]
    with x value addition scalar constant
  rw [addition,Pi.add_apply,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one] at value
  unfold periodicRaw
  linear_combination value

end OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
