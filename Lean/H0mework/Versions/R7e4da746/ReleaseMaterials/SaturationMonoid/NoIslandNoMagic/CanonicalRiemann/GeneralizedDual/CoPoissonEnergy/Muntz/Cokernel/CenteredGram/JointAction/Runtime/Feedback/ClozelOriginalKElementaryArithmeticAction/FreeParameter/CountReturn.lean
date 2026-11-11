import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.CountLipschitz
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.CountReturn
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.CountGeometry OriginalKElementaryArithmeticAction.FreeParameter.CountLipschitz
open scoped InnerProductSpace Topology FourierTransform
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2

def countRaw (b:Hq) (x:ℝ) : ℂ :=
 ∑n∈DualSourceRaw.channels x,centeredRaw b ((n:ℝ)*|x|)

theorem countRaw_measurable (b:Hq) : Measurable (countRaw b) := by
 let f:ℕ→ℝ→ℂ:=fun N x=>∑n∈Finset.Icc 1 N,centeredRaw b ((n:ℝ)*|x|)
 have finite (N:ℕ):Measurable (f N):=by
  apply Finset.measurable_fun_sum
  intro n _
  exact ((centeredRaw_continuous b).comp (continuous_const.mul continuous_abs)).measurable
 have joint:Measurable (fun p:ℕ×ℝ=>f p.1 p.2):=measurable_from_prod_countable_right finite
 have count:Measurable (fun x:ℝ=>⌊q/|x|⌋₊):=(measurable_const.div continuous_abs.measurable).nat_floor
 change Measurable (fun x:ℝ=>∑n∈Finset.Icc 1 ⌊q/|x|⌋₊,centeredRaw b ((n:ℝ)*|x|))
 simpa only [f,Function.comp_def,id_eq] using
  joint.comp (count.prodMk measurable_id)

def countBound : ℝ := 2*Real.pi*q*Real.sqrt (2*q)*q+2*Real.sqrt (2*q)

theorem countBound_nonnegative : 0≤countBound := by unfold countBound;positivity

theorem countRaw_bound (b:Hq) (x:ℝ) : ‖countRaw b x‖≤countBound*‖b‖ := by
 by_cases zero:x=0
 · subst x
   simp only [countRaw,DualSourceRaw.channels,abs_zero,div_zero,Nat.floor_zero,
    Finset.Icc_eq_empty_of_lt (by decide:(0:ℕ)<1),Finset.sum_empty,norm_zero]
   exact mul_nonneg countBound_nonnegative (norm_nonneg b)
 have paid:=RegularQuadrature.quadrature_bound (centeredRaw b) (centeredRaw_continuous b).continuousOn
  (2*Real.pi*q*Real.sqrt (2*q)*‖b‖) (2*Real.sqrt (2*q)*‖b‖) (by positivity) (by positivity)
  (fun a _ d _=>centeredRaw_lipschitz b a d) (fun t _=>centeredRaw_bound b t) |x| (abs_pos.mpr zero)
 rw [centeredRaw_half_zero,mul_zero,sub_zero] at paid
 exact paid.trans_eq (by unfold countBound;ring)

theorem countRaw_outside (b:Hq) (x:ℝ) (outside:q < |x|) : countRaw b x=0 := by
 have positive:0 < |x|:=(by norm_num:(0:ℝ)<q).trans outside
 have index:⌊q/|x|⌋₊=0:=Nat.floor_eq_zero.mpr ((div_lt_one positive).mpr outside)
 simp only [countRaw,DualSourceRaw.channels,index,Finset.Icc_eq_empty_of_lt (by decide:(0:ℕ)<1),Finset.sum_empty]

theorem countRaw_memLp (b:Hq) : MemLp (countRaw b) 2 volume := by
 have dominant:MemLp ((symmetricInterval q).indicator (fun _:ℝ=>((countBound*‖b‖:ℝ):ℂ))) 2 volume:=
  memLp_indicator_const 2 (measurableSet_symmetricInterval q) _ (Or.inr (by simp [symmetricInterval]))
 apply dominant.mono (countRaw_measurable b).aestronglyMeasurable
 filter_upwards with x
 by_cases inside:x∈symmetricInterval q
 · rw [indicator_of_mem inside,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg countBound_nonnegative (norm_nonneg b))]
   exact countRaw_bound b x
 · rw [indicator_of_notMem inside,countRaw_outside b x
    (lt_of_not_ge (fun small=>inside (abs_le.mp small))),norm_zero]

def countValue (b:Hq) : BurnolL2 := (countRaw_memLp b).toLp (countRaw b)

theorem countValue_read (b:Hq) : (countValue b:ℝ→ℂ)=ᵐ[volume] countRaw b :=
 (countRaw_memLp b).coeFn_toLp

theorem countRaw_add (a b:Hq) (x:ℝ) : countRaw (a+b) x=countRaw a x+countRaw b x := by
 simp only [countRaw,centeredRaw_add,Finset.sum_add_distrib]

theorem countRaw_smul (z:ℂ) (b:Hq) (x:ℝ) : countRaw (z•b) x=z*countRaw b x := by
 simp only [countRaw,centeredRaw_smul,Finset.mul_sum]

theorem countValue_add (a b:Hq) : countValue (a+b)=countValue a+countValue b := by
 apply Lp.ext
 filter_upwards [countValue_read (a+b),countValue_read a,countValue_read b,
  Lp.coeFn_add (countValue a) (countValue b)] with x sum left right added
 rw [added,Pi.add_apply,sum,left,right,countRaw_add]

theorem countValue_smul (z:ℂ) (b:Hq) : countValue (z•b)=z•countValue b := by
 apply Lp.ext
 filter_upwards [countValue_read (z•b),countValue_read b,Lp.coeFn_smul z (countValue b)] with x scaled read scalar
 rw [scalar,Pi.smul_apply,smul_eq_mul,scaled,read,countRaw_smul]

theorem countValue_bound (b:Hq) : ‖countValue b‖≤(countBound*‖ConstantDual.seed‖)*‖b‖ := by
 have paid:‖countValue b‖≤(countBound*‖b‖)*‖ConstantDual.seed‖:=by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [countValue_read b,ConstantDual.seed_coeFn] with x read constant
  rw [read,constant,ConstantDual.seedRaw]
  by_cases inside:|x|≤q
  · rw [if_pos inside,norm_one,mul_one]
    exact countRaw_bound b x
  · rw [if_neg inside,countRaw_outside b x (lt_of_not_ge inside),norm_zero,mul_zero]
 exact paid.trans_eq (by ring)

def countLinear : Hq→ₗ[ℂ]BurnolL2 where
 toFun:=countValue
 map_add':=countValue_add
 map_smul':=fun z b=>countValue_smul z b

/-- The actual complete arithmetic return count is a fixed bounded linear read of its Fourier input. -/
def countReader : Hq→L[ℂ]BurnolL2 :=
 countLinear.mkContinuous (countBound*‖ConstantDual.seed‖) countValue_bound

theorem countReader_read (b:Hq) : (countReader b:ℝ→ℂ)=ᵐ[volume] countRaw b := countValue_read b

open private half_integral_zero from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReturnCounting

private theorem actual_symFourier (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
 symFourier (burnolRieszSingleFourierSource c:Hq) x=burnolRieszReturnRaw c x+
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource c:Hq)) := by
 have read (y:ℝ):burnolRadiusTruncatedFourierRaw q (burnolRieszSingleFourierSource c:Hq) y=
  burnolRieszReturnRaw c y+
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource c:Hq)):=by
  unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw;ring
 rw [symFourier,read x,read (-x),return_raw_even c x]
 ring

private theorem actual_halfMean (c:BurnolCompletedMellinCoordinate) :
 halfMean (burnolRieszSingleFourierSource c:Hq)=
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource c:Hq)) := by
 have zero:(∫x:ℝ in (0:ℝ)..q,burnolRieszReturnRaw c x)=0:=by
  rw [intervalIntegral.integral_of_le (by norm_num:(0:ℝ)≤q)]
  exact half_integral_zero c
 unfold halfMean
 simp_rw [actual_symFourier]
 rw [intervalIntegral.integral_add ((burnolRieszReturnRaw_continuous c).intervalIntegrable _ _)
  intervalIntegrable_const,zero,zero_add,intervalIntegral.integral_const]
 simp only [sub_zero,Complex.real_smul]
 norm_num
 ring

theorem actual_centeredRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
 centeredRaw (burnolRieszSingleFourierSource c:Hq) x=burnolRieszReturnRaw c x := by
 rw [centeredRaw,actual_symFourier,actual_halfMean,add_sub_cancel_right]

/-- No zero law is used: the original complete ReturnCounting value is this fixed reader. -/
theorem actual_original_return_count (c:BurnolCompletedMellinCoordinate) :
 countReader (burnolRieszSingleFourierSource c:Hq)=ReturnCounting.value c := by
 apply Lp.ext
 filter_upwards [countReader_read (burnolRieszSingleFourierSource c:Hq),ReturnCounting.value_coeFn c]
  with x generated original
 rw [generated,original]
 unfold countRaw ReturnCounting.eventRaw
 apply Finset.sum_congr rfl
 intro n _
 exact actual_centeredRaw c _

/-- The original free whole position source now has a fixed arithmetic carrier for parameter reads. -/
theorem actual_whole_inverse_reader (c:BurnolCompletedMellinCoordinate) :
 OriginalKElementaryArithmeticAction.FreeParameter.Position.wholeValue c=
  -OriginalKElementaryArithmeticAction.unitResolventSource c ConstantDual.value-
   countReader (burnolRieszSingleFourierSource c:Hq) := by
 rw [actual_original_return_count]
 exact OriginalKElementaryArithmeticAction.FreeParameter.Inverse.actual_whole_inverse_source c

end OriginalKElementaryArithmeticAction.FreeParameter.CountReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
