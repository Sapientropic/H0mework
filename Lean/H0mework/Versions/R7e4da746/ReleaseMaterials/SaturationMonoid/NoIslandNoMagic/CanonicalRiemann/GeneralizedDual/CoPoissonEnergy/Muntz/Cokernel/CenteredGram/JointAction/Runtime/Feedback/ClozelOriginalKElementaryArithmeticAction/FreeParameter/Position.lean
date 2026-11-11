import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.ResponseForcing.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.JointCounting
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.Position
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology ENNReal
local notation "q" => (1/4:ℝ)
open private overflow_bound position_mean_balance from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCounting

theorem actual_free_power_quadrature (eta : ℂ) (etaPositive : 0 < eta.re) (etaBelow : eta.re < 1)
    (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, (((n : ℝ) * x : ℝ) : ℂ) ^ (eta - 1)) -
      (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta -
      (x : ℂ) ^ (eta - 1) * riemannZeta (1 - eta)‖ ≤
      (DirichletRate.constant (1 - eta) + 1) * q ^ (eta.re - 1) := by
  let M : ℕ := ⌊q / x⌋₊
  let N : ℕ := M + 1
  have indexPositive : 0 < N := Nat.succ_pos M
  have basePositive : (0 : ℝ) < N := by exact_mod_cast indexPositive
  have lower : q ≤ (N : ℝ) * x := by
    have actual := Nat.lt_floor_add_one (q / x)
    have scaled := (div_lt_iff₀ positive).mp actual
    dsimp only [N, M]
    push_cast
    linarith
  have width : (N : ℝ) * x - q ≤ x := by
    have actual := (le_div_iff₀ positive).mp (Nat.floor_le (by positivity : (0 : ℝ) ≤ q / x))
    dsimp only [N, M]
    push_cast
    linarith
  have counted : (∑ n ∈ Finset.Icc 1 M, (((n : ℝ) * x : ℝ) : ℂ) ^ (eta - 1)) =
      (x : ℂ) ^ (eta - 1) *
        (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-(1 - eta))) := by
    rw [Finset.mul_sum]
    have indices : Finset.Icc 1 M = Finset.Ico 1 N := by simp only [N, Finset.Ico_add_one_right_eq_Icc]
    rw [indices]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) positive.le,
      Complex.ofReal_natCast, neg_sub]
    ring
  have continuousTerm : (x : ℂ) ^ (eta - 1) *
      (N : ℂ) ^ (1 - (1 - eta)) / (1 - (1 - eta)) =
      (x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ eta / eta := by
    rw [sub_sub_cancel, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), cpow_one,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg basePositive.le positive.le, Complex.ofReal_natCast]
    ring
  have decomposition : (∑ n ∈ Finset.Icc 1 M, (((n : ℝ) * x : ℝ) : ℂ) ^ (eta - 1)) -
      (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta -
      (x : ℂ) ^ (eta - 1) * riemannZeta (1 - eta) =
      (x : ℂ) ^ (eta - 1) * (FiniteForcing.coefficient (1 - eta) N-riemannZeta (1-eta)) +
      ((x : ℂ)⁻¹ * (((N : ℝ) * x : ℝ) : ℂ) ^ eta / eta -
        (x : ℂ)⁻¹ * (q : ℂ) ^ eta / eta) := by
    rw [counted, ← continuousTerm]
    unfold FiniteForcing.coefficient
    ring
  have arithmetic : ‖(x : ℂ) ^ (eta - 1) * (FiniteForcing.coefficient (1 - eta) N-riemannZeta (1-eta))‖ ≤
      DirichletRate.constant (1 - eta) * q ^ (eta.re - 1) := by
    have positiveSource : 0 < (1 - eta).re := by simp only [sub_re, one_re]; linarith
    have belowSource : (1 - eta).re < 1 := by simp only [sub_re, one_re]; linarith
    have rate := DirichletRate.coefficient_rate (1 - eta) positiveSource belowSource N indexPositive
    simp only [sub_re, one_re, neg_sub] at rate
    have constantNonnegative : 0 ≤ DirichletRate.constant (1 - eta) := by
      have realPart : 0 < (1 - eta).re := by
        simp only [sub_re, one_re]
        linarith [etaBelow]
      unfold DirichletRate.constant
      positivity
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos positive]
    simp only [sub_re, one_re]
    calc
      _ ≤ x ^ (eta.re - 1) *
          (DirichletRate.constant (1 - eta) * (N : ℝ) ^ (eta.re - 1)) :=
        mul_le_mul_of_nonneg_left rate (Real.rpow_nonneg positive.le _)
      _ = DirichletRate.constant (1 - eta) * (((N : ℝ) * x) ^ (eta.re - 1)) := by
        rw [Real.mul_rpow basePositive.le positive.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by norm_num) lower (by linarith [etaBelow])) constantNonnegative
  change ‖(∑ n ∈ Finset.Icc 1 M, _) - _ - _‖ ≤ _
  rw [decomposition]
  exact (norm_add_le _ _).trans ((add_le_add arithmetic (overflow_bound eta etaPositive etaBelow x positive N lower width)).trans_eq (by ring))



theorem actual_free_singular_quadrature (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x) :
 ‖(∑ n∈Finset.Icc 1 ⌊q/x⌋₊, (((n:ℝ)*x:ℝ):ℂ)^(-star c.value))-
    (x:ℂ)⁻¹*(q:ℂ)^(1-star c.value)/(1-star c.value)-
    (x:ℂ)^(-star c.value)*riemannZeta (star c.value)‖≤
  (DirichletRate.constant (star c.value)+1)*q^(-c.value.re) := by
 have ep:0<(1-star c.value).re:=by simp only [sub_re,one_re,star_def,conj_re];linarith [c.belowOne]
 have eb:(1-star c.value).re<1:=by simp only [sub_re,one_re,star_def,conj_re];linarith [c.rightHalf]
 have paid:=actual_free_power_quadrature (1-star c.value) ep eb x positive
 simpa only [show (1-star c.value)-1= -star c.value by ring,sub_sub_cancel,
  sub_re,one_re,star_def,conj_re,sub_sub_cancel_left] using paid

/-- The actual free P count pays its entire singular zeta term before an L² value is formed. -/
theorem actual_free_position_bound (c:BurnolCompletedMellinCoordinate) (x:ℝ) (positive:0<x) :
 ‖(∑ n∈Finset.Icc 1 ⌊q/x⌋₊,positionSource c ((n:ℝ)*x))-
   (1/2:ℂ)*(x:ℂ)^(-star c.value)*riemannZeta (star c.value)‖≤PositionCounting.bound c := by
 let M:ℕ:=⌊q/x⌋₊
 let P:ℂ:=∑ n∈Finset.Icc 1 M,(((n:ℝ)*x:ℝ):ℂ)^(-star c.value)
 let R:ℂ:=∑ n∈Finset.Icc 1 M,burnolRieszReturnRaw c ((n:ℝ)*x)
 let J:ℂ:=∫t:ℝ in (0:ℝ)..q,burnolRieszReturnRaw c t
 let G:=GapEuler.gapMean q c
 have sourceSum:(∑ n∈Finset.Icc 1 M,positionSource c ((n:ℝ)*x))=
   (1/2:ℂ)*P-(M:ℂ)*G-R := by
  simp only [positionSource,Finset.sum_sub_distrib,←Finset.mul_sum,
   Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,P,R,G]
 have decomposition:(∑ n∈Finset.Icc 1 M,positionSource c ((n:ℝ)*x))-
    (1/2:ℂ)*(x:ℂ)^(-star c.value)*riemannZeta (star c.value)=
   (1/2:ℂ)*(P-(x:ℂ)⁻¹*(q:ℂ)^(1-star c.value)/(1-star c.value)-
      (x:ℂ)^(-star c.value)*riemannZeta (star c.value))-
   (R-(x:ℂ)⁻¹*J)-((M:ℂ)-(q:ℂ)/(x:ℂ))*G := by
  rw [sourceSum]
  have mean:=position_mean_balance c
  change (1/2:ℂ)*((q:ℂ)^(1-star c.value)/(1-star c.value))-J=(q:ℂ)*G at mean
  linear_combination (x:ℂ)⁻¹*mean
 have constantDefect:‖(M:ℂ)-(q:ℂ)/(x:ℂ)‖≤1 := by
  have lower:=Nat.floor_le (by positivity:(0:ℝ)≤q/x)
  have upper:=Nat.lt_floor_add_one (q/x)
  rw [←Complex.ofReal_natCast,←Complex.ofReal_div,←Complex.ofReal_sub,Complex.norm_real,
   Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr lower)]
  linarith
 have singular:‖(1/2:ℂ)*(P-(x:ℂ)⁻¹*(q:ℂ)^(1-star c.value)/(1-star c.value)-
     (x:ℂ)^(-star c.value)*riemannZeta (star c.value))‖≤
   (1/2:ℝ)*(DirichletRate.constant (star c.value)+1)*q^(-c.value.re) := by
  rw [norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left (actual_free_singular_quadrature c x positive)
   (by norm_num:(0:ℝ)≤1/2)).trans_eq (by ring)
 have regular:‖R-(x:ℂ)⁻¹*J‖≤PositionCounting.returnSlopeBound c*q+PositionCounting.returnBound c:=
  PositionCounting.return_quadrature c x positive
 have contact:‖((M:ℂ)-(q:ℂ)/(x:ℂ))*G‖≤‖G‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right constantDefect (norm_nonneg G)).trans_eq (one_mul _)
 change ‖(∑n∈Finset.Icc 1 M,_) - _‖≤_
 rw [decomposition]
 exact (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans
  ((add_le_add (add_le_add singular regular) contact).trans_eq (by rfl)))

def cutRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
 (symmetricInterval q).indicator (fun t=>PositionCounting.eventRaw c t-
  (1/2:ℂ)*((|t|:ℝ):ℂ)^(-star c.value)*riemannZeta (star c.value)) x

private theorem power_measurable (c:BurnolCompletedMellinCoordinate) :
 Measurable (fun x:ℝ=>((|x|:ℝ):ℂ)^(-star c.value)) := by
 have whole:Measurable (fun t:ℝ=>(t:ℂ)^(-star c.value)) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro t outside
  exact (Complex.continuousAt_ofReal_cpow_const t (-star c.value)
   (Or.inr (by simpa only [mem_compl_iff,mem_singleton_iff] using outside))).continuousWithinAt
 exact whole.comp continuous_abs.measurable

theorem cut_aestronglyMeasurable (c:BurnolCompletedMellinCoordinate) : AEStronglyMeasurable (cutRaw c) volume :=
 ((PositionCounting.event_aestronglyMeasurable c).sub
  (((power_measurable c).aestronglyMeasurable.const_mul (1/2:ℂ)).mul_const
    (riemannZeta (star c.value)))).indicator (measurableSet_symmetricInterval q)

theorem actual_cut_bound (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ‖cutRaw c x‖≤PositionCounting.bound c := by
 by_cases inside:x∈symmetricInterval q
 · rw [cutRaw,indicator_of_mem inside]
   by_cases zero:x=0
   · subst x
     have exponent: -star c.value≠0 := by
      intro same
      have realPart:=congrArg Complex.re same
      simp only [neg_re,star_def,conj_re,zero_re] at realPart
      linarith [c.rightHalf]
     simp only [PositionCounting.eventRaw,DualSourceRaw.channels,abs_zero,div_zero,Nat.floor_zero,
      Finset.Icc_eq_empty_of_lt (by decide:(0:ℕ)<1),Finset.sum_empty,Complex.ofReal_zero,
      Complex.zero_cpow exponent,mul_zero,zero_mul,sub_zero,norm_zero]
     exact PositionCounting.bound_nonnegative c
   · exact actual_free_position_bound c |x| (abs_pos.mpr zero)
 · rw [cutRaw,indicator_of_notMem inside,norm_zero]
   exact PositionCounting.bound_nonnegative c

theorem actual_cut_memLp (c:BurnolCompletedMellinCoordinate) : MemLp (cutRaw c) 2 volume := by
 have dominant:MemLp ((symmetricInterval q).indicator (fun _:ℝ=>(PositionCounting.bound c:ℂ))) 2 volume:=
  memLp_indicator_const 2 (measurableSet_symmetricInterval q) _ (Or.inr (by simp [symmetricInterval]))
 apply dominant.mono (cut_aestronglyMeasurable c)
 filter_upwards with x
 by_cases inside:x∈symmetricInterval q
 · rw [indicator_of_mem inside,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (PositionCounting.bound_nonnegative c)]
   exact actual_cut_bound c x
 · rw [cutRaw,indicator_of_notMem inside,indicator_of_notMem inside,norm_zero]

def cutValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 := (actual_cut_memLp c).toLp (cutRaw c)

theorem actual_cut_read (c:BurnolCompletedMellinCoordinate) : (cutValue c:ℝ→ℂ)=ᵐ[volume]cutRaw c :=
 (actual_cut_memLp c).coeFn_toLp


def wholeTailRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
 if q < |x| then ((|x|:ℝ):ℂ)^(-star c.value) else 0

/-- This tail is the literal original even Mellin kernel at q, before any Unit normalization. -/
theorem actual_whole_tail_memLp (c:BurnolCompletedMellinCoordinate) : MemLp (wholeTailRaw c) 2 volume := by
 let raw:=burnolRadiusMellinTailKernelRaw q c.value
 have first:MemLp raw 2 volume:=burnolRadiusMellinTailKernelRaw_memLp (by norm_num) c.value c.rightHalf
 have complete:=first.add (first.comp_measurePreserving negMeasurePreserving)
 apply complete.ae_eq
 filter_upwards with x
 change raw x+raw (-x)=wholeTailRaw c x
 by_cases nonnegative:0≤x
 · have negOutside:¬q< -x:=by linarith
   simp only [raw,burnolRadiusMellinTailKernelRaw,mem_Ioi,negOutside,if_false,add_zero,
    wholeTailRaw,abs_of_nonneg nonnegative]
 · have negative:x<0:=lt_of_not_ge nonnegative
   have posOutside:¬q<x:=by linarith
   simp only [raw,burnolRadiusMellinTailKernelRaw,mem_Ioi,posOutside,if_false,zero_add,
    wholeTailRaw,abs_of_neg negative]

def wholeTailValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 (actual_whole_tail_memLp c).toLp (wholeTailRaw c)

theorem actual_whole_tail_read (c:BurnolCompletedMellinCoordinate) :
 (wholeTailValue c:ℝ→ℂ)=ᵐ[volume]wholeTailRaw c := (actual_whole_tail_memLp c).coeFn_toLp

def wholeRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
 cutRaw c x-((1/2:ℂ)*riemannZeta (star c.value))*wholeTailRaw c x

def wholeValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 cutValue c-((1/2:ℂ)*riemannZeta (star c.value)) • wholeTailValue c

theorem actual_whole_value_read (c:BurnolCompletedMellinCoordinate) :
 (wholeValue c:ℝ→ℂ)=ᵐ[volume]wholeRaw c := by
 filter_upwards [Lp.coeFn_sub (cutValue c) (((1/2:ℂ)*riemannZeta (star c.value)) • wholeTailValue c),
  Lp.coeFn_smul ((1/2:ℂ)*riemannZeta (star c.value)) (wholeTailValue c),
  actual_cut_read c,actual_whole_tail_read c] with x difference scalar cut tail
 change (cutValue c-((1/2:ℂ)*riemannZeta (star c.value)) • wholeTailValue c:BurnolL2) x=_
 rw [difference,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,cut,tail]
 rfl

/-- The global source equality keeps the outside tail as well as both inside mean contacts. -/
theorem actual_whole_raw_source (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
 wholeRaw c x=PositionCounting.eventRaw c x-
  (1/2:ℂ)*((|x|:ℝ):ℂ)^(-star c.value)*riemannZeta (star c.value) := by
 by_cases inside:x∈symmetricInterval q
 · have tail:¬(q < |x|):=not_lt.mpr (abs_le.mpr inside)
   rw [wholeRaw,cutRaw,indicator_of_mem inside,wholeTailRaw,if_neg tail,mul_zero,sub_zero]
 · have outside:q < |x|:=lt_of_not_ge (fun small=>inside (abs_le.mp small))
   rw [wholeRaw,cutRaw,indicator_of_notMem inside,wholeTailRaw,if_pos outside,
    PositionCounting.event_outside c x outside]
   ring

theorem actual_whole_native_read (c:BurnolCompletedMellinCoordinate) :
 (wholeValue c:ℝ→ℂ)=ᵐ[volume]fun x=>PositionCounting.eventRaw c x-
  (1/2:ℂ)*((|x|:ℝ):ℂ)^(-star c.value)*riemannZeta (star c.value) :=
 (actual_whole_value_read c).trans (Eventually.of_forall (actual_whole_raw_source c))

/-- The freely generated whole field specializes to the original zero-owned position count. -/
theorem actual_original_zero_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 wholeValue c=PositionCounting.value c zero := by
 have conjugateZero:riemannZeta (star c.value)=0:=by
  simpa only [star_def,zero,map_zero] using riemannZeta_conj c.value
 apply Lp.ext
 filter_upwards [actual_whole_native_read c,PositionCounting.value_coeFn c zero] with x free actual
 rw [conjugateZero,mul_zero,sub_zero] at free
 exact free.trans actual.symm

/-- Both actual P/b legs, with their original coefficients, belong to this same free full source. -/
def jointValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 Kernel.beta c • wholeValue c+Kernel.A c • CountingDual.value c

theorem actual_original_zero_joint (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
 jointValue c=JointCounting.value c zero := by
 rw [jointValue,actual_original_zero_value c zero]
 rfl

/-- The outer source is paid, not suppressed before exact-order parameter reading. -/
theorem actual_whole_outside_raw (c:BurnolCompletedMellinCoordinate) (x:ℝ) (outside:q < |x|) :
 wholeRaw c x= -((1/2:ℂ)*riemannZeta (star c.value))*((|x|:ℝ):ℂ)^(-star c.value) := by
 rw [actual_whole_raw_source,PositionCounting.event_outside c x outside]
 ring

end OriginalKElementaryArithmeticAction.FreeParameter.Position
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
