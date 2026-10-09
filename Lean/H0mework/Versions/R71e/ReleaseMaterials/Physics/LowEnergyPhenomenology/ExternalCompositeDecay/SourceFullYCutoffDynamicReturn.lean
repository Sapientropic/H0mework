import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCutoffOrbitPrice
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceRelativePowerTail
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSourceNext
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussUnitaryHistory FullYDynamicSource FullYSourceCutoffVolterra FullYSourceCutoffSharp
open SourceScalarPairedTransport MeasureTheory Filter
open scoped Topology InnerProductSpace Interval
attribute [local irreducible] embed diagonalAction GaussYukawaOperator.originalAction GaussFullHamiltonian.adjointAction

section Duhamel
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]
local instance :NormedAlgebra ℝ (E→L[ℂ]E):=NormedAlgebra.restrictScalars ℝ ℂ _
private theorem backward_time_derivative(A:E→L[ℂ]E)(t s:ℝ):
    HasDerivAt (fun v:ℝ=>SourceFiniteUnitary.time A (t-v))
      (Complex.I • (SourceFiniteUnitary.time A (t-s)*A)) s:=by
  have ht:=hasDerivAt_exp_smul_const ((-Complex.I) • A) (t-s)
  have hc:=ht.comp_const_sub t s
  change HasDerivAt (fun v:ℝ=>SourceFiniteUnitary.time A (t-v))
    (-(SourceFiniteUnitary.time A (t-s)*((-Complex.I) • A))) s at hc
  exact hc.congr_deriv (by rw [neg_smul,mul_neg,neg_neg,mul_smul_comm])
theorem source_forced_time_integral(A:E→L[ℂ]E)(u r:ℝ→E)
    (hu:∀s:ℝ,HasDerivAt u ((-Complex.I) • (A (u s)+r s)) s)
    (hr:Continuous r)(t:ℝ):
    u t-SourceFiniteUnitary.time A t (u 0)=
      (-Complex.I) • ∫s in (0:ℝ)..t,SourceFiniteUnitary.time A (t-s) (r s):=by
  have hd(s:ℝ):HasDerivAt (fun v:ℝ=>SourceFiniteUnitary.time A (t-v) (u v))
      ((-Complex.I) • SourceFiniteUnitary.time A (t-s) (r s)) s:=by
    have hc:=(ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt s
      (backward_time_derivative A t s)
    have h:=hc.clm_apply (hu s)
    change HasDerivAt (fun v:ℝ=>SourceFiniteUnitary.time A (t-v) (u v))
      ((Complex.I • (SourceFiniteUnitary.time A (t-s)*A)) (u s)+
        SourceFiniteUnitary.time A (t-s) ((-Complex.I) • (A (u s)+r s))) s at h
    apply h.congr_deriv
    change Complex.I • SourceFiniteUnitary.time A (t-s) (A (u s))+
      SourceFiniteUnitary.time A (t-s) ((-Complex.I) • (A (u s)+r s))=_
    rw [map_smul,map_add,smul_add]
    module
  have hc:Continuous (fun s:ℝ=>SourceFiniteUnitary.time A (t-s) (r s)):=
    (continuous_iff_continuousAt.mpr (fun s=>(backward_time_derivative A t s).continuousAt)).clm_apply hr
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hd s)
    ((hc.const_smul (-Complex.I)).intervalIntegrable 0 t)
  simpa only [sub_self,sub_zero,SourceFiniteUnitary.time_zero,one_apply_eq_self,
    intervalIntegral.integral_smul] using hi.symm
end Duhamel

def finiteCutTime(F:Index)(sharp:Bool)(n:ℕ)(t:ℝ):H→L[ℂ]H:=
  SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoffBranch sharp n) t
def dynamicCutoffResidual(F:Index)(sharp:Bool)(f:QuantumTest)(n:ℕ)(t:ℝ):H:=
  embed (sourceY sharp (literalCoreTime F sharp f t))-
    cutoffBranch sharp n (embed (literalCoreTime F sharp f t))
private theorem source_time_continuous(F:Index)(sharp:Bool)(f:QuantumTest):
    Continuous (fun t:ℝ=>embed (literalCoreTime F sharp f t)):=
  continuous_iff_continuousAt.mpr (fun t=>(literal_core_time_derivative F sharp f t).continuousAt)
theorem dynamic_cutoff_residual_continuous(F:Index)(sharp:Bool)(f:QuantumTest)(n:ℕ):
    Continuous (dynamicCutoffResidual F sharp f n):=
  (source_y_time_continuous F sharp f).sub ((cutoffBranch sharp n).continuous.comp (source_time_continuous F sharp f))

/-- The same literal uncut trajectory supplies the entire inhomogeneous cutoff error. -/
theorem actual_cutoff_dynamic_duhamel(F:Index)(sharp:Bool)(f:QuantumTest)(n:ℕ)(t:ℝ):
    embed (literalCoreTime F sharp f t)-finiteCutTime F sharp n t (embed f)=
      (-Complex.I) • ∫s in (0:ℝ)..t,
        finiteCutTime F sharp n (t-s) (dynamicCutoffResidual F sharp f n s):=by
  have he(q:QuantumTest):embed (SourceScalarPairedTransport.compressionCore F q)=
      GaussGradedCompression.compression F (embed q):=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hd(s:ℝ):HasDerivAt (fun v:ℝ=>embed (literalCoreTime F sharp f v))
      ((-Complex.I) • ((GaussGradedCompression.compression F+cutoffBranch sharp n)
        (embed (literalCoreTime F sharp f s))+dynamicCutoffResidual F sharp f n s)) s:=by
    apply (literal_core_time_derivative F sharp f s).congr_deriv
    apply congrArg (fun x:H=>(-Complex.I) • x)
    simp only [LinearMap.add_apply,map_add,he,add_apply,dynamicCutoffResidual]
    abel
  have h:=source_forced_time_integral (GaussGradedCompression.compression F+cutoffBranch sharp n)
    (fun s:ℝ=>embed (literalCoreTime F sharp f s)) (dynamicCutoffResidual F sharp f n)
    hd (dynamic_cutoff_residual_continuous F sharp f n) t
  simpa only [literal_core_time_zero,finiteCutTime] using h

private theorem recurrence_norm_bound {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    (Q B:E→L[ℂ]E)(K:ℕ→E→L[ℂ]E)(h0:K 0=B)(hstep:∀n,K (n+1)=B+Q*K n)
    (hQ:‖Q‖ ≤ 1)(n:ℕ):‖K n‖ ≤ ((n+1:ℕ):ℝ)*‖B‖:=by
  induction n with
  | zero => rw [h0];simp only [Nat.zero_add,Nat.cast_one,one_mul,le_refl]
  | succ n ih =>
    have hp:‖Q*K n‖ ≤ ‖K n‖:=
      (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))
    calc
      ‖K (n+1)‖ ≤ ‖B‖+‖Q*K n‖:=by rw [hstep];exact norm_add_le _ _
      _ ≤ ‖B‖+((n+1:ℕ):ℝ)*‖B‖:=add_le_add le_rfl (hp.trans ih)
      _=((n+1+1:ℕ):ℝ)*‖B‖:=by push_cast;ring
theorem cutoff_linear_norm(n:ℕ):
    ‖cutoff n‖ ≤ ((n+1:ℕ):ℝ)*‖GaussYukawaOperator.bounded‖:=
  recurrence_norm_bound (1-GaussRadialDomain.inverseRadius) GaussYukawaOperator.bounded cutoff
    rfl (fun _=>rfl)
    ((CStarAlgebra.norm_le_one_iff_of_nonneg SourceRelativePowerTail.sourceComplement
      SourceRelativePowerTail.source_complement_nonnegative).mpr SourceRelativePowerTail.source_complement_le_one) n
private theorem cut_time_bound(F:Index)(sharp:Bool)(n:ℕ)(t:ℝ):
    ‖finiteCutTime F sharp n t‖ ≤ sourceGrowth n |t|:=by
  cases sharp
  · exact source_finite_time_bound n F t
  · exact source_sharp_time_bound n F t

private theorem interval_displacement(t s:ℝ)(hs:s∈Set.Icc (min 0 t) (max 0 t)):
    |t-s| ≤ |t|:=by
  rcases le_total 0 t with ht|ht
  · simp only [min_eq_left ht,max_eq_right ht,Set.mem_Icc] at hs
    rw [abs_of_nonneg ht,abs_of_nonneg (sub_nonneg.mpr hs.2)]
    linarith [hs.1]
  · simp only [min_eq_right ht,max_eq_left ht,Set.mem_Icc] at hs
    rw [abs_of_nonpos ht,abs_of_nonpos (sub_nonpos.mpr hs.1)]
    linarith [hs.2]

/-- The old degree-56 cutoff propagator spends the newly generated actual uncut residual. -/
theorem actual_cutoff_dynamic_growth_price(F:Index)(sharp:Bool)(f:QuantumTest)(n:ℕ)(t:ℝ):
    ‖embed (literalCoreTime F sharp f t)-finiteCutTime F sharp n t (embed f)‖ ≤
      sourceGrowth n |t| * (∫s in (min 0 t)..(max 0 t),dynamicCutoffError F sharp f n s):=by
  let A:=GaussGradedCompression.compression F+cutoffBranch sharp n
  let v:=fun s:ℝ=>finiteCutTime F sharp n (t-s) (dynamicCutoffResidual F sharp f n s)
  have hc:Continuous v:=
    (continuous_iff_continuousAt.mpr (fun s=>(backward_time_derivative A t s).continuousAt)).clm_apply
      (dynamic_cutoff_residual_continuous F sharp f n)
  have hb(s:ℝ)(hs:s∈Set.Icc (min 0 t) (max 0 t)):
      ‖v s‖ ≤ sourceGrowth n |t| * dynamicCutoffError F sharp f n s:=by
    exact ((finiteCutTime F sharp n (t-s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((cut_time_bound F sharp n (t-s)).trans
        (sourceGrowth_mono n (abs_nonneg _) (interval_displacement t s hs))) (norm_nonneg _))
  have hnorm:‖∫s in (0:ℝ)..t,v s‖ ≤ ∫s in (min 0 t)..(max 0 t),‖v s‖:=by
    rcases le_total 0 t with ht|ht
    · simpa only [min_eq_left ht,max_eq_right ht] using intervalIntegral.norm_integral_le_integral_norm (f:=v) ht
    · rw [intervalIntegral.integral_symm t 0,norm_neg]
      simpa only [min_eq_right ht,max_eq_left ht] using intervalIntegral.norm_integral_le_integral_norm (f:=v) ht
  have hm:=intervalIntegral.integral_mono_on (show min (0:ℝ) t ≤ max 0 t from min_le_max)
    (hc.norm.intervalIntegrable (μ:=volume) (min 0 t) (max 0 t))
    ((continuous_const.mul (dynamic_cutoff_error_continuous F sharp f n)).intervalIntegrable (μ:=volume) (min 0 t) (max 0 t)) hb
  rw [actual_cutoff_dynamic_duhamel,norm_smul,norm_neg,Complex.norm_I,one_mul]
  exact hnorm.trans (by simpa only [Pi.mul_apply,intervalIntegral.integral_const_mul] using hm)
private theorem dynamic_error_integral_nonneg(F:Index)(sharp:Bool)(f:QuantumTest)(n:ℕ)
    (a b:ℝ)(hab:a ≤ b):0 ≤ ∫s in a..b,dynamicCutoffError F sharp f n s:=
  intervalIntegral.integral_nonneg hab (fun s _=>show 0 ≤ dynamicCutoffError F sharp f n s from norm_nonneg _)
private theorem growth_error_limit(F:Index)(sharp:Bool)(f:QuantumTest)(a b T:ℝ)(hab:a ≤ b)(hT:0 ≤ T):
    Tendsto (fun n:ℕ=>sourceGrowth n T*(∫s in a..b,dynamicCutoffError F sharp f n s)) atTop (𝓝 0):=by
  let E:=fun n:ℕ=>∫s in a..b,dynamicCutoffError F sharp f n s
  let upper:=fun n:ℕ=>∑j∈Finset.range 57,(T*‖GaussYukawaOperator.bounded‖)^j*(((n+1:ℕ):ℝ)^j*E n)
  have hb(n:ℕ):sourceGrowth n T*E n ≤ upper n:=by
    simp only [sourceGrowth,Finset.sum_mul,upper]
    apply Finset.sum_le_sum
    intro j _
    have hpow:=pow_le_pow_left₀ (mul_nonneg hT (norm_nonneg (cutoff n)))
      (mul_le_mul_of_nonneg_left (cutoff_linear_norm n) hT) j
    have he:T*(((n+1:ℕ):ℝ)*‖GaussYukawaOperator.bounded‖)=
        (T*‖GaussYukawaOperator.bounded‖)*((n+1:ℕ):ℝ):=by ring
    rw [he,mul_pow (T*‖GaussYukawaOperator.bounded‖) ((n+1:ℕ):ℝ)] at hpow
    exact (mul_le_mul_of_nonneg_right hpow (dynamic_error_integral_nonneg F sharp f n a b hab)).trans_eq
      (mul_assoc _ _ _)
  have hl:Tendsto upper atTop (𝓝 0):=by
    have h:=tendsto_finsetSum (Finset.range 57) (fun j _=>
      (actual_dynamic_cutoff_weighted_L1_return F sharp f a b hab j).2.const_mul
        ((T*‖GaussYukawaOperator.bounded‖)^j))
    simpa only [mul_zero,Finset.sum_const_zero,upper,E] using h
  have hn(n:ℕ):0 ≤ sourceGrowth n T*E n:=
    mul_nonneg (Finset.sum_nonneg (fun j _=>pow_nonneg (mul_nonneg hT (norm_nonneg (cutoff n))) j))
      (dynamic_error_integral_nonneg F sharp f n a b hab)
  exact squeeze_zero hn hb hl

private theorem tendsto_of_reverse_norm {E:Type*}[NormedAddCommGroup E](u:ℕ→E)(x:E)
    (h:Tendsto (fun n:ℕ=>‖x-u n‖) atTop (𝓝 0)):Tendsto u atTop (𝓝 x):=by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using h

/-- Literal primal and independent-sharp cutoff propagation converges to the source-generated uncut time. -/
theorem actual_uncut_time_from_original_cutoff(F:Index)(sharp:Bool)(f:QuantumTest)(t:ℝ):
    Tendsto (fun n:ℕ=>finiteCutTime F sharp n t (embed f)) atTop
      (𝓝 (embed (literalCoreTime F sharp f t))):=by
  have hl:=growth_error_limit F sharp f (min 0 t) (max 0 t) |t|
    (show min (0:ℝ) t ≤ max 0 t from min_le_max) (abs_nonneg t)
  have hnorm:Tendsto (fun n:ℕ=>‖embed (literalCoreTime F sharp f t)-finiteCutTime F sharp n t (embed f)‖)
      atTop (𝓝 0):=
    squeeze_zero (fun _=>norm_nonneg _) (fun n=>actual_cutoff_dynamic_growth_price F sharp f n t) hl
  exact tendsto_of_reverse_norm _ _ hnorm

end LowEnergy.FullYDynamicSourceNext
