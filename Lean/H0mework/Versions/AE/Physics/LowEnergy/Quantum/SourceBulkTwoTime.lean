import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeGapWardFirstJet
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBoundedInsertionTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceBulkTwoTime
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseNoetherChannelGap SourceInverseNoetherEnergy SourceJointResidualEnergy
open SourceRetardedIncrement SourceActualResolventEnergy FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem exp_eigen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : E →L[ℂ] E) (x : E) (c : ℂ) (h : D x=c • x) :
    NormedSpace.exp D x=Complex.exp c • x := by
  have hp (n : ℕ) : (D^n) x=c^n • x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_apply_eq_comp,ih,map_smul,h,smul_smul,pow_succ',mul_comm]
  let ev := ContinuousLinearMap.apply ℂ E x
  change ev (NormedSpace.exp D)=_
  rw [NormedSpace.exp_eq_tsum ℂ,ev.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) D)]
  change (∑' n : ℕ,((n.factorial : ℂ)⁻¹) • ((D^n) x))=Complex.exp c • x
  rw [Complex.exp_eq_exp_ℂ,NormedSpace.exp_eq_tsum ℂ]
  let sx : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight x
  have hs := sx.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) c)
  change (∑' n : ℕ,((n.factorial : ℂ)⁻¹) • c^n) • x=
    ∑' n : ℕ,(((n.factorial : ℂ)⁻¹) • c^n) • x at hs
  rw [hs]
  apply tsum_congr
  intro n
  rw [hp,smul_smul,smul_eq_mul]

/-- All original core channels, including escape, evolve with their actual graded eigenvalues. -/
def coreTime (F : Index) (g : diagonal.domain) (t : ℝ) : QuantumTest :=
  ∑ i : Channel F,Complex.exp ((-Complex.I)*(channelValue F i : ℂ)*(t : ℂ)) • channelTest F g i

private theorem channel_embed (F : Index) (g : diagonal.domain) (i : Channel F) :
    embed (channelTest F g i)=channel F i (g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem channel_eigen (F : Index) (g : diagonal.domain) (i : Channel F) :
    GaussGradedCompression.compression F (channel F i (g : H))=
      (channelValue F i : ℂ) • channel F i (g : H) := by
  have h := congrArg embed (actual_channel_eigen F g i)
  have he (q : QuantumTest) : embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simpa only [he,channel_embed,map_smul] using! h

private theorem time_channel (F : Index) (g : diagonal.domain) (i : Channel F) (t : ℝ) :
    SourceFiniteUnitary.time (GaussGradedCompression.compression F) t (channel F i (g : H))=
      Complex.exp ((-Complex.I)*(channelValue F i : ℂ)*(t : ℂ)) • channel F i (g : H) := by
  apply exp_eigen
  change (t : ℝ) • ((-Complex.I) • (GaussGradedCompression.compression F (channel F i (g : H))))=_
  rw [channel_eigen,smul_smul]
  rw [←smul_assoc,Complex.real_smul]
  congr 1
  ring

private theorem channel_resolution (F : Index) (g : H) : ∑ i : Channel F,channel F i g=g := by
  rw [Fintype.sum_option]
  simp only [channel]
  have hs := congrArg (supportSpan F).subtypeL
    ((sourceBasis F).sum_repr ((supportSpan F).orthogonalProjectionOnto g))
  simp only [map_sum,map_smul] at hs
  change escapeProjection F g+(∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i : H))=g
  change (∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i : H))=((supportSpan F).orthogonalProjectionOnto g : H) at hs
  rw [hs]
  change (g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g=g
  abel

/-- This is the original graded time action, lifted back to its own invariant source core. -/
theorem actual_core_time (F : Index) (g : diagonal.domain) (t : ℝ) :
    embed (coreTime F g t)=SourceFiniteUnitary.time (GaussGradedCompression.compression F) t (g : H) := by
  rw [←channel_resolution F (g : H),map_sum]
  simp only [coreTime,map_sum,map_smul,channel_embed,time_channel]

/-- The unbounded original bulk is evaluated on actual core trajectories, never on a chosen bounded substitute. -/
def kernel (F : Index) (T : End) (k g : diagonal.domain) (t s : ℝ) : ℂ :=
  sourcePair (T (coreTime F k t)) (bulkAction (T (coreTime F g s)))

def phase (a t : ℝ) : ℂ := Complex.exp ((-Complex.I)*(a : ℂ)*(t : ℂ))
def leg (z : ℂ) (a t : ℝ) : ℂ := Complex.exp (Complex.I*z*(t : ℂ))*phase a t

private theorem leg_exp (z : ℂ) (a t : ℝ) :
    leg z a t=Complex.exp ((Complex.I*(z-(a : ℂ)))*(t : ℂ)) := by
  rw [leg,phase,←Complex.exp_add]
  congr 1
  ring

private theorem exponent_negative (z : ℂ) (hz : 0<z.im) (a : ℝ) :
    (Complex.I*(z-(a : ℂ))).re<0 := by
  simpa only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.sub_im,Complex.ofReal_im,sub_zero,
    zero_mul,one_mul,zero_sub,neg_lt_zero] using hz

private theorem leg_integrable (z : ℂ) (hz : 0<z.im) (a : ℝ) : IntegrableOn (leg z a) (Set.Ioi 0) := by
  change IntegrableOn (fun t => leg z a t) _
  simp_rw [leg_exp]
  exact integrableOn_exp_mul_complex_Ioi (exponent_negative z hz a) 0

private theorem leg_star_integrable (z : ℂ) (hz : 0<z.im) (a : ℝ) :
    IntegrableOn (fun t => star (leg z a t)) (Set.Ioi 0) :=
  (RCLike.conjLIE (K := ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (leg_integrable z hz a)

private theorem leg_integral (z : ℂ) (hz : 0<z.im) (a : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,leg z a t)=(-Complex.I)*((a : ℂ)-z)⁻¹ := by
  simp_rw [leg_exp]
  rw [integral_exp_mul_complex_Ioi (exponent_negative z hz a) 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  have hn : (a : ℂ)-z≠0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hh
    exact hz.ne' hh
  have he : z-(a : ℂ)=-((a : ℂ)-z) := by ring
  rw [he,mul_neg,div_neg,neg_div,neg_neg,one_div,mul_inv,Complex.inv_I]

private theorem kernel_channels (F : Index) (T : End) (k g : diagonal.domain) (t s : ℝ) :
    kernel F T k g t s=∑ i : Channel F,∑ j : Channel F,
      star (phase (channelValue F i) t)*phase (channelValue F j) s*
        sourcePair (T (channelTest F k i)) (bulkAction (T (channelTest F g j))) := by
  simp only [kernel,coreTime,phase,map_sum,map_smul,sourcePair,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive diagonal energy and Hermitian exchange come from the same original bulk form. -/
theorem actual_kernel_diagonal (F : Index) (T : End) (g : diagonal.domain) (t : ℝ) :
    (kernel F T g g t t).re=inverseForm (T (coreTime F g t)) ∧
    (kernel F T g g t t).im=0 ∧ 0≤(kernel F T g g t t).re := by
  exact ⟨original_bulk_energy _,original_bulk_real _,by change 0≤(sourcePair _ (bulkAction _)).re;rw [original_bulk_energy];exact original_inverse_nonnegative _⟩

def weightedKernel (F : Index) (T : End) (k g : diagonal.domain) (zL zR : ℂ) (t s : ℝ) : ℂ :=
  star (Complex.exp (Complex.I*zL*(t : ℂ)))*Complex.exp (Complex.I*zR*(s : ℂ))*kernel F T k g t s

def laplaceKernel (F : Index) (T : End) (k g : diagonal.domain) (zL zR : ℂ) : ℂ :=
  ∫ s : ℝ in Set.Ioi 0,∫ t : ℝ in Set.Ioi 0,weightedKernel F T k g zL zR t s

private theorem weighted_channels (F : Index) (T : End) (k g : diagonal.domain) (zL zR : ℂ) (t s : ℝ) :
    weightedKernel F T k g zL zR t s=∑ i : Channel F,∑ j : Channel F,
      star (leg zL (channelValue F i) t)*leg zR (channelValue F j) s*
        sourcePair (T (channelTest F k i)) (bulkAction (T (channelTest F g j))) := by
  rw [weightedKernel,kernel_channels]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [leg,star_mul]
  ring

/-- The unbounded source insertion has an absolutely integrable, full two-time Laplace response. -/
theorem actual_kernel_integrable (F : Index) (T : End) (k g : diagonal.domain) (zL zR : ℂ)
    (hL : 0<zL.im) (hR : 0<zR.im) :
    Integrable (fun p : ℝ×ℝ => weightedKernel F T k g zL zR p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      ((leg_star_integrable zL hL (channelValue F i)).mul_prod
        (leg_integrable zR hR (channelValue F j))).mul_const
          (sourcePair (T (channelTest F k i)) (bulkAction (T (channelTest F g j))))))
  exact hi.congr (Eventually.of_forall (fun p => (weighted_channels F T k g zL zR p.1 p.2).symm))

private theorem separated_integral {ι : Type*} [Fintype ι] (f g : ι → ℝ → ℂ) (c : ι → ι → ℂ)
    (hf : ∀ i,IntegrableOn (f i) (Set.Ioi 0)) (hg : ∀ j,IntegrableOn (g j) (Set.Ioi 0)) :
    (∫ s : ℝ in Set.Ioi 0,∫ t : ℝ in Set.Ioi 0,∑ i,∑ j,f i t*g j s*c i j)=
      ∑ i,∑ j,(∫ t : ℝ in Set.Ioi 0,f i t)*(∫ s : ℝ in Set.Ioi 0,g j s)*c i j := by
  have hin (s : ℝ) : (∫ t : ℝ in Set.Ioi 0,∑ i,∑ j,f i t*g j s*c i j)=
      ∑ i,∑ j,(∫ t : ℝ in Set.Ioi 0,f i t)*g j s*c i j := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ((hf i).mul_const _).mul_const _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => ((hf i).mul_const _).mul_const _)]
    simp only [integral_mul_const]
  simp_rw [hin]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ((hg j).const_mul _).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => ((hg j).const_mul _).mul_const _)]
  simp only [integral_mul_const,integral_const_mul]

/-- Both nonreal source states are exactly the double Laplace readout of the same core-time bulk. -/
theorem actual_laplace_kernel (F : Index) (T : End) (k g : diagonal.domain) (zL zR : ℂ)
    (hL : 0<zL.im) (hR : 0<zR.im) :
    laplaceKernel F T k g zL zR=
      sourcePair (T (state F zL hL.ne' k)) (bulkAction (T (state F zR hR.ne' g))) := by
  unfold laplaceKernel
  simp_rw [weighted_channels]
  rw [separated_integral _ _ _ (fun i => leg_star_integrable zL hL (channelValue F i))
    (fun j => leg_integrable zR hR (channelValue F j))]
  have hs (i : Channel F) : (∫ t : ℝ in Set.Ioi 0,star (leg zL (channelValue F i) t))=
      star ((-Complex.I)*((channelValue F i : ℂ)-zL)⁻¹) := by
    change (∫ t : ℝ in Set.Ioi 0,(starRingEnd ℂ) (leg zL (channelValue F i) t))=(starRingEnd ℂ) _
    rw [integral_conj,leg_integral zL hL]
  simp_rw [hs,leg_integral zR hR]
  rw [actual_state_channels,actual_state_channels]
  simp only [map_sum,map_smul,sourcePair,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x x_1 =>
    ((channelValue F x : ℂ)-zR)⁻¹*(star (((channelValue F x_1 : ℂ)-zL)⁻¹)*
      inner ℂ (embed (T (channelTest F k x_1))) (embed (bulkAction (T (channelTest F g x))))))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [star_mul,star_neg,Complex.star_def,Complex.conj_I,neg_neg]
  ring_nf
  norm_num [Complex.I_sq]

open GaussAdjointHistory SourceInverseGapWardFirstJet

/-- The original signed current is read from the two-time bulk without bounding that insertion. -/
def timeCurrent (F : Index) (μ : ℝ) (g k : diagonal.domain) (T : End) : ℝ :=
  ∫ w : ℝ,‖finiteResolvent F (star (line μ w)) (k : H)‖^2*
    (-(laplaceKernel F T (iterate 1 g) g (line μ w) (line μ w))).im

theorem actual_fixed_source_time_current (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (T : End) :
    fixedSourceCurrent F μ hμ g k T=timeCurrent F μ g k T := by
  unfold fixedSourceCurrent timeCurrent
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => by
    dsimp only
    rw [actual_laplace_kernel F T (iterate 1 g) g (line μ w) (line μ w)
      (by simpa only [line_im] using hμ) (by simpa only [line_im] using hμ)]
    simp only [Complex.neg_im])

/-- The complete original cost consumes this kernel at the same cutoff and cofinal source occurrence. -/
theorem actual_original_time_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g : H) (k : H) ≤
          ε+(4*SourceScalarSignedInverseReturn.formPrice sharp/μ)*
            timeCurrent F μ g k (SourceScalarInverseRetardedBudget.theta m ell) := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_original_fixed_source_budget sharp μ hμ g k ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  simpa only [actual_fixed_source_time_current F μ hμ] using hF

end LowEnergy.SourceBulkTwoTime
