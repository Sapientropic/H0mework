import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.WholeLift
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PowerCountingOrigin


set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.PowerWhole
open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalPaPhysicalGreen
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Q" => Constructor.zeroMean
local instance : IsFiniteMeasure μq :=
  ⟨lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)⟩
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def exponent (c:BurnolCompletedMellinCoordinate) : ℂ := 1-star c.value
private theorem exponent_range (c:BurnolCompletedMellinCoordinate) :
    0<(exponent c).re ∧ (exponent c).re<1/2 := by
  simp only [exponent,sub_re,one_re,star_def,conj_re]
  constructor <;> linarith [c.rightHalf,c.belowOne]
private theorem exponent_ne_one (c:BurnolCompletedMellinCoordinate) : exponent c≠1 := by
  intro same
  have h:=(exponent_range c).2
  rw [same] at h
  norm_num at h
private theorem exponent_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    riemannZeta (exponent c)=0 :=
  tendsto_nhds_unique (DirichletCoefficient.coefficient_tendsto_riemannZeta
    (exponent c) (exponent_range c).1 (exponent_ne_one c))
    (DirichletCoefficient.original_coefficient_limits c zero).2

private def compactRaw (c:BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  (symmetricInterval q).indicator (SingularCounting.powerRaw c)
private def finiteRaw (c:BurnolCompletedMellinCoordinate) (N:ℕ) (x:ℝ) : ℂ :=
  (∑n∈Finset.Ico 1 N,compactRaw c ((n:ℝ)*x))-
    ∫a:ℝ in Ioc 0 (N:ℝ),compactRaw c (a*x)
def limitRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
  PowerCountingOrigin.error (exponent c) |x|+
    (q:ℂ)^(-exponent c)*((1/2:ℂ)-((Int.fract (q/|x|):ℝ):ℂ))

private theorem power_read (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
    SingularCounting.powerRaw c x=((|x|:ℝ):ℂ)^(-exponent c) := by
  unfold SingularCounting.powerRaw exponent
  congr 1
  ring
private theorem compact_measurable (c:BurnolCompletedMellinCoordinate) : Measurable (compactRaw c) := by
  apply Measurable.indicator _ (measurableSet_symmetricInterval q)
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  exact (Complex.continuousAt_ofReal_cpow_const |x| (star c.value-1)
    (Or.inr (abs_ne_zero.mpr outside))).comp continuous_abs.continuousAt |>.continuousWithinAt
private theorem compact_source (c:BurnolCompletedMellinCoordinate) :
    (E (SingularCounting.powerL2 c):ℝ→ℂ)=ᵐ[volume] compactRaw c := by
  have localRead:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (SingularCounting.power_coeFn c)
  filter_upwards [burnolQuarterZeroExtension_coe (SingularCounting.powerL2 c),localRead] with x extended actual
  rw [extended]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,compactRaw,indicator_of_mem inside,actual inside]
  · rw [indicator_of_notMem inside,compactRaw,indicator_of_notMem inside]

private theorem source_raw (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    (DualSource.source N (E (SingularCounting.powerL2 c)):ℝ→ℂ)=ᵐ[volume] finiteRaw c N := by
  let seed:=E (SingularCounting.powerL2 c)
  have normalization:=source_l2_bochner_coeFn (volume.restrict (Ioc 0 (N:ℝ)))
    (fun a=>ContinuousChannels.channel 1 a seed) (ContinuousChannels.channel_integrable 1 N seed)
    (fun p:ℝ×ℝ=>compactRaw c (p.1*p.2)) ((compact_measurable c).comp (by fun_prop)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
      exact DualSourceRaw.channel_coeFn seed _ (compact_source c) a inside.1)
  have channels:∀ᵐ x:ℝ ∂volume,∀n:{n:ℕ//n∈Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n:ℝ) seed x=compactRaw c ((n:ℝ)*x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn seed _ (compact_source c) (n:ℝ)
      (by exact_mod_cast (Finset.mem_Ico.mp n.property).1)
  filter_upwards [Lp.coeFn_sub (∑n∈Finset.Ico 1 N,ContinuousChannels.channel 1 n seed)
    (∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a seed),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n=>ContinuousChannels.channel 1 n seed),normalization,channels]
    with x difference summed average channel
  change ((∑n∈Finset.Ico 1 N,ContinuousChannels.channel 1 n seed)-
    ∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 a seed:BurnolL2) x=_
  rw [difference,Pi.sub_apply,summed,average]
  unfold finiteRaw
  congr 1
  exact Finset.sum_congr rfl (fun n inside=>channel ⟨n,inside⟩)

private theorem cutoff_read (c:BurnolCompletedMellinCoordinate) (a x:ℝ) (positive:0<a) (nonzero:x≠0) :
    compactRaw c (a*x)=(Ioc 0 q).indicator (fun t:ℝ=>(t:ℂ)^(-exponent c)) (a*|x|) := by
  have magnitude:|a*x|=a*|x|:=by rw [abs_mul,abs_of_pos positive]
  have lower:0<a*|x|:=mul_pos positive (abs_pos.mpr nonzero)
  by_cases inside:a*|x|≤q
  · have sourceInside:a*x∈symmetricInterval q:=abs_le.mp (magnitude.trans_le inside)
    have targetInside:a*|x|∈Ioc 0 q:=⟨lower,inside⟩
    rw [compactRaw,indicator_of_mem sourceInside,power_read,magnitude,indicator_of_mem targetInside]
  · have sourceOutside:a*x∉symmetricInterval q:=fun h=>inside (magnitude.symm.trans_le (abs_le.mpr h))
    have targetOutside:a*|x|∉Ioc 0 q:=fun h=>inside h.2
    rw [compactRaw,indicator_of_notMem sourceOutside,indicator_of_notMem targetOutside]

private theorem normalization_read (c:BurnolCompletedMellinCoordinate) (N:ℕ) (x:ℝ) (nonzero:x≠0) :
    (∫a:ℝ in Ioc 0 (N:ℝ),compactRaw c (a*x))=
      ((|x|:ℝ):ℂ)⁻¹*((min ((N:ℝ)*|x|) q:ℝ):ℂ)^(1-exponent c)/(1-exponent c) := by
  have positive:=abs_pos.mpr nonzero
  have changeSource:=setIntegral_congr_fun (μ:=volume) measurableSet_Ioc
    (fun a (inside:a∈Ioc 0 (N:ℝ))=>cutoff_read c a x inside.1 nonzero)
  rw [changeSource,←intervalIntegral.integral_of_le (Nat.cast_nonneg N),
    intervalIntegral.integral_comp_mul_right _ positive.ne',zero_mul,
    intervalIntegral.integral_of_le (by positivity:0≤(N:ℝ)*|x|),
    integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,Ioc_inter_Ioc,
    max_self,min_comm q ((N:ℝ)*|x|),←intervalIntegral.integral_of_le (by positivity:0≤min ((N:ℝ)*|x|) q)]
  rw [integral_cpow (Or.inl (by have h:=(exponent_range c).2;simp only [neg_re];linarith)),
    show -exponent c+1=1-exponent c by ring,Complex.ofReal_zero,
    zero_cpow (sub_ne_zero.mpr (Ne.symm (exponent_ne_one c))),sub_zero]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  ring

private theorem integer_read (c:BurnolCompletedMellinCoordinate) (N:ℕ) (x:ℝ) (nonzero:x≠0) :
    (∑n∈Finset.Ico 1 N,compactRaw c ((n:ℝ)*x))=
      ∑n∈Finset.Icc 1 (min ⌊q/|x|⌋₊ (N-1)),(((n:ℝ)*|x|:ℝ):ℂ)^(-exponent c) := by
  have incidence (n:ℕ) (positive:1≤n):|(n:ℝ)*x|≤q ↔ n≤⌊q/|x|⌋₊ := by
    rw [Nat.le_floor_iff' (by omega),abs_mul,abs_of_nonneg (Nat.cast_nonneg n),le_div_iff₀ (abs_pos.mpr nonzero)]
  have indices:(Finset.Ico 1 N).filter (fun n:ℕ=>|(n:ℝ)*x|≤q)=
      Finset.Icc 1 (min ⌊q/|x|⌋₊ (N-1)) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Ico,Finset.mem_Icc,le_min_iff]
    constructor
    · rintro ⟨⟨positive,upper⟩,member⟩
      exact ⟨positive,(incidence n positive).mp member,by omega⟩
    · rintro ⟨positive,upper,cutoff⟩
      exact ⟨⟨positive,by omega⟩,(incidence n positive).mpr upper⟩
  have term (n:ℕ):compactRaw c ((n:ℝ)*x)=
      if |(n:ℝ)*x|≤q then (((n:ℝ)*|x|:ℝ):ℂ)^(-exponent c) else 0 := by
    by_cases inside:|(n:ℝ)*x|≤q
    · have member:(n:ℝ)*x∈symmetricInterval q:=abs_le.mp inside
      rw [compactRaw,indicator_of_mem member,if_pos inside,power_read,abs_mul,
        abs_of_nonneg (show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n)]
    · have outside:(n:ℝ)*x∉symmetricInterval q:=fun h=>inside (abs_le.mpr h)
      rw [compactRaw,indicator_of_notMem outside,if_neg inside]
  simp_rw [term]
  rw [←Finset.sum_filter,indices]

private theorem finite_large (c:BurnolCompletedMellinCoordinate) (N:ℕ) (x:ℝ)
    (nonzero:x≠0) (after:q/|x|<(N:ℝ)) : finiteRaw c N x=limitRaw c x := by
  have floorBelow:⌊q/|x|⌋₊<N:=by exact_mod_cast (Nat.floor_le (by positivity)).trans_lt after
  have covered:q≤(N:ℝ)*|x|:=((div_lt_iff₀ (abs_pos.mpr nonzero)).mp after).le
  rw [finiteRaw,integer_read c N x nonzero,normalization_read c N x nonzero,
    min_eq_left (by omega:⌊q/|x|⌋₊≤N-1),min_eq_right covered,limitRaw,PowerCountingOrigin.error]
  ring

private theorem finite_small (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) (x:ℝ)
    (nonzero:x≠0) (before:(N:ℝ)≤q/|x|) :
    finiteRaw c N x=((|x|:ℝ):ℂ)^(-exponent c)*FiniteForcing.coefficient (exponent c) N := by
  have small:(N:ℝ)*|x|≤q:=(le_div_iff₀ (abs_pos.mpr nonzero)).mp before
  have integer:N≤⌊q/|x|⌋₊:=(Nat.le_floor_iff' positive.ne').mpr before
  have indices:Finset.Icc 1 (N-1)=Finset.Ico 1 N := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  have product:(((N:ℝ)*|x|:ℝ):ℂ)^(1-exponent c)=
      (N:ℂ)^(1-exponent c)*((|x|:ℝ):ℂ)^(1-exponent c) := by
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg N) (abs_nonneg x),Complex.ofReal_natCast]
  have amplitude:((|x|:ℝ):ℂ)⁻¹*((|x|:ℝ):ℂ)^(1-exponent c)=((|x|:ℝ):ℂ)^(-exponent c) := by
    have native:=Complex.cpow_sub (1-exponent c) 1
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero))
    rw [show 1-exponent c-1= -exponent c by ring,Complex.cpow_one] at native
    calc
      _=((|x|:ℝ):ℂ)^(1-exponent c)/((|x|:ℝ):ℂ) := by rw [div_eq_mul_inv,mul_comm]
      _=_ := native.symm

  rw [finiteRaw,integer_read c N x nonzero,normalization_read c N x nonzero,
    min_eq_right (by omega:N-1≤⌊q/|x|⌋₊),min_eq_left small,indices]
  have sumRead:(∑n∈Finset.Ico 1 N,(((n:ℝ)*|x|:ℝ):ℂ)^(-exponent c))=
      ((|x|:ℝ):ℂ)^(-exponent c)*(∑n∈Finset.Ico 1 N,(n:ℂ)^(-exponent c)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) (abs_nonneg x),Complex.ofReal_natCast,mul_comm]
  rw [sumRead,product,FiniteForcing.coefficient]
  rw [show ((|x|:ℝ):ℂ)⁻¹*((N:ℂ)^(1-exponent c)*((|x|:ℝ):ℂ)^(1-exponent c))=
    ((|x|:ℝ):ℂ)^(-exponent c)*(N:ℂ)^(1-exponent c) by rw [mul_left_comm,amplitude,mul_comm]]
  ring


private theorem coefficient_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (N:ℕ) (positive:0<N) :
    ‖FiniteForcing.coefficient (exponent c) N‖≤RefinedRate.constant (exponent c)+1/2 := by
  have range:=(exponent_range c).1
  have one:(1:ℝ)≤N:=by exact_mod_cast positive
  have constantNonnegative:0≤RefinedRate.constant (exponent c) := by
    unfold RefinedRate.constant
    positivity
  have rate:=RefinedRate.coefficient_error_bound (exponent c) range (exponent_ne_one c) N positive
  rw [exponent_zero c zero,sub_zero] at rate
  have first:‖FiniteForcing.coefficient (exponent c) N+(1/2:ℂ)*(N:ℂ)^(-exponent c)‖≤
      RefinedRate.constant (exponent c) := by
    exact rate.trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos one (by linarith)) constantNonnegative).trans_eq (mul_one _))
  have power:‖(N:ℂ)^(-exponent c)‖≤1 := by
    rw [Complex.norm_natCast_cpow_of_pos positive,neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos one (by linarith)
  have half:‖(1/2:ℂ)*(N:ℂ)^(-exponent c)‖≤1/2 := by
    rw [norm_mul]
    norm_num
    linarith
  have decomposition:FiniteForcing.coefficient (exponent c) N=
      (FiniteForcing.coefficient (exponent c) N+(1/2:ℂ)*(N:ℂ)^(-exponent c))-
        (1/2:ℂ)*(N:ℂ)^(-exponent c) := by ring
  rw [decomposition]
  exact (norm_sub_le _ _).trans (add_le_add first half)

private def dominationConstant (c:BurnolCompletedMellinCoordinate) : ℝ :=
  |RefinedRate.constant (exponent c)|+1+|PowerCountingOrigin.bound (exponent c)| *q+
    2*‖(q:ℂ)^(-exponent c)‖
private def envelope (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℝ :=
  dominationConstant c*(‖SingularCounting.powerRaw c x‖+1)
private theorem constant_nonnegative (c:BurnolCompletedMellinCoordinate) : 0≤dominationConstant c := by
  unfold dominationConstant
  positivity
private theorem envelope_nonnegative (c:BurnolCompletedMellinCoordinate) (x:ℝ) : 0≤envelope c x :=
  mul_nonneg (constant_nonnegative c) (by positivity)

private theorem limit_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (x:ℝ) (nonzero:x≠0) (inside:x∈symmetricInterval q) : ‖limitRaw c x‖≤dominationConstant c := by
  have native:=PowerCountingOrigin.error_bound (exponent c) (exponent_range c).1
    (by linarith [(exponent_range c).2]) (exponent_zero c zero) |x| (abs_pos.mpr nonzero)
  have error:‖PowerCountingOrigin.error (exponent c) |x|‖≤|PowerCountingOrigin.bound (exponent c)| *q := by
    exact native.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg x)).trans
      (mul_le_mul_of_nonneg_left (abs_le.mpr inside) (abs_nonneg _)))
  have fraction:‖(1/2:ℂ)-((Int.fract (q/|x|):ℝ):ℂ)‖≤2 := by
    have bound:=norm_sub_le (1/2:ℂ) ((Int.fract (q/|x|):ℝ):ℂ)
    rw [Complex.norm_of_nonneg (Int.fract_nonneg (q/|x|))] at bound
    norm_num at bound
    linarith [Int.fract_lt_one (q/|x|)]
  rw [limitRaw]
  have multiplied:=mul_le_mul_of_nonneg_left fraction (norm_nonneg ((q:ℂ)^(-exponent c)))
  rw [←norm_mul] at multiplied
  exact (norm_add_le _ _).trans (by unfold dominationConstant;linarith [abs_nonneg (RefinedRate.constant (exponent c))])

private theorem finite_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (N:ℕ) (x:ℝ) (nonzero:x≠0) (inside:x∈symmetricInterval q) : ‖finiteRaw c N x‖≤envelope c x := by
  by_cases atZero:N=0
  · subst N
    have raw:finiteRaw c 0 x=0 := by simp [finiteRaw]
    rw [raw,norm_zero]
    exact envelope_nonnegative c x
  by_cases after:q/|x|<(N:ℝ)
  · rw [finite_large c N x nonzero after]
    exact (limit_bound c zero x nonzero inside).trans (by
      unfold envelope
      nlinarith [constant_nonnegative c,norm_nonneg (SingularCounting.powerRaw c x)])
  · rw [finite_small c N (Nat.pos_of_ne_zero atZero) x nonzero (le_of_not_gt after),norm_mul,←power_read]
    have source:=coefficient_bound c zero N (Nat.pos_of_ne_zero atZero)
    have constant:RefinedRate.constant (exponent c)+1/2≤dominationConstant c := by
      unfold dominationConstant
      have first:=le_abs_self (RefinedRate.constant (exponent c))
      have second:0≤|PowerCountingOrigin.bound (exponent c)| *q:=by positivity
      have third:=norm_nonneg ((q:ℂ)^(-exponent c))
      linarith
    exact (mul_le_mul_of_nonneg_left (source.trans constant) (norm_nonneg _)).trans (by
      unfold envelope
      nlinarith [constant_nonnegative c])

private theorem finite_eventually (c:BurnolCompletedMellinCoordinate) (x:ℝ) (nonzero:x≠0) :
    ∀ᶠ N:ℕ in atTop,finiteRaw c N x=limitRaw c x := by
  filter_upwards [eventually_gt_atTop ⌊q/|x|⌋₊] with N after
  exact finite_large c N x nonzero ((Nat.lt_floor_add_one (q/|x|)).trans_le (by exact_mod_cast after))

private theorem quarter_read (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    (Rq (DualSource.source N (E (SingularCounting.powerL2 c))):ℝ→ℂ)=ᵐ[μq] finiteRaw c N := by
  exact (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) _).trans (ae_restrict_of_ae (source_raw c N))
private theorem finite_memLp (c:BurnolCompletedMellinCoordinate) (N:ℕ) : MemLp (finiteRaw c N) 2 μq :=
  (Lp.memLp (Rq (DualSource.source N (E (SingularCounting.powerL2 c))))).ae_eq (quarter_read c N)
private theorem limit_measurable (c:BurnolCompletedMellinCoordinate) : AEStronglyMeasurable (limitRaw c) μq := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun N=>(finite_memLp c N).aestronglyMeasurable)
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x nonzero
  exact tendsto_const_nhds.congr' ((finite_eventually c x nonzero).mono (fun _ h=>h.symm))
private theorem envelope_memLp (c:BurnolCompletedMellinCoordinate) : MemLp (envelope c) 2 μq :=
  ((SingularCounting.power_memLp c).norm.add (memLp_const (1:ℝ))).const_mul (dominationConstant c)
private theorem limit_memLp (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    MemLp (limitRaw c) 2 μq := by
  apply (envelope_memLp c).mono (limit_measurable c)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x inside nonzero
  rw [Real.norm_of_nonneg (envelope_nonnegative c x)]
  exact (limit_bound c zero x nonzero inside).trans (by
    unfold envelope
    nlinarith [constant_nonnegative c,norm_nonneg (SingularCounting.powerRaw c x)])

def reverseQuarterValue (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) : Hq :=
  (limit_memLp c zero).toLp (limitRaw c)

/-- The actual uncentered power source retains its full finite window and generated normalization. -/
theorem reverse_power_quarter_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>Rq (DualSource.source N (E (SingularCounting.powerL2 c)))) atTop
      (𝓝 (reverseQuarterValue c zero)) := by
  have squareLimit:Tendsto (fun N:ℕ=>∫x:ℝ,‖finiteRaw c N x-limitRaw c x‖^2 ∂μq) atTop (𝓝 0) := by
    have limit:=tendsto_integral_of_dominated_convergence (μ:=μq) (fun x:ℝ=>4*(envelope c x)^2)
      (F:=fun N x=>‖finiteRaw c N x-limitRaw c x‖^2) (f:=fun _=>(0:ℝ))
      (fun N=>((finite_memLp c N).aestronglyMeasurable.sub (limit_measurable c)).norm.pow 2)
      ((envelope_memLp c).integrable_sq.const_mul 4) ?_ ?_
    · simpa using limit
    · intro N
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q),
        ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x inside nonzero
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have first:=finite_bound c zero N x nonzero inside
      have second:‖limitRaw c x‖≤envelope c x := by
        exact (limit_bound c zero x nonzero inside).trans (by
          unfold envelope
          nlinarith [constant_nonnegative c,norm_nonneg (SingularCounting.powerRaw c x)])
      have bound:‖finiteRaw c N x-limitRaw c x‖≤2*envelope c x := (norm_sub_le _ _).trans (by linarith)
      nlinarith [norm_nonneg (finiteRaw c N x-limitRaw c x)]
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with x nonzero
      have pointwise:Tendsto (fun N:ℕ=>finiteRaw c N x) atTop (𝓝 (limitRaw c x)) :=
        tendsto_const_nhds.congr' ((finite_eventually c x nonzero).mono (fun _ h=>h.symm))
      simpa using (pointwise.sub (tendsto_const_nhds (x:=limitRaw c x))).norm.pow 2
  have source (N:ℕ):Rq (DualSource.source N (E (SingularCounting.powerL2 c)))=
      (finite_memLp c N).toLp (finiteRaw c N) := by
    apply Lp.ext
    exact (quarter_read c N).trans (finite_memLp c N).coeFn_toLp.symm
  simp_rw [source]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (finiteRaw c) (finite_memLp c)
    (limitRaw c) (limit_memLp c zero)).mpr
  have rootLimit:=squareLimit.rpow_const (p:=(2:ℝ)⁻¹) (Or.inr (by norm_num))
  have limit:=ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using rootLimit)
  convert limit using 1
  · ext N
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((finite_memLp c N).sub (limit_memLp c zero))]
    simp
  · simp

open private reverse_whole_tendsto forward_whole_tendsto from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.WholeLift
open private centered_log_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction

def centeredReverseValue (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) : M :=
  Q (reverseQuarterValue c zero)-burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) • countedUnitLimit

private theorem centered_reverse_source (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    CenteredCountingDual.reverse N (SingularCounting.centeredPower c)=
      Q (Rq (DualSource.source N (E (SingularCounting.powerL2 c))))-
        burnolQuarterMeanCoefficient (SingularCounting.powerL2 c) • countedUnit N := by
  unfold CenteredCountingDual.reverse SingularCounting.centeredPower
  rw [Constructor.zeroMean_read]
  simp only [CountingDual.dual_eq_adjoint,map_sub,map_smul,countedUnit]

private theorem centered_reverse_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>CenteredCountingDual.reverse N (SingularCounting.centeredPower c)) atTop
      (𝓝 (centeredReverseValue c zero)) := by
  have first:=((Q).continuous.tendsto _).comp (reverse_power_quarter_tendsto c zero)
  have actual:=first.sub (countedUnit_tendsto.const_smul (burnolQuarterMeanCoefficient (SingularCounting.powerL2 c)))
  apply actual.congr'
  exact Eventually.of_forall (fun N=>(centered_reverse_source c N).symm)

private theorem centered_even (c:BurnolCompletedMellinCoordinate) :
    reflectRestricted q (SingularCounting.centeredPower c:Hq)=SingularCounting.centeredPower c :=
  congrArg (fun state:M=>(state:Hq)) (centered_log_even c 0)

/-- Paid reverse support restores the whole centered power source, including its original ordinary mean. -/
theorem actual_reverse_power_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (SingularCounting.centeredPower c:Hq))) atTop
      (𝓝 (reverseWholeValue (SingularCounting.centeredPower c) (centeredReverseValue c zero))) :=
  reverse_whole_tendsto _ (centered_even c) _ (centered_reverse_tendsto c zero)

theorem actual_forward_power_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (SingularCounting.centeredPower c:Hq))) atTop
      (𝓝 (forwardWholeValue (SingularCounting.centeredPower c))) :=
  forward_whole_tendsto _ _ (actual_reverse_power_tendsto c zero)

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.PowerWhole
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
