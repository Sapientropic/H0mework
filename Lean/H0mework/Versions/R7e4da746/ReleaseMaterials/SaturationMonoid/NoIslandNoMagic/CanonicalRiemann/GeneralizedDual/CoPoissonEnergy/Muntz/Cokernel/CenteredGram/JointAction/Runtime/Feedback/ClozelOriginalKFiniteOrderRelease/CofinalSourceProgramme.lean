import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.RCurrentCoPoissonSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCofinalSourceProgramme
open MeasureTheory Set Filter BurnolPhysicalState
open scoped BigOperators Topology
namespace Source
export OriginalKFiniteOrderRelease.CofinalMobiusL2Source
 (sourceRaw source_raw_zero source_raw_gap source_native reciprocalMoment source_reciprocal_moment valueRaw)
end Source
namespace CM
export OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
  (rawIterate sourceIndex seedRaw raw_iterate_mean_update)
end CM
open private seed_raw_mean from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial

def expPartial (j:Nat) (z:ℂ) : ℂ := ∑ k∈Finset.range j,z^k/(k.factorial:ℂ)

private theorem expPartial_succ (j:Nat) (z:ℂ) :
    expPartial (j+1) z=expPartial j z+z^j/(j.factorial:ℂ) := by
  simp only [expPartial,Finset.sum_range_succ]

private theorem expPartial_zero (j:Nat) : expPartial (j+1) 0=1 := by
  induction j with
  | zero => norm_num [expPartial]
  | succ j ih => rw [expPartial_succ,ih];simp

private theorem expPartial_deriv (j:Nat) {f:ℝ→ℂ} {f':ℂ} {x:ℝ}
    (hf:HasDerivAt f f' x) :
    HasDerivAt (fun t=>expPartial (j+1) (f t)) (f'*expPartial j (f x)) x := by
  induction j with
  | zero => simpa [expPartial] using hasDerivAt_const x (1:ℂ)
  | succ j ih =>
    have generated:=ih.add ((hf.fun_pow (j+1)).div_const ((j+1).factorial:ℂ))
    have factorial:(j.factorial:ℂ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have coefficient : f'*expPartial (j+1) (f x) =
        f'*expPartial j (f x)+
          (j+1:ℂ)*f x^(j+1-1)*f'/((j+1).factorial:ℂ) := by
      rw [expPartial_succ,Nat.factorial_succ,Nat.cast_mul]
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp [factorial]
    rw [coefficient]
    convert generated using 1 <;> first
      | rfl
      | (funext t;exact expPartial_succ (j+1) (f t))
      | simp only [Nat.cast_add,Nat.cast_one]

def stepNumerator (c:BurnolCompletedMellinCoordinate) (j:Nat) (a t:ℝ) : ℂ :=
  (t:ℂ)^c.value-(a:ℂ)^c.value*expPartial j (c.value*(Real.log (t/a):ℂ))

def stepProfile (c:BurnolCompletedMellinCoordinate) (j:Nat) (a x:ℝ) : ℂ :=
  if a≤|x| then ((|x|:ℝ):ℂ)^(-c.value)*stepNumerator c j a |x| else 0

def boxProgramme (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) : ℂ :=
  (2:ℂ)*(-2/c.value)^j*(stepProfile c j 1 x-stepProfile c j (3/2) x)

private theorem coordinate_ne (c:BurnolCompletedMellinCoordinate) : c.value≠0 := by
  intro zero;have positive:=c.rightHalf;rw [zero] at positive;norm_num at positive

private theorem log_deriv {a x:ℝ} (ap:0<a) (xp:0<x) :
    HasDerivAt (fun t:ℝ=>(Real.log (t/a):ℂ)) ((x:ℂ)⁻¹) x := by
  have raw:=((hasDerivAt_id x).div_const a).log (div_ne_zero xp.ne' ap.ne')
  have coefficient : (1/a)/(id x/a)=x⁻¹ := by
    simp only [id_eq]
    field_simp
  rw [coefficient] at raw
  simpa only [id_eq,Complex.ofReal_inv] using raw.ofReal_comp

private theorem numerator_deriv (c:BurnolCompletedMellinCoordinate) (j:Nat)
    {a x:ℝ} (ap:0<a) (xp:0<x) :
    HasDerivAt (stepNumerator c (j+1) a)
      (c.value*((x:ℂ)^(c.value-1)-(a:ℂ)^c.value*(x:ℂ)⁻¹*
        expPartial j (c.value*(Real.log (x/a):ℂ)))) x := by
  have power:=hasDerivAt_ofReal_cpow_const xp.ne' (coordinate_ne c)
  have poly:=expPartial_deriv j ((log_deriv ap xp).const_mul c.value)
  have coefficient : c.value*((x:ℂ)^(c.value-1)-(a:ℂ)^c.value*(x:ℂ)⁻¹*
      expPartial j (c.value*(Real.log (x/a):ℂ))) =
      c.value*(x:ℂ)^(c.value-1)-(a:ℂ)^c.value*
        (c.value*(x:ℂ)⁻¹*expPartial j (c.value*(Real.log (x/a):ℂ))) := by ring
  rw [coefficient]
  exact power.sub (poly.const_mul ((a:ℂ)^c.value))

private theorem numerator_at_base (c:BurnolCompletedMellinCoordinate) (j:Nat)
    {a:ℝ} (ap:0<a) : stepNumerator c (j+1) a a=0 := by
  simp only [stepNumerator,div_self ap.ne',Real.log_one,Complex.ofReal_zero,mul_zero,
    expPartial_zero,mul_one,sub_self]

private theorem step_base (c:BurnolCompletedMellinCoordinate) {a x:ℝ}
    (ap:0<a) : stepProfile c 0 a x=if a≤|x| then 1 else 0 := by
  by_cases inside:a≤|x|
  · have xn:((|x|:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ap.trans_le inside).ne'
    simp only [stepProfile,if_pos inside,stepNumerator,expPartial,Finset.range_zero,
      Finset.sum_empty,mul_zero,sub_zero]
    rw [←Complex.cpow_add _ _ xn,neg_add_cancel,Complex.cpow_zero]
  · simp only [stepProfile,if_neg inside]

private theorem box_initial (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
    boxProgramme c 0 x=OriginalKFiniteOrderRelease.CofinalMobiusL2Source.seedSourceRaw x := by
  rw [boxProgramme,step_base c (by norm_num),step_base c (by norm_num)]
  unfold OriginalKFiniteOrderRelease.CofinalMobiusL2Source.seedSourceRaw burnolTateStepBoxRaw
  split_ifs <;> simp_all <;> linarith

private theorem expPartial_continuous (j:Nat) : Continuous (expPartial j) := by
  induction j with
  | zero =>
    change Continuous (fun _:ℂ=>0)
    exact continuous_const
  | succ j ih =>
    have generated:expPartial (j+1)=(fun z:ℂ=>expPartial j z+z^j/(j.factorial:ℂ)):=
      funext (expPartial_succ j)
    rw [generated]
    exact ih.add ((continuous_id.pow j).div_const (j.factorial:ℂ))

private theorem weighted_profile (c:BurnolCompletedMellinCoordinate) (j:Nat)
    {a t:ℝ} (ap:0<a) (after:a≤t) :
    (t:ℂ)^(c.value-1)*stepProfile c j a t=
      (t:ℂ)^(c.value-1)-(a:ℂ)^c.value*(t:ℂ)⁻¹*
        expPartial j (c.value*(Real.log (t/a):ℂ)) := by
  have tp:=ap.trans_le after
  have tn: (t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr tp.ne'
  have mix : (c.value-1)+(-c.value)=(-1:ℂ) := by ring
  have lead : (t:ℂ)⁻¹*(t:ℂ)^c.value=(t:ℂ)^(c.value-1) := by
    rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ tn]
    congr 1
    ring
  simp only [stepProfile,abs_of_pos tp,if_pos after,stepNumerator]
  rw [←mul_assoc,←Complex.cpow_add _ _ tn,mix,Complex.cpow_neg_one,mul_sub,lead]
  ring

private theorem weighted_profile_continuous (c:BurnolCompletedMellinCoordinate) (j:Nat)
    {a r:ℝ} (ap:0<a) :
    ContinuousOn (fun t:ℝ=>(t:ℂ)^(c.value-1)*stepProfile c j a t) (Icc a r) := by
  have regular:ContinuousOn (fun t:ℝ=>(t:ℂ)^(c.value-1)-(a:ℂ)^c.value*(t:ℂ)⁻¹*
      expPartial j (c.value*(Real.log (t/a):ℂ))) (Icc a r) := by
    intro t ht
    have tp:=ap.trans_le ht.1
    have power:ContinuousAt (fun x:ℝ=>(x:ℂ)^(c.value-1)) t:=
      (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr tp)).comp
        Complex.continuous_ofReal.continuousAt
    have inverse:ContinuousAt (fun x:ℝ=>(x:ℂ)⁻¹) t:=
      Complex.continuous_ofReal.continuousAt.inv₀ (Complex.ofReal_ne_zero.mpr tp.ne')
    have poly:ContinuousAt (fun x:ℝ=>expPartial j (c.value*(Real.log (x/a):ℂ))) t:=
      (expPartial_continuous j).continuousAt.comp ((log_deriv ap tp).continuousAt.const_mul c.value)
    exact (power.sub ((inverse.const_mul ((a:ℂ)^c.value)).mul poly)).continuousWithinAt
  apply regular.congr
  intro t ht
  exact weighted_profile c j ap ht.1

private theorem weighted_profile_primitive (c:BurnolCompletedMellinCoordinate) (j:Nat)
    {a r:ℝ} (ap:0<a) (ar:a≤r) :
    (∫ t:ℝ in a..r,(t:ℂ)^(c.value-1)*stepProfile c j a t)=
      stepNumerator c (j+1) a r/c.value := by
  have hd:∀t∈uIcc a r,
      HasDerivAt (fun x=>stepNumerator c (j+1) a x/c.value)
        ((t:ℂ)^(c.value-1)*stepProfile c j a t) t := by
    intro t ht
    rw [uIcc_of_le ar] at ht
    have generated:=(numerator_deriv c j ap (ap.trans_le ht.1)).div_const c.value
    rw [weighted_profile c j ap ht.1]
    convert generated using 1 <;> first
      | rfl
      | (field_simp [coordinate_ne c])
  have hc:ContinuousOn (fun t:ℝ=>(t:ℂ)^(c.value-1)*stepProfile c j a t) (uIcc a r):=by
    rw [uIcc_of_le ar]
    exact weighted_profile_continuous c j ap
  have computed:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa only [numerator_at_base c j ap,zero_div,sub_zero] using computed

private theorem profile_prefix (c:BurnolCompletedMellinCoordinate) (j:Nat)
    {a r:ℝ} (ap:0<a) (rp:0≤r) :
    IntervalIntegrable (fun t:ℝ=>(t:ℂ)^(c.value-1)*stepProfile c j a t) volume 0 r ∧
    (∫t:ℝ in 0..r,(t:ℂ)^(c.value-1)*stepProfile c j a t)=
      if a≤r then stepNumerator c (j+1) a r/c.value else 0 := by
  have zeroBefore {b:ℝ} (bp:0≤b) (ba:b≤a) :
      EqOn (fun t:ℝ=>(t:ℂ)^(c.value-1)*stepProfile c j a t) (fun _=>0) (uIoo 0 b) := by
    intro t ht
    rw [uIoo_of_le bp] at ht
    simp only [stepProfile,abs_of_pos ht.1,if_neg (not_le.mpr (ht.2.trans_le ba)),mul_zero]
  have zeroPrefix {b:ℝ} (bp:0≤b) (ba:b≤a) :
      IntervalIntegrable (fun t:ℝ=>(t:ℂ)^(c.value-1)*stepProfile c j a t) volume 0 b ∧
      (∫t:ℝ in 0..b,(t:ℂ)^(c.value-1)*stepProfile c j a t)=0 := by
    constructor
    · exact (intervalIntegrable_congr_uIoo (zeroBefore bp ba)).mpr (intervalIntegrable_const)
    · rw [intervalIntegral.integral_congr_uIoo (zeroBefore bp ba),intervalIntegral.integral_zero]
  by_cases ar:a≤r
  · have lower:=zeroPrefix ap.le le_rfl
    have upper:IntervalIntegrable (fun t:ℝ=>(t:ℂ)^(c.value-1)*stepProfile c j a t) volume a r:=by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ar]
      exact weighted_profile_continuous c j ap
    refine ⟨lower.1.trans upper,?_⟩
    rw [if_pos ar,←intervalIntegral.integral_add_adjacent_intervals lower.1 upper,
      lower.2,zero_add,weighted_profile_primitive c j ap ar]
  · have lower:=zeroPrefix rp (le_of_not_ge ar)
    exact ⟨lower.1,by rw [if_neg ar];exact lower.2⟩

private theorem box_origin (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    boxProgramme c j 0=0 := by
  norm_num [boxProgramme,stepProfile]

theorem box_action (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) :
    OriginalKCenteredMobiusRSource.sourceRRaw c (boxProgramme c j) x=boxProgramme c (j+1) x := by
  have first:=profile_prefix c j (a:=1) (by norm_num) (abs_nonneg x)
  have second:=profile_prefix c j (a:=3/2) (by norm_num) (abs_nonneg x)
  have body:(fun t:ℝ=>(t:ℂ)^(c.value-1)*boxProgramme c j t)=
      (fun t:ℝ=>(2:ℂ)*(-2/c.value)^j*
        ((t:ℂ)^(c.value-1)*stepProfile c j 1 t-
          (t:ℂ)^(c.value-1)*stepProfile c j (3/2) t)):=by
    funext t
    unfold boxProgramme
    ring
  simp only [OriginalKCenteredMobiusRSource.sourceRRaw,box_origin,mul_zero,zero_div,
    OriginalKCenteredMobiusRSource.weightedCentered,sub_zero]
  rw [body,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub first.1 second.1,first.2,second.2]
  unfold boxProgramme stepProfile
  split_ifs <;> simp only [pow_succ] <;> field_simp [coordinate_ne c] <;> ring

theorem actual_source_programme (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) :
    Source.sourceRaw c j x=boxProgramme c j x := by
  induction j generalizing x with
  | zero => exact (box_initial c x).symm
  | succ j previous =>
    change OriginalKCenteredMobiusRSource.sourceRRaw c (Source.sourceRaw c j) x=_
    have same:Source.sourceRaw c j=boxProgramme c j:=funext previous
    rw [same,box_action]

theorem actual_source_tail (c:BurnolCompletedMellinCoordinate) (j:Nat) {x:ℝ}
    (outside:(3/2:ℝ)≤|x|) :
    Source.sourceRaw c j x=(2:ℂ)*(-2/c.value)^j*((|x|:ℝ):ℂ)^(-c.value)*
      (((3/2:ℝ):ℂ)^c.value*expPartial j (c.value*(Real.log (|x|/(3/2)):ℂ))-
        expPartial j (c.value*(Real.log |x|:ℂ))) := by
  rw [actual_source_programme]
  have first:(1:ℝ)≤|x|:=by linarith
  simp only [boxProgramme,stepProfile,if_pos first,if_pos outside,stepNumerator,
    Complex.ofReal_one,Complex.one_cpow,div_one,one_mul]
  ring

private theorem actual_value_origin (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    Source.valueRaw c j 0= -2*(Real.log (3/2:ℝ):ℂ)*(-2/c.value)^j := by
  induction j with
  | zero =>
    change CM.seedRaw 0=_
    rw [seed_raw_mean,pow_zero,mul_one]
  | succ j previous =>
    change CM.rawIterate c CM.seedRaw (j+1) 0=_
    rw [CM.raw_iterate_mean_update]
    change -2*Source.valueRaw c j 0/c.value=_
    rw [previous,pow_succ]
    ring

theorem actual_reciprocal_moment (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    Source.reciprocalMoment c j=2*(Real.log (3/2:ℝ):ℂ)*(-2/c.value)^j := by
  rw [Source.source_reciprocal_moment,actual_value_origin]
  ring

/-- The integer inventory is spatial; the source iteration index remains an independent argument. -/
def valueProgramme (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) : ℂ :=
  (∑n∈Finset.range (Nat.floor |x|),((n+1:ℕ):ℂ)⁻¹*boxProgramme c j (x/((n+1:ℕ):ℝ)))-
    2*(Real.log (3/2:ℝ):ℂ)*(-2/c.value)^j

private theorem actual_forward_finite (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) :
    burnolInnerGapForward (Source.sourceRaw c j) x=
      ∑n∈Finset.range (Nat.floor |x|),((n+1:ℕ):ℂ)⁻¹*Source.sourceRaw c j (x/((n+1:ℕ):ℝ)) := by
  have reindex:burnolInnerGapForward (Source.sourceRaw c j) x=
      ∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*Source.sourceRaw c j (x/((n+1:ℕ):ℝ)):=
    (Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
      (fun n:ℕ+=>((n:ℕ):ℂ)⁻¹*Source.sourceRaw c j (x/(n:ℕ)))).symm
  rw [reindex]
  apply tsum_eq_sum
  intro n outside
  have beyond:Nat.floor |x|≤n:=by simpa only [Finset.mem_range,not_lt] using outside
  have positive:(0:ℝ)<((n+1:ℕ):ℝ):=by positivity
  have bound:|x|<((n+1:ℕ):ℝ):=by
    have floorBound:=Nat.lt_floor_add_one |x|
    have order:(Nat.floor |x|:ℝ)+1≤((n+1:ℕ):ℝ):=by exact_mod_cast Nat.add_le_add_right beyond 1
    exact floorBound.trans_le order
  have gap:Source.sourceRaw c j (x/((n+1:ℕ):ℝ))=0:=by
    apply Source.source_raw_gap c j
    rw [abs_div,abs_of_pos positive]
    exact (div_lt_one positive).mpr bound
  rw [gap,mul_zero]

theorem actual_value_programme (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) :
    OriginalKFiniteOrderRelease.RCurrentCoPoissonSource.sourceValueRaw c j x=valueProgramme c j x := by
  unfold OriginalKFiniteOrderRelease.RCurrentCoPoissonSource.sourceValueRaw valueProgramme
  rw [actual_forward_finite,actual_reciprocal_moment]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [actual_source_programme]

namespace Original
export OriginalKFiniteOrderRelease.RCurrentCoPoissonSource
  (Praw Praw_native Pfield Pfield_coeFn sourceValueRaw)
end Original

def pointProgramme (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (ordinal:Nat) (x:ℝ) : ℂ :=
  let c:=burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
  valueProgramme c (m+(ordinal+6)) x-valueProgramme c (m+(ordinal+4)) x

theorem actual_point_programme (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (ordinal:Nat) (x:ℝ) :
    Original.Praw observation half ordinal x=pointProgramme observation half ordinal x := by
  unfold Original.Praw pointProgramme
  rw [actual_value_programme,actual_value_programme]
  unfold CM.sourceIndex
  congr 2

theorem point_programme_native (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (ordinal:Nat) :
    MemLp (pointProgramme observation half ordinal) 2 volume := by
  have same:Original.Praw observation half ordinal=pointProgramme observation half ordinal:=
    funext (actual_point_programme observation half ordinal)
  rw [←same]
  exact Original.Praw_native observation half ordinal

theorem actual_field_programme (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (ordinal:Nat) :
    (Original.Pfield observation half ordinal:ℝ→ℂ)=ᵐ[volume]
      pointProgramme observation half ordinal := by
  apply (Original.Pfield_coeFn observation half ordinal).trans
  exact Filter.Eventually.of_forall (actual_point_programme observation half ordinal)

theorem actual_programme_price (observation:GeneratedRiemannZeroObservation)
    (half:OriginalKCombCalculation.Half observation) (ordinal:Nat) :
    ‖Original.Pfield observation half ordinal‖^2=
      (∫x:ℝ,star (pointProgramme observation half ordinal x)*pointProgramme observation half ordinal x).re := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ),L2.inner_def]
  have scalar : (∫x:ℝ,inner ℂ (Original.Pfield observation half ordinal x)
      (Original.Pfield observation half ordinal x))=
      ∫x:ℝ,star (pointProgramme observation half ordinal x)*pointProgramme observation half ordinal x := by
    apply integral_congr_ae
    filter_upwards [actual_field_programme observation half ordinal] with x same
    rw [same]
    simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]
  exact congrArg Complex.re scalar

end OriginalCofinalSourceProgramme
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
