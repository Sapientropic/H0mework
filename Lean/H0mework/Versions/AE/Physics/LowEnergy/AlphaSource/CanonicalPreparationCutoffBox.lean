import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCutoffChi
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalSourceBudget

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCutoffBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

private theorem finite_order (n : ℕ) : (n : ℕ∞ω)≤∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

private theorem affine_derivative (n : ℕ) (a b : ℝ) (f : ℝ → ℝ) (smooth : ContDiff ℝ ∞ f) :
    iteratedDeriv n (fun t => f (b+a*t))=fun t => a^n*iteratedDeriv n f (b+a*t) := by
  have compose := iteratedDeriv_comp_const_mul ((smooth.comp (contDiff_const.add contDiff_id)).of_le (finite_order n)) a
    (f:=fun t => f (b+t))
  rw [iteratedDeriv_comp_const_add] at compose
  exact compose

private theorem affine_chi_budget (n : ℕ) (a b t : ℝ) :
    |iteratedDeriv n (fun d => sourceChi (b+a*d)) t|≤|a|^n*chiBound n := by
  rw [affine_derivative n a b sourceChi sourceChi_smooth]
  change |a^n*iteratedDeriv n sourceChi (b+a*t)|≤_
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (actual_sourceChi_budget n _) (by positivity)

theorem sourceCutFactor_budget (n : ℕ) (d : ℝ) :
    |iteratedDeriv n sourceCutFactor d|≤(sourceRadius⁻¹)^n*chiBound n := by
  by_cases zero : d=0
  · subst d
    have germ : sourceCutFactor=ᶠ[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) := by
      have near : ∀ᶠ t : ℝ in 𝓝 0,|t|<sourceRadius :=
        continuous_abs.continuousAt.eventually (isOpen_lt continuous_id continuous_const |>.mem_nhds (by simp [radius_small.1]))
      filter_upwards [near] with t ht
      unfold sourceCutFactor
      rw [if_neg (by linarith [radius_small.1]),if_neg (not_lt.mpr ht.le)]
    rw [germ.iteratedDeriv n |>.eq_of_nhds]
    cases n
    · simp [chiBound_zero]
    · simp only [iteratedDeriv_const,Nat.add_one_ne_zero,if_false,abs_zero]
      exact mul_nonneg (pow_nonneg (inv_nonneg.mpr radius_small.1.le) _) (chiBound_nonnegative _)
  · by_cases positive : 0<d
    · have germ : sourceCutFactor=ᶠ[𝓝 d] (fun t => sourceChi (3-sourceRadius⁻¹*t)) := by
        filter_upwards [lt_mem_nhds positive] with t ht
        rw [sourceCutFactor_transition,sourceChi_transition,abs_of_pos ht]
        congr 1
        ring
      rw [germ.iteratedDeriv n |>.eq_of_nhds]
      have estimate := affine_chi_budget n (-sourceRadius⁻¹) 3 d
      simpa only [abs_neg,abs_of_pos (inv_pos.mpr radius_small.1),sub_eq_add_neg,neg_mul] using estimate
    · have negative : d<0 := lt_of_le_of_ne (le_of_not_gt positive) zero
      have germ : sourceCutFactor=ᶠ[𝓝 d] (fun t => sourceChi (3+sourceRadius⁻¹*t)) := by
        filter_upwards [gt_mem_nhds negative] with t ht
        rw [sourceCutFactor_transition,sourceChi_transition,abs_of_neg ht]
        congr 1
        ring
      rw [germ.iteratedDeriv n |>.eq_of_nhds]
      have estimate := affine_chi_budget n (sourceRadius⁻¹) 3 d
      simpa only [abs_of_pos (inv_pos.mpr radius_small.1)] using estimate

def phaseCoordinate (s : Slot) : Phase →L[ℝ] ℝ :=
  if s.2 then (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 100 => ℝ) s.1).comp (ContinuousLinearMap.snd ℝ _ _)
  else (ContinuousLinearMap.proj s.1).comp (ContinuousLinearMap.fst ℝ _ _)

def phaseCenter (s : Slot) : ℝ := if s.2 then sourceUnitMomentum s.1 else flatSource s.1

def boxFactor (s : Slot) (d : ℝ) : ℝ := sourceCutFactor (2*(d-phaseCenter s))

def boxTensor (alpha : Slot → ℕ) : Symbol := fun x =>
  ∏ s : Slot,iteratedDeriv (alpha s) (boxFactor s) (phaseCoordinate s x)

def sourceFlatTheta (x : Phase) : ℝ := sourceTheta x.1 (WithLp.ofLp x.2)

def chiMaximum (m : ℕ) : ℝ :=
  (Finset.range (m+1)).sup' ⟨0,by simp⟩ chiBound

theorem chiMaximum_read (m n : ℕ) (within : n≤ m) : chiBound n≤ chiMaximum m :=
  Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

theorem chiMaximum_one (m : ℕ) : 1≤ chiMaximum m := by
  simpa only [chiBound_zero] using chiMaximum_read m 0 (Nat.zero_le _)

theorem boxFactor_smooth (s : Slot) : ContDiff ℝ ∞ (boxFactor s) :=
  sourceCutFactor_smooth.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem boxFactor_budget (s : Slot) (n : ℕ) (d : ℝ) :
    |iteratedDeriv n (boxFactor s) d|≤(2*sourceRadius⁻¹)^n*chiBound n := by
  have affine := affine_derivative n 2 (-2*phaseCenter s) sourceCutFactor sourceCutFactor_smooth
  have same : boxFactor s=fun d => sourceCutFactor (-2*phaseCenter s+2*d) := by funext d; unfold boxFactor; congr 1; ring
  rw [same,affine]
  change |2^n*iteratedDeriv n sourceCutFactor _|≤_
  rw [abs_mul,abs_pow]
  norm_num
  have estimate := mul_le_mul_of_nonneg_left (sourceCutFactor_budget n (-2*phaseCenter s+2*d)) (pow_nonneg (by norm_num : (0 : ℝ)≤2) n)
  simpa only [←mul_assoc,←mul_pow,neg_mul] using estimate

theorem phaseCoordinate_direction (s t : Slot) :
    phaseCoordinate s (slotDirection t)=if s=t then 1 else 0 := by
  rcases s with ⟨i,a⟩
  rcases t with ⟨j,b⟩
  cases a <;> cases b <;> simp [phaseCoordinate,slotDirection,qDirection,pDirection,Pi.single_apply,Prod.mk.injEq,eq_comm]

private theorem factor_derivative (s : Slot) (n : ℕ) (x : Phase) :
    HasFDerivAt (fun y => iteratedDeriv n (boxFactor s) (phaseCoordinate s y))
      (iteratedDeriv (n+1) (boxFactor s) (phaseCoordinate s x) • phaseCoordinate s) x := by
  have hd := (boxFactor_smooth s).differentiable_iteratedDeriv n
    (by exact_mod_cast ENat.natCast_lt_top n)
  have actual : HasDerivAt (iteratedDeriv n (boxFactor s))
      (iteratedDeriv (n+1) (boxFactor s) (phaseCoordinate s x)) (phaseCoordinate s x) := by
    rw [iteratedDeriv_succ]
    exact (hd _).hasDerivAt
  have composition := actual.comp_hasFDerivAt x (phaseCoordinate s).hasFDerivAt
  exact composition

private theorem tensor_derivative (alpha : Slot → ℕ) (s : Slot) (x : Phase) :
    fderiv ℝ (boxTensor alpha) x (slotDirection s)=
      boxTensor (Function.update alpha s (alpha s+1)) x := by
  classical
  have whole := HasFDerivAt.finsetProd (u:=Finset.univ) (fun t _ => factor_derivative t (alpha t) x)
  change HasFDerivAt (boxTensor alpha) _ x at whole
  rw [whole.fderiv]
  simp only [sum_apply,smul_apply,phaseCoordinate_direction,smul_eq_mul]
  rw [Finset.sum_eq_single s]
  · unfold boxTensor
    have updated : (fun t => iteratedDeriv (Function.update alpha s (alpha s+1) t)
        (boxFactor t) (phaseCoordinate t x))=
        Function.update (fun t => iteratedDeriv (alpha t) (boxFactor t) (phaseCoordinate t x)) s
          (iteratedDeriv (alpha s+1) (boxFactor s) (phaseCoordinate s x)) := by
      funext t
      by_cases same : t=s
      · subst t; simp
      · simp [same]
    rw [updated,Finset.prod_update_of_mem (Finset.mem_univ s)]
    simp only [if_true,mul_one,Finset.sdiff_singleton_eq_erase]
    ring
  · intro t _ notsame
    simp [notsame]
  · simp

private theorem boxTensor_zero : boxTensor (fun _ => 0)=sourceFlatTheta := by
  funext x
  simp only [boxTensor,iteratedDeriv_zero,Fintype.prod_prod_type]
  simp [boxFactor,phaseCoordinate,phaseCenter,sourceFlatTheta,sourceTheta,Finset.prod_mul_distrib,mul_comm]

private theorem count_directions (ss : List Slot) :
    listJet (ss.map slotDirection) sourceFlatTheta=boxTensor (fun s => ss.count s) := by
  classical
  induction ss with
  | nil => simpa only [List.map_nil,List.count_nil,listJet,List.foldr_nil] using boxTensor_zero.symm
  | cons s ss ih =>
    funext x
    simp only [List.map_cons,listJet,List.foldr_cons]
    change fderiv ℝ (listJet (ss.map slotDirection) sourceFlatTheta) x (slotDirection s)=_
    rw [ih,tensor_derivative]
    congr 1
    funext t
    by_cases same : t=s
    · subst t; simp
    · simp [same,Ne.symm same]

private theorem total_count (ss : List Slot) : (∑ s : Slot,ss.count s)=ss.length := by
  classical
  induction ss with
  | nil => simp
  | cons t ss ih =>
    simp only [List.count_cons,List.length_cons,Finset.sum_add_distrib]
    simp [ih]

theorem sourceFlatTheta_canonical_budget (m : ℕ) (w : Word m) (x : Phase) :
    |jet m sourceFlatTheta w x|≤(chiMaximum m*(2*sourceRadius⁻¹))^m := by
  classical
  let ss := List.ofFn w
  have length : ss.length=m := List.length_ofFn
  have smooth : ContDiff ℝ ∞ sourceFlatTheta := by
    rw [←boxTensor_zero]
    simpa only [boxTensor,iteratedDeriv_zero,Function.comp_apply] using!
      (contDiff_prod (fun s (_ : s∈Finset.univ) => (boxFactor_smooth s).comp (phaseCoordinate s).contDiff))
  have replay := listJet_ofFn isOpen_univ smooth.contDiffOn m (slotDirection∘w) x (Set.mem_univ x)
  rw [←List.map_ofFn] at replay
  rw [show jet m sourceFlatTheta w x=listJet (ss.map slotDirection) sourceFlatTheta x from replay.symm,
    count_directions]
  have term (s : Slot) :
      |iteratedDeriv (ss.count s) (boxFactor s) (phaseCoordinate s x)|≤
        (chiMaximum m*(2*sourceRadius⁻¹))^(ss.count s) := by
    have within : ss.count s≤ m := by simpa only [length] using (List.count_le_length (a:=s) (l:=ss))
    have maxBound := chiMaximum_read m (ss.count s) within
    have powerBound : chiBound (ss.count s)≤(chiMaximum m)^(ss.count s) := by
      cases h : ss.count s with
      | zero => simp [chiBound_zero]
      | succ n =>
        rw [h] at maxBound
        exact maxBound.trans (le_self_pow₀ (n:=n+1) (chiMaximum_one m) (by omega))
    have estimate := (boxFactor_budget s (ss.count s) (phaseCoordinate s x)).trans
      (mul_le_mul_of_nonneg_left powerBound
        (pow_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr radius_small.1.le)) _))
    simpa only [mul_pow,mul_comm] using estimate
  unfold boxTensor
  rw [Finset.abs_prod]
  calc
    _≤∏ s : Slot,(chiMaximum m*(2*sourceRadius⁻¹))^(ss.count s) :=
      Finset.prod_le_prod (fun s _ => abs_nonneg _) (fun s _ => term s)
    _=(chiMaximum m*(2*sourceRadius⁻¹))^m := by rw [Finset.prod_pow_eq_pow_sum,total_count,length]

end LowEnergy.PreparationVacuumCutoffBudget
