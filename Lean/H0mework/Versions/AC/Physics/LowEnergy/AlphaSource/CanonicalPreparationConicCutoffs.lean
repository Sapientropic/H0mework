import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationConicPartition

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumConicComposition
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open PreparationVacuumCanonicalMoyal PreparationVacuumCutoffBudget PreparationVacuumConicBudget
open PreparationVacuumMoyalSymmetry
open scoped BigOperators ContDiff Topology

private theorem finite_order (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

def boxBound (m : ℕ) : ℝ := (chiMaximum m*(2*sourceRadius⁻¹))^m

def thetaBound (m : ℕ) : ℝ := composeBound boxBound angularBudget m

def radialChiBound (m : ℕ) : ℝ := composeBound chiBound radialInnerBudget m

def sourceConicTheta : Symbol := sourceFlatTheta ∘ normalizedPhase

def sourceRadialChi (R : ℝ) : Symbol := sourceChi ∘ (fun x => rho x/R)

theorem boxBound_nonnegative (m : ℕ) : 0 ≤ boxBound m := by
  exact pow_nonneg (mul_nonneg ((chiMaximum_one m).trans' (by norm_num))
    (mul_nonneg (by norm_num) (inv_nonneg.mpr radius_small.1.le))) _

theorem angularBudget_nonnegative (m : ℕ) : 0 ≤ angularBudget m := by
  unfold angularBudget
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by norm_num) (add_nonneg (radialBound_nonnegative _ _)
      (mul_nonneg (Nat.cast_nonneg _) (radialBound_nonnegative _ _)))

theorem radialInnerBudget_nonnegative (m : ℕ) : 0 ≤ radialInnerBudget m := by
  unfold radialInnerBudget
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by norm_num) (radialBound_nonnegative _ _)

theorem sourceFlatTheta_smooth : ContDiff ℝ ∞ sourceFlatTheta := by
  have identity : sourceFlatTheta=fun x => ∏ s : Slot,boxFactor s (phaseCoordinate s x) := by
    funext x
    simp only [Fintype.prod_prod_type]
    simp [boxFactor,phaseCoordinate,phaseCenter,sourceFlatTheta,sourceTheta,Finset.prod_mul_distrib,mul_comm]
  rw [identity]
  exact contDiff_prod (fun s (_ : s∈Finset.univ) => (boxFactor_smooth s).comp (phaseCoordinate s).contDiff)

theorem normalizedPhase_smooth (x : Phase) (hx : x∈punctured) :
    ContDiffAt ℝ ∞ normalizedPhase x := by
  have normSmooth : ContDiffAt ℝ ∞ rho x := (contDiffAt_norm ℝ hx).comp x contDiffAt_snd
  have normNonzero : rho x≠0 := norm_ne_zero_iff.mpr hx
  exact contDiffAt_fst.prodMk ((normSmooth.inv normNonzero).smul contDiffAt_snd)

theorem sourceConicTheta_smooth (x : Phase) (hx : x∈punctured) :
    ContDiffAt ℝ ∞ sourceConicTheta x :=
  sourceFlatTheta_smooth.contDiffAt.comp x (normalizedPhase_smooth x hx)

theorem sourceConicTheta_native (x : Phase) :
    sourceConicTheta x=sourceTheta x.1 (normalizedMomentum x.2) := by
  have components : (rho x)⁻¹ • WithLp.ofLp x.2=normalizedMomentum x.2 := by
    funext i
    change (‖x.2‖)⁻¹*x.2 i=x.2 i/‖x.2‖
    ring
  change sourceTheta x.1 (WithLp.ofLp ((rho x)⁻¹ • x.2))=_
  rw [WithLp.ofLp_smul,components]

/-- Literal original Bell budget on the full ambient unit-cotangent jets. -/
theorem actual_conicTheta_unit_budget (m : ℕ) (w : Word m) (x : Phase) (unit : rho x=1) :
    |jet m sourceConicTheta w x|≤thetaBound m := by
  have hx : x∈punctured := by
    intro zero
    simp [rho,zero] at unit
  apply canonical_composition_budget sourceFlatTheta normalizedPhase x sourceFlatTheta_smooth.contDiffAt
    (normalizedPhase_smooth x hx) boxBound angularBudget boxBound_nonnegative m
  · intro k _ v
    exact sourceFlatTheta_canonical_budget k v _
  · intro k positive _ v
    exact actual_conic_unit_budget k positive v x unit

private theorem rho_inverse_power (x : Phase) (m : ℕ) :
    (rho x)^(-(m : ℝ))=((rho x)⁻¹)^m := by
  rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast,inv_pow]

/-- Actual radial cutoff at every nonzero p; the upper transition annulus is source-generated. -/
theorem actual_radialChi_budget (R : ℝ) (radius : 0 < R) (m : ℕ) (w : Word m)
    (x : Phase) (hx : x∈punctured) :
    |jet m (sourceRadialChi R) w x|≤radialChiBound m*((rho x)⁻¹)^m := by
  have innerSmooth : ContDiffAt ℝ ∞ (fun y : Phase => rho y/R) x :=
    ((contDiffAt_norm ℝ hx).comp x contDiffAt_snd).div_const R
  by_cases annulus : rho x/R ≤ 2
  · apply scalar_composition_budget sourceChi (fun y => rho y/R) x sourceChi_smooth.contDiffAt
      innerSmooth chiBound radialInnerBudget chiBound_nonnegative
      ((rho x)⁻¹) m
    · intro k _; exact actual_sourceChi_budget k _
    · intro k positive _ v
      simpa only [rho_inverse_power] using actual_radial_inner_budget k positive v x hx R radius annulus
  · have high : 2 < rho x/R := lt_of_not_ge annulus
    have germ : sourceRadialChi R=ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      have near : ∀ᶠ y : Phase in 𝓝 x, 2 < rho y/R :=
        innerSmooth.continuousAt.eventually (lt_mem_nhds high)
      filter_upwards [near] with y hy
      simp [sourceRadialChi,sourceChi,show ¬rho y/R ≤ 1 by linarith,hy.le]
    have read := (germ.iteratedFDeriv ℝ m).eq_of_nhds
    unfold jet
    rw [read]
    cases m with
    | zero =>
      simp [iteratedFDeriv_zero_apply,radialChiBound,composeBound_zero,chiBound_zero]
    | succ m =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply,zero_apply,abs_zero]
      exact mul_nonneg (by
        unfold radialChiBound composeBound
        apply Finset.sum_nonneg
        intro k _
        exact mul_nonneg (chiBound_nonnegative _) (partialBell_nonnegative _ radialInnerBudget_nonnegative _ _))
        (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)

theorem actual_radialChi_q_zero (R : ℝ) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈punctured) (i : Fin m) (q : (w i).2=false) :
    jet m (sourceRadialChi R) w x=0 := by
  let D : Set PhysicalMomentum := {p | p≠0}
  let g : PhysicalMomentum → ℝ := fun p => sourceChi (‖p‖/R)
  let projection : Phase →L[ℝ] PhysicalMomentum := ContinuousLinearMap.snd ℝ _ _
  have openD : IsOpen D := isOpen_ne
  have openPullback : IsOpen (projection ⁻¹' D) := openD.preimage projection.continuous
  have smooth : ContDiffOn ℝ ∞ g D := by
    intro p hp
    exact (sourceChi_smooth.contDiffAt.comp p ((contDiffAt_norm ℝ hp).div_const R)).contDiffWithinAt
  have native : g ∘ projection=sourceRadialChi R := rfl
  have derivative := projection.iteratedFDerivWithin_comp_right smooth openD.uniqueDiffOn
    openPullback.uniqueDiffOn (x:=x) hx (finite_order m)
  have targetRead : iteratedFDerivWithin ℝ m g D (projection x)=iteratedFDeriv ℝ m g (projection x) :=
    iteratedFDerivWithin_of_isOpen m openD (show projection x∈D from hx)
  rw [iteratedFDerivWithin_of_isOpen m openPullback hx,targetRead,native] at derivative
  rw [jet,derivative,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply (iteratedFDeriv ℝ m g (projection x)).map_coord_zero i
  simp [projection,slotDirection,q,qDirection]

def dilation (r : ℝ) : Phase →L[ℝ] Phase :=
  (ContinuousLinearMap.fst ℝ CanonicalPreparationCutoff.FlatConfiguration PhysicalMomentum).prod
    (r • ContinuousLinearMap.snd ℝ CanonicalPreparationCutoff.FlatConfiguration PhysicalMomentum)

theorem dilation_slot (r : ℝ) (s : Slot) :
    dilation r (slotDirection s)=(if s.2 then r else 1) • slotDirection s := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [dilation,slotDirection,pDirection,qDirection]

theorem punctured_dilation (r : ℝ) (positive : 0 < r) (x : Phase) (hx : x∈punctured) :
    dilation r x∈punctured := by
  change r • x.2≠0
  exact smul_ne_zero positive.ne' hx

theorem rho_dilation (r : ℝ) (positive : 0 < r) (x : Phase) :
    rho (dilation r x)=r*rho x := by
  simp [rho,dilation,norm_smul,Real.norm_eq_abs,abs_of_pos positive]

theorem normalizedPhase_dilation (r : ℝ) (positive : 0 < r) (x : Phase) :
    normalizedPhase (dilation r x)=normalizedPhase x := by
  apply Prod.ext
  · rfl
  · change (rho (dilation r x))⁻¹ • (r • x.2)=(rho x)⁻¹ • x.2
    rw [rho_dilation r positive,smul_smul,mul_inv_rev]
    congr 1
    field_simp

private def PositiveRadialLaw (d : ℤ) (f : Symbol) : Prop :=
  ∀ r : ℝ,0 < r → ∀ x∈punctured,f (dilation r x)=r^d*f x

private def canonicalD (s : Slot) (f : Symbol) : Symbol := fun x => fderiv ℝ f x (slotDirection s)

private theorem canonicalD_radial (d : ℤ) (s : Slot) (f : Symbol)
    (smooth : ∀ x∈punctured,ContDiffAt ℝ ∞ f x) (law : PositiveRadialLaw d f) :
    PositiveRadialLaw (d-(if s.2 then 1 else 0)) (canonicalD s f) := by
  intro r positive x hx
  have scaled := punctured_dilation r positive x hx
  have germ : (fun y => f (dilation r y))=ᶠ[𝓝 x] (fun y => r^d*f y) := by
    filter_upwards [punctured_open.mem_nhds hx] with y hy
    exact law r positive y hy
  have derivative := congrArg (fun L : Phase →L[ℝ] ℝ => L (slotDirection s)) germ.fderiv_eq
  rw [fderiv_fun_comp x ((smooth _ scaled).differentiableAt (by simp)) (dilation r).differentiableAt,
    (dilation r).fderiv,fderiv_const_mul ((smooth x hx).differentiableAt (by simp))] at derivative
  simp only [ContinuousLinearMap.comp_apply,dilation_slot,map_smul,smul_apply,smul_eq_mul] at derivative
  unfold canonicalD
  cases b : s.2
  · simp only [b,Bool.false_eq_true,if_false,sub_zero,one_mul] at derivative ⊢
    exact derivative
  · simp only [b,ite_true] at derivative ⊢
    have power : r^(d-1)*r=r^d := by
      calc
        _=r^(d-1)*r^(1 : ℤ) := by rw [zpow_one]
        _=_ := by rw [←zpow_add₀ positive.ne']; congr 1; omega
    apply mul_left_cancel₀ positive.ne'
    rw [derivative,←mul_assoc,mul_comm r (r^(d-1)),power]

def momentumCount (vs : List Slot) : ℕ := vs.countP (fun s => s.2)

/-- Radial-cutoff mixed words have the same p-count units as the original conic recipe. -/
theorem actual_radialChi_mixed_budget (R : ℝ) (radius : 0 < R) (m : ℕ) (w : Word m)
    (x : Phase) (hx : x∈punctured) :
    |jet m (sourceRadialChi R) w x|≤radialChiBound m*((rho x)⁻¹)^(momentumCount (List.ofFn w)) := by
  classical
  by_cases pure : ∀ i : Fin m,(w i).2=true
  · have count : momentumCount (List.ofFn w)=m := by
      unfold momentumCount
      rw [List.countP_eq_length_filter,List.filter_eq_self.mpr, List.length_ofFn]
      intro s hs
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
      exact pure i
    rw [count]
    exact actual_radialChi_budget R radius m w x hx
  · obtain ⟨i,hi⟩ := not_forall.mp pure
    have q : (w i).2=false := Bool.eq_false_of_not_eq_true hi
    rw [actual_radialChi_q_zero R m w x hx i q,abs_zero]
    exact mul_nonneg (by
      unfold radialChiBound composeBound
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (chiBound_nonnegative _) (partialBell_nonnegative _ radialInnerBudget_nonnegative _ _))
      (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)

private theorem listJet_radial (d : ℤ) (vs : List Slot) (f : Symbol)
    (smooth : ∀ x∈punctured,ContDiffAt ℝ ∞ f x) (law : PositiveRadialLaw d f) :
    PositiveRadialLaw (d-(momentumCount vs : ℤ)) (listJet (vs.map slotDirection) f) := by
  induction vs with
  | nil => simpa [momentumCount,listJet] using law
  | cons s vs ih =>
    have lower : ∀ x∈punctured,ContDiffAt ℝ ∞ (listJet (vs.map slotDirection) f) x :=
      fun x hx => listJet_smooth _ (smooth x hx)
    have step := canonicalD_radial (d-(momentumCount vs : ℤ)) s _ lower ih
    change PositiveRadialLaw (d-(momentumCount (s::vs) : ℤ)) (canonicalD s (listJet (vs.map slotDirection) f))
    convert step using 1
    unfold momentumCount
    cases h : s.2
    · simp [h]
    · simp [h]; omega

private theorem conicTheta_jet_radial (m : ℕ) (w : Word m) :
    PositiveRadialLaw (-(momentumCount (List.ofFn w) : ℤ)) (jet m sourceConicTheta w) := by
  have law : PositiveRadialLaw 0 sourceConicTheta := by
    intro r positive x hx
    simp [sourceConicTheta,normalizedPhase_dilation r positive x]
  have generated := listJet_radial 0 (List.ofFn w) sourceConicTheta sourceConicTheta_smooth law
  have smooth : ContDiffOn ℝ ∞ sourceConicTheta punctured :=
    fun x hx => (sourceConicTheta_smooth x hx).contDiffWithinAt
  intro r positive x hx
  have value := generated r positive x hx
  simp only [List.map_ofFn,zero_sub] at value
  rw [listJet_ofFn punctured_open smooth m _ _ (punctured_dilation r positive x hx),
    listJet_ofFn punctured_open smooth m _ _ hx] at value
  exact value

/-- The original mixed q/p radial law counts p directions, while q directions retain degree zero. -/
theorem actual_conicTheta_budget (m : ℕ) (w : Word m) (x : Phase) (hx : x∈punctured) :
    |jet m sourceConicTheta w x|≤thetaBound m*((rho x)⁻¹)^(momentumCount (List.ofFn w)) := by
  have positive : 0 < rho x := norm_pos_iff.mpr hx
  let u := dilation ((rho x)⁻¹) x
  have unit : rho u=1 := by rw [rho_dilation _ (inv_pos.mpr positive)]; exact inv_mul_cancel₀ positive.ne'
  have hu : u∈punctured := punctured_dilation _ (inv_pos.mpr positive) x hx
  have recover : dilation (rho x) u=x := by
    apply Prod.ext
    · rfl
    · change (rho x) • ((rho x)⁻¹ • x.2)=x.2
      rw [smul_smul,mul_inv_cancel₀ positive.ne',one_smul]
  have read := conicTheta_jet_radial m w (rho x) positive u hu
  rw [recover] at read
  have scale : (rho x)^(-(momentumCount (List.ofFn w) : ℤ))=((rho x)⁻¹)^(momentumCount (List.ofFn w)) := by
    rw [zpow_neg,zpow_natCast,inv_pow]
  rw [read,scale,abs_mul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr positive.le) _)]
  exact (mul_le_mul_of_nonneg_left (actual_conicTheta_unit_budget m w u unit)
    (pow_nonneg (inv_nonneg.mpr positive.le) _)).trans_eq (mul_comm _ _)

end LowEnergy.PreparationVacuumConicComposition
