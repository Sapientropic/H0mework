import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationConicRadialTerms

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumConicBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget
open scoped BigOperators ContDiff Topology

def GoodTerm (m : ℕ) (t : RadialTerm) : Prop :=
  t.contractions≤ m ∧ t.coordinates.length≤ m ∧ 2*t.contractions=m+t.coordinates.length

def radialTerms (a : ℝ) (vs : List Slot) : List RadialTerm :=
  vs.foldr (fun s ts => ts.flatMap (termNext a s)) [⟨1,0,[]⟩]

def coefficientMass (ts : List RadialTerm) : ℝ := (ts.map (fun t => |t.coefficient|)).sum

def radialBound (a : ℝ) (m : ℕ) : ℝ := ∏ j∈Finset.range m,(|a|+3*j)

theorem radialBound_zero (a : ℝ) : radialBound a 0=1 := by simp [radialBound]
theorem radialBound_next (a : ℝ) (m : ℕ) : radialBound a (m+1)=radialBound a m*(|a|+3*m) := by
  simp [radialBound,Finset.prod_range_succ]

theorem radialBound_nonnegative (a : ℝ) (m : ℕ) : 0≤ radialBound a m := by
  exact Finset.prod_nonneg (fun j _ => by positivity)

private theorem erased_length (xs : List (Fin 100)) (i : Fin xs.length) :
    (xs.take i.val++xs.drop (i.val+1)).length=xs.length-1 := by
  simp only [List.length_append,List.length_take,List.length_drop]
  have := i.isLt
  omega

theorem next_good (a : ℝ) (s : Slot) (t : RadialTerm) (m : ℕ) (good : GoodTerm m t)
    (u : RadialTerm) (member : u∈termNext a s t) : GoodTerm (m+1) u := by
  unfold termNext at member
  split_ifs at member with hs
  · rcases List.mem_cons.mp member with rfl|member
    · unfold GoodTerm at *
      simp only [List.length_cons]
      omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
      unfold GoodTerm at *
      simp only [erased_length]
      have := i.isLt
      omega
  · simp at member

theorem radialTerms_good (a : ℝ) (vs : List Slot) : ∀ t∈radialTerms a vs,GoodTerm vs.length t := by
  induction vs with
  | nil => intro t ht; simp [radialTerms] at ht; subst t; simp [GoodTerm]
  | cons s vs ih =>
    intro t ht
    change t∈(radialTerms a vs).flatMap (termNext a s) at ht
    obtain ⟨u,hu,ht⟩ := List.mem_flatMap.mp ht
    exact next_good a s u vs.length (ih u hu) t ht

private theorem term_step_mass (a : ℝ) (s : Slot) (t : RadialTerm) (m : ℕ) (good : GoodTerm m t) :
    coefficientMass (termNext a s t)≤(|a|+3*m)*|t.coefficient| := by
  unfold termNext
  cases h : s.2
  · change 0≤(|a|+3*m)*|t.coefficient|
    positivity
  · simp only [if_true,coefficientMass,List.map_cons,List.sum_cons,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    have triangle := abs_add_le a (-(2*(t.contractions : ℝ)))
    rw [←sub_eq_add_neg,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ)≤2*t.contractions)] at triangle
    have count : (t.contractions : ℝ)≤ m := by exact_mod_cast good.1
    have size : (t.coordinates.length : ℝ)≤ m := by exact_mod_cast good.2.1
    have radial := mul_le_mul_of_nonneg_left triangle (abs_nonneg t.coefficient)
    have coordinates : (∑ i : Fin t.coordinates.length,|if s.1=t.coordinates.get i then t.coefficient else 0|)≤
        t.coordinates.length*|t.coefficient| := by
      calc
        _≤∑ _i : Fin t.coordinates.length,|t.coefficient| := Finset.sum_le_sum (fun i _ => by split_ifs <;> simp)
        _=_ := by simp
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right count (abs_nonneg t.coefficient),
      mul_le_mul_of_nonneg_right size (abs_nonneg t.coefficient)]

theorem radialTerms_mass (a : ℝ) (vs : List Slot) : coefficientMass (radialTerms a vs)≤ radialBound a vs.length := by
  induction vs with
  | nil => simp [coefficientMass,radialTerms,radialBound]
  | cons s vs ih =>
    change coefficientMass ((radialTerms a vs).flatMap (termNext a s))≤ radialBound a (vs.length+1)
    have generic (ts : List RadialTerm) (good : ∀ t∈ts,GoodTerm vs.length t) :
        coefficientMass (ts.flatMap (termNext a s))≤(|a|+3*vs.length)*coefficientMass ts := by
      induction ts with
      | nil => simp [coefficientMass]
      | cons t ts ih =>
        have tail := ih (fun u hu => good u (by simp [hu]))
        have first := term_step_mass a s t vs.length (good t (by simp))
        simpa only [List.flatMap_cons,coefficientMass,List.map_append,List.sum_append,List.map_cons,List.sum_cons,mul_add]
          using add_le_add first tail
    exact (generic _ (radialTerms_good a vs)).trans (by
      rw [radialBound_next]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left ih (by positivity : 0≤|a|+3*vs.length))

private theorem monomial_norm_bound (xs : List (Fin 100)) (x : Phase) :
    |(xs.map (fun i => momentumCoordinate i x)).prod|≤(rho x)^xs.length := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons,List.prod_cons,abs_mul,List.length_cons,pow_succ]
    have coordinate : |momentumCoordinate i x|≤ rho x := by
      simpa [momentumCoordinate,rho] using (PiLp.norm_apply_le (p:=2) x.2 i)
    exact (mul_le_mul coordinate ih (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem termValue_budget (a : ℝ) (m : ℕ) (t : RadialTerm) (good : GoodTerm m t)
    (x : Phase) (hx : x∈punctured) : |termValue a t x|≤|t.coefficient| *(rho x)^(a-m) := by
  have positive : 0<rho x := norm_pos_iff.mpr hx
  have monomial := monomial_norm_bound t.coordinates x
  unfold termValue radialPower
  rw [abs_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos positive _)]
  have estimate := mul_le_mul_of_nonneg_left monomial
    (mul_nonneg (abs_nonneg t.coefficient) (Real.rpow_nonneg positive.le (a-2*(t.contractions : ℝ))))
  have degree : a-2*(t.contractions : ℝ)+(t.coordinates.length : ℝ)=a-m := by
    have balanced : 2*(t.contractions : ℝ)=(m : ℝ)+t.coordinates.length := by exact_mod_cast good.2.2
    linarith
  have same : |t.coefficient| *(rho x)^(a-2*(t.contractions : ℝ))*(rho x)^t.coordinates.length=
      |t.coefficient| *(rho x)^(a-m) := by
    rw [mul_assoc,←Real.rpow_add_natCast positive.ne',degree]
  exact estimate.trans_eq same

theorem radialTerms_replay (a : ℝ) (vs : List Slot) :
    Set.EqOn (listJet (vs.map slotDirection) (radialPower a))
      (fun x => ((radialTerms a vs).map (fun t => termValue a t x)).sum) punctured := by
  induction vs with
  | nil => intro x _; simp [listJet,radialTerms,termValue]
  | cons s vs ih =>
    intro x hx
    have germ : listJet (vs.map slotDirection) (radialPower a)=ᶠ[𝓝 x]
        (fun y => ((radialTerms a vs).map (fun t => termValue a t y)).sum) := by
      filter_upwards [punctured_open.mem_nhds hx] with y hy
      exact ih hy
    change fderiv ℝ (listJet (vs.map slotDirection) (radialPower a)) x (slotDirection s)=_
    rw [germ.fderiv_eq]
    have derivative (ts : List RadialTerm) :
        fderiv ℝ (fun y => (ts.map (fun t => termValue a t y)).sum) x (slotDirection s)=
          ((ts.flatMap (termNext a s)).map (fun t => termValue a t x)).sum := by
      induction ts with
      | nil => simp [fderiv_const_apply]
      | cons t ts ih =>
        have first := (termValue_smooth a t x hx).contDiffAt (punctured_open.mem_nhds hx)
        have tail : ContDiffAt ℝ ∞ (fun y => (ts.map (fun t => termValue a t y)).sum) x := by
          clear ih
          induction ts with
          | nil => exact contDiffAt_const
          | cons u us ih => simpa only [List.map_cons,List.sum_cons] using! ((termValue_smooth a u x hx).contDiffAt (punctured_open.mem_nhds hx)).add ih
        simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append]
        rw [fderiv_fun_add (first.differentiableAt (by simp)) (tail.differentiableAt (by simp)),add_apply,
          termValue_differential a s t x hx,ih]
    exact derivative (radialTerms a vs)

theorem actual_radialPower_budget (a : ℝ) (m : ℕ) (w : Word m) (x : Phase) (hx : x∈punctured) :
    |jet m (radialPower a) w x|≤ radialBound a m*(rho x)^(a-m) := by
  have replay := listJet_ofFn punctured_open (radialPower_smooth a) m (slotDirection∘w) x hx
  rw [←List.map_ofFn] at replay
  change |iteratedFDeriv ℝ m (radialPower a) x (slotDirection∘w)|≤_
  rw [←replay,radialTerms_replay a (List.ofFn w) hx]
  have positive : 0≤(rho x)^(a-m) := Real.rpow_nonneg (norm_nonneg _) _
  have total (ts : List RadialTerm) (good : ∀ t∈ts,GoodTerm m t) :
      |(ts.map (fun t => termValue a t x)).sum|≤ coefficientMass ts*(rho x)^(a-m) := by
    induction ts with
    | nil => simp [coefficientMass]
    | cons t ts ih =>
      have first := termValue_budget a m t (good t (by simp)) x hx
      have tail := ih (fun u hu => good u (by simp [hu]))
      simp only [List.map_cons,List.sum_cons,coefficientMass,add_mul]
      exact (abs_add_le _ _).trans (add_le_add first tail)
  exact (total _ (by simpa only [List.length_ofFn] using radialTerms_good a (List.ofFn w))).trans
    (by simpa only [List.length_ofFn] using mul_le_mul_of_nonneg_right (radialTerms_mass a (List.ofFn w)) positive)

end LowEnergy.PreparationVacuumConicBudget
