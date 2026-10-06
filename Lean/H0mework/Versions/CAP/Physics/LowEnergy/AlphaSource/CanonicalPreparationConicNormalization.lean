import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationConicRadialBudget

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumConicBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget PreparationVacuumEngineSource
open scoped BigOperators ContDiff Topology

private theorem finite_order (n : ℕ) : (n : ℕ∞ω)≤∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

def normalizedCoordinate (i : Fin 100) : Symbol := fun x => normalizedMomentum x.2 i

def angularBudget (m : ℕ) : ℝ :=
  if m=0 then 0 else 200*(radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1))

def radialInnerBudget (m : ℕ) : ℝ := if m=0 then 0 else 2*radialBound 1 m

def coordinateBudget (x : Phase) (n : ℕ) : ℝ :=
  if n=0 then rho x else if n=1 then 1 else 0

private theorem linear_constant_tail (L : Phase →L[ℝ] ℝ) (v w : Phase) (vs : List Phase) :
    listJet (v::w::vs) (fun x => L x)=fun _ => 0 := by
  induction vs generalizing v w with
  | nil =>
    change (fun x => fderiv ℝ (fun y => fderiv ℝ L y w) x v)=_
    simp only [L.fderiv]
    simp [fderiv_const_apply]
  | cons u vs ih =>
    change (fun x => fderiv ℝ (listJet (w::u::vs) (fun y => L y)) x v)=_
    rw [ih w u]
    simp [fderiv_const_apply]

theorem coordinate_canonical_budget (i : Fin 100) (m : ℕ) (w : Word m) (x : Phase) :
    |jet m (fun y => momentumCoordinate i y) w x|≤ coordinateBudget x m := by
  cases m with
  | zero =>
    simp only [jet,iteratedFDeriv_zero_apply,coordinateBudget,if_true]
    simpa [momentumCoordinate,rho] using PiLp.norm_apply_le (p:=2) x.2 i
  | succ m =>
    cases m with
    | zero =>
      have axis : |momentumCoordinate i (slotDirection (w 0))|≤1 := by
        rw [momentumCoordinate_direction]
        split_ifs <;> norm_num
      simpa [jet,coordinateBudget] using axis
    | succ m =>
      have replay := listJet_ofFn isOpen_univ (momentumCoordinate i).contDiff.contDiffOn
        (m+2) (slotDirection∘w) x (Set.mem_univ x)
      change |iteratedFDeriv ℝ (m+2) (fun y => momentumCoordinate i y) x (slotDirection∘w)|≤_
      rw [←replay,List.ofFn_succ,List.ofFn_succ,linear_constant_tail]
      simp [coordinateBudget]

theorem normalizedCoordinate_native (i : Fin 100) :
    normalizedCoordinate i=fun x => momentumCoordinate i x*radialPower (-1) x := by
  funext x
  simp [normalizedCoordinate,normalizedMomentum,radialPower,momentumCoordinate,rho,Real.rpow_neg_one,div_eq_mul_inv]

private theorem coordinate_convolution (m : ℕ) (positive : 0< m) (x : Phase) (D : ℕ → ℝ) :
    convolution m 0 (coordinateBudget x) D=rho x*D m+(m : ℝ)*D (m-1) := by
  classical
  let term : ℕ → ℝ := fun a => (m.choose a : ℝ)*coordinateBudget x a*D (m-a)
  have selection : (∑ a∈Finset.range (m+1),term a)=∑ a∈({0,1} : Finset ℕ),term a := by
    symm
    apply Finset.sum_subset
    · intro a ha; simp only [Finset.mem_insert,Finset.mem_singleton] at ha; rcases ha with rfl|rfl <;> simp [positive]
    · intro a _ ha
      have absent : a≠0 ∧ a≠1 := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using ha
      simp [term,coordinateBudget,absent.1,absent.2]
  simp only [convolution,Nat.zero_add]
  change (∑ a∈Finset.range (m+1),term a)=_
  rw [selection]
  simp [term,coordinateBudget,Nat.choose_one_right]

theorem normalizedCoordinate_canonical_budget (i : Fin 100) (m : ℕ) (positive : 0< m)
    (w : Word m) (x : Phase) (hx : x∈punctured) :
    |jet m (normalizedCoordinate i) w x|≤
      (radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1))*(rho x)^(-(m : ℝ)) := by
  let D : ℕ → ℝ := fun n => radialBound (-1) n*(rho x)^((-1 : ℝ)-(n : ℝ))
  have bs : ∀ n,0≤ coordinateBudget x n := by
    intro n; unfold coordinateBudget; split_ifs
    · exact norm_nonneg x.2
    · norm_num
    · norm_num
  have left : LeafJetBound (fun y => momentumCoordinate i y) m (coordinateBudget x) x :=
    fun n _ w => coordinate_canonical_budget i n w x
  have right : LeafJetBound (radialPower (-1)) m D x := fun n _ w => actual_radialPower_budget (-1) n w x hx
  have product := scalarJordan_canonical_budget punctured_open 0 m
    (fun y => momentumCoordinate i y) (radialPower (-1)) (momentumCoordinate i).contDiff.contDiffOn
    (radialPower_smooth (-1)) w x hx (coordinateBudget x) D bs (by simpa only [Nat.zero_add] using left) (by simpa only [Nat.zero_add] using right)
  rw [scalarJordan_zero] at product
  change |jet m (fun y => momentumCoordinate i y*radialPower (-1) y) w x|≤_ at product
  rw [moyalScale] at product
  norm_num at product
  rw [coordinate_convolution m positive x D] at product
  rw [normalizedCoordinate_native]
  have rhoPositive : 0< rho x := norm_pos_iff.mpr hx
  have degree : (-1 : ℝ)-↑(m-1)=-(m : ℝ) := by
    have h : m-1+1=m := by omega
    have cast := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at cast
    linarith
  have first : rho x*D m=radialBound (-1) m*(rho x)^(-(m : ℝ)) := by
    dsimp [D]
    have radial : rho x*(rho x)^(-1-(m : ℝ))=(rho x)^(-(m : ℝ)) := by
      calc
        _=(rho x)^(1+(-1-(m : ℝ))) := by rw [Real.rpow_add rhoPositive,Real.rpow_one]
        _=_ := by congr 1; ring
    rw [mul_left_comm,radial]
  have sum : rho x*D m+(m : ℝ)*D (m-1)=
      (radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1))*(rho x)^(-(m : ℝ)) := by
    rw [first]
    dsimp [D]
    rw [degree]
    ring
  exact product.trans_eq sum

theorem actual_normalized_components_budget (m : ℕ) (positive : 0< m) (w : Word m)
    (x : Phase) (hx : x∈punctured) :
    (∑ i : Fin 100,|jet m (normalizedCoordinate i) w x|)≤ angularBudget m*(rho x)^(-(m : ℝ)) := by
  calc
    _≤∑ _i : Fin 100,(radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1))*(rho x)^(-(m : ℝ)) :=
      Finset.sum_le_sum (fun i _ => normalizedCoordinate_canonical_budget i m positive w x hx)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,angularBudget,if_neg positive.ne']
      have positivePower : 0≤(rho x)^(-(m : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      have positiveCoefficient : 0≤ radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1) :=
        add_nonneg (radialBound_nonnegative _ _) (mul_nonneg (Nat.cast_nonneg _) (radialBound_nonnegative _ _))
      norm_num only [Nat.cast_ofNat]
      nlinarith [mul_nonneg positiveCoefficient positivePower]

theorem actual_radial_inner_budget (m : ℕ) (positive : 0< m) (w : Word m) (x : Phase) (hx : x∈punctured)
    (R : ℝ) (radius : 0< R) (annulus : rho x/R≤2) :
    |jet m (fun y => rho y/R) w x|≤ radialInnerBudget m*(rho x)^(-(m : ℝ)) := by
  have actual := actual_radialPower_budget 1 m w x hx
  have smooth : ContDiffAt ℝ m (radialPower 1) x :=
    ((radialPower_smooth 1 x hx).contDiffAt (punctured_open.mem_nhds hx)).of_le (finite_order m)
  have identity : (fun y => rho y/R)=fun y => R⁻¹*radialPower 1 y := by
    funext y; simp [radialPower,Real.rpow_one,div_eq_mul_inv,mul_comm]
  rw [identity]
  change |(iteratedFDeriv ℝ m (R⁻¹ • radialPower 1) x) (slotDirection∘w)|≤_
  rw [iteratedFDeriv_const_smul_apply smooth]
  simp only [smul_apply]
  simp only [smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr radius)]
  have product := mul_le_mul_of_nonneg_left actual (inv_nonneg.mpr radius.le)
  have rhoPositive : 0< rho x := norm_pos_iff.mpr hx
  have split : (rho x)^(1-(m : ℝ))=rho x*(rho x)^(-(m : ℝ)) := by
    rw [sub_eq_add_neg,Real.rpow_add rhoPositive,Real.rpow_one]
  rw [split] at product
  have ratio : R⁻¹*rho x≤2 := by simpa only [div_eq_mul_inv,mul_comm] using annulus
  rw [radialInnerBudget,if_neg positive.ne']
  calc
    _≤ R⁻¹*(radialBound 1 m*(rho x*(rho x)^(-(m : ℝ)))) := product
    _≤_ := by
      have positivityCoefficient := mul_nonneg (radialBound_nonnegative 1 m)
        (Real.rpow_nonneg rhoPositive.le (-(m : ℝ)))
      nlinarith [mul_le_mul_of_nonneg_right ratio positivityCoefficient]

def normalizedPhase (x : Phase) : Phase := (x.1,(rho x)⁻¹ • x.2)

def conicCoordinate (s : Slot) : Symbol :=
  fun x => PreparationVacuumCutoffBudget.phaseCoordinate s (normalizedPhase x)

theorem conicCoordinate_native (s : Slot) :
    conicCoordinate s=if s.2 then normalizedCoordinate s.1 else fun x => x.1 s.1 := by
  funext x
  cases h : s.2 <;>
    simp [conicCoordinate,normalizedPhase,PreparationVacuumCutoffBudget.phaseCoordinate,
      normalizedCoordinate,normalizedMomentum,rho,h,div_eq_mul_inv,mul_comm]

private theorem linear_positive_budget (L : Phase →L[ℝ] ℝ)
    (axes : ∀ s : Slot,|L (slotDirection s)|≤1) (m : ℕ) (positive : 0< m)
    (w : Word m) (x : Phase) : |jet m (fun y => L y) w x|≤1 := by
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      simp only [jet]
      rw [iteratedFDeriv_one_apply,L.fderiv]
      exact axes (w 0)
    | succ m =>
      have replay := listJet_ofFn isOpen_univ L.contDiff.contDiffOn (m+2) (slotDirection∘w) x (Set.mem_univ x)
      change |iteratedFDeriv ℝ (m+2) (fun y => L y) x (slotDirection∘w)|≤_
      rw [←replay,List.ofFn_succ,List.ofFn_succ,linear_constant_tail]
      norm_num

theorem angularCoefficient_one (m : ℕ) :
    1≤radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1) := by
  have whole : 1≤radialBound (-1) m := by
    apply Finset.one_le_prod
    intro j _
    norm_num
  exact whole.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (radialBound_nonnegative _ _)))

/-- Original full 200-coordinate inner array on the actual unit cotangent fiber. -/
theorem actual_conic_unit_budget (m : ℕ) (positive : 0< m) (w : Word m) (x : Phase)
    (unit : rho x=1) : (∑ s : Slot,|jet m (conicCoordinate s) w x|)≤angularBudget m := by
  have hx : x∈punctured := by
    change x.2≠0
    intro zero
    simp [rho,zero] at unit
  have term (s : Slot) : |jet m (conicCoordinate s) w x|≤
      radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1) := by
    rw [conicCoordinate_native]
    cases h : s.2
    · change |jet m (fun y => y.1 s.1) w x|≤_
      let L : Phase →L[ℝ] ℝ := PreparationVacuumCutoffBudget.phaseCoordinate (s.1,false)
      have exactCoordinate : (fun y : Phase => y.1 s.1)=fun y => L y := by
        funext y; simp [L,PreparationVacuumCutoffBudget.phaseCoordinate]
      rw [exactCoordinate]
      have axis (t : Slot) : |L (slotDirection t)|≤1 := by
        rw [PreparationVacuumCutoffBudget.phaseCoordinate_direction]
        split_ifs <;> norm_num
      exact (linear_positive_budget L axis m positive w x).trans (angularCoefficient_one m)
    · simp only [if_true]
      simpa only [unit,Real.one_rpow,mul_one] using normalizedCoordinate_canonical_budget s.1 m positive w x hx
  calc
    _≤∑ _s : Slot,(radialBound (-1) m+(m : ℝ)*radialBound (-1) (m-1)) := Finset.sum_le_sum (fun s _ => term s)
    _=angularBudget m := by simp [angularBudget,Slot,positive.ne']; ring

end LowEnergy.PreparationVacuumConicBudget
