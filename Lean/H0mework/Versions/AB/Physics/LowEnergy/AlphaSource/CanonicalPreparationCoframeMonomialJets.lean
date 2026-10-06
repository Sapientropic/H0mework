import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeBudget
open scoped BigOperators ContDiff Topology

abbrev Phase := (Fin 100 → ℝ) × EuclideanSpace ℝ (Fin 100)
abbrev Symbol := Phase → ℝ
abbrev Slot := Fin 100 × Bool
abbrev Word (m : ℕ) := Fin m → Slot

def slotDirection (s : Slot) : Phase :=
  if s.2 then (0,WithLp.toLp 2 (Pi.single s.1 1)) else (Pi.single s.1 1,0)
def jet (m : ℕ) (f : Symbol) (w : Word m) (x : Phase) : ℝ :=
  iteratedFDeriv ℝ m f x (slotDirection ∘ w)

private theorem finite_order (n : ℕ) : (n : ℕ∞ω)≤∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

abbrev Powers := Fin 6 → ℕ

def qSlot (i : Fin 6) : Slot := (⟨i.val,by omega⟩,false)
def qCoordinate (i : Fin 6) : Phase →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (qSlot i).1).comp (ContinuousLinearMap.fst ℝ _ _)
def diagonal (i : Fin 6) : Prop := i=0 ∨ i=2 ∨ i=5
instance : DecidablePred diagonal := fun i => by unfold diagonal; infer_instance

def coframeDomain : Set Phase := {x | ∀ i,diagonal i → qCoordinate i x≠0}
def poleSupported (a : Powers) : Prop := ∀ i,a i≠0 → diagonal i

def degree (a : Powers) : ℕ := ∑ i,a i

def powerFactor (pole : Bool) (n : ℕ) (t : ℝ) : ℝ := if pole then (t⁻¹)^n else t^n

def monomial (pole : Bool) (a : Powers) : Symbol := fun x => ∏ i,powerFactor pole (a i) (qCoordinate i x)

def numeratorBound (d n : ℕ) : ℝ := (d.descFactorial n : ℝ)*15^(d-n)
def reciprocalBound (d n : ℕ) : ℝ := (d.ascFactorial n : ℝ)*15^(d+n)
def monomialBound (pole : Bool) (d n : ℕ) : ℝ := if pole then reciprocalBound d n else numeratorBound d n

theorem qCoordinate_direction (i : Fin 6) (s : Slot) :
    qCoordinate i (slotDirection s)=if qSlot i=s then 1 else 0 :=
by
  rcases s with ⟨j,b⟩
  cases b <;> simp [qCoordinate,slotDirection,qSlot,Pi.single_apply,eq_comm]

theorem coframeDomain_open : IsOpen coframeDomain := by
  rw [show coframeDomain=(⋂ i : Fin 6,⋂ (_ : diagonal i),{x | qCoordinate i x≠0}) by ext x; simp [coframeDomain]]
  exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun _ => isOpen_ne.preimage (qCoordinate i).continuous))

theorem monomial_smooth (pole : Bool) (a : Powers) (supported : pole=true → poleSupported a) :
    ContDiffOn ℝ ∞ (monomial pole a) coframeDomain := by
  intro x hx
  unfold monomial
  apply contDiffWithinAt_prod
  intro i _
  by_cases zero : a i=0
  · simp only [powerFactor,zero,pow_zero,ite_self]
    exact contDiffWithinAt_const
  · cases pole
    · exact ((qCoordinate i).contDiff.contDiffAt.pow _).contDiffWithinAt
    · exact (((qCoordinate i).contDiff.contDiffAt.inv (hx i (supported rfl i zero))).pow _).contDiffWithinAt

theorem monomialBound_nonnegative (pole : Bool) (d n : ℕ) : 0≤monomialBound pole d n := by
  cases pole <;> simp only [monomialBound] <;> unfold numeratorBound reciprocalBound <;> positivity

def stepPowers (pole : Bool) (a : Powers) (i : Fin 6) : Powers :=
  Function.update a i (if pole then a i+1 else a i-1)

def factorSlope (pole : Bool) (n : ℕ) (t : ℝ) : ℝ :=
  if pole then -(n : ℝ)*(t⁻¹)^(n+1) else (n : ℝ)*t^(n-1)

theorem factor_derivative (pole : Bool) (n : ℕ) (t : ℝ) (regular : pole=true → n≠0 → t≠0) :
    HasDerivAt (powerFactor pole n) (factorSlope pole n t) t := by
  cases pole
  · change HasDerivAt (fun x : ℝ => x^n) ((n : ℝ)*t^(n-1)) t
    exact hasDerivAt_pow n t
  · cases n with
    | zero =>
      have same : powerFactor true 0=(fun _ : ℝ => 1) := by funext x; simp [powerFactor]
      rw [same]
      simpa [factorSlope] using hasDerivAt_const t (1 : ℝ)
    | succ n =>
      have ht := regular rfl (by omega)
      have h := ((hasDerivAt_id t).inv ht).pow (n+1)
      change HasDerivAt (fun y : ℝ => (y⁻¹)^(n+1)) _ t
      convert! h using 1
      simp [factorSlope,pow_succ,div_eq_mul_inv]
      ring

theorem factor_slope_zero (pole : Bool) (t : ℝ) : factorSlope pole 0 t=0 := by
  cases pole <;> simp [factorSlope]

theorem qSlot_injective : Function.Injective qSlot := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun s : Slot => s.1.val) h

theorem monomial_direction (pole : Bool) (a : Powers) (supported : pole=true → poleSupported a)
    (s : Slot) (x : Phase) (hx : x∈coframeDomain) :
    fderiv ℝ (monomial pole a) x (slotDirection s)=
      ∑ i : Fin 6,(∏ j∈Finset.univ.erase i,powerFactor pole (a j) (qCoordinate j x))*
        factorSlope pole (a i) (qCoordinate i x)*(if qSlot i=s then 1 else 0) := by
  have factors (i : Fin 6) :=
    (factor_derivative pole (a i) (qCoordinate i x)
      (fun hp hi => hx i (supported hp i hi))).comp_hasFDerivAt x (qCoordinate i).hasFDerivAt
  have whole := HasFDerivAt.finsetProd (u:=Finset.univ) (fun i _ => factors i)
  change HasFDerivAt (monomial pole a) _ x at whole
  rw [whole.fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul,qCoordinate_direction,mul_assoc,Function.comp_apply]

theorem monomial_q_derivative (pole : Bool) (a : Powers) (supported : pole=true → poleSupported a)
    (i : Fin 6) (x : Phase) (hx : x∈coframeDomain) :
    fderiv ℝ (monomial pole a) x (slotDirection (qSlot i))=
      (if a i=0 then 0 else (if pole then -(a i : ℝ) else (a i : ℝ))*
        monomial pole (stepPowers pole a i) x) := by
  classical
  rw [monomial_direction pole a supported]
  simp only [qSlot_injective.eq_iff]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true,mul_one]
    by_cases zero : a i=0
    · simp [zero,factor_slope_zero]
    · rw [if_neg zero]
      have updated : monomial pole (stepPowers pole a i) x=
          powerFactor pole (if pole then a i+1 else a i-1) (qCoordinate i x)*
          ∏ j∈Finset.univ.erase i,powerFactor pole (a j) (qCoordinate j x) := by
        unfold monomial stepPowers
        rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
        simp only [Function.update_self,Finset.sdiff_singleton_eq_erase]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
      rw [updated]
      cases pole <;> simp only [factorSlope,powerFactor,Bool.false_eq_true,if_false,if_true] <;> ring
  · intro j _ hji
    simp [hji]
  · simp
  · exact hx

theorem monomial_other_derivative (pole : Bool) (a : Powers) (supported : pole=true → poleSupported a)
    (s : Slot) (other : ∀ i : Fin 6,qSlot i≠s) (x : Phase) (hx : x∈coframeDomain) :
    fderiv ℝ (monomial pole a) x (slotDirection s)=0 := by
  rw [monomial_direction pole a supported s x hx]
  simp [other]

theorem step_supported (pole : Bool) (a : Powers) (supported : pole=true → poleSupported a)
    (i : Fin 6) (positive : a i≠0) : pole=true → poleSupported (stepPowers pole a i) := by
  intro hp j hj
  by_cases same : j=i
  · subst j
    exact supported hp i positive
  · exact supported hp j (by simpa [stepPowers,same] using hj)

theorem coordinate_degree (a : Powers) (i : Fin 6) : a i≤degree a :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)

theorem step_degree (pole : Bool) (a : Powers) (i : Fin 6) (positive : a i≠0) :
    degree (stepPowers pole a i)=if pole then degree a+1 else degree a-1 := by
  classical
  have split : degree a=a i+∑ j∈Finset.univ.erase i,a j :=
    (Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) a).trans (by simp only [Finset.sdiff_singleton_eq_erase])
  have update : degree (stepPowers pole a i)=
      (if pole then a i+1 else a i-1)+∑ j∈Finset.univ.erase i,a j := by
    unfold degree stepPowers
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
  rw [update,split]
  cases pole <;> simp <;> omega

theorem monomialBound_step (pole : Bool) (d n : ℕ) (positive : 0<d) :
    (d : ℝ)*monomialBound pole (if pole then d+1 else d-1) n=monomialBound pole d (n+1) := by
  cases pole
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    simp only [monomialBound,Bool.false_eq_true,if_false,numeratorBound,
      Nat.succ_descFactorial_succ,Nat.cast_mul,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Nat.cast_succ]
    ring
  · simp only [monomialBound,if_true,reciprocalBound]
    rw [←mul_assoc,←Nat.cast_mul,Nat.succ_ascFactorial,←Nat.ascFactorial_succ]
    congr 2
    omega

theorem monomial_value_budget (pole : Bool) (a : Powers) (supported : pole=true → poleSupported a)
    (x : Phase) (bound : ∀ i,|qCoordinate i x|≤15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹|≤15) :
    |monomial pole a x|≤(15 : ℝ)^degree a := by
  unfold monomial
  rw [Finset.abs_prod]
  unfold degree
  rw [←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro i _; exact abs_nonneg _
  · intro i _
    by_cases zero : a i=0
    · simp [powerFactor,zero]
    · cases pole
      · simpa [powerFactor,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (bound i) (a i)
      · simpa [powerFactor,abs_pow] using pow_le_pow_left₀ (abs_nonneg _)
          (inverse i (supported rfl i zero)) (a i)

theorem jet_succ_right (f : Symbol) (m : ℕ) (w : Word (m+1)) (x : Phase)
    (smooth : ContDiffAt ℝ ∞ f x) :
    jet (m+1) f w x=jet m (fun y => fderiv ℝ f y (slotDirection (w (Fin.last m)))) (Fin.init w) x := by
  unfold jet
  rw [iteratedFDeriv_succ_apply_right]
  have read := (ContinuousLinearMap.apply ℝ ℝ (slotDirection (w (Fin.last m)))).iteratedFDeriv_comp_left
    (smooth.fderiv_right (m:=∞) (by simp)) (finite_order m)
  exact (congrArg (fun L => L (slotDirection ∘ Fin.init w)) read).symm

theorem jet_germ {f g : Symbol} {x : Phase} (same : f=ᶠ[𝓝 x] g) (m : ℕ) (w : Word m) :
    jet m f w x=jet m g w x := by
  unfold jet
  rw [(same.iteratedFDeriv ℝ m).eq_of_nhds]

theorem jet_scale (c : ℝ) (f : Symbol) (m : ℕ) (w : Word m) (x : Phase)
    (smooth : ContDiffAt ℝ ∞ f x) : jet m (fun y => c*f y) w x=c*jet m f w x := by
  unfold jet
  change (iteratedFDeriv ℝ m (fun y => c • f y) x) _=_
  rw [iteratedFDeriv_const_smul_apply' (smooth.of_le (finite_order m))]
  rfl

theorem jet_zero (m : ℕ) (w : Word m) (x : Phase) : jet m (fun _ => 0) w x=0 := by
  cases m with
  | zero => simp [jet]
  | succ m => simp [jet]

/-- The actual coordinate word updates the same exponent at every repeated q hit. -/
theorem actual_monomial_budget (pole : Bool) (a : Powers) (supported : pole=true → poleSupported a)
    (m : ℕ) (w : Word m) (x : Phase) (hx : x∈coframeDomain)
    (bound : ∀ i,|qCoordinate i x|≤15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹|≤15) :
    |jet m (monomial pole a) w x|≤monomialBound pole (degree a) m := by
  induction m generalizing a with
  | zero =>
    have estimate := monomial_value_budget pole a supported x bound inverse
    simpa [jet,iteratedFDeriv_zero_apply,monomialBound,numeratorBound,reciprocalBound] using estimate
  | succ m ih =>
    have smooth := (monomial_smooth pole a supported x hx).contDiffAt (coframeDomain_open.mem_nhds hx)
    rw [jet_succ_right _ m w x smooth]
    let s := w (Fin.last m)
    change |jet m (fun y => fderiv ℝ (monomial pole a) y (slotDirection s)) (Fin.init w) x|≤_
    by_cases hit : ∃ i : Fin 6,qSlot i=s
    · obtain ⟨i,hi⟩ := hit
      rw [←hi]
      by_cases zero : a i=0
      · have germ : (fun y => fderiv ℝ (monomial pole a) y (slotDirection (qSlot i)))=ᶠ[𝓝 x] (fun _ => 0) := by
          filter_upwards [coframeDomain_open.mem_nhds hx] with y hy
          simp [monomial_q_derivative pole a supported i y hy,zero]
        rw [jet_germ germ,jet_zero,abs_zero]
        exact monomialBound_nonnegative _ _ _
      · have next := step_supported pole a supported i zero
        have germ : (fun y => fderiv ℝ (monomial pole a) y (slotDirection (qSlot i)))=ᶠ[𝓝 x]
            (fun y => (if pole then -(a i : ℝ) else (a i : ℝ))*monomial pole (stepPowers pole a i) y) := by
          filter_upwards [coframeDomain_open.mem_nhds hx] with y hy
          simp [monomial_q_derivative pole a supported i y hy,zero]
        rw [jet_germ germ,jet_scale _ _ _ _ _
          ((monomial_smooth pole _ next x hx).contDiffAt (coframeDomain_open.mem_nhds hx)),abs_mul]
        have coefficient : |if pole then -(a i : ℝ) else (a i : ℝ)|=(a i : ℝ) := by
          cases pole <;> simp
        rw [coefficient]
        have estimate := mul_le_mul_of_nonneg_left (ih _ next (Fin.init w)) (Nat.cast_nonneg (a i))
        refine estimate.trans ?_
        rw [step_degree pole a i zero]
        have degreePositive : 0<degree a := lt_of_lt_of_le (Nat.pos_of_ne_zero zero) (coordinate_degree a i)
        have final := mul_le_mul_of_nonneg_right (show (a i : ℝ)≤degree a by exact_mod_cast coordinate_degree a i)
          (monomialBound_nonnegative pole (if pole then degree a+1 else degree a-1) m)
        exact final.trans_eq (monomialBound_step pole (degree a) m degreePositive)
    · have other : ∀ i : Fin 6,qSlot i≠s := fun i h => hit ⟨i,h⟩
      have germ : (fun y => fderiv ℝ (monomial pole a) y (slotDirection s))=ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [coframeDomain_open.mem_nhds hx] with y hy
        exact monomial_other_derivative pole a supported s other y hy
      rw [jet_germ germ,jet_zero,abs_zero]
      exact monomialBound_nonnegative _ _ _

end LowEnergy.PreparationVacuumCoframeBudget
