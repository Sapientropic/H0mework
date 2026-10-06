import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoframeMonomialJets
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeBudget
open scoped BigOperators ContDiff Topology

private theorem finite_order (n : ℕ) : (n : ℕ∞ω)≤∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

abbrev PolynomialTerms := List (ℚ × Powers)

def absoluteCeiling (c : ℚ) : ℕ := ⌈|c|⌉₊
def polynomialValue (ts : PolynomialTerms) : Symbol := fun x =>
  (ts.map (fun t => (t.1 : ℝ)*monomial false t.2 x)).sum

def numeratorArray (ts : PolynomialTerms) (n : ℕ) : ℕ :=
  (ts.map (fun t => absoluteCeiling t.1*(degree t.2).descFactorial n*15^(degree t.2-n))).sum

def reciprocalArray (d n : ℕ) : ℕ := d.ascFactorial n*15^(d+n)

structure RationalEntry where
  numerator : PolynomialTerms
  poles : Powers

def entryValue (e : RationalEntry) : Symbol := fun x =>
  polynomialValue e.numerator x*monomial true e.poles x

def entryArray (e : RationalEntry) (n : ℕ) : ℕ :=
  ∑ k∈Finset.range (n+1),n.choose k*numeratorArray e.numerator k*reciprocalArray (degree e.poles) (n-k)

theorem absoluteCeiling_bound (c : ℚ) : |(c : ℝ)|≤(absoluteCeiling c : ℝ) := by
  exact_mod_cast Nat.le_ceil (|c|)

theorem polynomialValue_smooth (ts : PolynomialTerms) : ContDiffOn ℝ ∞ (polynomialValue ts) coframeDomain := by
  induction ts with
  | nil => exact contDiffOn_const
  | cons t ts ih =>
    exact (contDiffOn_const.mul (monomial_smooth false t.2 (by simp))).add ih

theorem polynomialValue_budget (ts : PolynomialTerms) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈coframeDomain) (bound : ∀ i,|qCoordinate i x|≤15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹|≤15) :
    |jet m (polynomialValue ts) w x|≤(numeratorArray ts m : ℝ) := by
  induction ts with
  | nil =>
    rw [show polynomialValue []=(fun _ : Phase => 0) by funext y; rfl,jet_zero]
    simp [numeratorArray]
  | cons t ts ih =>
    have smooth := (monomial_smooth false t.2 (by simp) x hx).contDiffAt (coframeDomain_open.mem_nhds hx)
    have tail := (polynomialValue_smooth ts x hx).contDiffAt (coframeDomain_open.mem_nhds hx)
    have read : jet m (polynomialValue (t::ts)) w x=
        (t.1 : ℝ)*jet m (monomial false t.2) w x+jet m (polynomialValue ts) w x := by
      change (iteratedFDeriv ℝ m (fun y => (t.1 : ℝ)*monomial false t.2 y+polynomialValue ts y) x) _=_
      rw [fun_iteratedFDeriv_add_apply ((contDiffAt_const.mul smooth).of_le (finite_order m))
        (tail.of_le (finite_order m)),add_apply]
      change jet m (fun y => (t.1 : ℝ)*monomial false t.2 y) w x+_=_
      rw [jet_scale _ _ _ _ _ smooth]
      rfl
    rw [read]
    have oneTerm := actual_monomial_budget false t.2 (by simp) m w x hx bound inverse
    have estimate := mul_le_mul (absoluteCeiling_bound t.1) oneTerm (abs_nonneg _) (Nat.cast_nonneg _)
    refine (abs_add_le _ _).trans ((add_le_add (by simpa only [abs_mul] using estimate) ih).trans_eq ?_)
    simp [numeratorArray,monomialBound,numeratorBound,Nat.cast_add,Nat.cast_mul,mul_assoc]

theorem entryValue_smooth (e : RationalEntry) (supported : poleSupported e.poles) :
    ContDiffOn ℝ ∞ (entryValue e) coframeDomain :=
  (polynomialValue_smooth e.numerator).mul (monomial_smooth true e.poles (fun _ => supported))

def convolution (B D : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k∈Finset.range (n+1),(n.choose k : ℝ)*B k*D (n-k)

theorem jet_add (f g : Symbol) (m : ℕ) (w : Word m) (x : Phase)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    jet m (fun y => f y+g y) w x=jet m f w x+jet m g w x := by
  unfold jet
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (finite_order m)) (hg.of_le (finite_order m))]
  rfl

private theorem convolution_step (B D : ℕ → ℝ) (n : ℕ) :
    convolution (fun k => B (k+1)) D n+convolution B (fun k => D (k+1)) n=convolution B D (n+1) := by
  unfold convolution
  rw [show n+1+1=n+2 by omega]
  simp only [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => B i*D j) n]
  rw [add_comm]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply Finset.sum_congr rfl
    intro k hk
    have kn : k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [show n+1-k=n-k+1 by omega]
  · rfl

/-- Literal binomial product on raw canonical jets, without an operator-norm conversion. -/
theorem product_jet_budget (f g : Symbol) (fs : ContDiffOn ℝ ∞ f coframeDomain)
    (gs : ContDiffOn ℝ ∞ g coframeDomain) (B D : ℕ → ℝ) (nonnegative : ∀ n,0≤B n)
    (x : Phase) (hx : x∈coframeDomain)
    (left : ∀ n (v : Word n),|jet n f v x|≤B n)
    (right : ∀ n (v : Word n),|jet n g v x|≤D n)
    (m : ℕ) (w : Word m) : |jet m (fun y => f y*g y) w x|≤convolution B D m := by
  induction m generalizing f g B D with
  | zero =>
    simpa [jet,convolution] using mul_le_mul (left 0 w) (right 0 w) (abs_nonneg _) (nonnegative 0)
  | succ m ih =>
    let s := w (Fin.last m)
    let df : Symbol := fun y => fderiv ℝ f y (slotDirection s)
    let dg : Symbol := fun y => fderiv ℝ g y (slotDirection s)
    have dfs : ContDiffOn ℝ ∞ df coframeDomain := by
      intro y hy
      exact (((fs y hy).contDiffAt (coframeDomain_open.mem_nhds hy)).fderiv_right (by simp)).clm_apply
        contDiffAt_const |>.contDiffWithinAt
    have dgs : ContDiffOn ℝ ∞ dg coframeDomain := by
      intro y hy
      exact (((gs y hy).contDiffAt (coframeDomain_open.mem_nhds hy)).fderiv_right (by simp)).clm_apply
        contDiffAt_const |>.contDiffWithinAt
    have derivativeBound (h : Symbol) (hs : ContDiffOn ℝ ∞ h coframeDomain) (A : ℕ → ℝ)
        (hb : ∀ n (v : Word n),|jet n h v x|≤A n) (n : ℕ) (v : Word n) :
        |jet n (fun y => fderiv ℝ h y (slotDirection s)) v x|≤A (n+1) := by
      have identity := jet_succ_right h n (Fin.snoc v s) x
        ((hs x hx).contDiffAt (coframeDomain_open.mem_nhds hx))
      simp only [Fin.snoc_last,Fin.init_snoc] at identity
      rw [←identity]
      exact hb _ _
    have first := ih df g dfs gs (fun n => B (n+1)) D (fun n => nonnegative (n+1))
      (derivativeBound f fs B left) right (Fin.init w)
    have second := ih f dg fs dgs B (fun n => D (n+1)) nonnegative left
      (derivativeBound g gs D right) (Fin.init w)
    rw [jet_succ_right _ m w x (((fs.mul gs) x hx).contDiffAt (coframeDomain_open.mem_nhds hx))]
    have germ : (fun y => fderiv ℝ (fun z => f z*g z) y (slotDirection s))=ᶠ[𝓝 x]
        (fun y => df y*g y+f y*dg y) := by
      filter_upwards [coframeDomain_open.mem_nhds hx] with y hy
      rw [fderiv_fun_mul (((fs y hy).contDiffAt (coframeDomain_open.mem_nhds hy)).differentiableAt (by simp))
        (((gs y hy).contDiffAt (coframeDomain_open.mem_nhds hy)).differentiableAt (by simp))]
      simp [df,dg,mul_comm,add_comm]
    rw [jet_germ germ,jet_add _ _ _ _ _
      (((dfs.mul gs) x hx).contDiffAt (coframeDomain_open.mem_nhds hx))
      (((fs.mul dgs) x hx).contDiffAt (coframeDomain_open.mem_nhds hx))]
    exact (abs_add_le _ _).trans ((add_le_add first second).trans_eq (convolution_step B D m))

/-- Every primitive estimate in the original rational-entry convolution is generated above. -/
theorem actual_entry_budget (e : RationalEntry) (supported : poleSupported e.poles)
    (m : ℕ) (w : Word m) (x : Phase) (hx : x∈coframeDomain)
    (bound : ∀ i,|qCoordinate i x|≤15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹|≤15) :
    |jet m (entryValue e) w x|≤(entryArray e m : ℝ) := by
  have result := product_jet_budget (polynomialValue e.numerator) (monomial true e.poles)
    (polynomialValue_smooth e.numerator) (monomial_smooth true e.poles (fun _ => supported))
    (fun n => (numeratorArray e.numerator n : ℝ)) (fun n => (reciprocalArray (degree e.poles) n : ℝ))
    (fun _ => Nat.cast_nonneg _) x hx
    (fun n v => polynomialValue_budget e.numerator n v x hx bound inverse)
    (fun n v => by simpa [reciprocalArray,monomialBound,reciprocalBound] using
      actual_monomial_budget true e.poles (fun _ => supported) n v x hx bound inverse) m w
  exact result.trans_eq (by simp [convolution,entryArray,Nat.cast_sum,Nat.cast_mul])

/-- A momentum direction vanishes at its actual position, including mixed and repeated words. -/
theorem entry_p_zero (e : RationalEntry) (supported : poleSupported e.poles)
    (m : ℕ) (w : Word m) (x : Phase) (hx : x∈coframeDomain)
    (k : Fin m) (momentum : (w k).2=true) : jet m (entryValue e) w x=0 := by
  let embedding : (Fin 100 → ℝ) →L[ℝ] Phase := (ContinuousLinearMap.id ℝ _).prod 0
  let projection : Phase →L[ℝ] (Fin 100 → ℝ) := ContinuousLinearMap.fst ℝ _ _
  let D : Set (Fin 100 → ℝ) := embedding ⁻¹' coframeDomain
  let g : (Fin 100 → ℝ) → ℝ := entryValue e ∘ embedding
  have openD : IsOpen D := coframeDomain_open.preimage embedding.continuous
  have openPullback : IsOpen (projection ⁻¹' D) := openD.preimage projection.continuous
  have smooth : ContDiffOn ℝ ∞ g D := by
    intro z hz
    exact (((entryValue_smooth e supported (embedding z) hz).contDiffAt
      (coframeDomain_open.mem_nhds hz)).comp z embedding.contDiff.contDiffAt).contDiffWithinAt
  have member : projection x∈D := hx
  have native : g ∘ projection=entryValue e := rfl
  have derivative := projection.iteratedFDerivWithin_comp_right smooth openD.uniqueDiffOn
    openPullback.uniqueDiffOn (x:=x) member (finite_order m)
  have targetRead : iteratedFDerivWithin ℝ m g D (projection x)=iteratedFDeriv ℝ m g (projection x) :=
    iteratedFDerivWithin_of_isOpen m openD member
  rw [iteratedFDerivWithin_of_isOpen m openPullback member,targetRead,native] at derivative
  rw [jet,derivative,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply (iteratedFDeriv ℝ m g (projection x)).map_coord_zero k
  simp [projection,slotDirection,momentum]

def matrixArray {r c : ℕ} (M : Fin r → Fin c → RationalEntry) (n : ℕ) : ℕ :=
  max (Finset.univ.sup (fun i => ∑ j,entryArray (M i j) n))
      (Finset.univ.sup (fun j => ∑ i,entryArray (M i j) n))

theorem matrix_row_budget {r c : ℕ} (M : Fin r → Fin c → RationalEntry)
    (supported : ∀ i j,poleSupported (M i j).poles) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈coframeDomain) (bound : ∀ i,|qCoordinate i x|≤15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹|≤15) (i : Fin r) :
    (∑ j,|jet m (entryValue (M i j)) w x|)≤(matrixArray M m : ℝ) := by
  refine (Finset.sum_le_sum (fun j _ => actual_entry_budget (M i j) (supported i j) m w x hx bound inverse)).trans ?_
  rw [←Nat.cast_sum]
  exact_mod_cast (Finset.le_sup (f:=fun i => ∑ j,entryArray (M i j) m) (Finset.mem_univ i)).trans (Nat.le_max_left _ _)

theorem matrix_column_budget {r c : ℕ} (M : Fin r → Fin c → RationalEntry)
    (supported : ∀ i j,poleSupported (M i j).poles) (m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈coframeDomain) (bound : ∀ i,|qCoordinate i x|≤15)
    (inverse : ∀ i,diagonal i → |(qCoordinate i x)⁻¹|≤15) (j : Fin c) :
    (∑ i,|jet m (entryValue (M i j)) w x|)≤(matrixArray M m : ℝ) := by
  refine (Finset.sum_le_sum (fun i _ => actual_entry_budget (M i j) (supported i j) m w x hx bound inverse)).trans ?_
  rw [←Nat.cast_sum]
  exact_mod_cast (Finset.le_sup (f:=fun j => ∑ i,entryArray (M i j) m) (Finset.mem_univ j)).trans (Nat.le_max_right _ _)

end LowEnergy.PreparationVacuumCoframeBudget
