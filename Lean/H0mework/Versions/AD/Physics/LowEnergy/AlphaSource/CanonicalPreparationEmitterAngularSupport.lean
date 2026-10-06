import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralRowsProgram

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalEmitter
open PreparationVacuumDAGSemantic PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open scoped BigOperators Pointwise

-- The finite carrier depends only on the source program's constructors and exponents.
-- In particular it performs no equality test on actual scalar functions.
def angularSupport {s : ExprSort} (e : Expression s) : Finset AngularExponent :=
  Expression.rec (motive:=fun _ _=>Finset AngularExponent)
    (fun _=>∅) (fun _ _ _ _=>∅) (fun _ _=>∅) (fun _ _ _ _=>∅)
    (fun _ _=>∅) (fun _ _ _=>∅) (fun _ _=>∅)
    ∅ (fun u _ _=>{u}) (fun _ _ a b=>a∪b) (fun _ a=>a)
    (fun _ _ a b=>a+b) (fun _ values=>Finset.univ.biUnion values)
    (fun _ _ _ a b=>a+b) e

theorem weighted_support_subset (r : ℕ) (P Q : AngularPolynomial) :
    (weighted r P Q).support⊆P.support+Q.support := by
  intro u member
  by_contra outside
  have zero : MvPolynomial.coeff u (weighted r P Q)=0 := by
    simp only [weighted,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have different : a+b≠u := by
      intro same
      apply outside
      exact Finset.mem_add.mpr ⟨a,ha,b,hb,same⟩
    simp only [different,if_false]
  exact (MvPolynomial.mem_support_iff.mp member) zero

def Covered : (s : ExprSort) → Expression s → Prop
  | .symbol,_=>True
  | .polynomial,e=>(evaluate e).support⊆angularSupport e

theorem angularSupport_covers {s : ExprSort} (e : Expression s) : Covered s e := by
  induction e with
  | primitive _=>trivial
  | addS _ _ _ _=>trivial
  | negS _ _=>trivial
  | mulS _ _ _ _=>trivial
  | sumS _ _=>trivial
  | coefficient _ _ _=>trivial
  | average _ _=>trivial
  | zeroP=>exact Finset.empty_subset _
  | monomial _ _ _=>exact MvPolynomial.support_monomial_subset
  | addP e f he hf=>
    exact (MvPolynomial.support_add).trans (Finset.union_subset_union he hf)
  | negP e he=>simpa only [Covered,evaluate,angularSupport,MvPolynomial.support_neg] using he
  | mulP e f he hf=>
    intro u hu
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul (evaluate e) (evaluate f) hu)
    exact Finset.mem_add.mpr ⟨a,he ha,b,hf hb,rfl⟩
  | sumP terms ih=>
    intro u hu
    obtain ⟨i,hi,h⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
    exact Finset.mem_biUnion.mpr ⟨i,hi,ih i h⟩
  | weighted r e f he hf=>
    intro u hu
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (weighted_support_subset r (evaluate e) (evaluate f) hu)
    exact Finset.mem_add.mpr ⟨a,he ha,b,hf hb,rfl⟩

theorem polynomial_over_cover (P : AngularPolynomial) (S : Finset AngularExponent) (cover : P.support⊆S) :
    P=∑ u∈S,MvPolynomial.monomial u (MvPolynomial.coeff u P) := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  apply Finset.sum_subset cover
  intro u _ outside
  rw [MvPolynomial.notMem_support_iff.mp outside,MvPolynomial.monomial_zero]

theorem coefficient_product_cover (P Q : AngularPolynomial) (S R : Finset AngularExponent)
    (left : P.support⊆S) (right : Q.support⊆R) (u : AngularExponent) :
    MvPolynomial.coeff u (P*Q)=∑ a∈S,∑ b∈R,
      if a+b=u then MvPolynomial.coeff a P*MvPolynomial.coeff b Q else 0 := by
  conv_lhs => rw [polynomial_over_cover P S left,polynomial_over_cover Q R right]
  simp only [Finset.sum_mul,Finset.mul_sum,MvPolynomial.monomial_mul,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  exact Finset.sum_comm

theorem weighted_over_cover (r : ℕ) (P Q : AngularPolynomial) (S R : Finset AngularExponent)
    (left : P.support⊆S) (right : Q.support⊆R) :
    weighted r P Q=∑ a∈S,∑ b∈R,
      MvPolynomial.monomial (a+b) (scalarJordan r (MvPolynomial.coeff a P) (MvPolynomial.coeff b Q)) := by
  unfold weighted
  trans ∑ a∈S,∑ b∈Q.support,
    MvPolynomial.monomial (a+b) (scalarJordan r (MvPolynomial.coeff a P) (MvPolynomial.coeff b Q))
  · apply Finset.sum_subset left
    intro a _ outside
    simp only [MvPolynomial.notMem_support_iff.mp outside,scalarJordan_zero_left,MvPolynomial.monomial_zero,Finset.sum_const_zero]
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_subset right
    intro b _ outside
    simp only [MvPolynomial.notMem_support_iff.mp outside,scalarJordan_zero_right,MvPolynomial.monomial_zero]

theorem coefficient_weighted_cover (r : ℕ) (P Q : AngularPolynomial) (S R : Finset AngularExponent)
    (left : P.support⊆S) (right : Q.support⊆R) (u : AngularExponent) :
    MvPolynomial.coeff u (weighted r P Q)=∑ a∈S,∑ b∈R,
      if a+b=u then scalarJordan r (MvPolynomial.coeff a P) (MvPolynomial.coeff b Q) else 0 := by
  rw [weighted_over_cover r P Q S R left right]
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]

theorem average_over_cover (P : AngularPolynomial) (S : Finset AngularExponent) (cover : P.support⊆S) :
    average P=∑ u∈S,(fun x=>angularMoment u*MvPolynomial.coeff u P x) := by
  unfold average
  apply Finset.sum_subset cover
  intro u _ outside
  rw [MvPolynomial.notMem_support_iff.mp outside]
  simp only [Pi.zero_apply,mul_zero]
  rfl

end LowEnergy.PreparationVacuumOriginalEmitter
