import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceActualEffective
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedControl
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

def coefficientPrice (c : SourceCoefficient) : ℚ:=|c.re.re|+2*|c.re.im|+4*|c.im.re|+8*|c.im.im|
def termsPrice (terms : List SourceTerm) : ℚ:=(terms.map (fun a=>coefficientPrice a.coefficient)).sum

theorem coefficientPrice_nonneg (c : SourceCoefficient) : 0≤coefficientPrice c :=by
  unfold coefficientPrice
  positivity

theorem termsPrice_nonneg (terms : List SourceTerm) : 0≤termsPrice terms :=by
  induction terms with
  | nil=>simp [termsPrice]
  | cons a rest ih=>
    change 0≤coefficientPrice a.coefficient+termsPrice rest
    exact add_nonneg (coefficientPrice_nonneg _) ih

private theorem norm_rootTwo : ‖rootTwo‖≤2 :=by
  rw [rootTwo,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_iff).2 ⟨by norm_num,by norm_num⟩
private theorem norm_rootFifteen : ‖rootFifteen‖≤4 :=by
  rw [rootFifteen,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_iff).2 ⟨by norm_num,by norm_num⟩

theorem coefficientValue_price (c : SourceCoefficient) : ‖coefficientValue c‖≤(coefficientPrice c:ℝ) :=by
  have r2:=norm_rootTwo
  have r15:=norm_rootFifteen
  have castNorm (q : ℚ) : ‖(q:ℂ)‖=(|q|:ℝ):=by norm_cast
  calc
    _≤‖(c.re.re:ℂ)‖+‖(c.re.im:ℂ)*rootTwo‖+
        ‖((c.im.re:ℂ)+(c.im.im:ℂ)*rootTwo)*rootFifteen‖:=by
      unfold coefficientValue
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _≤(|c.re.re|:ℝ)+(|c.re.im|:ℝ)*2+
        ((|c.im.re|:ℝ)+(|c.im.im|:ℝ)*2)*4:=by
      simp only [norm_mul,castNorm]
      gcongr
      exact (norm_add_le _ _).trans (by simp only [norm_mul,castNorm];gcongr)
    _=(coefficientPrice c:ℝ):=by
      unfold coefficientPrice
      push_cast
      ring

private theorem single_price (row column : Fin 289) (z : ℂ) :
    ‖(Matrix.single row column z : Matrix (Fin 289) (Fin 289) ℂ)‖≤‖z‖ :=by
  have rows : ∀i : Fin 289,(∑j : Fin 289,‖(Matrix.single row column z) i j‖₊)≤‖z‖₊ :=by
    intro i
    by_cases h : row=i
    · subst i
      simp only [Matrix.single_apply,true_and]
      simp only [apply_ite,nnnorm_zero]
      simp
    · simp [h]
  have bound:=Finset.sup_le (fun i (_ : i∈(Finset.univ:Finset (Fin 289)))=>rows i)
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast bound

private theorem powers_price (a : Powers) (p : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (bound : ∀i,‖p i‖≤r) : ‖a.value p‖≤r^a.total :=by
  simp only [Powers.value,norm_mul,norm_pow,Powers.total,pow_add]
  gcongr <;> exact bound _

theorem sourceTerm_price (a : SourceTerm) (p : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (bound : ∀i,‖p i‖≤r) : ‖a.matrix p‖≤(coefficientPrice a.coefficient:ℝ)*r^a.powers.total :=by
  calc
    _≤‖coefficientValue a.coefficient*a.powers.value p‖:=single_price _ _ _
    _=‖coefficientValue a.coefficient‖*‖a.powers.value p‖:=norm_mul _ _
    _≤ _ :=mul_le_mul (coefficientValue_price _) (powers_price _ _ _ nonneg bound)
      (norm_nonneg _) (by exact_mod_cast coefficientPrice_nonneg _)

theorem sourceMatrix_homogeneous_price (terms : List SourceTerm) (degree : ℕ)
    (homogeneous : ∀a∈terms,a.powers.total=degree) (p : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (bound : ∀i,‖p i‖≤r) : ‖sourceMatrix terms p‖≤(termsPrice terms:ℝ)*r^degree :=by
  induction terms with
  | nil=>simp [sourceMatrix,termsPrice]
  | cons a rest ih=>
    have first:=sourceTerm_price a p r nonneg bound
    rw [homogeneous a (by simp)] at first
    have remaining:=ih (fun b hb=>homogeneous b (by simp [hb]))
    rw [sourceMatrix_cons]
    calc
      _≤‖a.matrix p‖+‖sourceMatrix rest p‖:=norm_add_le _ _
      _≤(coefficientPrice a.coefficient:ℝ)*r^degree+(termsPrice rest:ℝ)*r^degree:=add_le_add first remaining
      _=(termsPrice (a::rest):ℝ)*r^degree:=by
        change _=((coefficientPrice a.coefficient+termsPrice rest:ℚ):ℝ)*r^degree
        push_cast
        ring

def positiveTerms (terms : List SourceTerm) : List SourceTerm:=terms.filter (fun a=>decide (a.powers.total≠0))

theorem sourceMatrix_positive_price (terms : List SourceTerm) (p : Fin 4→ℂ) (r : ℝ)
    (nonneg : 0≤r) (small : r≤1) (bound : ∀i,‖p i‖≤r) :
    ‖sourceMatrix (positiveTerms terms) p‖≤(termsPrice (positiveTerms terms):ℝ)*r :=by
  have termBound (a : SourceTerm) (ha : a∈positiveTerms terms) :
      ‖a.matrix p‖≤(coefficientPrice a.coefficient:ℝ)*r :=by
    have positive : 0<a.powers.total:=Nat.pos_of_ne_zero (of_decide_eq_true (List.mem_filter.mp ha).2)
    have power : r^a.powers.total≤r:=by
      simpa using pow_le_pow_of_le_one nonneg small positive
    exact (sourceTerm_price a p r nonneg bound).trans (mul_le_mul_of_nonneg_left power (by exact_mod_cast coefficientPrice_nonneg _))
  generalize positiveTerms terms=selected at termBound ⊢
  induction selected with
  | nil=>simp [sourceMatrix,termsPrice]
  | cons a rest ih=>
    have first:=termBound a (by simp)
    have tail : ‖sourceMatrix rest p‖≤(termsPrice rest:ℝ)*r:=by
      apply ih
      intro b hb
      exact termBound b (by simp [hb])
    rw [sourceMatrix_cons]
    calc
      _≤‖a.matrix p‖+‖sourceMatrix rest p‖:=norm_add_le _ _
      _≤(coefficientPrice a.coefficient:ℝ)*r+(termsPrice rest:ℝ)*r:=add_le_add first tail
      _=(termsPrice (a::rest):ℝ)*r:=by
        change _=((coefficientPrice a.coefficient+termsPrice rest:ℚ):ℝ)*r
        push_cast
        ring

private theorem powers_scaled (a : Powers) (z : ℂ) (p : Fin 4→ℂ) :
    a.value (z • p)=z^a.total*a.value p :=by
  simp only [Powers.value,Pi.smul_apply,smul_eq_mul,mul_pow,Powers.total,pow_add]
  ring

private theorem term_scaled (a : SourceTerm) (z : ℂ) (p : Fin 4→ℂ) :
    a.matrix (z • p)=z^a.powers.total • a.matrix p :=by
  ext i j
  simp only [SourceTerm.matrix,Matrix.single_apply,Matrix.smul_apply,smul_eq_mul,powers_scaled]
  split_ifs <;> ring

theorem sourceMatrix_homogeneous (terms : List SourceTerm) (degree : ℕ)
    (homogeneous : ∀a∈terms,a.powers.total=degree) (z : ℂ) (p : Fin 4→ℂ) :
    sourceMatrix terms (z • p)=z^degree • sourceMatrix terms p :=by
  induction terms with
  | nil=>simp [sourceMatrix]
  | cons a rest ih=>
    rw [sourceMatrix_cons,sourceMatrix_cons,term_scaled,homogeneous a (by simp),
      ih (fun b hb=>homogeneous b (by simp [hb])),smul_add]

theorem sourceMatrix_partition (terms : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix terms p=sourceMatrix (originTerms terms) p+sourceMatrix (positiveTerms terms) p :=by
  induction terms with
  | nil=>simp [sourceMatrix,originTerms,positiveTerms]
  | cons a rest ih=>
    by_cases h : a.powers.total=0
    · simp [originTerms,positiveTerms,h,sourceMatrix_cons,ih,add_assoc]
    · simp [originTerms,positiveTerms,h,sourceMatrix_cons,ih,add_left_comm]

theorem sourceMatrix_origin_constant (terms : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (originTerms terms) p=sourceMatrix (originTerms terms) 0 :=by
  have homogeneous : ∀a∈originTerms terms,a.powers.total=0:=by
    intro a ha
    exact of_decide_eq_true (List.mem_filter.mp ha).2
  have scaled:=sourceMatrix_homogeneous (originTerms terms) 0 homogeneous (0:ℂ) p
  simpa only [zero_smul,pow_zero,one_smul] using scaled.symm

theorem sourceMatrix_delta (terms : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix terms p-sourceMatrix terms 0=sourceMatrix (positiveTerms terms) p :=by
  rw [sourceMatrix_partition terms p,sourceMatrix_origin_constant,←originTerms_generated terms]
  abel

end LowEnergy.PreparationVacuumMixedControl
