import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCutoffPsi

set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCutoffBudget
open CanonicalPreparationCutoff
open scoped BigOperators ContDiff Topology

abbrev ChiAt (n : ℕ) := Fin (n+1) → ℝ

def nextChi {n : ℕ} (previous : ChiAt n) : ChiAt (n+1) := fun j =>
  if h : j.val<n+1 then previous ⟨j.val,h⟩ else
    9*(psiBound (n+1)+∑ r : Fin (n+1),((n+1).choose (r.val+1) : ℝ)*
      (2*psiBound (r.val+1))*previous ⟨n-r.val,by have := r.isLt; omega⟩)

def chiTable (n : ℕ) : ChiAt n :=
  Nat.rec (motive:=ChiAt) (fun _ => 1) (fun _ previous => nextChi previous) n

def chiBound (n : ℕ) : ℝ := chiTable n (Fin.last n)

theorem chiTable_preserves (n : ℕ) (j : Fin (n+1)) : chiTable (n+1) (Fin.castSucc j)=chiTable n j := by
  simp only [chiTable,nextChi,Fin.val_castSucc,j.isLt,dif_pos]

theorem chiTable_previous (small big : ℕ) (paid : small≤ big) (j : Fin (small+1)) :
    chiTable big (Fin.castLE (by omega) j)=chiTable small j := by
  induction big,paid using Nat.le_induction with
  | base => rfl
  | succ big paid ih =>
    have index : (Fin.castLE (by omega) j : Fin (big+2))=
        Fin.castSucc (Fin.castLE (by omega) j : Fin (big+1)) := rfl
    rw [index,chiTable_preserves,ih]

theorem chiTable_readback (n : ℕ) (j : Fin (n+1)) : chiTable n j=chiBound j.val := by
  have read := chiTable_previous j.val n (by have := j.isLt; omega) (Fin.last j.val)
  have same : (Fin.castLE (by have := j.isLt; omega) (Fin.last j.val) : Fin (n+1))=j := by apply Fin.ext; rfl
  rw [same] at read
  exact read

theorem chiBound_zero : chiBound 0=1 := rfl
theorem chiBound_succ (n : ℕ) : chiBound (n+1)=9*(psiBound (n+1)+
    ∑ r : Fin (n+1),((n+1).choose (r.val+1) : ℝ)*(2*psiBound (r.val+1))*chiBound (n-r.val)) := by
  unfold chiBound
  simp only [chiTable,nextChi,Fin.val_last,lt_self_iff_false,dite_false]
  congr 2
  apply Finset.sum_congr rfl
  intro r _
  change ((n+1).choose (r.val+1) : ℝ)*(2*psiBound (r.val+1))*
    chiTable n ⟨n-r.val,by have := r.isLt; omega⟩ =
    ((n+1).choose (r.val+1) : ℝ)*(2*psiBound (r.val+1))*chiBound (n-r.val)
  rw [chiTable_readback]

theorem chiBound_nonnegative (n : ℕ) : 0≤ chiBound n := by
  have table : ∀ n (j : Fin (n+1)),0≤ chiTable n j := by
    intro n
    induction n with
    | zero => intro j; norm_num [chiTable]
    | succ n ih =>
      intro j
      change 0≤ nextChi (chiTable n) j
      unfold nextChi
      split_ifs
      · exact ih _
      · apply mul_nonneg (by norm_num)
        apply add_nonneg (psiBound_nonnegative _)
        exact Finset.sum_nonneg (fun r _ => mul_nonneg
          (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (psiBound_nonnegative _))) (ih _))
  exact table n (Fin.last n)

def chiDenominator (x : ℝ) : ℝ := expNegInvGlue x+expNegInvGlue (1-x)

theorem chiDenominator_smooth : ContDiff ℝ ∞ chiDenominator :=
  expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

private theorem finite_order (n : ℕ) : (n : ℕ∞ω)≤∞ := by exact_mod_cast (ENat.natCast_lt_top n).le

theorem chiDenominator_budget (n : ℕ) (x : ℝ) : |iteratedDeriv n chiDenominator x|≤2*psiBound n := by
  unfold chiDenominator
  rw [iteratedDeriv_fun_add (f:=expNegInvGlue) (g:=fun y : ℝ => expNegInvGlue (1-y)) (x:=x) (expNegInvGlue.contDiff.contDiffAt.of_le (finite_order n))
    ((expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)).contDiffAt.of_le (finite_order n)),
    iteratedDeriv_comp_const_sub]
  have first := actual_psi_budget n x
  have second := actual_psi_budget n (1-x)
  change |iteratedDeriv n expNegInvGlue x+(-1 : ℝ)^n*iteratedDeriv n expNegInvGlue (1-x)|≤2*psiBound n
  have triangle := abs_add_le (iteratedDeriv n expNegInvGlue x)
    ((-1 : ℝ)^n*iteratedDeriv n expNegInvGlue (1-x))
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] at triangle
  exact triangle.trans (by linarith)

theorem chiDenominator_identity : (fun x => chiDenominator x*Real.smoothTransition x)=expNegInvGlue := by
  funext x
  rw [Real.smoothTransition]
  change chiDenominator x*(expNegInvGlue x/chiDenominator x)=_
  have regular : chiDenominator x≠0 := (Real.smoothTransition.pos_denom x).ne'
  field_simp [regular]

theorem actual_transition_budget (n : ℕ) (x : ℝ) : |iteratedDeriv n Real.smoothTransition x|≤ chiBound n := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    cases n with
    | zero =>
      rw [chiBound_zero,iteratedDeriv_zero,abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    | succ n =>
      let term : ℕ → ℝ := fun r => ((n+1).choose r : ℝ)*iteratedDeriv r chiDenominator x*
        iteratedDeriv (n+1-r) Real.smoothTransition x
      have relation := iteratedDeriv_fun_mul (x:=x) (n:=n+1) (chiDenominator_smooth.contDiffAt.of_le (finite_order (n+1)))
        (Real.smoothTransition.contDiff.contDiffAt.of_le (finite_order (n+1)))
      change iteratedDeriv (n+1) (fun y => chiDenominator y*Real.smoothTransition y) x=
        ∑ r∈Finset.range (n+2),term r at relation
      rw [chiDenominator_identity,Finset.sum_range_succ'] at relation
      have coefficient : term 0=chiDenominator x*iteratedDeriv (n+1) Real.smoothTransition x := by simp [term]
      rw [coefficient] at relation
      have tail : |∑ r∈Finset.range (n+1),term (r+1)|≤
          ∑ r : Fin (n+1),((n+1).choose (r.val+1) : ℝ)*(2*psiBound (r.val+1))*chiBound (n-r.val) := by
        calc
          _≤∑ r∈Finset.range (n+1),|term (r+1)| := Finset.abs_sum_le_sum_abs _ _
          _=∑ r : Fin (n+1),|term (r.val+1)| := (Fin.sum_univ_eq_sum_range _ _).symm
          _≤_ := by
            apply Finset.sum_le_sum
            intro r _
            have small : n-r.val<n+1 := by omega
            have second := ih (n-r.val) small x
            have first := chiDenominator_budget (r.val+1) x
            have index : n+1-(r.val+1)=n-r.val := by omega
            have nonnegativeChoose : 0≤((n+1).choose (r.val+1) : ℝ) := by positivity
            simp only [term,abs_mul,abs_of_nonneg nonnegativeChoose,index]
            exact mul_le_mul (mul_le_mul_of_nonneg_left first nonnegativeChoose) second
              (abs_nonneg _) (mul_nonneg nonnegativeChoose (mul_nonneg (by norm_num) (psiBound_nonnegative _)))
      have isolated : chiDenominator x*iteratedDeriv (n+1) Real.smoothTransition x=
          iteratedDeriv (n+1) expNegInvGlue x-∑ r∈Finset.range (n+1),term (r+1) := by linarith [relation]
      have absolute := congrArg abs isolated
      have denominator := transition_denominator x
      change (1/9 : ℝ)<chiDenominator x at denominator
      rw [abs_mul,abs_of_pos (by linarith : 0<chiDenominator x)] at absolute
      have triangle := abs_add_le (iteratedDeriv (n+1) expNegInvGlue x)
        (-(∑ r∈Finset.range (n+1),term (r+1)))
      simp only [←sub_eq_add_neg,abs_neg] at triangle
      have bound := triangle.trans (add_le_add (actual_psi_budget (n+1) x) tail)
      rw [←absolute] at bound
      rw [chiBound_succ]
      nlinarith [abs_nonneg (iteratedDeriv (n+1) Real.smoothTransition x)]

theorem actual_sourceChi_budget (n : ℕ) (t : ℝ) : |iteratedDeriv n sourceChi t|≤ chiBound n := by
  have identity : sourceChi=fun t : ℝ => Real.smoothTransition (t-1) := funext sourceChi_transition
  rw [identity,iteratedDeriv_comp_sub_const]
  exact actual_transition_budget n (t-1)

end LowEnergy.PreparationVacuumCutoffBudget
