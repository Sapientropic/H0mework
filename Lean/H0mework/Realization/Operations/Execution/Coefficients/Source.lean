import H0mework.Realization.Operations.Execution.Run

/-! The actual integer generates repeated addition and the original negation
primitive. The trace charges this source syntax rather than a zsmul callback;
original operation values and units are unchanged. -/

set_option autoImplicit false
noncomputable section
universe u v w
namespace SaturationMonoid.SourceOperationExecution.Coefficients
open SourceOperationEffects SaturationMonoid.SourceOperationExecution
variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ sort, AddCommGroup (Value sort)]

def naturalExpansion {target : Sorts} (count : Nat) (argument : Expr Value Var target) :
    Expr Value Var target := match count with
  | 0 => .const 0
  | count + 1 => .add argument (naturalExpansion count argument)

theorem naturalExpansion_eval {target : Sorts} (count : Nat)
    (environment : Env Value Var) (argument : Expr Value Var target) :
    (naturalExpansion count argument).eval environment = count • argument.eval environment := by
  induction count with
  | zero => simp only [naturalExpansion, Expr.eval, zero_nsmul]
  | succ count previous =>
      simp only [naturalExpansion, Expr.eval, previous, succ_nsmul]
      exact add_comm _ _

theorem naturalExpansion_remaining {target : Sorts} (count : Nat) (argument : Expr Value Var target) :
    remaining (naturalExpansion count argument) = count * (remaining argument + 1) := by
  induction count with
  | zero => simp only [naturalExpansion, remaining, Nat.zero_mul]
  | succ count previous =>
      simp only [naturalExpansion, remaining, previous, Nat.succ_mul]
      omega

def integerExpansion {target : Sorts} (integer : ℤ) (argument : Expr Value Var target) :
    Expr Value Var target := match integer with
  | .ofNat count => naturalExpansion count argument
  | .negSucc count => .linear (-AddMonoidHom.id _) (naturalExpansion (count + 1) argument)

theorem integerExpansion_eval {target : Sorts} (integer : ℤ)
    (environment : Env Value Var) (argument : Expr Value Var target) :
    (integerExpansion integer argument).eval environment = integer • argument.eval environment := by
  cases integer with
  | ofNat count =>
      change (naturalExpansion count argument).eval environment = (count : ℤ) • argument.eval environment
      rw [natCast_zsmul]
      exact naturalExpansion_eval count environment argument
  | negSucc count =>
      simp only [integerExpansion, Expr.eval, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
        naturalExpansion_eval, negSucc_zsmul]

def integerSourceCost (integer : ℤ) (argumentCost : Nat) : Nat := match integer with
  | .ofNat count => count * (argumentCost + 1)
  | .negSucc count => (count + 1) * (argumentCost + 1) + 1

theorem integerExpansion_remaining {target : Sorts} (integer : ℤ) (argument : Expr Value Var target) :
    remaining (integerExpansion integer argument) = integerSourceCost integer (remaining argument) := by
  cases integer <;> simp only [integerExpansion, integerSourceCost, remaining, naturalExpansion_remaining]

def integerTrace {target : Sorts} (integer : ℤ)
    (environment : Env Value Var) (argument : Expr Value Var target) :
    Trace environment (integerExpansion integer argument) (.const (integer • argument.eval environment)) :=
  (integerExpansion_eval integer environment argument) ▸ execution environment (integerExpansion integer argument)

theorem integerTrace_cost {target : Sorts} (integer : ℤ)
    (environment : Env Value Var) (argument : Expr Value Var target) :
    (integerTrace integer environment argument).length = integerSourceCost integer (remaining argument) :=
  (integerTrace integer environment argument).length_to_const.trans
    (integerExpansion_remaining integer argument)

theorem integerExpansion_effect {target : Sorts} (integer : ℤ)
    (environment increment : Env Value Var) (argument : Expr Value Var target) :
    (integerExpansion integer argument).effect environment increment = integer • argument.effect environment increment := by
  apply add_left_cancel (a := (integerExpansion integer argument).eval environment)
  rw [← Expr.eval_update, integerExpansion_eval, integerExpansion_eval, Expr.eval_update, zsmul_add]

end SaturationMonoid.SourceOperationExecution.Coefficients
