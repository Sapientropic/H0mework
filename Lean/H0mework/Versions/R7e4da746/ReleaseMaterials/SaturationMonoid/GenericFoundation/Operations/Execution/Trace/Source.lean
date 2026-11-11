import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Add
import H0mework.Realization.Operations.Execution.Coefficients.Words

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace SaturationMonoid.SourceOperationExecution.Trace
open SourceOperationEffects
universe u v w
variable {S : Type u} {V : S → Type v} {X : S → Type w}
 [∀ s, AddCommGroup (V s)] {environment : Env V X} {s : S}

inductive LinearInterleaving (operation : V s →+ V s) :
 {body : Expr V X s} → {total input : V s} →
 Trace environment (.linear operation body) (.const total) →
 Trace environment body (.const input) → Type (max u v w)
 | last (input : V s) : LinearInterleaving operation
   (.single (.linearConst operation input)) (.nil (.const input))
 | step {body middle : Expr V X s} {total input : V s}
   (paid : Step environment body middle)
   {actual : Trace environment (.linear operation middle) (.const total)}
   {inside : Trace environment middle (.const input)}
   (tail : LinearInterleaving operation actual inside) :
   LinearInterleaving operation (.cons (.linear operation paid) actual) (.cons paid inside)

structure LinearSplit {operation : V s →+ V s} {body : Expr V X s} {total : V s}
 (actual : Trace environment (.linear operation body) (.const total)) where
 input : V s
 trace : Trace environment body (.const input)
 interleaving : LinearInterleaving operation actual trace

def splitLinear {operation : V s →+ V s} {body : Expr V X s} {total : V s}
 (actual : Trace environment (.linear operation body) (.const total)) : LinearSplit actual :=
 match actual with
 | .cons (.linearConst _ input) (.nil _) => ⟨input, .nil _, .last input⟩
 | .cons (.linearConst _ _) (.cons impossible _) => nomatch impossible
 | .cons (.linear _ paid) tail =>
   let cut := splitLinear tail
   ⟨cut.input, .cons paid cut.trace, .step paid cut.interleaving⟩

theorem LinearSplit.length_eq {operation : V s →+ V s} {body : Expr V X s} {total : V s}
 {actual : Trace environment (.linear operation body) (.const total)} (cut : LinearSplit actual) :
 actual.length = cut.trace.length + 1 := by
 rcases cut with ⟨input,trace,interleaving⟩
 induction interleaving with
 | last => rfl
 | step _ _ prior => simp only [Trace.length] at *; omega

/-- Every cut retains the given parent history, rather than executing its syntax again. -/
inductive Subtrace :
 {whole part : Expr V X s} → {total value : V s} →
 Trace environment whole (.const total) → Trace environment part (.const value) → Type (max u v w)
 | refl {whole : Expr V X s} {total : V s} (actual : Trace environment whole (.const total)) :
   Subtrace actual actual
 | left {left right part : Expr V X s} {total value : V s}
   {actual : Trace environment (.add left right) (.const total)}
   {inside : Trace environment part (.const value)}
   (cut : AddSplit actual) (tail : Subtrace cut.leftTrace inside) : Subtrace actual inside
 | right {left right part : Expr V X s} {total value : V s}
   {actual : Trace environment (.add left right) (.const total)}
   {inside : Trace environment part (.const value)}
   (cut : AddSplit actual) (tail : Subtrace cut.rightTrace inside) : Subtrace actual inside
 | linear {operation : V s →+ V s} {body part : Expr V X s} {total value : V s}
   {actual : Trace environment (.linear operation body) (.const total)}
   {inside : Trace environment part (.const value)}
   (cut : LinearSplit actual) (tail : Subtrace cut.trace inside) : Subtrace actual inside

def Subtrace.trans {whole middle part : Expr V X s} {total mid value : V s}
 {actual : Trace environment whole (.const total)} {between : Trace environment middle (.const mid)}
 {inside : Trace environment part (.const value)} (outer : Subtrace actual between)
 (inner : Subtrace between inside) : Subtrace actual inside :=
 match outer with
 | .refl _ => inner
 | .left cut tail => .left cut (tail.trans inner)
 | .right cut tail => .right cut (tail.trans inner)
 | .linear cut tail => .linear cut (tail.trans inner)

def Subtrace.address {whole part : Expr V X s} {total value : V s}
 {actual : Trace environment whole (.const total)} {inside : Trace environment part (.const value)} :
 Subtrace actual inside → List Nat
 | .refl _ => []
 | .left _ tail => 0 :: tail.address
 | .right _ tail => 1 :: tail.address
 | .linear _ tail => 2 :: tail.address

theorem Subtrace.length_le {whole part : Expr V X s} {total value : V s}
 {actual : Trace environment whole (.const total)} {inside : Trace environment part (.const value)}
 (retained : Subtrace actual inside) : inside.length ≤ actual.length := by
 induction retained with
 | refl => exact Nat.le_refl _
 | left cut _ prior => have sum := cut.length_eq; omega
 | right cut _ prior => have sum := cut.length_eq; omega
 | linear cut _ prior => have sum := cut.length_eq; omega

structure SourceReceipt {whole : Expr V X s} {total : V s}
 (actual : Trace environment whole (.const total)) (expression : Expr V X s) where
 value : V s
 trace : Trace environment expression (.const value)
 retained : Subtrace actual trace

namespace SourceReceipt
def integer {coefficient : ℤ} {expression : Expr V X s} {total : V s}
 (actual : Trace environment (Coefficients.integerExpansion coefficient expression) (.const total))
 (nonzero : coefficient ≠ 0) : SourceReceipt actual expression := by
 cases coefficient with
 | ofNat count =>
   cases count with
   | zero => exact False.elim (nonzero rfl)
   | succ count =>
     let cut := splitAdd actual
     exact ⟨cut.leftValue,cut.leftTrace,.left cut (.refl _)⟩
 | negSucc count =>
   let outer := splitLinear actual
   let inner := splitAdd outer.trace
   exact ⟨inner.leftValue,inner.leftTrace,.linear outer (.left inner (.refl _))⟩

/-- The list index distinguishes equal expressions at different source positions. -/
def item (items : List (Expr V X s × ℤ)) {total : V s}
 (actual : Trace environment (Coefficients.terms items) (.const total))
 (index : Fin items.length) (nonzero : (items[index]).2 ≠ 0) :
 SourceReceipt actual (items[index]).1 := by
 cases items with
 | nil => exact Fin.elim0 index
 | cons head tail =>
   let cut := splitAdd actual
   cases index using Fin.cases with
   | zero =>
     let result := integer cut.leftTrace nonzero
     exact ⟨result.value,result.trace,.left cut result.retained⟩
   | succ index =>
     let result := item tail cut.rightTrace index nonzero
     exact ⟨result.value,result.trace,.right cut result.retained⟩

end SourceReceipt
end SaturationMonoid.SourceOperationExecution.Trace
