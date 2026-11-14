import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Alias
set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.CouncilParityProbe

def parityBlock {n : Nat} (a b c : CNFLiteral n) : CNFFormula n :=
  [[a,b,c], [a,Alias.negate b,Alias.negate c],
   [Alias.negate a,b,Alias.negate c], [Alias.negate a,Alias.negate b,c]]

theorem parityBlock_eval {n : Nat} (a b c : CNFLiteral n) (x : Nat → Bool) :
    CNFFormula.eval (parityBlock a b c) x =
      (a.eval x ^^ (b.eval x ^^ c.eval x)) := by
  simp only [parityBlock, CNFFormula.eval, List.all_cons, List.all_nil,
    CNFClause.eval, List.any_cons, List.any_nil, Alias.negate_eval]
  cases ha : a.eval x <;> cases hb : b.eval x <;> cases hc : c.eval x <;> rfl

def relationBlock {n : Nat} (a b c : CNFLiteral n) (rhs : Bool) : CNFFormula n :=
  parityBlock (if rhs then a else Alias.negate a) b c

theorem relationBlock_eval {n : Nat} (a b c : CNFLiteral n) (rhs : Bool) (x : Nat → Bool) :
    CNFFormula.eval (relationBlock a b c rhs) x = true ↔
      (a.eval x ^^ (b.eval x ^^ c.eval x)) = rhs := by
  simp only [relationBlock, parityBlock_eval]
  cases rhs <;> simp only [Bool.false_eq_true, if_false, Alias.negate_eval, if_true]
  all_goals cases ha : a.eval x <;> cases hb : b.eval x <;> cases hc : c.eval x <;> decide

end SaturationMonoid.ComplexityProjection.SATSource.CouncilParityProbe
