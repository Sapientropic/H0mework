import H0mework.Realization.Operations.DerivationPresentation
import H0mework.Realization.Operations.DerivationInventory
import H0mework.Checks.Realization.OperationRelations
import H0mework.Checks.Realization.OperationMixedTrace

/-! Generated proofs retain actual bindings, full update effects, and operation order. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationDerivations.Controls

open SourceOperationEffects SourceOperationRelations SourceOperationPresentation
open SourceOperationInventoryLift SourceOperationRelations.Controls
open SourceOperationEffects.MixedTraceControls

noncomputable section

def squareAddDerivation :
    Derivation (one + one) (.add square xTerm) (.const 6) :=
  Derivation.normalize (one + one) (.add square xTerm)

theorem generated_square_add_readback :
    (Expr.add square xTerm).eval (one + one) = 6 :=
  squareAddDerivation.sound

theorem actual_increment_changes_generated_relation_range :
    accidentalRelation ∈ LinearMap.range (relationMap one) ∧
    updateInventory one one accidentalRelation = (0, 2) ∧
    liftMap accidentalRelation ∉ LinearMap.range (relationMap (pairEnvironment one one)) := by
  constructor
  · rw [relation_range_eq_kernel]
    exact accidental_old_relation_zero
  constructor
  · change (evaluation one accidentalRelation, effectEvaluator one one accidentalRelation) = _
    rw [accidental_old_relation_zero, actual_increment_generates_nonzero_effect]
  · rw [relation_range_eq_kernel]
    intro killed
    have readback := LinearMap.congr_fun (evaluation_liftMap one one) accidentalRelation
    change evaluation (pairEnvironment one one) (liftMap accidentalRelation) =
      updateInventory one one accidentalRelation at readback
    have inventoryZero := readback.symm.trans killed
    have effectZero := congrArg Prod.snd inventoryZero
    change effectEvaluator one one accidentalRelation = 0 at effectZero
    rw [actual_increment_generates_nonzero_effect] at effectZero
    norm_num at effectZero

def matrixABTerm : Expr (fun _ : Unit => Mat) (fun _ => Unit) () :=
  .bilinear (s := ()) (t := ()) AddMonoidHom.mul (.const matrixA) (.const matrixB)

def matrixBATerm : Expr (fun _ : Unit => Mat) (fun _ => Unit) () :=
  .bilinear (s := ()) (t := ()) AddMonoidHom.mul (.const matrixB) (.const matrixA)

theorem matrix_operation_order_not_derivable :
    ¬ Nonempty (Derivation (fun _ _ => matrixA) matrixABTerm matrixBATerm) := by
  rintro ⟨derivation⟩
  exact matrix_cross_terms_distinct derivation.sound

def incrementBinding : ∀ s, ScalarVar s → Expr ScalarValue ScalarVar s :=
  fun _ _ => .add (.var ()) (.const 1)

/-- Substitution replays the new binding's source reduction inside the old proof. -/
def substitutedSquareDerivation :
    Derivation one (square.subst incrementBinding) (.const 4) :=
  (Derivation.normalize (fun s x => (incrementBinding s x).eval one) square).subst
    incrementBinding one

theorem substituted_binding_readback :
    (square.subst incrementBinding).eval one = 4 :=
  substitutedSquareDerivation.sound

end

end SaturationMonoid.SourceOperationDerivations.Controls
