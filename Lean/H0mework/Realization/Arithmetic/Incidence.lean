import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Arithmetic as exact incidence testimony

Addition and multiplication acquire mathematical authority from typed
incidence, not from a bare numeral equality.  A sum receipt says that the
whole carrier is a tagged disjoint union; a product receipt says that it is
the complete joint-pair carrier.  The resulting cardinal equations are
derived readouts and contain no caller-selected result.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ArithmeticIncidence

universe u v w

/-- Exact additive incidence: every whole occurrence belongs to exactly one
tagged side.  `Nonempty` keeps the presentation proof-irrelevant and prevents
it from becoming a selector. -/
def ParallelIncidenceAt
    (Whole : Type u) (Left : Type v) (Right : Type w) : Prop :=
  Nonempty (Whole ≃ Left ⊕ Right)

/-- Exact multiplicative incidence: the whole occurrence is the complete
carrier of left/right pairs, with no hidden forbidden pair or quotient. -/
def JointIncidenceAt
    (Whole : Type u) (Left : Type v) (Right : Type w) : Prop :=
  Nonempty (Whole ≃ Left × Right)

/-- Addition is the cardinal readout of exact tagged parallel incidence. -/
theorem card_eq_add_of_parallel
    (Whole : Type u) (Left : Type v) (Right : Type w)
    [Fintype Whole] [Fintype Left] [Fintype Right]
    (incidence : ParallelIncidenceAt Whole Left Right) :
    Fintype.card Whole = Fintype.card Left + Fintype.card Right := by
  rcases incidence with ⟨presentation⟩
  rw [Fintype.card_congr presentation, Fintype.card_sum]

/-- Multiplication is the cardinal readout of complete joint incidence. -/
theorem card_eq_mul_of_joint
    (Whole : Type u) (Left : Type v) (Right : Type w)
    [Fintype Whole] [Fintype Left] [Fintype Right]
    (incidence : JointIncidenceAt Whole Left Right) :
    Fintype.card Whole = Fintype.card Left * Fintype.card Right := by
  rcases incidence with ⟨presentation⟩
  rw [Fintype.card_congr presentation, Fintype.card_prod]

/-- A wrong additive total cannot obtain a parallel-incidence receipt. -/
theorem no_parallel_incidence_of_card_ne
    (Whole : Type u) (Left : Type v) (Right : Type w)
    [Fintype Whole] [Fintype Left] [Fintype Right]
    (different :
      Fintype.card Whole ≠ Fintype.card Left + Fintype.card Right) :
    ParallelIncidenceAt Whole Left Right → False :=
  fun incidence => different
    (card_eq_add_of_parallel Whole Left Right incidence)

/-- A constrained or quotiented joint carrier cannot masquerade as a free
product when its cardinality exposes the missing incidence. -/
theorem no_joint_incidence_of_card_ne
    (Whole : Type u) (Left : Type v) (Right : Type w)
    [Fintype Whole] [Fintype Left] [Fintype Right]
    (different :
      Fintype.card Whole ≠ Fintype.card Left * Fintype.card Right) :
    JointIncidenceAt Whole Left Right → False :=
  fun incidence => different
    (card_eq_mul_of_joint Whole Left Right incidence)

/-- Canonical finite parallel occurrence.  The result `left + right` is an
index of the generated carrier, never an independently submitted field. -/
theorem finParallelIncidence (left right : Nat) :
    ParallelIncidenceAt (Fin (left + right)) (Fin left) (Fin right) :=
  ⟨finSumFinEquiv.symm⟩

/-- Canonical finite joint occurrence. -/
theorem finJointIncidence (left right : Nat) :
    JointIncidenceAt (Fin (left * right)) (Fin left) (Fin right) :=
  ⟨finProdFinEquiv.symm⟩

theorem fin_card_add (left right : Nat) :
    Fintype.card (Fin (left + right)) =
      Fintype.card (Fin left) + Fintype.card (Fin right) :=
  card_eq_add_of_parallel _ _ _ (finParallelIncidence left right)

theorem fin_card_mul (left right : Nat) :
    Fintype.card (Fin (left * right)) =
      Fintype.card (Fin left) * Fintype.card (Fin right) :=
  card_eq_mul_of_joint _ _ _ (finJointIncidence left right)

end ArithmeticIncidence
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
