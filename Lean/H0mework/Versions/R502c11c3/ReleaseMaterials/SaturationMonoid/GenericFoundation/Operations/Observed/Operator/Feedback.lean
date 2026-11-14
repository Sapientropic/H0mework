import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.BigOperators

set_option autoImplicit false

namespace SaturationMonoid.SourceLinearFeedback

open scoped BigOperators

variable {K V O : Type*} [CommRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup O] [Module K O]

variable (observe : V →ₗ[K] O) (lift : O →ₗ[K] V)

/-- The part left after using the actual section of the observation. -/
def residual : V →ₗ[K] V := LinearMap.id - lift.comp observe

private theorem split (point : V) :
    lift (observe point) + residual observe lift point = point := by
  change lift (observe point) + (point - lift (observe point)) = point
  rw [add_comm, sub_add_cancel]

variable (action : V →ₗ[K] V)

/-- Advance the unobserved part and remove the newly visible component. -/
def hiddenAction : V →ₗ[K] V := (residual observe lift).comp action

/-- Each read enters the hidden carrier through the actual action on its section. -/
def response (lag : Nat) : O →ₗ[K] V :=
  (hiddenAction observe lift action ^ lag).comp ((hiddenAction observe lift action).comp lift)

theorem hidden_step (point : V) :
    residual observe lift (action point) =
      hiddenAction observe lift action (residual observe lift point) +
      response observe lift action 0 (observe point) := by
  change hiddenAction observe lift action point =
    hiddenAction observe lift action (residual observe lift point) +
      hiddenAction observe lift action (lift (observe point))
  rw [← map_add, add_comm, split observe lift]

/-- The old hidden material and the finite read history generate the complete current field. -/
def reassemble (hidden : V) (reads : Nat → O) (n : Nat) : V :=
  lift (reads n) + ((hiddenAction observe lift action ^ n) hidden +
    ∑ j ∈ Finset.range n, response observe lift action (n-(j+1)) (reads j))

private theorem residual_history (source : V) (n : Nat) :
    residual observe lift ((action ^ n) source) =
      (hiddenAction observe lift action ^ n) (residual observe lift source) +
        ∑ j ∈ Finset.range n, response observe lift action (n-(j+1)) (observe ((action ^ j) source)) := by
  let A := hiddenAction observe lift action
  let injection := fun j : Nat => A (lift (observe ((action ^ j) source)))
  change residual observe lift ((action ^ n) source) =
    (A ^ n) (residual observe lift source) + ∑ j ∈ Finset.range n, (A ^ (n-(j+1))) (injection j)
  induction n with
  | zero => simp
  | succ n previous =>
    have step :
        residual observe lift ((action ^ (n+1)) source) =
          A (residual observe lift ((action ^ n) source)) + injection n := by
      rw [pow_succ', Module.End.mul_apply]
      exact hidden_step observe lift action _
    rw [step, previous, map_add, map_sum,
      Finset.sum_range_succ, Nat.sub_self, pow_zero, Module.End.one_apply,
      pow_succ' A, Module.End.mul_apply, add_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro j belongs
    have earlier : j < n := Finset.mem_range.mp belongs
    have advance : n+1-(j+1) = (n-(j+1))+1 := by omega
    rw [advance, pow_succ', Module.End.mul_apply]

theorem reassemble_action (source : V) (n : Nat) :
    reassemble observe lift action (residual observe lift source)
      (fun j => observe ((action ^ j) source)) n = (action ^ n) source := by
  unfold reassemble
  rw [← residual_history observe lift action]
  exact split observe lift _

end SaturationMonoid.SourceLinearFeedback
