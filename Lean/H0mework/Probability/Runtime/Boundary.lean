import H0mework.Probability.Runtime.Expectation
import H0mework.Realization.HistoryTopology.Probability
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith

/-!
# The boundary of a shifted actual-history mean

The two decompositions of the same finite history leave its actual first and
last values. A bounded continuous function controls those two field values by
its own norm, producing the finite error used by invariant-limit consumers.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRuntimeHistoryProbability

open SourceGeneratedScalarCofinalTopology.NativeProbability
open scoped BoundedContinuousFunction

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

theorem mean_shift_boundary (runtime : LivingRuntimeState process) (bound : Nat)
    (read : process.State → ℝ) :
    ((bound + 1 : Nat) : ℝ) * (mean runtime.tick.next bound read - mean runtime bound read) =
      read (history runtime bound).target.state - read runtime.state := by
  have first : ((bound + 2 : Nat) : ℝ) * mean runtime (bound + 1) read =
      read runtime.state + ((bound + 1 : Nat) : ℝ) * mean runtime.tick.next bound read := by
    rw [count_mul_mean, count_mul_mean, Fin.sum_univ_succ]
    change read runtime.state +
        ∑ index : Fin (bound + 1), read (runtime.advance (index.val + 1)).state =
      read runtime.state +
        ∑ index : Fin (bound + 1), read (runtime.tick.next.advance index.val).state
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    rw [SourceOperationRuntime.runtime_tail]
  rw [mul_sub]
  linarith only [first, mean_extension runtime bound read]

variable {B : Type u} [AddCommGroup B]

theorem bounded_field_mean_shift (observation : process.State → B)
    (runtime : LivingRuntimeState process) (bound : Nat) :
    letI : UniformSpace (Field observation) := fieldUniform observation
    ∀ f : Field observation →ᵇ ℝ,
      |mean runtime.tick.next bound (fun state => f (fieldPoint observation state)) -
          mean runtime bound (fun state => f (fieldPoint observation state))| ≤
        2 * ‖f‖ / ((bound + 1 : Nat) : ℝ) := by
  let : UniformSpace (Field observation) := fieldUniform observation
  intro f
  have positive : 0 < ((bound + 1 : Nat) : ℝ) := by positivity
  have boundary := mean_shift_boundary runtime bound (fun state => f (fieldPoint observation state))
  apply (le_div_iff₀ positive).mpr
  calc
    |mean runtime.tick.next bound (fun state => f (fieldPoint observation state)) -
        mean runtime bound (fun state => f (fieldPoint observation state))| * ((bound + 1 : Nat) : ℝ) =
        |((bound + 1 : Nat) : ℝ) *
          (mean runtime.tick.next bound (fun state => f (fieldPoint observation state)) -
            mean runtime bound (fun state => f (fieldPoint observation state)))| := by
      rw [abs_mul, abs_of_pos positive]
      exact mul_comm _ _
    _ = |f (fieldPoint observation (history runtime bound).target.state) -
        f (fieldPoint observation runtime.state)| := congrArg abs boundary
    _ ≤ 2 * ‖f‖ := by
      simpa only [Real.dist_eq] using
        f.dist_le_two_norm (fieldPoint observation (history runtime bound).target.state)
          (fieldPoint observation runtime.state)

end

end SourceGeneratedRuntimeHistoryProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
