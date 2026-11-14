import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.BigOperators

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedObservedImpulse

open scoped BigOperators

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
variable (action : V →ₗ[K] V) (read : V →ₗ[K] K) (unit : V)
variable {amount : Nat → K} {state : Nat → V}
variable (initial : state 0 = 0)
variable (write : ∀ n, state (n+1) = action (state n) + amount n • unit)

/-- A single actually injected unit generates the complete linear impulse read. -/
def response (lag : Nat) : K := read ((action^lag) unit)

include initial write

private theorem state_convolution (n : Nat) :
    state (n+1) = ∑ i ∈ Finset.range (n+1), amount i • ((action^(n-i)) unit) := by
  induction n with
  | zero =>
    rw [write,initial,map_zero,zero_add,Finset.sum_range_one,Nat.sub_self,pow_zero,Module.End.one_apply]
  | succ n previous =>
    rw [write,previous,map_sum,
      Finset.sum_range_succ (fun i => amount i • ((action^(n+1-i)) unit)) (n+1),
      Nat.sub_self,pow_zero,Module.End.one_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i inside
    have index : n+1-i = (n-i)+1 := by
      have paid := Finset.mem_range.mp inside
      omega
    rw [map_smul,index,pow_succ',Module.End.mul_apply]

theorem read_convolution (n : Nat) :
    read (state (n+1)) = ∑ i ∈ Finset.range (n+1), amount i * response action read unit (n-i) := by
  rw [state_convolution action unit initial write,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,smul_eq_mul,response]

/-- Before the first visible impulse, only the original opening amount can pay the new read. -/
theorem first_read (lag : Nat) (before : ∀ i < lag, response action read unit i = 0) :
    read (state (lag+1)) = amount 0 * response action read unit lag := by
  rw [read_convolution action read unit initial write,Finset.sum_eq_single 0,Nat.sub_zero]
  · intro i inside later
    have active := Finset.mem_range.mp inside
    rw [before _ (by omega),mul_zero]
  · exact fun missing => (missing (Finset.mem_range.mpr (Nat.zero_lt_succ lag))).elim

variable [NoZeroDivisors K]

/-- An actual nonzero opening makes complete return silence equivalent to impulse silence. -/
theorem silence_iff (opening : amount 0 ≠ 0) :
    (∀ n, read (state n) = 0) ↔ ∀ lag, response action read unit lag = 0 := by
  constructor
  · intro quiet n
    induction n using Nat.strong_induction_on with
    | h n earlier =>
      have paid := first_read action read unit initial write n earlier
      rw [quiet] at paid
      exact (mul_eq_zero.mp paid.symm).resolve_left opening
  · intro quiet n
    cases n with
    | zero => rw [initial,map_zero]
    | succ n => simp only [read_convolution action read unit initial write,quiet,mul_zero,Finset.sum_const_zero]

end SourceGeneratedObservedImpulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
