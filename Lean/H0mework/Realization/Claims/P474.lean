/-
  Proposition 474: null is not an autonomous alternative.

  P469 proved the endpoint facts: complement sends `0` to `1` and `1` to `0`,
  and neither singleton endpoint is complement-closed in a nontrivial carrier.

  This file packages the sharper dependency statement behind the prose

      Null cannot stand alone.

  Any complement-closed semantic carrier that contains `0` must also contain
  `1`; any such carrier that contains `1` must also contain `0`.  Thus the
  smallest complement-closed endpoint carrier containing either endpoint is
  the pair `{0, 1}`.

  Boundary: this is still algebra, not metaphysics.  It proves that, once the
  framework has accepted the complement involution as structure, an isolated
  null endpoint is not a coherent closed carrier unless the ambient algebra is
  degenerate.
-/

import H0mework.Physics.RepresentationSources.P473
import H0mework.Realization.Claims.P469

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Endpoint dependency under complement closure -/

/-- THEOREM 1: in a complement-closed carrier, containing null forces
containing everything. -/
theorem mem_one_of_complementClosed_mem_zero
    {K : Type*} [Ring K] {S : Set K}
    (hclosed : ComplementClosed S) (hzero : (0 : K) ∈ S) :
    (1 : K) ∈ S := by
  simpa [complement] using hclosed hzero

/-- THEOREM 2: in a complement-closed carrier, containing everything forces
containing null. -/
theorem mem_zero_of_complementClosed_mem_one
    {K : Type*} [Ring K] {S : Set K}
    (hclosed : ComplementClosed S) (hone : (1 : K) ∈ S) :
    (0 : K) ∈ S := by
  simpa [complement] using hclosed hone

/-- THEOREM 3: any complement-closed carrier containing null contains the
whole null/everything endpoint pair. -/
theorem nullEverythingPair_subset_of_complementClosed_mem_zero
    {K : Type*} [Ring K] {S : Set K}
    (hclosed : ComplementClosed S) (hzero : (0 : K) ∈ S) :
    nullEverythingPair K ⊆ S := by
  intro x hx
  rcases hx with hx | hx
  · subst x
    exact hzero
  · subst x
    exact mem_one_of_complementClosed_mem_zero hclosed hzero

/-- THEOREM 4: any complement-closed carrier containing everything contains
the whole null/everything endpoint pair. -/
theorem nullEverythingPair_subset_of_complementClosed_mem_one
    {K : Type*} [Ring K] {S : Set K}
    (hclosed : ComplementClosed S) (hone : (1 : K) ∈ S) :
    nullEverythingPair K ⊆ S := by
  intro x hx
  rcases hx with hx | hx
  · subst x
    exact mem_zero_of_complementClosed_mem_one hclosed hone
  · subst x
    exact hone

/-- THEOREM 5: there is no complement-closed carrier that contains null while
excluding everything. -/
theorem no_autonomous_null_carrier
    {K : Type*} [Ring K] {S : Set K} :
    ¬ (ComplementClosed S ∧ (0 : K) ∈ S ∧ (1 : K) ∉ S) := by
  rintro ⟨hclosed, hzero, hnot_one⟩
  exact hnot_one (mem_one_of_complementClosed_mem_zero hclosed hzero)

/-- THEOREM 6: there is no complement-closed carrier that contains everything
while excluding null. -/
theorem no_autonomous_everything_carrier
    {K : Type*} [Ring K] {S : Set K} :
    ¬ (ComplementClosed S ∧ (1 : K) ∈ S ∧ (0 : K) ∉ S) := by
  rintro ⟨hclosed, hone, hnot_zero⟩
  exact hnot_zero (mem_zero_of_complementClosed_mem_one hclosed hone)

/-- THEOREM 7: the endpoint pair is the smallest complement-closed carrier
containing null, in the subset sense. -/
theorem nullEverythingPair_minimal_containing_zero
    {K : Type*} [Ring K] :
    ComplementClosed (nullEverythingPair K) ∧
      (0 : K) ∈ nullEverythingPair K ∧
      ∀ S : Set K, ComplementClosed S -> (0 : K) ∈ S ->
        nullEverythingPair K ⊆ S := by
  refine ⟨nullEverythingPair_complementClosed, ?_, ?_⟩
  · simp [nullEverythingPair]
  · intro S hclosed hzero
    exact nullEverythingPair_subset_of_complementClosed_mem_zero
      hclosed hzero

/-- THEOREM 8: the endpoint pair is also the smallest complement-closed
carrier containing everything. -/
theorem nullEverythingPair_minimal_containing_one
    {K : Type*} [Ring K] :
    ComplementClosed (nullEverythingPair K) ∧
      (1 : K) ∈ nullEverythingPair K ∧
      ∀ S : Set K, ComplementClosed S -> (1 : K) ∈ S ->
        nullEverythingPair K ⊆ S := by
  refine ⟨nullEverythingPair_complementClosed, ?_, ?_⟩
  · simp [nullEverythingPair]
  · intro S hclosed hone
    exact nullEverythingPair_subset_of_complementClosed_mem_one
      hclosed hone

/-! ## Bundled receipt -/

/-- A compact receipt for the endpoint dependency layer. -/
structure AutonomousNullDissolutionReceipt (K : Type*) [Ring K] : Prop where
  null_forces_everything :
    ∀ S : Set K, ComplementClosed S -> (0 : K) ∈ S -> (1 : K) ∈ S
  everything_forces_null :
    ∀ S : Set K, ComplementClosed S -> (1 : K) ∈ S -> (0 : K) ∈ S
  no_closed_null_without_everything :
    ∀ S : Set K,
      ¬ (ComplementClosed S ∧ (0 : K) ∈ S ∧ (1 : K) ∉ S)
  no_closed_everything_without_null :
    ∀ S : Set K,
      ¬ (ComplementClosed S ∧ (1 : K) ∈ S ∧ (0 : K) ∉ S)
  endpoint_pair_minimal_from_null :
    ComplementClosed (nullEverythingPair K) ∧
      (0 : K) ∈ nullEverythingPair K ∧
      ∀ S : Set K, ComplementClosed S -> (0 : K) ∈ S ->
        nullEverythingPair K ⊆ S
  endpoint_pair_minimal_from_everything :
    ComplementClosed (nullEverythingPair K) ∧
      (1 : K) ∈ nullEverythingPair K ∧
      ∀ S : Set K, ComplementClosed S -> (1 : K) ∈ S ->
        nullEverythingPair K ⊆ S

/-- THEOREM 9: every ring carrier has the autonomous-null dissolution
receipt. -/
theorem autonomousNullDissolutionReceipt
    (K : Type*) [Ring K] :
    AutonomousNullDissolutionReceipt K where
  null_forces_everything :=
    fun _ hclosed hzero =>
      mem_one_of_complementClosed_mem_zero hclosed hzero
  everything_forces_null :=
    fun _ hclosed hone =>
      mem_zero_of_complementClosed_mem_one hclosed hone
  no_closed_null_without_everything :=
    fun _ => no_autonomous_null_carrier
  no_closed_everything_without_null :=
    fun _ => no_autonomous_everything_carrier
  endpoint_pair_minimal_from_null :=
    nullEverythingPair_minimal_containing_zero
  endpoint_pair_minimal_from_everything :=
    nullEverythingPair_minimal_containing_one

end AffineRelaxation
end SaturationMonoid
