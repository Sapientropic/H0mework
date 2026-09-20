/-
  Proposition 97: cost-aware rewrite certificates for finite stateful
  generative queries.

  Proposition 50 added Codd-style cost-aware rewrites for the finite Kleisli
  (stateless) generative fragment.  Propositions 73/78/79 then introduced the
  agent-native stateful shape:

      State -> Row -> State

  together with finite denotation and workload cost bounds.  This file adds
  the missing optimizer layer for that stateful read/generate/write fragment.
  A rewrite certificate proves both:

    * the finite stateful result set is unchanged at every current state;
    * the structural `workBound` of the rewrite target does not increase.

  Boundary: these are local rewrite laws, not a complete optimizer.  They give
  the stateful algebra a verified optimization surface and make the cost model
  rewritable, but they do not solve global plan search or cache policy.
-/

import H0mework.Realization.QueryPlans.P79

namespace FiniteStatefulGenAlg

/-! ## Rewrite certificates -/

/-- Two finite stateful queries are denotationally equivalent in a fixed finite
environment when they return the same `(row, nextState)` set for every current
state. -/
def FiniteEquivalent {State Row Prim : Type*} [DecidableEq State]
    [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (lhs rhs : FiniteStatefulGenAlg State Row Prim) : Prop :=
  forall x,
    evalFinset stateDomain rowDomain env lhs x =
      evalFinset stateDomain rowDomain env rhs x

/-- An oriented stateful rewrite certificate.  `lhs` may be replaced by `rhs`
without changing finite denotation and without increasing the structural
worst-case work bound. -/
structure RewriteCertificate {State Row Prim : Type*} [DecidableEq State]
    [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (lhs rhs : FiniteStatefulGenAlg State Row Prim) where
  result_eq :
    forall env : Prim -> State -> Finset (Row × State),
      (forall p x, env p x ⊆ pairDomain stateDomain rowDomain) ->
      (forall row, row ∈ rowDomain) ->
      (forall x, x ∈ stateDomain) ->
      FiniteEquivalent stateDomain rowDomain env lhs rhs
  workBound_le :
    workBound stateDomain rowDomain rhs ≤
      workBound stateDomain rowDomain lhs

namespace RewriteCertificate

variable {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
variable {stateDomain : Finset State} {rowDomain : Finset Row}

/-- THEOREM 1: applying a stateful rewrite certificate preserves finite
denotation at every current state. -/
theorem preserves_eval
    {lhs rhs : FiniteStatefulGenAlg State Row Prim}
    (C : RewriteCertificate stateDomain rowDomain lhs rhs)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv : forall p x, env p x ⊆ pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (x : State) :
    evalFinset stateDomain rowDomain env lhs x =
      evalFinset stateDomain rowDomain env rhs x :=
  C.result_eq env hEnv hRow hCurrent x

/-- THEOREM 2: applying a stateful rewrite certificate is structurally
cost-nonincreasing. -/
theorem nonincreasing
    {lhs rhs : FiniteStatefulGenAlg State Row Prim}
    (C : RewriteCertificate stateDomain rowDomain lhs rhs) :
    workBound stateDomain rowDomain rhs ≤
      workBound stateDomain rowDomain lhs :=
  C.workBound_le

end RewriteCertificate

/-! ## Local cost-aware stateful rewrites -/

/-- Remove an empty branch on the left of a union. -/
theorem rewrite_union_empty_left {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain (union empty q) q where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]
    omega

/-- Remove an empty branch on the right of a union. -/
theorem rewrite_union_empty_right {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain (union q empty) q where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]
    omega

/-- Intersecting with the empty query is empty. -/
theorem rewrite_inter_empty_left {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain (inter empty q) empty where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]

/-- Intersecting with the empty query on the right is empty. -/
theorem rewrite_inter_empty_right {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain (inter q empty) empty where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]

/-- Remove subtracting the empty query. -/
theorem rewrite_diff_empty_right {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain (diff q empty) q where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]
    omega

/-- Replace subtracting a query from itself by empty. -/
theorem rewrite_diff_self {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain (diff q q) empty where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]

/-- Remove a guard whose predicate is always true. -/
theorem rewrite_guard_true {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain
      (guard (fun _x _row _y => true) q) q where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]

/-- Replace a guard whose predicate is always false by empty. -/
theorem rewrite_guard_false {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain
      (guard (fun _x _row _y => false) q) empty where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]

/-- Fuse two consecutive stateful guards into one Boolean conjunction. -/
theorem rewrite_guard_guard {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (outer inner : State -> Row -> State -> Bool)
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain
      (guard outer (guard inner q))
      (guard (fun x row y => outer x row y && inner x row y) q) where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    ext pair
    by_cases hOuter : outer x pair.1 pair.2 = true <;>
      by_cases hInner : inner x pair.1 pair.2 = true <;>
      simp [evalFinset, hOuter, hInner]
  workBound_le := by
    simp [workBound]

/-- Replace `bind empty k` by `empty`. -/
theorem rewrite_bind_empty {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (k : Row -> FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain (bind empty k) empty where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    simp [evalFinset]
  workBound_le := by
    simp [workBound]

/-- Fuse two stateful generated branches with the same continuation:

`union (bind p k) (bind q k)` can be evaluated as `bind (union p q) k`.

This preserves denotation and avoids a duplicated continuation fanout in the
structural bound. -/
theorem rewrite_union_bind_fuse {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (p q : FiniteStatefulGenAlg State Row Prim)
    (k : Row -> FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain
      (union (bind p k) (bind q k))
      (bind (union p q) k) where
  result_eq := by
    intro env _hEnv _hRow _hCurrent x
    ext pair
    simp [evalFinset]
    constructor
    · intro h
      rcases h with h | h
      · rcases h with ⟨source, mid, hsource, hpair⟩
        exact ⟨source, mid, Or.inl hsource, hpair⟩
      · rcases h with ⟨source, mid, hsource, hpair⟩
        exact ⟨source, mid, Or.inr hsource, hpair⟩
    · intro h
      rcases h with ⟨source, mid, hsource, hpair⟩
      rcases hsource with hsource | hsource
      · exact Or.inl ⟨source, mid, hsource, hpair⟩
      · exact Or.inr ⟨source, mid, hsource, hpair⟩
  workBound_le := by
    simp [workBound]
    omega

/-! ## Reusable projections -/

/-- THEOREM 3: any stateful query optimized with a certified rewrite has the
same finite result set at every current state. -/
theorem rewrite_preserves_eval {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    {stateDomain : Finset State} {rowDomain : Finset Row}
    {lhs rhs : FiniteStatefulGenAlg State Row Prim}
    (C : RewriteCertificate stateDomain rowDomain lhs rhs)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv : forall p x, env p x ⊆ pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (x : State) :
    evalFinset stateDomain rowDomain env lhs x =
      evalFinset stateDomain rowDomain env rhs x :=
  C.preserves_eval env hEnv hRow hCurrent x

/-- THEOREM 4: any stateful query optimized with a certified rewrite is
structurally no more expensive under `workBound`. -/
theorem rewrite_workBound_nonincreasing {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    {stateDomain : Finset State} {rowDomain : Finset Row}
    {lhs rhs : FiniteStatefulGenAlg State Row Prim}
    (C : RewriteCertificate stateDomain rowDomain lhs rhs) :
    workBound stateDomain rowDomain rhs ≤
      workBound stateDomain rowDomain lhs :=
  C.nonincreasing

end FiniteStatefulGenAlg

/-!
  Summary:
  - Finite stateful read/generate/write queries now have a cost-aware rewrite
    certificate surface analogous to Proposition 50's stateless Kleisli one.
  - The laws are local but operational: remove empty branches, erase impossible
    branches, fuse guards, eliminate `bind empty`, and fuse duplicate generated
    branches that share a continuation.
  - This strengthens the complexity story from "there is a structural
    worst-case bound" to "there are Lean-checked denotation-preserving,
    cost-nonincreasing rewrites for the stateful algebra."
-/
