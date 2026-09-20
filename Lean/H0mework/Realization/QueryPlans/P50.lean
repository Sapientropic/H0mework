/-
  Proposition 50: cost-aware rewrite certificates for finite generative
  queries.

  Proposition 49 packages finite runtime plans with denotation and total-cost
  certificates.  Codd-style database theory also needs an optimization layer:
  algebraic rewrites that preserve denotation and do not worsen the structural
  cost model.

  This file adds the first finite/materialized optimization slice.  A rewrite
  certificate is oriented from `lhs` to `rhs` and proves:

    * the finite result set is unchanged for every environment;
    * `workBound rhs <= workBound lhs`.

  The laws below are intentionally small but operationally meaningful: remove
  empty/no-op branches, collapse redundant selections, erase impossible
  branches, and fuse a union of two generated branches into one generated
  branch over a union seed.
-/

import H0mework.Realization.QueryPlans.P49

/-! ## Rewrite certificates -/

namespace FiniteKleisliFieldAlg

/-- Two finite Kleisli queries are denotationally equivalent in a fixed finite
environment when their finite result sets are equal. -/
def FiniteEquivalent {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (lhs rhs : FiniteKleisliFieldAlg Row Base) : Prop :=
  evalFinset domain env lhs = evalFinset domain env rhs

/-- An oriented rewrite certificate: `lhs` may be replaced by `rhs` without
changing results and without increasing the structural worst-case work bound. -/
structure RewriteCertificate {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (lhs rhs : FiniteKleisliFieldAlg Row Base) where
  result_eq :
    forall env : Base -> Finset Row,
      (forall b, env b ⊆ domain) ->
      FiniteEquivalent domain env lhs rhs
  workBound_le :
    workBound domain rhs <= workBound domain lhs

namespace RewriteCertificate

variable {Row Base : Type*} [DecidableEq Row]
variable {domain : Finset Row}

/-- THEOREM 1: applying a rewrite certificate preserves finite denotation. -/
theorem preserves_eval
    {lhs rhs : FiniteKleisliFieldAlg Row Base}
    (C : RewriteCertificate domain lhs rhs)
    (env : Base -> Finset Row)
    (hEnv : forall b, env b ⊆ domain) :
    evalFinset domain env lhs = evalFinset domain env rhs :=
  C.result_eq env hEnv

/-- THEOREM 2: applying a rewrite certificate is structurally cost
non-increasing. -/
theorem nonincreasing
    {lhs rhs : FiniteKleisliFieldAlg Row Base}
    (C : RewriteCertificate domain lhs rhs) :
    workBound domain rhs <= workBound domain lhs :=
  C.workBound_le

end RewriteCertificate

/-! ## Local cost-aware rewrites -/

/-- Remove an empty branch on the left of a union. -/
theorem rewrite_union_empty_left {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (union empty q) q where
  result_eq := by
    intro env _hEnv
    simp [FiniteEquivalent, evalFinset]
  workBound_le := by
    simp [workBound]
    omega

/-- Remove an empty branch on the right of a union. -/
theorem rewrite_union_empty_right {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (union q empty) q where
  result_eq := by
    intro env _hEnv
    simp [FiniteEquivalent, evalFinset]
  workBound_le := by
    simp [workBound]
    omega

/-- Remove a top branch on the left of an intersection. -/
theorem rewrite_inter_top_left {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (inter top q) q where
  result_eq := by
    intro env hEnv
    ext row
    simp [evalFinset]
    exact fun hx => evalFinset_subset_domain domain env hEnv q hx
  workBound_le := by
    simp [workBound]
    omega

/-- Remove a top branch on the right of an intersection. -/
theorem rewrite_inter_top_right {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (inter q top) q where
  result_eq := by
    intro env hEnv
    ext row
    simp [evalFinset]
    exact fun hx => evalFinset_subset_domain domain env hEnv q hx
  workBound_le := by
    simp [workBound]
    omega

/-- Remove subtracting the empty query. -/
theorem rewrite_diff_empty_right {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (diff q empty) q where
  result_eq := by
    intro env _hEnv
    simp [FiniteEquivalent, evalFinset]
  workBound_le := by
    simp [workBound]
    omega

/-- Replace `q \ q` by the empty query. -/
theorem rewrite_diff_self {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (diff q q) empty where
  result_eq := by
    intro env _hEnv
    simp [FiniteEquivalent, evalFinset]
  workBound_le := by
    simp [workBound]

/-- Remove a selection whose predicate is always true. -/
theorem rewrite_select_true {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (select (fun _row => true) q) q where
  result_eq := by
    intro env _hEnv
    simp [FiniteEquivalent, evalFinset]
  workBound_le := by
    simp [workBound]

/-- Replace a selection whose predicate is always false by the empty query. -/
theorem rewrite_select_false {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (select (fun _row => false) q) empty where
  result_eq := by
    intro env _hEnv
    simp [FiniteEquivalent, evalFinset]
  workBound_le := by
    simp [workBound]

/-- Fuse two consecutive selections into one Boolean conjunction. -/
theorem rewrite_select_select {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (outer inner : Row -> Bool)
    (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain
      (select outer (select inner q))
      (select (fun row => outer row && inner row) q) where
  result_eq := by
    intro env _hEnv
    ext row
    by_cases hOuter : outer row = true <;>
      by_cases hInner : inner row = true <;>
      simp [evalFinset, hOuter, hInner]
  workBound_le := by
    simp [workBound]

/-- Replace `bind empty k` by `empty`. -/
theorem rewrite_bind_empty {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (k : Row -> FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain (bind empty k) empty where
  result_eq := by
    intro env _hEnv
    simp [FiniteEquivalent, evalFinset]
  workBound_le := by
    simp [workBound]

/-- Fuse two generated branches with the same continuation:

`union (bind p k) (bind q k)` can be evaluated as `bind (union p q) k`.

This is a generative-query optimization law: it preserves denotation and
removes one full continuation fanout plus one union merge from the structural
bound. -/
theorem rewrite_union_bind_fuse {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row)
    (p q : FiniteKleisliFieldAlg Row Base)
    (k : Row -> FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain
      (union (bind p k) (bind q k))
      (bind (union p q) k) where
  result_eq := by
    intro env _hEnv
    ext row
    simp [evalFinset]
    constructor
    · intro h
      rcases h with h | h
      · rcases h with ⟨source, hsource, hrow⟩
        exact ⟨source, Or.inl hsource, hrow⟩
      · rcases h with ⟨source, hsource, hrow⟩
        exact ⟨source, Or.inr hsource, hrow⟩
    · intro h
      rcases h with ⟨source, hsource, hrow⟩
      rcases hsource with hsource | hsource
      · exact Or.inl ⟨source, hsource, hrow⟩
      · exact Or.inr ⟨source, hsource, hrow⟩
  workBound_le := by
    simp [workBound]
    omega

/-! ## Reusable projections -/

/-- THEOREM 3: any query optimized with one of the certified rewrites has the
same finite result set. -/
theorem rewrite_preserves_eval {Row Base : Type*} [DecidableEq Row]
    {domain : Finset Row} {lhs rhs : FiniteKleisliFieldAlg Row Base}
    (C : RewriteCertificate domain lhs rhs)
    (env : Base -> Finset Row)
    (hEnv : forall b, env b ⊆ domain) :
    evalFinset domain env lhs = evalFinset domain env rhs :=
  C.preserves_eval env hEnv

/-- THEOREM 4: any query optimized with one of the certified rewrites is
structurally no more expensive under `workBound`. -/
theorem rewrite_workBound_nonincreasing {Row Base : Type*} [DecidableEq Row]
    {domain : Finset Row} {lhs rhs : FiniteKleisliFieldAlg Row Base}
    (C : RewriteCertificate domain lhs rhs) :
    workBound domain rhs <= workBound domain lhs :=
  C.nonincreasing

end FiniteKleisliFieldAlg

/-!
  Summary:
  - `RewriteCertificate` is the finite generative-query analog of a
    cost-aware algebraic optimization rule.
  - The certified laws eliminate empty/no-op branches, collapse redundant
    filters, and fuse a union of generated branches into a single generated
    branch.
  - This is not a full optimizer or a complete rewrite system.  It is the first
    Lean-checked optimization algebra slice sitting on top of the P49
    finite/materialized query certificate.
-/
