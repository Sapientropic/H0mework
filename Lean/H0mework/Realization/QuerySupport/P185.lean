import H0mework.Realization.QuerySupport.P180

/-!
# Proposition 185: semantic-image completeness for the atom/field query fragment

P180 packages the finite named AIppocampus query fragment as one certificate:
runtime plans, Kleisli field algebra, and range-restricted calculus mutually
preserve denotation, with finite workload cost envelopes attached.

This file exposes the Codd-style statement that is easier to cite:

* the predicates expressible by runtime generative plans are exactly the
  predicates expressible by the Kleisli atom/field algebra;
* the same semantic image is exactly the predicates expressible by the
  range-restricted calculus.

Boundary: this theorem is still certificate-relative and named-fragment
relative.  It does not claim unrestricted relational completeness, recursion,
external source-open materialization, or production runtime mechanism
faithfulness beyond the P180 certificate.
-/

namespace SaturationMonoid

namespace AtomFieldGenerativeQueryAlgebraCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base → Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator → Row → Row → Bool}

/-! ## Semantic images -/

/-- A row predicate is expressible by a named runtime generative plan. -/
def RuntimeExpressible
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (env : Base → Finset Row)
    (target : Row → Prop) : Prop :=
  ∃ p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
    ∀ row,
      target row ↔
        RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
          coverage.runtimeRel p row

/-- A row predicate is expressible by the Kleisli atom/field algebra. -/
def KleisliExpressible
    (env : Base → Finset Row)
    (target : Row → Prop) : Prop :=
  ∃ alg : KleisliFieldAlg Row Base,
    ∀ row,
      target row ↔
        KleisliFieldAlg.eval (finiteRuntimeEnvProp env) alg row

/-- A row predicate is expressible by the range-restricted calculus. -/
def CalculusExpressible
    (env : Base → Finset Row)
    (target : Row → Prop) : Prop :=
  ∃ formula : KleisliFieldCalc Row Base,
    ∀ row,
      target row ↔
        KleisliFieldCalc.eval (finiteRuntimeEnvProp env) formula row

/-! ## Codd-style semantic-image equality -/

/-- THEOREM 1: runtime plans and the Kleisli atom/field algebra have the same
semantic image under a P180 certificate. -/
theorem runtimeExpressible_iff_kleisliExpressible
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (target : Row → Prop) :
    RuntimeExpressible coverage env target ↔
      KleisliExpressible env target := by
  rcases C.runtime_kleisli_calculus_complete with
    ⟨runtime_to_kleisli, kleisli_to_runtime, _runtime_to_calc,
      _calc_to_runtime⟩
  constructor
  · rintro ⟨p, hp⟩
    rcases runtime_to_kleisli p with ⟨alg, halg⟩
    exact ⟨alg, fun row => (hp row).trans ((halg row).symm)⟩
  · rintro ⟨alg, halg⟩
    rcases kleisli_to_runtime alg with ⟨p, hp⟩
    exact ⟨p, fun row => (halg row).trans ((hp row).symm)⟩

/-- THEOREM 2: runtime plans and the range-restricted calculus have the same
semantic image under a P180 certificate. -/
theorem runtimeExpressible_iff_calculusExpressible
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (target : Row → Prop) :
    RuntimeExpressible coverage env target ↔
      CalculusExpressible env target := by
  rcases C.runtime_kleisli_calculus_complete with
    ⟨_runtime_to_kleisli, _kleisli_to_runtime, runtime_to_calc,
      calc_to_runtime⟩
  constructor
  · rintro ⟨p, hp⟩
    rcases runtime_to_calc p with ⟨formula, hformula⟩
    exact ⟨formula, fun row => (hp row).trans ((hformula row).symm)⟩
  · rintro ⟨formula, hformula⟩
    rcases calc_to_runtime formula with ⟨p, hp⟩
    exact ⟨p, fun row => (hformula row).trans ((hp row).symm)⟩

/-- THEOREM 3: the Kleisli atom/field algebra and the range-restricted
calculus have the same semantic image under a P180 certificate. -/
theorem kleisliExpressible_iff_calculusExpressible
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (target : Row → Prop) :
    KleisliExpressible env target ↔
      CalculusExpressible env target := by
  exact
    (runtimeExpressible_iff_kleisliExpressible C target).symm.trans
      (runtimeExpressible_iff_calculusExpressible C target)

/-- THEOREM 4: compact three-way semantic-image equality for the certified
atom/field query fragment. -/
theorem semanticImages_coincide
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (target : Row → Prop) :
    (RuntimeExpressible coverage env target ↔ KleisliExpressible env target) ∧
    (RuntimeExpressible coverage env target ↔ CalculusExpressible env target) ∧
    (KleisliExpressible env target ↔ CalculusExpressible env target) := by
  exact ⟨runtimeExpressible_iff_kleisliExpressible C target,
    runtimeExpressible_iff_calculusExpressible C target,
    kleisliExpressible_iff_calculusExpressible C target⟩

/-!
  Summary:
  - P185 turns P180's mutual translation tuple into semantic-image equality:
    the certified runtime, Kleisli atom/field algebra, and range-restricted
    calculus express exactly the same row predicates.
  - This is the clean citation surface for the first-layer query-completeness
    claim.

  Remaining boundary:
  - The theorem is still relative to the P180 finite named certificate.  It
    does not remove the need for runtime relation bridges, finite
    materialization, candidate-enumeration dominance, source-open cost models,
    recursion, aggregation, or full production mechanism-faithfulness.
-/


end AtomFieldGenerativeQueryAlgebraCertificate

end SaturationMonoid
