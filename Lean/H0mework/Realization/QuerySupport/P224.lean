import H0mework.Realization.QuerySupport.P185

/-!
# Proposition 224: semantic-image closure for the atom/field query algebra

P185 proves the Codd-style semantic-image equality:

  runtime generative plans ⇔ Kleisli atom/field algebra ⇔
  range-restricted calculus.

This file proves the complementary algebra fact: those semantic images are
closed under the operations that make them a query algebra.  In particular,
the runtime image is closed under empty/top, Boolean set operations, selection,
runtime generation, and Kleisli bind; the Kleisli image is closed under the
same Boolean/Kleisli operations and arbitrary field images; the calculus image
is closed under falsity/truth, Boolean connectives, and range-restricted
existential bind.

Boundary: this is still the same named, finite/certificate-relative fragment
as P185 when used through `AtomFieldGenerativeQueryAlgebraCertificate`.  It
does not add aggregation, recursion, source-open latency, or production
mechanism-faithfulness.
-/

namespace SaturationMonoid

namespace AtomFieldGenerativeQueryAlgebraCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {env : Base → Finset Row}

/-! ## Runtime semantic-image closure -/

/-- THEOREM 1: the runtime semantic image contains the empty predicate. -/
theorem runtimeExpressible_empty :
    RuntimeExpressible coverage env (fun _row : Row => False) := by
  refine ⟨RuntimeGenerativePlan.empty, ?_⟩
  intro row
  rfl

/-- THEOREM 2: the runtime semantic image contains the universal predicate. -/
theorem runtimeExpressible_top :
    RuntimeExpressible coverage env (fun _row : Row => True) := by
  refine ⟨RuntimeGenerativePlan.top, ?_⟩
  intro row
  rfl

/-- THEOREM 3: the runtime semantic image is closed under union. -/
theorem RuntimeExpressible.union
    {p q : Row → Prop}
    (hp : RuntimeExpressible coverage env p)
    (hq : RuntimeExpressible coverage env q) :
    RuntimeExpressible coverage env (fun row => p row ∨ q row) := by
  rcases hp with ⟨rp, hp⟩
  rcases hq with ⟨rq, hq⟩
  refine ⟨RuntimeGenerativePlan.union rp rq, ?_⟩
  intro row
  simp [RuntimeGenerativePlan.eval, hp row, hq row]

/-- THEOREM 4: the runtime semantic image is closed under intersection. -/
theorem RuntimeExpressible.inter
    {p q : Row → Prop}
    (hp : RuntimeExpressible coverage env p)
    (hq : RuntimeExpressible coverage env q) :
    RuntimeExpressible coverage env (fun row => p row ∧ q row) := by
  rcases hp with ⟨rp, hp⟩
  rcases hq with ⟨rq, hq⟩
  refine ⟨RuntimeGenerativePlan.inter rp rq, ?_⟩
  intro row
  simp [RuntimeGenerativePlan.eval, hp row, hq row]

/-- THEOREM 5: the runtime semantic image is closed under set difference. -/
theorem RuntimeExpressible.diff
    {p q : Row → Prop}
    (hp : RuntimeExpressible coverage env p)
    (hq : RuntimeExpressible coverage env q) :
    RuntimeExpressible coverage env (fun row => p row ∧ ¬ q row) := by
  rcases hp with ⟨rp, hp⟩
  rcases hq with ⟨rq, hq⟩
  refine ⟨RuntimeGenerativePlan.diff rp rq, ?_⟩
  intro row
  simp [RuntimeGenerativePlan.eval, hp row, hq row]

/-- THEOREM 6: the runtime semantic image is closed under selection. -/
theorem RuntimeExpressible.select
    (predicate : Row → Prop)
    {p : Row → Prop}
    (hp : RuntimeExpressible coverage env p) :
    RuntimeExpressible coverage env (fun row => predicate row ∧ p row) := by
  rcases hp with ⟨rp, hp⟩
  refine ⟨RuntimeGenerativePlan.select predicate rp, ?_⟩
  intro row
  simp [RuntimeGenerativePlan.eval, hp row]

/-- THEOREM 7: the runtime semantic image is closed under one runtime
generator step. -/
theorem RuntimeExpressible.generate
    (generator : AippocampusRuntimeGenerator)
    {p : Row → Prop}
    (hp : RuntimeExpressible coverage env p) :
    RuntimeExpressible coverage env
      (fun row => ∃ source, p source ∧ coverage.runtimeRel generator source row) := by
  rcases hp with ⟨rp, hp⟩
  refine ⟨RuntimeGenerativePlan.generate generator rp, ?_⟩
  intro row
  constructor
  · rintro ⟨source, hsource, hrel⟩
    exact ⟨source, (hp source).mp hsource, hrel⟩
  · rintro ⟨source, hsource, hrel⟩
    exact ⟨source, (hp source).mpr hsource, hrel⟩

/-- THEOREM 8: the runtime semantic image is closed under Kleisli bind. -/
theorem RuntimeExpressible.bind
    {p : Row → Prop} {k : Row → Row → Prop}
    (hp : RuntimeExpressible coverage env p)
    (hk : ∀ source, RuntimeExpressible coverage env (k source)) :
    RuntimeExpressible coverage env
      (fun row => ∃ source, p source ∧ k source row) := by
  classical
  rcases hp with ⟨rp, hp⟩
  let rk : Row → RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator :=
    fun source => Classical.choose (hk source)
  have hrk :
      ∀ source row,
        k source row ↔
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
            coverage.runtimeRel (rk source) row := by
    intro source row
    exact Classical.choose_spec (hk source) row
  refine ⟨RuntimeGenerativePlan.bind rp rk, ?_⟩
  intro row
  constructor
  · rintro ⟨source, hsource, hkrow⟩
    exact ⟨source, (hp source).mp hsource, (hrk source row).mp hkrow⟩
  · rintro ⟨source, hsource, hkrow⟩
    exact ⟨source, (hp source).mpr hsource, (hrk source row).mpr hkrow⟩

/-! ## Kleisli semantic-image closure -/

/-- THEOREM 9: the Kleisli semantic image contains the empty predicate. -/
theorem kleisliExpressible_empty :
    KleisliExpressible (env := env) (fun _row : Row => False) := by
  refine ⟨KleisliFieldAlg.empty, ?_⟩
  intro row
  rfl

/-- THEOREM 10: the Kleisli semantic image contains the universal predicate. -/
theorem kleisliExpressible_top :
    KleisliExpressible (env := env) (fun _row : Row => True) := by
  refine ⟨KleisliFieldAlg.top, ?_⟩
  intro row
  rfl

/-- THEOREM 11: the Kleisli semantic image is closed under union. -/
theorem KleisliExpressible.union
    {p q : Row → Prop}
    (hp : KleisliExpressible (env := env) p)
    (hq : KleisliExpressible (env := env) q) :
    KleisliExpressible (env := env) (fun row => p row ∨ q row) := by
  rcases hp with ⟨ap, hp⟩
  rcases hq with ⟨aq, hq⟩
  refine ⟨KleisliFieldAlg.union ap aq, ?_⟩
  intro row
  simp [KleisliFieldAlg.eval, hp row, hq row]

/-- THEOREM 12: the Kleisli semantic image is closed under intersection. -/
theorem KleisliExpressible.inter
    {p q : Row → Prop}
    (hp : KleisliExpressible (env := env) p)
    (hq : KleisliExpressible (env := env) q) :
    KleisliExpressible (env := env) (fun row => p row ∧ q row) := by
  rcases hp with ⟨ap, hp⟩
  rcases hq with ⟨aq, hq⟩
  refine ⟨KleisliFieldAlg.inter ap aq, ?_⟩
  intro row
  simp [KleisliFieldAlg.eval, hp row, hq row]

/-- THEOREM 13: the Kleisli semantic image is closed under set difference. -/
theorem KleisliExpressible.diff
    {p q : Row → Prop}
    (hp : KleisliExpressible (env := env) p)
    (hq : KleisliExpressible (env := env) q) :
    KleisliExpressible (env := env) (fun row => p row ∧ ¬ q row) := by
  rcases hp with ⟨ap, hp⟩
  rcases hq with ⟨aq, hq⟩
  refine ⟨KleisliFieldAlg.diff ap aq, ?_⟩
  intro row
  simp [KleisliFieldAlg.eval, hp row, hq row]

/-- THEOREM 14: the Kleisli semantic image is closed under selection. -/
theorem KleisliExpressible.select
    (predicate : Row → Prop)
    {p : Row → Prop}
    (hp : KleisliExpressible (env := env) p) :
    KleisliExpressible (env := env) (fun row => predicate row ∧ p row) := by
  rcases hp with ⟨ap, hp⟩
  refine ⟨KleisliFieldAlg.select predicate ap, ?_⟩
  intro row
  simp [KleisliFieldAlg.eval, hp row]

/-- THEOREM 15: the Kleisli semantic image is closed under arbitrary field
image. -/
theorem KleisliExpressible.image
    (relation : Row → Row → Prop)
    {p : Row → Prop}
    (hp : KleisliExpressible (env := env) p) :
    KleisliExpressible (env := env)
      (fun row => ∃ source, p source ∧ relation source row) := by
  rcases hp with ⟨ap, hp⟩
  refine ⟨KleisliFieldAlg.image relation ap, ?_⟩
  intro row
  calc
    (∃ source, p source ∧ relation source row) ↔
        ∃ source,
          KleisliFieldAlg.eval (finiteRuntimeEnvProp env) ap source ∧
            relation source row := by
      constructor
      · rintro ⟨source, hsource, hrel⟩
        exact ⟨source, (hp source).mp hsource, hrel⟩
      · rintro ⟨source, hsource, hrel⟩
        exact ⟨source, (hp source).mpr hsource, hrel⟩
    _ ↔ KleisliFieldAlg.eval (finiteRuntimeEnvProp env)
          (KleisliFieldAlg.image relation ap) row :=
      (KleisliFieldAlg.image_eval (finiteRuntimeEnvProp env)
        relation ap row).symm

/-- THEOREM 16: the Kleisli semantic image is closed under bind. -/
theorem KleisliExpressible.bind
    {p : Row → Prop} {k : Row → Row → Prop}
    (hp : KleisliExpressible (env := env) p)
    (hk : ∀ source, KleisliExpressible (env := env) (k source)) :
    KleisliExpressible (env := env)
      (fun row => ∃ source, p source ∧ k source row) := by
  classical
  rcases hp with ⟨ap, hp⟩
  let ak : Row → KleisliFieldAlg Row Base :=
    fun source => Classical.choose (hk source)
  have hak :
      ∀ source row,
        k source row ↔ KleisliFieldAlg.eval (finiteRuntimeEnvProp env)
          (ak source) row := by
    intro source row
    exact Classical.choose_spec (hk source) row
  refine ⟨KleisliFieldAlg.bind ap ak, ?_⟩
  intro row
  constructor
  · rintro ⟨source, hsource, hkrow⟩
    exact ⟨source, (hp source).mp hsource, (hak source row).mp hkrow⟩
  · rintro ⟨source, hsource, hkrow⟩
    exact ⟨source, (hp source).mpr hsource, (hak source row).mpr hkrow⟩

/-! ## Calculus semantic-image closure -/

/-- THEOREM 17: the calculus semantic image contains falsity. -/
theorem calculusExpressible_empty :
    CalculusExpressible (env := env) (fun _row : Row => False) := by
  refine ⟨KleisliFieldCalc.falsity, ?_⟩
  intro row
  rfl

/-- THEOREM 18: the calculus semantic image contains truth. -/
theorem calculusExpressible_top :
    CalculusExpressible (env := env) (fun _row : Row => True) := by
  refine ⟨KleisliFieldCalc.truth, ?_⟩
  intro row
  rfl

/-- THEOREM 19: the calculus semantic image is closed under union. -/
theorem CalculusExpressible.union
    {p q : Row → Prop}
    (hp : CalculusExpressible (env := env) p)
    (hq : CalculusExpressible (env := env) q) :
    CalculusExpressible (env := env) (fun row => p row ∨ q row) := by
  rcases hp with ⟨fp, hp⟩
  rcases hq with ⟨fq, hq⟩
  refine ⟨KleisliFieldCalc.or fp fq, ?_⟩
  intro row
  simp [KleisliFieldCalc.eval, hp row, hq row]

/-- THEOREM 20: the calculus semantic image is closed under intersection. -/
theorem CalculusExpressible.inter
    {p q : Row → Prop}
    (hp : CalculusExpressible (env := env) p)
    (hq : CalculusExpressible (env := env) q) :
    CalculusExpressible (env := env) (fun row => p row ∧ q row) := by
  rcases hp with ⟨fp, hp⟩
  rcases hq with ⟨fq, hq⟩
  refine ⟨KleisliFieldCalc.and fp fq, ?_⟩
  intro row
  simp [KleisliFieldCalc.eval, hp row, hq row]

/-- THEOREM 21: the calculus semantic image is closed under complement. -/
theorem CalculusExpressible.compl
    {p : Row → Prop}
    (hp : CalculusExpressible (env := env) p) :
    CalculusExpressible (env := env) (fun row => ¬ p row) := by
  rcases hp with ⟨fp, hp⟩
  refine ⟨KleisliFieldCalc.not fp, ?_⟩
  intro row
  simp [KleisliFieldCalc.eval, hp row]

/-- THEOREM 22: the calculus semantic image is closed under set difference. -/
theorem CalculusExpressible.diff
    {p q : Row → Prop}
    (hp : CalculusExpressible (env := env) p)
    (hq : CalculusExpressible (env := env) q) :
    CalculusExpressible (env := env) (fun row => p row ∧ ¬ q row) := by
  exact hp.inter hq.compl

/-- THEOREM 23: the calculus semantic image is closed under predicates. -/
theorem calculusExpressible_pred
    (predicate : Row → Prop) :
    CalculusExpressible (env := env) predicate := by
  refine ⟨KleisliFieldCalc.pred predicate, ?_⟩
  intro row
  rfl

/-- THEOREM 24: the calculus semantic image is closed under selection. -/
theorem CalculusExpressible.select
    (predicate : Row → Prop)
    {p : Row → Prop}
    (hp : CalculusExpressible (env := env) p) :
    CalculusExpressible (env := env) (fun row => predicate row ∧ p row) :=
  (calculusExpressible_pred (env := env) predicate).inter hp

/-- THEOREM 25: the calculus semantic image is closed under
range-restricted existential bind. -/
theorem CalculusExpressible.bindExists
    {p : Row → Prop} {k : Row → Row → Prop}
    (hp : CalculusExpressible (env := env) p)
    (hk : ∀ source, CalculusExpressible (env := env) (k source)) :
    CalculusExpressible (env := env)
      (fun row => ∃ source, p source ∧ k source row) := by
  classical
  rcases hp with ⟨fp, hp⟩
  let fk : Row → KleisliFieldCalc Row Base :=
    fun source => Classical.choose (hk source)
  have hfk :
      ∀ source row,
        k source row ↔ KleisliFieldCalc.eval (finiteRuntimeEnvProp env)
          (fk source) row := by
    intro source row
    exact Classical.choose_spec (hk source) row
  refine ⟨KleisliFieldCalc.bindExists fp fk, ?_⟩
  intro row
  constructor
  · rintro ⟨source, hsource, hkrow⟩
    exact ⟨source, (hp source).mp hsource, (hfk source row).mp hkrow⟩
  · rintro ⟨source, hsource, hkrow⟩
    exact ⟨source, (hp source).mpr hsource, (hfk source row).mpr hkrow⟩

/-! ## Certificate-relative common closure facts -/

/-- THEOREM 26: under a P180 certificate, runtime/Kleisli/calculus semantic
images are all closed under the same Boolean union operation. -/
theorem semanticImages_union_closed
    {domain : Finset Row}
    {runtimeRel : AippocampusRuntimeGenerator → Row → Row → Bool}
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    {p q : Row → Prop} :
    ((RuntimeExpressible coverage env p ∧ RuntimeExpressible coverage env q) →
      RuntimeExpressible coverage env (fun row => p row ∨ q row)) ∧
    ((KleisliExpressible (env := env) p ∧ KleisliExpressible (env := env) q) →
      KleisliExpressible (env := env) (fun row => p row ∨ q row)) ∧
    ((CalculusExpressible (env := env) p ∧ CalculusExpressible (env := env) q) →
      CalculusExpressible (env := env) (fun row => p row ∨ q row)) ∧
    ((RuntimeExpressible coverage env p ∧
        CalculusExpressible (env := env) q) →
      RuntimeExpressible coverage env (fun row => p row ∨ q row)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact h.1.union h.2
  · intro h
    exact h.1.union h.2
  · intro h
    exact h.1.union h.2
  · intro h
    have hqRuntime : RuntimeExpressible coverage env q :=
      ((runtimeExpressible_iff_calculusExpressible C q).mpr h.2)
    exact h.1.union hqRuntime

/-!
  Summary:
  - P224 makes the "query algebra" word literal at the semantic-image level.
  - P185 gave equality of images; P224 proves each image is closed under the
    constructors that matter for finite atom/field querying.
  - The mixed union theorem illustrates how P185 transports closure across
    runtime/Kleisli/calculus syntax once a P180 certificate is supplied.

  Remaining boundary:
  - Closure is still for the current finite/named atom-field syntax.
  - Aggregation, recursion, probabilistic ranking objectives, source-open
    latency, and production mechanism-faithfulness remain separate obligations.
-/


end AtomFieldGenerativeQueryAlgebraCertificate

end SaturationMonoid
