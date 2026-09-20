/-
  Proposition 101: runtime semantic pullback yields the packed foundation
  certificate.

  Proposition 94 gives the strong runtime-facing mechanism certificate:
  a production state space projects faithfully and surjectively into the
  concrete `2^7` semantic Boolean slice, and memory production is the pullback
  of primitive semantic failure support.

  Proposition 100 packages the downstream foundation theorem, but it expects a
  finite raw support-discovery table.  This file closes that connector: the
  P94 pullback certificate induces the diagonal finite table from Proposition
  93, and therefore directly emits the P100 foundation certificate.

  This is still not a proof that a particular production runtime has supplied
  the P94 certificate.  It proves that once it does, no additional ontology or
  hand-written obstruction/memory equivalence is needed.
-/

import H0mework.Realization.Relations.P94
import H0mework.Realization.QuerySupport.P100

namespace SemanticBoolMemoryPullback

universe u

variable {State : Type u}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State SemanticAtom}

/-! ## P94 pullback as the P100 finite discovery table -/

/-- THEOREM 1: a faithful semantic-memory pullback induces the diagonal finite
support-discovery table over the seven primitive semantic atoms.

The rows are the concrete `semanticBoolSupportRows` from Proposition 93.  The
row proof is not fixture-specific: it follows from the runtime projection and
memory-pullback fields of the P94 certificate. -/
noncomputable def toRawAtomicSupportDiscoveryTable
    (C : SemanticBoolMemoryPullback P M) :
    RawAtomicSupportDiscoveryTable P M where
  rows := semanticBoolSupportRows
  row_support_iff := by
    intro m a hrow x
    have hma : m = a := semanticBoolSupportRows_mem_eq hrow
    subst a
    calc
      M.produces x m <->
          semanticBoolMemoryContract.produces (C.projection.project x) m :=
        C.memory_pullback x m
      _ <-> semanticBoolValue (C.projection.project x) m = false :=
        Iff.rfl
      _ <->
          AtomFailure (semanticObligationSemantics semanticBoolPredicates)
            (C.projection.project x) m :=
        (semanticBoolFailure_iff_value_false (C.projection.project x) m).symm
      _ <->
          AtomFailure (semanticObligationSemantics P) x m :=
        (C.projection.atomFailure_iff_project x m).symm
      _ <->
          BoolQuery.eval (semanticObligationSemantics P)
            (singletonFailureQuery m) x :=
        (singletonFailureQuery_eval_iff P m x).symm
  memory_total := by
    intro m
    exact semanticBoolMemoryRows_cover m
  semantic_total := by
    intro a
    exact semanticBoolSemanticRows_cover a

/-! ## Packed foundation certificate -/

/-- THEOREM 2: a P94 semantic-memory pullback directly constructs the packed
P100 foundation certificate.

The semantic atom independence used by P100 is not another assumption here: it
is transported from the surjective semantic Boolean projection in P94. -/
noncomputable def toFiniteDiscoveryFoundationCertificate
    (C : SemanticBoolMemoryPullback P M) :
    FiniteDiscoveryFoundationCertificate.{u, 0, 0, 0, 0} P M :=
  foundationCertificate_of_finiteDiscoveryTable P M
    C.toRawAtomicSupportDiscoveryTable
    C.projection.atomIndependent

/-- THEOREM 3: under a P94 pullback certificate, raw memory production is
exactly global unsafety. -/
theorem finiteFoundation_raw_nonempty_iff_not_csafe
    (C : SemanticBoolMemoryPullback P M) (x : State) :
    (exists a, M.produces x a) <-> (CSafe P x -> False) := by
  let F : FiniteDiscoveryFoundationCertificate.{u, 0, 0, 0, 0} P M :=
    C.toFiniteDiscoveryFoundationCertificate
  exact F.raw_nonempty_iff_not_csafe x

/-- THEOREM 4: under a P94 pullback certificate, quotient memory production is
exactly global unsafety. -/
theorem finiteFoundation_quotient_nonempty_iff_not_csafe
    (C : SemanticBoolMemoryPullback P M) (x : State) :
    (exists q, (memorySupportQuotientContract M).produces x q) <->
      (CSafe P x -> False) := by
  let F : FiniteDiscoveryFoundationCertificate.{u, 0, 0, 0, 0} P M :=
    C.toFiniteDiscoveryFoundationCertificate
  exact F.quotient_nonempty_iff_not_csafe x

/-- THEOREM 5: the quotient memory support emitted by the generated foundation
certificate is exactly primitive semantic obstruction support. -/
theorem finiteFoundation_produces_iff_obstruction
    (C : SemanticBoolMemoryPullback P M)
    (x : State) (q : MemorySupportQuotient M) :
    (memorySupportQuotientContract M).produces x q <->
      AtomFailure (semanticObligationSemantics P) x
        (C.toFiniteDiscoveryFoundationCertificate.equivalence.atomEquiv q) := by
  let F : FiniteDiscoveryFoundationCertificate.{u, 0, 0, 0, 0} P M :=
    C.toFiniteDiscoveryFoundationCertificate
  exact F.produces_iff_obstruction x q

/-- THEOREM 6: the generated quotient memory layer is silent exactly on
`C_safe`. -/
theorem finiteFoundation_quotient_silent_iff_csafe
    (C : SemanticBoolMemoryPullback P M) (x : State) :
    (memorySupportQuotientContract M).memorySilent x <-> CSafe P x := by
  let F : FiniteDiscoveryFoundationCertificate.{u, 0, 0, 0, 0} P M :=
    C.toFiniteDiscoveryFoundationCertificate
  exact F.quotient_silent_iff_csafe x

end SemanticBoolMemoryPullback

/-!
  Summary:
  - P94's runtime semantic projection/memory-pullback certificate now feeds
    directly into the P100 packed foundation bridge.
  - The finite table is the diagonal semantic-atom table from P93; the row
    support proof is derived from the P94 pullback, not assumed as a fixture.
  - The remaining mechanism-faithfulness obligation is concrete and external:
    the production runtime must still emit/prove the P94 projection,
    surjectivity, and memory-pullback fields.
-/
