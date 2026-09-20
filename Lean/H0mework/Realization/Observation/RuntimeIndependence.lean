/-
  Proposition 16: constructive independence for a structured `(R,G,W,E)` state.

  Proposition 15 isolates the final runtime certificate: product shape,
  independence, and failure-mode completeness.  This file discharges the
  independence part for a structured semantic runtime slice, not for the fully
  free semantics where a state is merely `SemanticAtom -> Prop`.

  The state has four components:
    * R: source / authority / freshness;
    * G: graph confluence / Ω gluing;
    * W: gauge / contraction;
    * E: trace-source preservation.

  Each lower semantic atom is read from its owning component.  The theorem
  proves that every truth assignment over the seven `SemanticAtom`s is realized
  by some `(R,G,W,E)` state.

  Remaining runtime debt: connect the concrete Python reducer/source/Ω/router
  objects to this structured semantic slice.
-/

import H0mework.Realization.Observation.ProductSafety

/-- Real/source side of the semantic runtime slice. -/
structure RuntimeR where
  sourceReachable : Prop
  authorityMonotone : Prop
  freshnessValid : Prop

/-- Graph / ontology side of the semantic runtime slice. -/
structure RuntimeG where
  graphConfluent : Prop
  omegaGluable : Prop

/-- Salience / observation side of the semantic runtime slice. -/
structure RuntimeW where
  gaugeInvariant : Prop
  contractionCertified : Prop

/-- Event-log side of the semantic runtime slice. -/
structure RuntimeE where
  tracePreservesSourceTruth : Prop

/-- A structured semantic runtime state with the same `(R,G,W,E)` shape used in
    the prose model. -/
structure RuntimeSemanticState where
  R : RuntimeR
  G : RuntimeG
  W : RuntimeW
  E : RuntimeE

/-- Interpret the seven semantic atoms on the structured runtime slice. -/
def runtimeSemanticHolds : SemanticAtom → RuntimeSemanticState → Prop
  | SemanticAtom.sourceReachability, x =>
      x.R.sourceReachable ∧ x.E.tracePreservesSourceTruth
  | SemanticAtom.authorityMonotonicity, x =>
      x.R.authorityMonotone
  | SemanticAtom.graphConfluence, x =>
      x.G.graphConfluent
  | SemanticAtom.gaugeInvariance, x =>
      x.W.gaugeInvariant
  | SemanticAtom.contractionCertification, x =>
      x.W.contractionCertified
  | SemanticAtom.omegaGluing, x =>
      x.G.omegaGluable
  | SemanticAtom.freshnessValidity, x =>
      x.R.freshnessValid

/-- The `CSafePredicates` instance induced by the structured semantic slice. -/
def runtimeSemanticPredicates : CSafePredicates RuntimeSemanticState where
  sourceBacked := runtimeSemanticHolds SemanticAtom.sourceReachability
  authoritySafe := runtimeSemanticHolds SemanticAtom.authorityMonotonicity
  graphConfluent := runtimeSemanticHolds SemanticAtom.graphConfluence
  gaugeNonleaking := runtimeSemanticHolds SemanticAtom.gaugeInvariance
  contractionSafe := runtimeSemanticHolds SemanticAtom.contractionCertification
  omegaConsistent := runtimeSemanticHolds SemanticAtom.omegaGluing
  freshnessSafe := runtimeSemanticHolds SemanticAtom.freshnessValidity

/-- Convert a truth assignment into a structured `(R,G,W,E)` witness. -/
def runtimeSemanticStateFromAssignment
    (assignment : SemanticAtom → Prop) : RuntimeSemanticState :=
  { R :=
      { sourceReachable := assignment SemanticAtom.sourceReachability
        authorityMonotone := assignment SemanticAtom.authorityMonotonicity
        freshnessValid := assignment SemanticAtom.freshnessValidity }
    G :=
      { graphConfluent := assignment SemanticAtom.graphConfluence
        omegaGluable := assignment SemanticAtom.omegaGluing }
    W :=
      { gaugeInvariant := assignment SemanticAtom.gaugeInvariance
        contractionCertified := assignment SemanticAtom.contractionCertification }
    E :=
      { tracePreservesSourceTruth := True } }

/-- THEOREM 1: the structured `(R,G,W,E)` semantic slice realizes every
    assignment over the seven lower semantic atoms. -/
theorem runtimeSemanticState_independent :
    AtomIndependent (semanticObligationSemantics runtimeSemanticPredicates) := by
  classical
  refine ⟨?_⟩
  intro assignment
  refine ⟨runtimeSemanticStateFromAssignment assignment, ?_⟩
  intro a
  cases a with
  | sourceReachability =>
      simp [semanticObligationSemantics, semanticHolds, runtimeSemanticPredicates,
        runtimeSemanticHolds, runtimeSemanticStateFromAssignment]
  | authorityMonotonicity =>
      simp [semanticObligationSemantics, semanticHolds, runtimeSemanticPredicates,
        runtimeSemanticHolds, runtimeSemanticStateFromAssignment]
  | graphConfluence =>
      simp [semanticObligationSemantics, semanticHolds, runtimeSemanticPredicates,
        runtimeSemanticHolds, runtimeSemanticStateFromAssignment]
  | gaugeInvariance =>
      simp [semanticObligationSemantics, semanticHolds, runtimeSemanticPredicates,
        runtimeSemanticHolds, runtimeSemanticStateFromAssignment]
  | contractionCertification =>
      simp [semanticObligationSemantics, semanticHolds, runtimeSemanticPredicates,
        runtimeSemanticHolds, runtimeSemanticStateFromAssignment]
  | omegaGluing =>
      simp [semanticObligationSemantics, semanticHolds, runtimeSemanticPredicates,
        runtimeSemanticHolds, runtimeSemanticStateFromAssignment]
  | freshnessValidity =>
      simp [semanticObligationSemantics, semanticHolds, runtimeSemanticPredicates,
        runtimeSemanticHolds, runtimeSemanticStateFromAssignment]

/-- THEOREM 2: every lower semantic atom is primitive in the structured runtime
    slice. -/
theorem runtimeSemanticState_atoms_primitive :
    ∀ a, PrimitiveFailureAtom
      (semanticObligationSemantics runtimeSemanticPredicates) a := by
  exact primitiveAtom_of_independent
    (semanticObligationSemantics runtimeSemanticPredicates)
    runtimeSemanticState_independent

/-- THEOREM 3: Prop15's final-mile obstruction theorem applies to the
    structured runtime semantic slice with the reopen taxonomy basis. -/
theorem runtimeSemanticState_finalMile :
    (∀ x,
      (∃ r, taxonomyWitness runtimeSemanticPredicates x r) ↔
        ¬ CSafe runtimeSemanticPredicates x) ∧
      (∀ r, PrimitiveFailureMode
        (taxonomyFailureBasis runtimeSemanticPredicates) r) := by
  exact cSafe_finalMile_obstructions_are_canonical
    runtimeSemanticPredicates
    runtimeSemanticState_independent

/-!
  Summary:
  - This proves the exact `AtomIndependent` certificate needed by Proposition
    15 for a structured `(R,G,W,E)` semantic runtime slice.
  - It is intentionally stronger than the free assignment model, because the
    seven atoms are read through their owning stack components.
  - The concrete runtime still has to show that its reducer/source/graph/Ω
    objects faithfully project into this slice.
-/
