import H0mework.Realization.QuerySupport.P105
import H0mework.Realization.Relations.P177

/-!
# Proposition 178: primitive equivalence forces projection uniqueness

P177 turns the three primitive slogan families into a seven-facet projection
once the P94 mechanism fields are supplied.  This file proves the uniqueness
side needed by Strategy D: if two primitive axiom classes agree extensionally
on the seven induced primitive facets, then their semantic Boolean projections
are equal at every runtime state.

Boundary: this proves uniqueness relative to the declared primitive facet
semantics.  It does not prove that production code already satisfies those
primitive equivalences; that remains the mechanism-faithfulness/runtime
certificate layer.
-/

namespace SaturationMonoid

namespace AippocampusPrimitiveAxiomClass

variable {State : Type*}

/-! ## Extensional equivalence of primitive axiom classes -/

/-- Two primitive axiom classes are equivalent when all seven primitive facet
predicates agree extensionally on runtime states. -/
def Equivalent
    (A B : AippocampusPrimitiveAxiomClass State) : Prop :=
  (∀ x, A.sourceBacked.sourceReachability x ↔
    B.sourceBacked.sourceReachability x) ∧
  (∀ x, A.navigationOnly.authorityMonotonicity x ↔
    B.navigationOnly.authorityMonotonicity x) ∧
  (∀ x, A.reflexive.graphConfluence x ↔
    B.reflexive.graphConfluence x) ∧
  (∀ x, A.reflexive.gaugeInvariance x ↔
    B.reflexive.gaugeInvariance x) ∧
  (∀ x, A.reflexive.contractionCertification x ↔
    B.reflexive.contractionCertification x) ∧
  (∀ x, A.sourceBacked.omegaGluing x ↔
    B.sourceBacked.omegaGluing x) ∧
  (∀ x, A.sourceBacked.freshnessValidity x ↔
    B.sourceBacked.freshnessValidity x)

/-- THEOREM 1: primitive equivalence is exactly equivalence of the induced
seven-facet obligation semantics. -/
theorem semantic_holds_iff_of_equivalent
    {A B : AippocampusPrimitiveAxiomClass State}
    (h : Equivalent A B)
    (x : State) (a : SemanticAtom) :
    (semanticObligationSemantics A.sevenFacetPredicates).holds a x ↔
      (semanticObligationSemantics B.sevenFacetPredicates).holds a x := by
  rcases h with
    ⟨hsource, hauthority, hgraph, hgauge, hcontraction, homega, hfresh⟩
  cases a <;>
    simp [sevenFacetPredicates, semanticObligationSemantics, semanticHolds]
  · exact hsource x
  · exact hauthority x
  · exact hgraph x
  · exact hgauge x
  · exact hcontraction x
  · exact homega x
  · exact hfresh x

/-- A primitive axiom class reads the same Boolean value as its induced
obligation semantics. -/
theorem semanticBoolValue_true_iff_primitive
    (A : AippocampusPrimitiveAxiomClass State)
    (x : State) (a : SemanticAtom) :
    semanticBoolValue (A.sevenFacetProjection x) a = true ↔
      (semanticObligationSemantics A.sevenFacetPredicates).holds a x := by
  calc
    semanticBoolValue (A.sevenFacetProjection x) a = true ↔
        (semanticObligationSemantics semanticBoolPredicates).holds a
          (A.sevenFacetProjection x) :=
      (semanticBoolHolds_iff_value (A.sevenFacetProjection x) a).symm
    _ ↔ (semanticObligationSemantics A.sevenFacetPredicates).holds a x :=
      (A.sevenFacetProjection_atom_iff x a).symm

/-- THEOREM 2: equivalent primitive classes have equal seven-facet
projections at every runtime state. -/
theorem projection_eq_of_equivalent
    {A B : AippocampusPrimitiveAxiomClass State}
    (h : Equivalent A B)
    (x : State) :
    A.sevenFacetProjection x = B.sevenFacetProjection x := by
  apply StructureDeterminedSevenFacetSystem.semanticBoolState_eq_of_values
  intro a
  apply StructureDeterminedSevenFacetSystem.bool_eq_of_true_iff
  calc
    semanticBoolValue (A.sevenFacetProjection x) a = true ↔
        (semanticObligationSemantics A.sevenFacetPredicates).holds a x :=
      A.semanticBoolValue_true_iff_primitive x a
    _ ↔ (semanticObligationSemantics B.sevenFacetPredicates).holds a x :=
      semantic_holds_iff_of_equivalent h x a
    _ ↔ semanticBoolValue (B.sevenFacetProjection x) a = true :=
      (B.semanticBoolValue_true_iff_primitive x a).symm

/-- THEOREM 3: primitive equivalence also forces equality of the P94
projection certificates extensionally on states. -/
theorem projectionCertificate_project_eq_of_equivalent
    {A B : AippocampusPrimitiveAxiomClass State}
    (h : Equivalent A B)
    (x : State) :
    A.toSemanticBoolProjectionCertificate.project x =
      B.toSemanticBoolProjectionCertificate.project x :=
  projection_eq_of_equivalent h x

/-- THEOREM 4: induced primitive memory production is unique under primitive
equivalence. -/
theorem memoryContract_produces_iff_of_equivalent
    {A B : AippocampusPrimitiveAxiomClass State}
    (h : Equivalent A B)
    (x : State) (a : SemanticAtom) :
    A.memoryContract.produces x a ↔ B.memoryContract.produces x a := by
  have hp : A.sevenFacetProjection x = B.sevenFacetProjection x :=
    projection_eq_of_equivalent h x
  change semanticBoolMemoryContract.produces (A.sevenFacetProjection x) a ↔
    semanticBoolMemoryContract.produces (B.sevenFacetProjection x) a
  rw [hp]

/-- THEOREM 5: the induced global `C_safe` predicates are extensionally
equivalent under primitive equivalence. -/
theorem cSafe_iff_of_equivalent
    {A B : AippocampusPrimitiveAxiomClass State}
    (h : Equivalent A B)
    (x : State) :
    CSafe A.sevenFacetPredicates x ↔ CSafe B.sevenFacetPredicates x := by
  rcases h with
    ⟨hsource, hauthority, hgraph, hgauge, hcontraction, homega, hfresh⟩
  unfold CSafe
  simp [sevenFacetPredicates]
  constructor
  · intro hx
    exact ⟨
      (hsource x).mp hx.1,
      (hauthority x).mp hx.2.1,
      (hgraph x).mp hx.2.2.1,
      (hgauge x).mp hx.2.2.2.1,
      (hcontraction x).mp hx.2.2.2.2.1,
      (homega x).mp hx.2.2.2.2.2.1,
      (hfresh x).mp hx.2.2.2.2.2.2⟩
  · intro hx
    exact ⟨
      (hsource x).mpr hx.1,
      (hauthority x).mpr hx.2.1,
      (hgraph x).mpr hx.2.2.1,
      (hgauge x).mpr hx.2.2.2.1,
      (hcontraction x).mpr hx.2.2.2.2.1,
      (homega x).mpr hx.2.2.2.2.2.1,
      (hfresh x).mpr hx.2.2.2.2.2.2⟩

end AippocampusPrimitiveAxiomClass

/-!
  Summary:
  - P178 proves the uniqueness half of Strategy D at the projection layer.
  - Once two primitive axiom classes agree on the seven primitive facets, the
    induced P94 Boolean projection and memory production are forced.
-/


end SaturationMonoid
