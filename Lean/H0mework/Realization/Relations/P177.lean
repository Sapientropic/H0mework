import H0mework.Realization.QuerySupport.P104

/-!
# Proposition 177: primitive slogans generate the seven-facet projection

Strategy D starts upstream of the seven-facet checklist.  Instead of treating
the seven semantic atoms as an external obligation list, this file packages the
three AIppocampus primitive slogans as typed axiom families:

* source-backed continuity;
* navigation-only authority;
* reflexive read/write memory.

Those three primitive families deterministically induce the seven CSafe
predicates.  If the runtime also supplies the four P94 mechanism fields
(`project`, atom preservation, surjectivity, and memory pullback), the usual
`StructureDeterminedSevenFacetSystem` follows automatically.

Boundary: this is the first formal Strategy-D bridge.  It formalizes the
slogans as primitive axiom families plus explicit projection correctness
fields.  It does not yet prove those fields from production code.
-/

namespace SaturationMonoid

/-! ## The three primitive axiom families -/

/-- Source-backed continuity supplies the source/freshness side of the seven
facets. -/
structure SourceBackedPrimitiveAxioms (State : Type*) where
  sourceReachability : State → Prop
  omegaGluing : State → Prop
  freshnessValidity : State → Prop

/-- Navigation-only authority supplies the authority monotonicity facet. -/
structure NavigationOnlyPrimitiveAxioms (State : Type*) where
  authorityMonotonicity : State → Prop

/-- Reflexive read/write memory supplies the dynamic/runtime facets. -/
structure ReflexivePrimitiveAxioms (State : Type*) where
  graphConfluence : State → Prop
  gaugeInvariance : State → Prop
  contractionCertification : State → Prop

/-- The primitive AIppocampus axiom class.  The first three fields are the
semantic slogans; the remaining fields are the P94 projection mechanism
certificates that make those slogans visible as the seven Boolean facets. -/
structure AippocampusPrimitiveAxiomClass (State : Type*) where
  sourceBacked : SourceBackedPrimitiveAxioms State
  navigationOnly : NavigationOnlyPrimitiveAxioms State
  reflexive : ReflexivePrimitiveAxioms State
  project : State → SemanticBoolState
  sourceReachability_iff :
    ∀ x, sourceBacked.sourceReachability x ↔
      (project x).sourceReachability = true
  authorityMonotonicity_iff :
    ∀ x, navigationOnly.authorityMonotonicity x ↔
      (project x).authorityMonotonicity = true
  graphConfluence_iff :
    ∀ x, reflexive.graphConfluence x ↔
      (project x).graphConfluence = true
  gaugeInvariance_iff :
    ∀ x, reflexive.gaugeInvariance x ↔
      (project x).gaugeInvariance = true
  contractionCertification_iff :
    ∀ x, reflexive.contractionCertification x ↔
      (project x).contractionCertification = true
  omegaGluing_iff :
    ∀ x, sourceBacked.omegaGluing x ↔
      (project x).omegaGluing = true
  freshnessValidity_iff :
    ∀ x, sourceBacked.freshnessValidity x ↔
      (project x).freshnessValidity = true
  state_surjective :
    ∀ y : SemanticBoolState, ∃ x : State, project x = y

namespace AippocampusPrimitiveAxiomClass

variable {State : Type*}

/-! ## The induced seven-facet system -/

/-- The seven CSafe facets induced by the three primitive axiom families. -/
def sevenFacetPredicates
    (A : AippocampusPrimitiveAxiomClass State) : CSafePredicates State where
  sourceBacked := A.sourceBacked.sourceReachability
  authoritySafe := A.navigationOnly.authorityMonotonicity
  graphConfluent := A.reflexive.graphConfluence
  gaugeNonleaking := A.reflexive.gaugeInvariance
  contractionSafe := A.reflexive.contractionCertification
  omegaConsistent := A.sourceBacked.omegaGluing
  freshnessSafe := A.sourceBacked.freshnessValidity

/-- The projected semantic Boolean state induced by the primitive axiom class.
-/
def sevenFacetProjection
    (A : AippocampusPrimitiveAxiomClass State) : State → SemanticBoolState :=
  A.project

/-- THEOREM 1: every lower semantic atom is exactly preserved by the primitive
seven-facet projection. -/
theorem sevenFacetProjection_atom_iff
    (A : AippocampusPrimitiveAxiomClass State)
    (x : State) (a : SemanticAtom) :
    (semanticObligationSemantics A.sevenFacetPredicates).holds a x ↔
      (semanticObligationSemantics semanticBoolPredicates).holds a
        (A.sevenFacetProjection x) := by
  cases a <;>
    simp [sevenFacetPredicates, sevenFacetProjection,
      semanticObligationSemantics, semanticHolds, semanticBoolPredicates]
  · exact A.sourceReachability_iff x
  · exact A.authorityMonotonicity_iff x
  · exact A.graphConfluence_iff x
  · exact A.gaugeInvariance_iff x
  · exact A.contractionCertification_iff x
  · exact A.omegaGluing_iff x
  · exact A.freshnessValidity_iff x

/-- THEOREM 2: the primitive axiom class emits the P94 projection certificate.
-/
def toSemanticBoolProjectionCertificate
    (A : AippocampusPrimitiveAxiomClass State) :
    SemanticBoolProjectionCertificate A.sevenFacetPredicates where
  project := A.sevenFacetProjection
  atom_iff := A.sevenFacetProjection_atom_iff
  state_surjective := A.state_surjective

/-! ## Primitive memory production as semantic failure pullback -/

/-- Memory production induced by the primitive projection: a memory atom is
produced exactly when the corresponding semantic Boolean facet is false after
projection. -/
noncomputable def memoryContract
    (A : AippocampusPrimitiveAxiomClass State) :
    MemoryProductionContract State SemanticAtom where
  produces := fun x a =>
    semanticBoolMemoryContract.produces (A.sevenFacetProjection x) a
  memorySilent := fun x =>
    semanticBoolMemoryContract.memorySilent (A.sevenFacetProjection x)
  product_shape := by
    intro x
    rfl
  independent := by
    classical
    intro assignment
    rcases semanticBoolMemoryContract.independent assignment with ⟨y, hy⟩
    rcases A.state_surjective y with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro m
    simpa [sevenFacetProjection, hx] using hy m

/-- THEOREM 3: induced primitive memory is exactly the P94 semantic Boolean
memory pullback. -/
theorem memory_pullback
    (A : AippocampusPrimitiveAxiomClass State)
    (x : State) (a : SemanticAtom) :
    A.memoryContract.produces x a ↔
      semanticBoolMemoryContract.produces
        (A.toSemanticBoolProjectionCertificate.project x) a := by
  rfl

/-- THEOREM 4: the primitive axiom class emits the P94 memory-pullback
certificate. -/
noncomputable def toSemanticBoolMemoryPullback
    (A : AippocampusPrimitiveAxiomClass State) :
    SemanticBoolMemoryPullback A.sevenFacetPredicates A.memoryContract where
  projection := A.toSemanticBoolProjectionCertificate
  memory_pullback := A.memory_pullback

/-- THEOREM 5: the primitive axiom class emits the downstream
structure-determined seven-facet system used by P104/P133. -/
noncomputable def toStructureDeterminedSevenFacetSystem
    (A : AippocampusPrimitiveAxiomClass State) :
    StructureDeterminedSevenFacetSystem State where
  predicates := A.sevenFacetPredicates
  memory := A.memoryContract
  pullback := A.toSemanticBoolMemoryPullback

end AippocampusPrimitiveAxiomClass

/-!
  Summary:
  - The three slogans are now typed primitive axiom families.
  - Their projection induces the seven CSafe facets and satisfies the P94
    projection/pullback conditions.
  - Therefore the primitive class already reaches the P104
    `StructureDeterminedSevenFacetSystem` interface.
-/


end SaturationMonoid
