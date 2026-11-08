import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.OntologyFace

/-!
# Optional ontology-face regression

This fixture instantiates P179 on the semantic Boolean state space itself.
The primitive predicates are exactly the seven Boolean coordinates, and the
projection is the identity.  It exercises the optional P133/P179 face only;
it is not a Go ontology instance.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace OntologyFaceRegression

/-- Identity primitive class on the concrete seven-Boolean semantic state.
Every primitive predicate is the corresponding Boolean coordinate being true,
and the projection is definitionally the identity. -/
def semanticBoolIdentityPrimitive :
    AippocampusPrimitiveAxiomClass SemanticBoolState where
  sourceBacked := {
    sourceReachability := fun state => state.sourceReachability = true
    omegaGluing := fun state => state.omegaGluing = true
    freshnessValidity := fun state => state.freshnessValidity = true
  }
  navigationOnly := {
    authorityMonotonicity := fun state => state.authorityMonotonicity = true
  }
  reflexive := {
    graphConfluence := fun state => state.graphConfluence = true
    gaugeInvariance := fun state => state.gaugeInvariance = true
    contractionCertification := fun state =>
      state.contractionCertification = true
  }
  project := id
  sourceReachability_iff := by intro state; rfl
  authorityMonotonicity_iff := by intro state; rfl
  graphConfluence_iff := by intro state; rfl
  gaugeInvariance_iff := by intro state; rfl
  contractionCertification_iff := by intro state; rfl
  omegaGluing_iff := by intro state; rfl
  freshnessValidity_iff := by intro state; rfl
  state_surjective := by
    intro state
    exact ⟨state, rfl⟩

def identityOntologyFace : OntologyFace semanticBoolIdentityPrimitive :=
  attachOntologyFace semanticBoolIdentityPrimitive

theorem identity_projection_and_surjectivity_are_exact :
    semanticBoolIdentityPrimitive.strategyDProjection.project = id ∧
      ∀ target : SemanticBoolState,
        ∃ source : SemanticBoolState,
          semanticBoolIdentityPrimitive.strategyDProjection.project source =
            target := by
  constructor
  · rw [semanticBoolIdentityPrimitive.cascade_projection_eq]
    rfl
  · intro target
    exact ⟨target, rfl⟩

/-- The explicit P133 foundation constructor and P179's named ontology are one
and the same fixture-generated readout. -/
theorem identity_foundation_and_cascade_ontology_agree :
    identityOntologyFace.foundationOntologyIso =
      identityOntologyFace.cascadeOntologyIso :=
  identityOntologyFace.foundationOntologyIso_eq_cascadeOntologyIso

def sourceFailureState : SemanticBoolState where
  sourceReachability := false
  authorityMonotonicity := true
  graphConfluence := true
  gaugeInvariance := true
  contractionCertification := true
  omegaGluing := true
  freshnessValidity := true

noncomputable def sourceFailureAtom :
    MemorySupportQuotient semanticBoolIdentityPrimitive.memoryContract :=
  memorySupportQuotientMk semanticBoolIdentityPrimitive.memoryContract
    .sourceReachability

theorem source_failure_atom_is_produced :
    (memorySupportQuotientContract
      semanticBoolIdentityPrimitive.memoryContract).produces
        sourceFailureState sourceFailureAtom := by
  rfl

/-- Concrete nonempty support consumes both the direct P133 mouth and P179's
named cascade support mouth. -/
theorem source_failure_consumes_p133_and_p179_support :
    AtomFailure
        (semanticObligationSemantics
          semanticBoolIdentityPrimitive.sevenFacetPredicates)
        sourceFailureState
        (identityOntologyFace.foundationOntologyIso.atomEquiv
          sourceFailureAtom) ∧
      AtomFailure
        (semanticObligationSemantics
          semanticBoolIdentityPrimitive.sevenFacetPredicates)
        sourceFailureState
        (identityOntologyFace.cascadeOntologyIso.atomEquiv
          sourceFailureAtom) :=
  ⟨(identityOntologyFace.foundation_support_iff
      sourceFailureState sourceFailureAtom).mp source_failure_atom_is_produced,
    (identityOntologyFace.cascade_support_iff
      sourceFailureState sourceFailureAtom).mp source_failure_atom_is_produced⟩

def fullySupportedState : SemanticBoolState where
  sourceReachability := true
  authorityMonotonicity := true
  graphConfluence := true
  gaugeInvariance := true
  contractionCertification := true
  omegaGluing := true
  freshnessValidity := true

theorem fully_supported_state_is_csafe :
    CSafe semanticBoolIdentityPrimitive.sevenFacetPredicates
      fullySupportedState := by
  simp [CSafe, AippocampusPrimitiveAxiomClass.sevenFacetPredicates,
    semanticBoolIdentityPrimitive, fullySupportedState]

theorem fully_supported_state_is_silent_by_p133 :
    (memorySupportQuotientContract
      semanticBoolIdentityPrimitive.memoryContract).memorySilent
        fullySupportedState :=
  (identityOntologyFace.foundation_silent_iff fullySupportedState).mpr
    fully_supported_state_is_csafe

theorem fully_supported_state_is_silent_by_p179 :
    (memorySupportQuotientContract
      semanticBoolIdentityPrimitive.memoryContract).memorySilent
        fullySupportedState :=
  (identityOntologyFace.cascade_silent_iff fullySupportedState).mpr
    fully_supported_state_is_csafe

theorem p133_and_p179_silence_return_the_same_safe_face :
    (memorySupportQuotientContract
        semanticBoolIdentityPrimitive.memoryContract).memorySilent
          fullySupportedState ∧
      CSafe semanticBoolIdentityPrimitive.sevenFacetPredicates
        fullySupportedState :=
  ⟨fully_supported_state_is_silent_by_p133,
    (identityOntologyFace.cascade_silent_iff fullySupportedState).mp
      fully_supported_state_is_silent_by_p179⟩

end OntologyFaceRegression
end ProcessGame
end SaturationMonoid
