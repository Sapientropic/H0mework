import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.Proposition179

/-!
# Optional ontology face for process-generated games

The process-game core does not require an ontology.  When a domain already
produces an `AippocampusPrimitiveAxiomClass`, this zero-field dependent face
exposes the existing P133/P179 obstruction-memory ontology as an optional
readout.  No player, agent, process occurrence or ledger is reconstructed here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame

/-- Optional downstream ontology attached to an already generated primitive
axiom class.  The constructor carries no ontology or support data. -/
inductive OntologyFace {State : Type*}
    (primitive : AippocampusPrimitiveAxiomClass State) : Type where
  | generated

/-- The sole optional-face producer. -/
def attachOntologyFace {State : Type*}
    (primitive : AippocampusPrimitiveAxiomClass State) :
    OntologyFace primitive :=
  .generated

namespace OntologyFace

variable {State : Type*}
variable {primitive : AippocampusPrimitiveAxiomClass State}

/-- P133 ontology generated explicitly from P179's foundation certificate. -/
noncomputable def foundationOntologyIso
    (_face : OntologyFace primitive) :
    ObstructionMemoryOntologyIso primitive.sevenFacetPredicates
      primitive.memoryContract :=
  ObstructionMemoryOntologyIso.ofFoundationCertificate
    primitive.strategyDFoundation

/-- The named P179 cascade ontology on the same primitive source. -/
noncomputable def cascadeOntologyIso
    (_face : OntologyFace primitive) :
    ObstructionMemoryOntologyIso primitive.sevenFacetPredicates
      primitive.memoryContract :=
  primitive.ontologyIso

/-- P133's direct foundation construction and P179's named cascade are the
same generated ontology, not two independently supplied presentations. -/
theorem foundationOntologyIso_eq_cascadeOntologyIso
    (face : OntologyFace primitive) :
    face.foundationOntologyIso = face.cascadeOntologyIso :=
  rfl

/-- Direct P133 support readout from the foundation-generated ontology. -/
theorem foundation_support_iff
    (face : OntologyFace primitive) (state : State)
    (atom : MemorySupportQuotient primitive.memoryContract) :
    (memorySupportQuotientContract primitive.memoryContract).produces
        state atom ↔
      AtomFailure
        (semanticObligationSemantics primitive.sevenFacetPredicates) state
        (face.foundationOntologyIso.atomEquiv atom) :=
  face.foundationOntologyIso.support_iff state atom

/-- Direct P179 support readout from the named cascade ontology. -/
theorem cascade_support_iff
    (face : OntologyFace primitive) (state : State)
    (atom : MemorySupportQuotient primitive.memoryContract) :
    (memorySupportQuotientContract primitive.memoryContract).produces
        state atom ↔
      AtomFailure
        (semanticObligationSemantics primitive.sevenFacetPredicates) state
        (face.cascadeOntologyIso.atomEquiv atom) := by
  simpa [cascadeOntologyIso] using
    primitive.ontologyIso_support_iff state atom

/-- Direct P133 silence readout from the foundation-generated ontology. -/
theorem foundation_silent_iff
    (face : OntologyFace primitive) (state : State) :
    (memorySupportQuotientContract primitive.memoryContract).memorySilent
        state ↔
      CSafe primitive.sevenFacetPredicates state :=
  face.foundationOntologyIso.silent_iff_safe state

/-- Direct P179 silence readout from the named cascade ontology. -/
theorem cascade_silent_iff
    (_face : OntologyFace primitive) (state : State) :
    (memorySupportQuotientContract primitive.memoryContract).memorySilent
        state ↔
      CSafe primitive.sevenFacetPredicates state := by
  simpa using primitive.ontologyIso_silent_iff_csafe state

end OntologyFace

end ProcessGame
end SaturationMonoid
