import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Axiom-free authority core for cofinal perfect compression

This file records only the exact root occurrence, the source-generator
occurrence family and the cofinal diagram occurrence.  It is generic in the
diagram payload and imports no module, Noetherian, quotient, basis,
perfectness, quasi-isomorphism or determinant machinery.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPerfectCompressionAxiomFreeCore

universe u v w

/-- Sole authority mouth for a cofinal compression incidence. -/
structure RootGeneratedCofinalCompressionIncidenceAt
    {Root : Type w} {Generator : Type u} {Diagram : Type v}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (generatorOccurrences : Generator → RootedAccountedUnfolding Generator)
    (diagramOccurrence : RootedAccountedUnfolding Diagram) : Type where
  private mk ::
  generatorOccurrences_exact : ∀ generator,
    (generatorOccurrences generator).root = generator

namespace RootGeneratedCofinalCompressionIncidenceAt

variable {Root : Type w} {Generator : Type u} {Diagram : Type v}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {generatorOccurrences :
  Generator → RootedAccountedUnfolding Generator}
variable {diagramOccurrence : RootedAccountedUnfolding Diagram}

def generate
    (generatorOccurrences_exact : ∀ generator,
      (generatorOccurrences generator).root = generator) :
    RootGeneratedCofinalCompressionIncidenceAt rootOccurrence
      generatorOccurrences diagramOccurrence :=
  ⟨generatorOccurrences_exact⟩

def root
    (_face : RootGeneratedCofinalCompressionIncidenceAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def generators
    (_face : RootGeneratedCofinalCompressionIncidenceAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    Generator → RootedAccountedUnfolding Generator :=
  generatorOccurrences

def diagram
    (_face : RootGeneratedCofinalCompressionIncidenceAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    RootedAccountedUnfolding Diagram :=
  diagramOccurrence

theorem generatorOccurrence_root
    (face : RootGeneratedCofinalCompressionIncidenceAt rootOccurrence
      generatorOccurrences diagramOccurrence)
    (generator : Generator) :
    (face.generators generator).root = generator :=
  face.generatorOccurrences_exact generator

theorem preserves_occurrences
    (face : RootGeneratedCofinalCompressionIncidenceAt rootOccurrence
      generatorOccurrences diagramOccurrence) :
    face.root = rootOccurrence ∧
      face.generators = generatorOccurrences ∧
      face.diagram = diagramOccurrence :=
  ⟨rfl, rfl, rfl⟩

end RootGeneratedCofinalCompressionIncidenceAt

end CofinalPerfectCompressionAxiomFreeCore
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
