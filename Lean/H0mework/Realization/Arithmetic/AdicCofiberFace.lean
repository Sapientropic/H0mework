import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Axiom-free authority core for derived adic cofibers

Only the root, source-complex, target-complex and actual transition
occurrences live here.  The payload types are completely generic; mapping
cones, derived categories, exact triangles, perfectness and determinants are
not imported.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DerivedAdicCofiberAxiomFreeCore

universe a b m w

/-- Sole authority mouth for one source-generated derived transition. -/
structure RootGeneratedDerivedTransitionIncidenceAt
    {Root : Type w} {Source : Type a} {Target : Type b} {Transition : Type m}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (sourceOccurrence : RootedAccountedUnfolding Source)
    (targetOccurrence : RootedAccountedUnfolding Target)
    (transitionOccurrence : RootedAccountedUnfolding Transition) : Type where
  private mk ::

namespace RootGeneratedDerivedTransitionIncidenceAt

variable {Root : Type w} {Source : Type a} {Target : Type b}
variable {Transition : Type m}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrence : RootedAccountedUnfolding Source}
variable {targetOccurrence : RootedAccountedUnfolding Target}
variable {transitionOccurrence : RootedAccountedUnfolding Transition}

def generate : RootGeneratedDerivedTransitionIncidenceAt rootOccurrence
    sourceOccurrence targetOccurrence transitionOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedDerivedTransitionIncidenceAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :=
  rootOccurrence

def source
    (_face : RootGeneratedDerivedTransitionIncidenceAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :=
  sourceOccurrence

def target
    (_face : RootGeneratedDerivedTransitionIncidenceAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :=
  targetOccurrence

def transition
    (_face : RootGeneratedDerivedTransitionIncidenceAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :=
  transitionOccurrence

theorem preserves_occurrences
    (face : RootGeneratedDerivedTransitionIncidenceAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :
    face.root = rootOccurrence ∧
      face.source = sourceOccurrence ∧
      face.target = targetOccurrence ∧
      face.transition = transitionOccurrence :=
  ⟨rfl, rfl, rfl, rfl⟩

end RootGeneratedDerivedTransitionIncidenceAt

end DerivedAdicCofiberAxiomFreeCore
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
