import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Axiom-free authority core for derived arithmetic incidence

This file contains only the source/root incidence carrier.  It is generic in
the pairing payload type and therefore does not import matrix, determinant,
exterior-power, quotient-cardinality or finite-dimensional realization
machinery.  Typed algebraic kernels must factor through this face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DerivedArithmeticAxiomFreeCore

universe u v w p

/-- The sole authority mouth of a dual arithmetic incidence. -/
structure RootGeneratedDualIncidenceAt
    {Root : Type w} {Left : Type u} {Right : Type v} {Pairing : Type p}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (leftOccurrences : Left → RootedAccountedUnfolding Left)
    (rightOccurrences : Right → RootedAccountedUnfolding Right)
    (pairingOccurrence : RootedAccountedUnfolding Pairing) : Type where
  private mk ::

namespace RootGeneratedDualIncidenceAt

variable {Root : Type w} {Left : Type u} {Right : Type v} {Pairing : Type p}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {leftOccurrences : Left → RootedAccountedUnfolding Left}
variable {rightOccurrences : Right → RootedAccountedUnfolding Right}
variable {pairingOccurrence : RootedAccountedUnfolding Pairing}

def generate : RootGeneratedDualIncidenceAt rootOccurrence leftOccurrences
    rightOccurrences pairingOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedDualIncidenceAt rootOccurrence leftOccurrences
      rightOccurrences pairingOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def left
    (_face : RootGeneratedDualIncidenceAt rootOccurrence leftOccurrences
      rightOccurrences pairingOccurrence) :
    Left → RootedAccountedUnfolding Left :=
  leftOccurrences

def right
    (_face : RootGeneratedDualIncidenceAt rootOccurrence leftOccurrences
      rightOccurrences pairingOccurrence) :
    Right → RootedAccountedUnfolding Right :=
  rightOccurrences

def pairing
    (_face : RootGeneratedDualIncidenceAt rootOccurrence leftOccurrences
      rightOccurrences pairingOccurrence) :
    RootedAccountedUnfolding Pairing :=
  pairingOccurrence

end RootGeneratedDualIncidenceAt

end DerivedArithmeticAxiomFreeCore
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
