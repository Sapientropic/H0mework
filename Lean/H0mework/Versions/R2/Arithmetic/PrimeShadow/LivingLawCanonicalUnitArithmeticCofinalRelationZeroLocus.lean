import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawCanonicalUnitArithmeticCofinalRelationAction
import H0mework.Realization.Arithmetic.DerivedAdicCofiber
import H0mework.Realization.MappingCone.Functoriality

/-!
# Cofinal anti-invariant arithmetic relation cofiber

The source-generated reversal action on the full relation homotopy limit now
generates its actual `id - ι` transition.  The frozen derived-cofiber kernel
forms the mapping cocone and distinguished triangle on the identical rooted
occurrence.  Every finite relation complex remains an exact restriction of
this global anti-invariant transition.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCofinalRelationZeroLocus

open CanonicalUnitArithmeticCofinalRelationAction
open CanonicalUnitArithmeticCofinalRelationHomotopyLimit
open CategoryTheory
open CategoryTheory.Pretriangulated
open CochainMappingCoconeFunctoriality
open DerivedAdicCofiber

noncomputable section

attribute [local instance] HasDerivedCategory.standard

def relationLimitOccurrence : RootedAccountedUnfolding
    SequentialHomotopyLimit.IntegralCochainComplex :=
  homotopyLimitFace.root.map fun _root => derivedRelationLimit

noncomputable def antiInvariantTransition :
    derivedRelationLimit ⟶ derivedRelationLimit :=
  𝟙 derivedRelationLimit - derivedRelationReversal

def antiInvariantTransitionOccurrence : RootedAccountedUnfolding
    (relationLimitOccurrence.root ⟶ relationLimitOccurrence.root) :=
  homotopyLimitFace.root.map fun _root => antiInvariantTransition

/-- The exact source-owned cofiber of `id - reversal` on the cofinal relation
limit. -/
def zeroLocusFace : RootGeneratedDerivedAdicCofiberAt
    homotopyLimitFace.root relationLimitOccurrence relationLimitOccurrence
      antiInvariantTransitionOccurrence :=
  RootGeneratedDerivedAdicCofiberAt.generate

abbrev zeroLocusComplex : SequentialHomotopyLimit.IntegralCochainComplex :=
  zeroLocusFace.cofiberComplex

def zeroLocusOccurrence : RootedAccountedUnfolding
    SequentialHomotopyLimit.IntegralCochainComplex :=
  zeroLocusFace.cofiberOccurrence

noncomputable def stageAntiInvariantTransition (stage : Nat) :
    homotopyLimitFace.towerObject stage ⟶
      homotopyLimitFace.towerObject stage :=
  𝟙 (homotopyLimitFace.towerObject stage) -
    reversalActionFace.componentAt stage

/-- Every finite restriction is a square of the same global `id - ι`
transition. -/
theorem antiInvariantTransition_restriction_square (stage : Nat) :
    antiInvariantTransition ≫ homotopyLimitFace.restriction stage =
      homotopyLimitFace.restriction stage ≫
        stageAntiInvariantTransition stage := by
  unfold antiInvariantTransition stageAntiInvariantTransition
    derivedRelationReversal
  rw [Preadditive.sub_comp, Preadditive.comp_sub,
    reversalActionFace.homotopyLimitAction_restriction]
  simp

noncomputable def stageZeroLocusComplex (stage : Nat) :
    SequentialHomotopyLimit.IntegralCochainComplex :=
  CochainComplex.mappingCocone (stageAntiInvariantTransition stage)

/-- Actual finite restriction of the global anti-invariant cofiber, generated
from the transition square rather than supplied as a comparison map. -/
noncomputable def zeroLocusRestriction (stage : Nat) :
    zeroLocusComplex ⟶ stageZeroLocusComplex stage :=
  mappingCoconeMap antiInvariantTransition
    (stageAntiInvariantTransition stage)
    (homotopyLimitFace.restriction stage)
    (homotopyLimitFace.restriction stage)
    (antiInvariantTransition_restriction_square stage).symm

theorem zeroLocusRestriction_fst (stage : Nat) :
    zeroLocusRestriction stage ≫
        CochainComplex.mappingCocone.fst
          (stageAntiInvariantTransition stage) =
      CochainComplex.mappingCocone.fst antiInvariantTransition ≫
        homotopyLimitFace.restriction stage :=
  mappingCoconeMap_fst _ _ _ _ _

theorem zeroLocus_preserves_common_root_and_actual_transition :
    zeroLocusFace.root = homotopyLimitFace.root ∧
      zeroLocusFace.sourceComplex = derivedRelationLimit ∧
      zeroLocusFace.targetComplex = derivedRelationLimit ∧
      zeroLocusFace.actualTransition = antiInvariantTransition := by
  exact zeroLocusFace.preserves_actual_transition

theorem zeroLocus_derivedTriangle_distinguished :
    zeroLocusFace.derivedTriangle ∈
      distTriang (DerivedCategory (ModuleCat.{0} ℤ)) :=
  zeroLocusFace.derivedTriangle_distinguished

end
end CanonicalUnitArithmeticCofinalRelationZeroLocus
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
