import H0mework.Realization.Arithmetic.DerivedAdicCofiber

/-!
# Root-generated derived cofinal settlement

This is the global-closure mouth.  It consumes one actual rooted cochain map.
The generic mapping-cocone producer generates its cofiber and distinguished
derived triangle; an `IsIso` instance for the image of that same map in the
derived category then forces the cofiber object to be zero.  Thus the stable
mouth accepts genuine quasi-isomorphisms and does not demand a strict inverse
of cochain complexes.

Finite presented-history compactness is intentionally absent here.  It is a
separate perfect/determinant projection and cannot gate global cofinal
closure.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DerivedCofinalSettlement

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedAdicCofiber

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe w

/-- Stable generic global-settlement mouth.  The derived `IsIso` witness is
retained privately so downstream consumers cannot replace it by an unrelated
acyclicity or cofiber-zero receipt. -/
structure RootGeneratedDerivedCofinalSettlementAt
    {Root : Type w} {R : Type} [CommRing R]
    (rootOccurrence : RootedAccountedUnfolding Root)
    (sourceOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex R))
    (targetOccurrence : RootedAccountedUnfolding
      (IntegralCochainComplex R))
    (transitionOccurrence : RootedAccountedUnfolding
      (sourceOccurrence.root ⟶ targetOccurrence.root)) : Type where
  private mk ::
  derivedFace : RootGeneratedDerivedAdicCofiberAt rootOccurrence
    sourceOccurrence targetOccurrence transitionOccurrence
  transitionDerivedIsIso :
    IsIso (DerivedCategory.Q.map transitionOccurrence.root)

namespace RootGeneratedDerivedCofinalSettlementAt

variable {Root : Type w} {R : Type} [CommRing R]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrence targetOccurrence : RootedAccountedUnfolding
  (IntegralCochainComplex R)}
variable {transitionOccurrence : RootedAccountedUnfolding
  (sourceOccurrence.root ⟶ targetOccurrence.root)}

/-- The only extra authority is the framework's existing derived `IsIso`
instance for the actual transition.  No strict chain inverse, cofiber,
residual-zero or settlement receipt is accepted. -/
def generate [IsIso (DerivedCategory.Q.map transitionOccurrence.root)] :
    RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence :=
  ⟨RootGeneratedDerivedAdicCofiberAt.generate, inferInstance⟩

def root
    (_face : RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :=
  rootOccurrence

noncomputable def mappingCofiber
    (face : RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :
    IntegralCochainComplex R :=
  face.derivedFace.cofiberComplex

noncomputable def derivedTriangle
    (face : RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :
    Triangle (DerivedCategory (ModuleCat.{0} R)) :=
  face.derivedFace.derivedTriangle

/-- The generated cofiber residual object. -/
abbrev CofiberResidual
    (face : RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :=
  face.derivedTriangle.obj₁

/-- Framework-derived residual-zero: actual derived `IsIso` plus the generated
distinguished mapping-cocone triangle. -/
theorem cofiberResidualVanishes
    (face : RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :
    IsZero face.CofiberResidual := by
  let _ : IsIso (DerivedCategory.Q.map face.derivedFace.actualTransition) :=
    face.transitionDerivedIsIso
  exact face.derivedFace.derivedCofiber_isZero_of_derivedIsIso

/-- One theorem exposes the complete global settlement without mixing in a
finite-generation or perfectness gate. -/
theorem settlementMouth
    (face : RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :
    face.derivedFace.actualTransition = transitionOccurrence.root ∧
      face.derivedTriangle ∈
        distTriang (DerivedCategory (ModuleCat.{0} R)) ∧
      IsZero face.CofiberResidual ∧
      face.root = rootOccurrence :=
  ⟨rfl, face.derivedFace.derivedTriangle_distinguished,
    face.cofiberResidualVanishes, rfl⟩

theorem preserves_actual_rooted_transition
    (face : RootGeneratedDerivedCofinalSettlementAt rootOccurrence
      sourceOccurrence targetOccurrence transitionOccurrence) :
    face.root = rootOccurrence ∧
      face.derivedFace.sourceComplex = sourceOccurrence.root ∧
      face.derivedFace.targetComplex = targetOccurrence.root ∧
      face.derivedFace.actualTransition = transitionOccurrence.root :=
  ⟨rfl, rfl, rfl, rfl⟩

end RootGeneratedDerivedCofinalSettlementAt

end

end DerivedCofinalSettlement
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
