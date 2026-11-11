import Mathlib.Data.List.Forall2
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootGeneratedBoundedPerfectDeterminantKernel

/-!
# Naturality of the bounded perfect determinant carrier

An actual termwise chain equivalence generates the alternating determinant
line equivalence in every finite amplitude.  Even terms act covariantly;
odd terms act through the dual of the inverse top-exterior equivalence.
No frames or matrices enter the transporter.

This is strict isomorphism naturality.  Quasi-isomorphism invariance is the
next face and must be generated through the acyclic mapping cofiber, not by
renaming this transporter.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace BoundedPerfectDeterminantNaturality

open CategoryTheory
open BoundedPerfectDeterminant
open GradedIntegralDeterminantLine
open scoped TensorProduct

noncomputable section

universe w

/-- One actual equivalence between generated finite-free terms. -/
structure GeneratedFiniteFreeIntegralTermEquivAt
    (source target : GeneratedFiniteFreeIntegralTermAt) : Type where
  equivalence : source.module ≃ₗ[ℤ] target.module

namespace GeneratedFiniteFreeIntegralTermEquivAt

variable {source target : GeneratedFiniteFreeIntegralTermAt}

noncomputable def topLineEquiv
    (equivalence : GeneratedFiniteFreeIntegralTermEquivAt source target) :
    (evenDeterminantLine [source]) ≃ₗ[ℤ]
      (evenDeterminantLine [target]) := by
  letI : Module.Free ℤ source.module := source.free
  letI : Module.Finite ℤ source.module := source.finite
  letI : Module.Free ℤ target.module := target.free
  letI : Module.Finite ℤ target.module := target.finite
  exact topExteriorLineEquiv equivalence.equivalence

noncomputable def dualTopLineEquiv
    (equivalence : GeneratedFiniteFreeIntegralTermEquivAt source target) :
    (oddDeterminantLine [source]) ≃ₗ[ℤ]
      (oddDeterminantLine [target]) :=
  equivalence.topLineEquiv.symm.dualMap

end GeneratedFiniteFreeIntegralTermEquivAt

/-- Data-valued alignment of two finite term lists.  `List.Forall₂` is
Prop-valued and would erase the actual equivalences needed by the functor. -/
inductive GeneratedFiniteFreeIntegralTermEquivListAt :
    List GeneratedFiniteFreeIntegralTermAt →
      List GeneratedFiniteFreeIntegralTermAt → Type 2
  | nil : GeneratedFiniteFreeIntegralTermEquivListAt [] []
  | cons {source target sourceTail targetTail}
      (head : GeneratedFiniteFreeIntegralTermEquivAt source target)
      (tail : GeneratedFiniteFreeIntegralTermEquivListAt
        sourceTail targetTail) :
      GeneratedFiniteFreeIntegralTermEquivListAt
        (source :: sourceTail) (target :: targetTail)

mutual

noncomputable def evenDeterminantLineEquiv
    {source target : List GeneratedFiniteFreeIntegralTermAt} :
    GeneratedFiniteFreeIntegralTermEquivListAt source target →
      evenDeterminantLine source ≃ₗ[ℤ] evenDeterminantLine target
  | .nil => LinearEquiv.refl ℤ ℤ
  | .cons head .nil => head.topLineEquiv
  | .cons head tail@(.cons _ _) =>
      TensorProduct.congr head.topLineEquiv (oddDeterminantLineEquiv tail)

noncomputable def oddDeterminantLineEquiv
    {source target : List GeneratedFiniteFreeIntegralTermAt} :
    GeneratedFiniteFreeIntegralTermEquivListAt source target →
      oddDeterminantLine source ≃ₗ[ℤ] oddDeterminantLine target
  | .nil => LinearEquiv.refl ℤ ℤ
  | .cons head .nil => head.dualTopLineEquiv
  | .cons head tail@(.cons _ _) =>
      TensorProduct.congr head.dualTopLineEquiv
        (evenDeterminantLineEquiv tail)

end

/-- Actual chain equivalence on an arbitrary finite amplitude. -/
structure BoundedIntegralComplexEquivAt
    {length : Nat}
    (source target : FiniteIntegralCochainComplex length) : Type where
  termEquiv : ∀ degree, source.X degree ≃ₗ[ℤ] target.X degree
  commute : ∀ sourceDegree targetDegree,
    (termEquiv targetDegree).toLinearMap.comp
        (source.d sourceDegree targetDegree).hom =
      (target.d sourceDegree targetDegree).hom.comp
        (termEquiv sourceDegree).toLinearMap

namespace BoundedIntegralComplexEquivAt

variable {length : Nat}
variable {source target : FiniteIntegralCochainComplex length}
variable {sourceCalculation : RootGeneratedBoundedPerfectCalculationAt source}
variable {targetCalculation : RootGeneratedBoundedPerfectCalculationAt target}

def termEquivAt
    (equivalence : BoundedIntegralComplexEquivAt source target)
    (degree : Fin length) :
    GeneratedFiniteFreeIntegralTermEquivAt
      (sourceCalculation.term degree) (targetCalculation.term degree) :=
  ⟨equivalence.termEquiv degree⟩

def termEquivsAlong
    (equivalence : BoundedIntegralComplexEquivAt source target) :
    (degrees : List (Fin length)) →
      GeneratedFiniteFreeIntegralTermEquivListAt
        (degrees.map sourceCalculation.term)
        (degrees.map targetCalculation.term)
  | [] => .nil
  | degree :: tail =>
      .cons (equivalence.termEquivAt degree)
        (equivalence.termEquivsAlong tail)

def termEquivs
    (equivalence : BoundedIntegralComplexEquivAt source target) :
    GeneratedFiniteFreeIntegralTermEquivListAt
      sourceCalculation.terms targetCalculation.terms :=
  equivalence.termEquivsAlong (List.finRange length)

end BoundedIntegralComplexEquivAt

/-- Root-owned determinant transporter generated by one actual chain
equivalence occurrence. -/
structure RootGeneratedBoundedPerfectDeterminantNaturalityAt
    {Root : Type w} {length : Nat}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {sourceOccurrence targetOccurrence : RootedAccountedUnfolding
      (FiniteIntegralCochainComplex length)}
    {sourceCalculation : RootGeneratedBoundedPerfectCalculationAt
      sourceOccurrence.root}
    {targetCalculation : RootGeneratedBoundedPerfectCalculationAt
      targetOccurrence.root}
    (sourceState : RootGeneratedBoundedPerfectDeterminantAt rootOccurrence
      sourceOccurrence sourceCalculation)
    (targetState : RootGeneratedBoundedPerfectDeterminantAt rootOccurrence
      targetOccurrence targetCalculation)
    (equivalenceOccurrence : RootedAccountedUnfolding
      (BoundedIntegralComplexEquivAt sourceOccurrence.root
        targetOccurrence.root)) : Type where
  private mk ::

namespace RootGeneratedBoundedPerfectDeterminantNaturalityAt

variable {Root : Type w} {length : Nat}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {sourceOccurrence targetOccurrence : RootedAccountedUnfolding
  (FiniteIntegralCochainComplex length)}
variable {sourceCalculation : RootGeneratedBoundedPerfectCalculationAt
  sourceOccurrence.root}
variable {targetCalculation : RootGeneratedBoundedPerfectCalculationAt
  targetOccurrence.root}
variable {sourceState : RootGeneratedBoundedPerfectDeterminantAt rootOccurrence
  sourceOccurrence sourceCalculation}
variable {targetState : RootGeneratedBoundedPerfectDeterminantAt rootOccurrence
  targetOccurrence targetCalculation}
variable {equivalenceOccurrence : RootedAccountedUnfolding
  (BoundedIntegralComplexEquivAt sourceOccurrence.root
    targetOccurrence.root)}

def generate : RootGeneratedBoundedPerfectDeterminantNaturalityAt
    sourceState targetState equivalenceOccurrence :=
  ⟨⟩

def actualEquivalence
    (_face : RootGeneratedBoundedPerfectDeterminantNaturalityAt
      sourceState targetState equivalenceOccurrence) :=
  equivalenceOccurrence.root

noncomputable def integralLineEquiv
    (face : RootGeneratedBoundedPerfectDeterminantNaturalityAt
      sourceState targetState equivalenceOccurrence) :
    sourceState.integralLine ≃ₗ[ℤ] targetState.integralLine :=
  evenDeterminantLineEquiv
    (face.actualEquivalence.termEquivs
      (sourceCalculation := sourceCalculation)
      (targetCalculation := targetCalculation))

theorem preserves_same_root_and_actual_equivalence
    (face : RootGeneratedBoundedPerfectDeterminantNaturalityAt
      sourceState targetState equivalenceOccurrence) :
    sourceState.root = rootOccurrence ∧ targetState.root = rootOccurrence ∧
      face.actualEquivalence = equivalenceOccurrence.root :=
  ⟨rfl, rfl, rfl⟩

end RootGeneratedBoundedPerfectDeterminantNaturalityAt

end


end BoundedPerfectDeterminantNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
