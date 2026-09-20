import Mathlib.Algebra.Homology.Single
import H0mework.Arithmetic.UnitArithmetic.CommonCarrier
import H0mework.Realization.FiniteCell.FrontierDeterminant

/-!
# Determinant state of the coordinate-free unit arithmetic common carrier

The source-kernel residual generated from the UnitHistory-folded
Euler/reversal carrier is realized as a one-term integral complex.  Frozen
prime-power rigidity and canonical frontier compression generate its
determinant line and unit on the same common occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCommonDeterminantState

open AdditiveFamilyFaithfulRealization.RootGeneratedAdditiveFamilyFaithfulRealizationAt
open CanonicalFiniteFrontierCompression
open CanonicalFrontierDeterminant
open CanonicalUnitArithmeticCommonCarrier
open CategoryTheory
open CategoryTheory.Limits
open DerivedAdicCofiber
open PrimePowerKernelIncidenceRigidity.RootGeneratedPrimePowerKernelIncidenceRigidityAt

noncomputable section

abbrev ResidualGroup : Type :=
  (rigidityFace.faithfulFace.sourceComponentMap
    rigidityFace.additiveCalculation).ker

theorem residualGroup_eq_bot :
    (rigidityFace.faithfulFace.sourceComponentMap
      rigidityFace.additiveCalculation).ker = ⊥ :=
  sourceKernelResidualZero.vanishes

instance residualGroup_subsingleton : Subsingleton ResidualGroup where
  allEq := by
    intro left right
    apply Subtype.ext
    have leftZero : (left : Carrier) = 0 := by
      have membership : (left : Carrier) ∈ (⊥ : AddSubgroup Carrier) := by
        rw [← residualGroup_eq_bot]
        exact left.property
      simpa using membership
    have rightZero : (right : Carrier) = 0 := by
      have membership : (right : Carrier) ∈ (⊥ : AddSubgroup Carrier) := by
        rw [← residualGroup_eq_bot]
        exact right.property
      simpa using membership
    exact leftZero.trans rightZero.symm

abbrev ResidualObject : ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ ResidualGroup

theorem residualObjectIsZero : IsZero ResidualObject :=
  ModuleCat.isZero_of_subsingleton ResidualObject

noncomputable def residualComplex : IntegralCochainComplex ℤ :=
  (HomologicalComplex.single (ModuleCat.{0} ℤ)
    (ComplexShape.up ℤ) 0).obj ResidualObject

theorem residualComplexIsZero : IsZero residualComplex :=
  Functor.map_isZero
    (HomologicalComplex.single (ModuleCat.{0} ℤ)
      (ComplexShape.up ℤ) 0) residualObjectIsZero

def residualComplexOccurrence :
    RootedAccountedUnfolding (IntegralCochainComplex ℤ) :=
  rigidityFace.root.map fun _point => residualComplex

def compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
    rigidityFace.root residualComplexOccurrence :=
  RootGeneratedCanonicalFiniteFrontierCompressionAt.generate

theorem compression_actualComplex :
    compression.actualComplex = residualComplex := by
  simp [RootGeneratedCanonicalFiniteFrontierCompressionAt.actualComplex,
    residualComplexOccurrence]

theorem compressionActualIsZero : IsZero compression.actualComplex := by
  rw [compression_actualComplex]
  exact residualComplexIsZero

def determinantState :
    RootGeneratedCanonicalZeroResidualDeterminantStateAt
      compression compressionActualIsZero :=
  RootGeneratedCanonicalZeroResidualDeterminantStateAt.generate

noncomputable def globalSettlement :=
  compression.classifiedGlobalSettlement determinantState.settlement

abbrev IntegralLine := determinantState.integralLine

noncomputable def unitTorsor := determinantState.determinantFace.unitTorsor

noncomputable def canonicalIntegralState : IntegralLine :=
  determinantState.canonicalIntegralState

theorem canonicalIntegralState_ne_zero : canonicalIntegralState ≠ 0 :=
  determinantState.canonicalIntegralState_ne_zero

theorem determinant_preserves_common_occurrence :
    determinantState.determinantFace.root = commonOccurrence := by
  calc
    determinantState.determinantFace.root = rigidityFace.root := rfl
    _ = commonOccurrence := rigidity_preserves_common_occurrence

theorem determinant_projects_to_exact_unit_root :
    determinantState.determinantFace.root.map Prod.fst =
      CanonicalUnitArithmeticPrimePowerIncidence.rootOccurrence := by
  rw [determinant_preserves_common_occurrence]
  exact commonOccurrence_projects_to_exact_unit_root

theorem generated_global_settlement_and_unit :
    globalSettlement.root = rigidityFace.root ∧
      determinantState.determinantFace.root = rigidityFace.root ∧
      Module.finrank ℤ IntegralLine = 1 ∧
      canonicalIntegralState ≠ 0 :=
  ⟨rfl, rfl,
    determinantState.determinantFace.integralLine_finrank,
    canonicalIntegralState_ne_zero⟩

end

end CanonicalUnitArithmeticCommonDeterminantState
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
