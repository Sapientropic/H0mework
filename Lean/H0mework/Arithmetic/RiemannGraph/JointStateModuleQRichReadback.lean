import H0mework.Arithmetic.RiemannGraph.IntegralGraphCharacterReadback
import H0mework.Arithmetic.RiemannGraph.ZeroJointStateModuleOccurrence

/-!
# Direct q-rich readback of the joint state occurrence

The q-rich cycle is rebuilt from the normalized measurement of the integral
orbits stored in `zeroOwnedJointStateModuleOccurrence.root`.  This removes
the remaining parallel sibling route: the detector now consumes the joint
root itself and agrees with the previously certified integral-character
cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open InverseZeroFibre
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation

noncomputable section

def jointStateModuleSelectedBasisReadback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : ℂ :=
  (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
    (((zeroOwnedJointStateModuleOccurrence
      observation nontrivial).root.2).selectedIntegralOrbit
        (delta scale)).snd

def jointStateModuleReversalBasisReadback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : ℂ :=
  (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
    (((zeroOwnedJointStateModuleOccurrence
      observation nontrivial).root.2).reversalIntegralOrbit
        (delta scale)).snd

theorem jointStateModuleSelectedBasisReadback_eq_graph
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    jointStateModuleSelectedBasisReadback observation nontrivial scale =
      selectedGraphCharacterBasisReadback observation nontrivial scale := by
  rw [jointStateModuleSelectedBasisReadback,
    zeroOwnedJointStateModuleOccurrence_root_selectedOrbit,
    selectedIntegralGraphOrbit_delta]
  rfl

theorem jointStateModuleReversalBasisReadback_eq_graph
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    jointStateModuleReversalBasisReadback observation nontrivial scale =
      reversalGraphCharacterBasisReadback observation nontrivial scale := by
  rw [jointStateModuleReversalBasisReadback,
    zeroOwnedJointStateModuleOccurrence_root_reversalOrbit,
    reversalIntegralGraphOrbit_delta]
  rfl

def jointStateModuleSelectedEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  canonicalBasis.constr ℤ
    (jointStateModuleSelectedBasisReadback observation nontrivial)

def jointStateModuleReversalEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  canonicalBasis.constr ℤ
    (jointStateModuleReversalBasisReadback observation nontrivial)

@[simp] theorem jointStateModuleSelectedEvaluation_delta
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    jointStateModuleSelectedEvaluation observation nontrivial (delta scale) =
      jointStateModuleSelectedBasisReadback observation nontrivial scale := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

@[simp] theorem jointStateModuleReversalEvaluation_delta
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    jointStateModuleReversalEvaluation observation nontrivial (delta scale) =
      jointStateModuleReversalBasisReadback observation nontrivial scale := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

theorem jointStateModuleSelectedEvaluation_eq_graph
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    jointStateModuleSelectedEvaluation observation nontrivial =
      selectedGraphCharacterEvaluation observation nontrivial := by
  apply MonoidAlgebra.lhom_ext'
  intro scale
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale coefficient =
      coefficient • delta scale by simp [delta]]
  rw [map_smul, map_smul,
    jointStateModuleSelectedEvaluation_delta,
    selectedGraphCharacterEvaluation_delta,
    jointStateModuleSelectedBasisReadback_eq_graph]

theorem jointStateModuleReversalEvaluation_eq_graph
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    jointStateModuleReversalEvaluation observation nontrivial =
      reversalGraphCharacterEvaluation observation nontrivial := by
  apply MonoidAlgebra.lhom_ext'
  intro scale
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale coefficient =
      coefficient • delta scale by simp [delta]]
  rw [map_smul, map_smul,
    jointStateModuleReversalEvaluation_delta,
    reversalGraphCharacterEvaluation_delta,
    jointStateModuleReversalBasisReadback_eq_graph]

def jointStateModulePairEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] QRich.ClozelJPair where
  toFun value :=
    (jointStateModuleSelectedEvaluation observation nontrivial value,
      jointStateModuleReversalEvaluation observation nontrivial value)
  map_add' left right := by ext <;> simp
  map_smul' scalar value := by ext <;> exact map_smul _ _ _

def jointStateModuleZModTwoEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] QRich.ZModTwoCarrier :=
  (QRich.clozelJPairToZModTwo.toLinearMap.restrictScalars ℤ).comp
    (jointStateModulePairEvaluation observation nontrivial)

def jointStateModulePointFullRowHom
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    IntegralScaleCarrier →ₗ[ℤ]
      (((PointExtensionFunctor
          (mathlibZeroPoint observation.coordinate observation.mathlibZero)).obj
            PairDerivedScalarSingleOne) ⟶
        QRich.PointFullRowVerticalTotal
          (mathlibZeroPoint observation.coordinate observation.mathlibZero)
          stage) :=
  ((QRich.pointQRichZModTwoCombination
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage).restrictScalars ℤ).comp
    (jointStateModuleZModTwoEvaluation observation nontrivial)

def jointStateModulePointFullRowCycle
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    IntegralScaleCarrier →ₗ[ℤ]
      QRich.PointFullRowDegreeOneCycles
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage :=
  ((QRich.pointFullRowHomCycle
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage).restrictScalars ℤ).comp
    (jointStateModulePointFullRowHom observation nontrivial stage)

theorem jointStateModulePointFullRowCycle_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage)
    (value : IntegralScaleCarrier) :
    QRich.pointFullRowCycleCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (jointStateModulePointFullRowCycle
          observation nontrivial stage value) =
      -(quotientCoefficient row : ℂ) *
        (jointStateModuleSelectedEvaluation observation nontrivial value -
          jointStateModuleReversalEvaluation observation nontrivial value) := by
  change QRich.pointFullRowCycleCReadback
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage row
      (QRich.pointFullRowHomCycle
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage
        (jointStateModulePointFullRowHom
          observation nontrivial stage value)) = _
  rw [QRich.pointFullRowCycleCReadback, LinearMap.comp_apply,
    QRich.pointFullRowHomCycle_inclusion]
  change QRich.pointFullRowHomCReadback
      (mathlibZeroPoint observation.coordinate observation.mathlibZero)
      stage row
      (QRich.pointQRichZModTwoCombination
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage (jointStateModuleZModTwoEvaluation
          observation nontrivial value)) = _
  rw [QRich.pointQRichZModTwoCombination_readback]
  rfl

def jointStateModulePrimeCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) : ℂ :=
  jointStateModuleSelectedEvaluation observation nontrivial
      (delta (rowPrimeScaleUnit row)) -
    jointStateModuleReversalEvaluation observation nontrivial
      (delta (rowPrimeScaleUnit row))

theorem jointStateModulePrimeCurrent_eq_graph
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat} (row : FactorRow seedOccurrence.root stage) :
    jointStateModulePrimeCurrent observation nontrivial row =
      graphOrbitPrimeCurrent observation nontrivial row := by
  rw [jointStateModulePrimeCurrent, graphOrbitPrimeCurrent,
    jointStateModuleSelectedEvaluation_eq_graph,
    jointStateModuleReversalEvaluation_eq_graph]

theorem jointStateModulePrimeCurrent_fullRow_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    QRich.pointFullRowCycleCReadback
        (mathlibZeroPoint observation.coordinate observation.mathlibZero)
        stage row
        (jointStateModulePointFullRowCycle observation nontrivial stage
          (delta (rowPrimeScaleUnit row))) =
      -(quotientCoefficient row : ℂ) *
        jointStateModulePrimeCurrent observation nontrivial row := by
  exact jointStateModulePointFullRowCycle_readback
    observation nontrivial stage row (delta (rowPrimeScaleUnit row))

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
