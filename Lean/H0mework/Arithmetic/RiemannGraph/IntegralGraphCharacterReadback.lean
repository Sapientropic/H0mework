import H0mework.Arithmetic.RiemannGraph.IntegralGraphOrbit

/-!
# Character and detector readback from the integral graph orbit

Quarter-density normalization of the graph measurement coordinate recovers
the already generated full integral character.  Prime and Archimedean
currents are therefore literal readouts of the same graph orbit and feed the
existing q-rich detector without a comparator.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ThetaJRoleRepresentation
open SourceGeneratedIntegralCharacterGroupRing

noncomputable section

/-- Density-normalized measurement of one selected graph basis event. -/
def selectedGraphCharacterBasisReadback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : ℂ :=
  (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
    (selectedGraphOrbitBasis observation nontrivial scale).snd

def reversalGraphCharacterBasisReadback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) : ℂ :=
  (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
    (reversalGraphOrbitBasis observation nontrivial scale).snd

theorem selectedGraphCharacterBasisReadback_eq_Riesz
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    selectedGraphCharacterBasisReadback observation nontrivial scale =
      sourceSelectedRieszFullCharacterValue observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale := by
  unfold selectedGraphCharacterBasisReadback
    sourceSelectedRieszFullCharacterValue selectedNormalizedDilationTrace
    selectedDilationTrace selectedGraphOrbitBasis
  rw [occurrence_selectedRieszTrace_eq_functional]
  rfl

theorem reversalGraphCharacterBasisReadback_eq_Riesz
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    reversalGraphCharacterBasisReadback observation nontrivial scale =
      sourceReversalRieszFullCharacterValue observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale := by
  unfold reversalGraphCharacterBasisReadback
    sourceReversalRieszFullCharacterValue reversalNormalizedDilationTrace
    reversalDilationTrace reversalGraphOrbitBasis
  rw [occurrence_reversalRieszTrace_eq_functional]
  rfl

def selectedGraphCharacterEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  canonicalBasis.constr ℤ
    (selectedGraphCharacterBasisReadback observation nontrivial)

def reversalGraphCharacterEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  canonicalBasis.constr ℤ
    (reversalGraphCharacterBasisReadback observation nontrivial)

@[simp] theorem selectedGraphCharacterEvaluation_delta
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    selectedGraphCharacterEvaluation observation nontrivial (delta scale) =
      selectedGraphCharacterBasisReadback observation nontrivial scale := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

@[simp] theorem reversalGraphCharacterEvaluation_delta
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    reversalGraphCharacterEvaluation observation nontrivial (delta scale) =
      reversalGraphCharacterBasisReadback observation nontrivial scale := by
  rw [← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

theorem selectedGraphCharacterEvaluation_eq_RieszFullEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedGraphCharacterEvaluation observation nontrivial =
      selectedRieszFullEvaluation observation nontrivial := by
  apply MonoidAlgebra.lhom_ext'
  intro scale
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale coefficient =
      coefficient • delta scale by simp [delta]]
  rw [map_smul, map_smul]
  rw [selectedGraphCharacterEvaluation_delta,
    selectedRieszFullEvaluation_delta,
    selectedGraphCharacterBasisReadback_eq_Riesz]

theorem reversalGraphCharacterEvaluation_eq_RieszFullEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalGraphCharacterEvaluation observation nontrivial =
      reversalRieszFullEvaluation observation nontrivial := by
  apply MonoidAlgebra.lhom_ext'
  intro scale
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale coefficient =
      coefficient • delta scale by simp [delta]]
  rw [map_smul, map_smul]
  rw [reversalGraphCharacterEvaluation_delta,
    reversalRieszFullEvaluation_delta,
    reversalGraphCharacterBasisReadback_eq_Riesz]

theorem selectedGraphCharacterEvaluation_eq_integralOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedGraphCharacterEvaluation observation nontrivial =
      (zeroOwnedIntegralCharacterOccurrence observation).root.2.1 := by
  rw [selectedGraphCharacterEvaluation_eq_RieszFullEvaluation,
    selectedRieszFullEvaluation_eq_sourceCharacter]
  rfl

theorem reversalGraphCharacterEvaluation_eq_integralOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalGraphCharacterEvaluation observation nontrivial =
      (zeroOwnedIntegralCharacterOccurrence observation).root.2.2 := by
  rw [reversalGraphCharacterEvaluation_eq_RieszFullEvaluation,
    reversalRieszFullEvaluation_eq_sourceCharacter]
  rfl

/-- Prime current read from the two sibling graph faces. -/
def graphOrbitPrimeCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat}
    (row : CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.FactorRow
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence.root
      stage) : ℂ :=
  selectedGraphCharacterEvaluation observation nontrivial
      (delta (rowPrimeScaleUnit row)) -
    reversalGraphCharacterEvaluation observation nontrivial
      (delta (rowPrimeScaleUnit row))

theorem graphOrbitPrimeCurrent_eq_RieszFluxResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {stage : Nat}
    (row : CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.FactorRow
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence.root
      stage) :
    graphOrbitPrimeCurrent observation nontrivial row =
      primeRieszFluxResidual observation nontrivial row := by
  rw [graphOrbitPrimeCurrent,
    selectedGraphCharacterEvaluation_eq_integralOccurrence,
    reversalGraphCharacterEvaluation_eq_integralOccurrence]
  exact groupRingPrimeCurrent_eq_primeRieszFluxResidual
    observation nontrivial row

theorem graphOrbitPrimeCurrent_fullRow_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat)
    (row : CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.FactorRow
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence.root
      stage) :
    QRich.pointFullRowCycleCReadback
        (CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine.mathlibZeroPoint
          observation.coordinate observation.mathlibZero)
        stage row
        (zeroIntegralCharacterPointFullRowCycle observation stage
          (delta (rowPrimeScaleUnit row))) =
      -(CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier.quotientCoefficient
          row : ℂ) * graphOrbitPrimeCurrent observation nontrivial row := by
  rw [graphOrbitPrimeCurrent_eq_RieszFluxResidual]
  exact primeRieszFluxResidual_fullRow_readback
    observation nontrivial stage row

/-- Archimedean radial current from the same graph measurement faces. -/
def graphOrbitRadialCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℝ :=
  ‖selectedGraphCharacterEvaluation observation nontrivial
      (delta (stageSqrtScaleUnit stage))‖ -
    ‖reversalGraphCharacterEvaluation observation nontrivial
      (delta (stageSqrtScaleUnit stage))‖

theorem graphOrbitRadialCurrent_eq_RieszFluxResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    graphOrbitRadialCurrent observation nontrivial stage =
      radialRieszFluxResidual observation nontrivial stage := by
  rw [graphOrbitRadialCurrent,
    selectedGraphCharacterEvaluation_eq_integralOccurrence,
    reversalGraphCharacterEvaluation_eq_integralOccurrence]
  exact groupRingRadialCurrent_eq_radialRieszFluxResidual
    observation nontrivial stage

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
