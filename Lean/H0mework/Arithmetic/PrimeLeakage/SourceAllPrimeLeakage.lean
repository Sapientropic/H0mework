import H0mework.Arithmetic.PrimeLeakage.EulerWeightedAllPrimeLeakage
import H0mework.Arithmetic.RiemannGraph.ZeroJointStateModuleOccurrence

/-!
# Source-derived all-prime leakage

The selected and reversal all-prime characters are reconstructed from the
integral graph orbits stored in one joint-state payload.  Their primewise
difference, and hence the Euler-weighted quadratic, therefore consume the
actual source payload instead of adjoining an already completed leakage face.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Source

open ActionCofiber.RawEffect.AllPrimeCofinal
open ActionCofiber.RawEffect.AllPrimeLeakage
open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open EulerDiagonal
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation

noncomputable section

def selectedGraphCharacterEvaluationFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  canonicalBasis.constr ℤ fun scale =>
    (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
      (source.2.selectedIntegralOrbit (delta scale)).snd

def reversalGraphCharacterEvaluationFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  canonicalBasis.constr ℤ fun scale =>
    (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
      (source.2.reversalIntegralOrbit (delta scale)).snd

@[simp] theorem selectedGraphCharacterEvaluationFromSource_delta
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial)
    (scale : Units NNReal) :
    selectedGraphCharacterEvaluationFromSource source (delta scale) =
      (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
        (source.2.selectedIntegralOrbit (delta scale)).snd := by
  rw [selectedGraphCharacterEvaluationFromSource,
    ← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

@[simp] theorem reversalGraphCharacterEvaluationFromSource_delta
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial)
    (scale : Units NNReal) :
    reversalGraphCharacterEvaluationFromSource source (delta scale) =
      (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
        (source.2.reversalIntegralOrbit (delta scale)).snd := by
  rw [reversalGraphCharacterEvaluationFromSource,
    ← canonicalBasis_apply scale]
  exact canonicalBasis.constr_basis ℤ _ scale

theorem selectedGraphCharacterEvaluationFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedGraphCharacterEvaluationFromSource
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root =
      selectedGraphCharacterEvaluation observation nontrivial := by
  apply MonoidAlgebra.lhom_ext'
  intro scale
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale coefficient =
      coefficient • delta scale by simp [delta]]
  rw [map_smul, map_smul]
  apply congrArg (fun value : ℂ => coefficient • value)
  rw [selectedGraphCharacterEvaluationFromSource_delta,
    selectedGraphCharacterEvaluation_delta]
  simp [selectedGraphCharacterBasisReadback]

theorem reversalGraphCharacterEvaluationFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalGraphCharacterEvaluationFromSource
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root =
      reversalGraphCharacterEvaluation observation nontrivial := by
  apply MonoidAlgebra.lhom_ext'
  intro scale
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale coefficient =
      coefficient • delta scale by simp [delta]]
  rw [map_smul, map_smul]
  apply congrArg (fun value : ℂ => coefficient • value)
  rw [reversalGraphCharacterEvaluationFromSource_delta,
    reversalGraphCharacterEvaluation_delta]
  simp [reversalGraphCharacterBasisReadback]

def allPrimeSelectedCharacterMapFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    AllPrimeCurrent →ₗ[ℤ] ℂ :=
  (selectedGraphCharacterEvaluationFromSource source).comp
    allPrimeRawEffectMap

def allPrimeReversalCharacterMapFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    AllPrimeCurrent →ₗ[ℤ] ℂ :=
  (reversalGraphCharacterEvaluationFromSource source).comp
    allPrimeRawEffectMap

theorem allPrimeSelectedCharacterMapFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    allPrimeSelectedCharacterMapFromSource
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root =
      allPrimeSelectedCharacterMap observation nontrivial := by
  rw [allPrimeSelectedCharacterMapFromSource,
    allPrimeSelectedCharacterMap,
    selectedGraphCharacterEvaluationFromSource_root_eq]

theorem allPrimeReversalCharacterMapFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    allPrimeReversalCharacterMapFromSource
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root =
      allPrimeReversalCharacterMap observation nontrivial := by
  rw [allPrimeReversalCharacterMapFromSource,
    allPrimeReversalCharacterMap,
    reversalGraphCharacterEvaluationFromSource_root_eq]

def primeCharacterLeakageFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial)
    (prime : Nat.Primes) : ℂ :=
  allPrimeReversalCharacterMapFromSource source (Finsupp.single prime 1) -
    allPrimeSelectedCharacterMapFromSource source (Finsupp.single prime 1)

theorem primeCharacterLeakageFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) :
    primeCharacterLeakageFromSource
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root prime =
      generatedPrimeCharacterLeakage observation prime := by
  rw [primeCharacterLeakageFromSource,
    allPrimeSelectedCharacterMapFromSource_root_eq,
    allPrimeReversalCharacterMapFromSource_root_eq]
  exact (generatedPrimeCharacterLeakage_eq_characterDifference
    observation nontrivial prime).symm

def allPrimeCharacterLeakageMapFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial) :
    AllPrimeCurrent →ₗ[ℤ] PrimeLeakageCarrier :=
  (Finsupp.liftAddHom fun prime =>
    AddMonoidHom.flip (smulAddHom ℤ PrimeLeakageCarrier)
      (Finsupp.single prime
        (primeCharacterLeakageFromSource source prime))).toIntLinearMap

@[simp] theorem allPrimeCharacterLeakageMapFromSource_single
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial)
    (prime : Nat.Primes) (coefficient : ℤ) :
    allPrimeCharacterLeakageMapFromSource source
        (Finsupp.single prime coefficient) =
      coefficient • Finsupp.single prime
        (primeCharacterLeakageFromSource source prime) := by
  simp [allPrimeCharacterLeakageMapFromSource]

theorem allPrimeCharacterLeakageMapFromSource_coordinate
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (source : ZeroOwnedJointStateModulePayload observation nontrivial)
    (current : AllPrimeCurrent) (prime : Nat.Primes) :
    allPrimeCharacterLeakageMapFromSource source current prime =
      (current prime : ℂ) * primeCharacterLeakageFromSource source prime := by
  classical
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right leftHypothesis rightHypothesis =>
      rw [map_add, Finsupp.add_apply, Finsupp.add_apply,
        leftHypothesis, rightHypothesis]
      push_cast
      ring
  | single other coefficient =>
      rw [allPrimeCharacterLeakageMapFromSource_single]
      by_cases other_eq : other = prime
      · subst other
        simp
      · simp [other_eq]

theorem allPrimeCharacterLeakageMapFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    allPrimeCharacterLeakageMapFromSource
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root =
      allPrimeCharacterLeakageMap observation := by
  apply LinearMap.ext
  intro current
  ext prime
  rw [allPrimeCharacterLeakageMapFromSource_coordinate,
    allPrimeCharacterLeakageMap_coordinate,
    primeCharacterLeakageFromSource_root_eq]

def eulerWeightedLeakageEnergyFromSource
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {owner : CanonicalArithmeticState.AllPlaceEulerLog.GlobalGermOwner}
    (eulerFace : GeneratedEulerLogFaceAt owner)
    (source : ZeroOwnedJointStateModulePayload observation nontrivial)
    (current : AllPrimeCurrent) : ℝ :=
  (allPrimeCharacterLeakageMapFromSource source current).sum
    fun prime value => eulerFace.coefficients prime * ‖value‖ ^ 2

theorem eulerWeightedLeakageEnergyFromSource_root_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {owner : CanonicalArithmeticState.AllPlaceEulerLog.GlobalGermOwner}
    (eulerFace : GeneratedEulerLogFaceAt owner)
    (current : AllPrimeCurrent) :
    eulerWeightedLeakageEnergyFromSource eulerFace
        (zeroOwnedJointStateModuleOccurrence observation nontrivial).root
        current =
      generatedEulerFaceWeightedLeakageEnergy
        eulerFace observation current := by
  unfold eulerWeightedLeakageEnergyFromSource
    generatedEulerFaceWeightedLeakageEnergy
  rw [allPrimeCharacterLeakageMapFromSource_root_eq]

end
end Source
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
