import H0mework.Versions.Y.Arithmetic.PrimeLeakage.AllPlaceWeilRuntimeRoot

/-!
# Quadratic read of the installed runtime phase

The runtime `phase` is the already generated whole effect.  Its linear
conservation law is quadraticized before any local restriction.  The
remainder is generated forward from the centered trace and its cross term;
it is not defined by subtracting a desired finite contribution.
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
namespace Runtime
namespace Quadratic

open CanonicalUnitArithmeticRoot
open Character
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open Complex
open Material
open Root
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.PrimePower.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Source
open scoped InnerProductSpace

noncomputable section

def pairSkew (value : QRich.ClozelJPair) : ℂ :=
  value.2 - value.1

def normalizedPairSkew
    (scale : Units NNReal) (value : QRich.ClozelJPair) : ℂ :=
  (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
    pairSkew value

def runtimeFaceRetainedAmplitude
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) : ℂ :=
  normalizedPairSkew (stageSqrtScaleUnit face.stage)
    (runtimeJointBalanceFace face.retained)

def runtimeFacePhaseAmplitude
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) : ℂ :=
  normalizedPairSkew (stageSqrtScaleUnit face.stage)
    (runtimeJointBalanceFace face.phaseWhole)

def runtimeFaceCenteredAmplitude
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) : ℂ :=
  normalizedPairSkew (stageSqrtScaleUnit face.stage)
    (runtimeJointBalanceFace face.centeredTrace)

theorem runtimeFacePhaseAmplitude_eq_retained_add_centered
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    runtimeFacePhaseAmplitude face =
      runtimeFaceRetainedAmplitude face +
        runtimeFaceCenteredAmplitude face := by
  rw [runtimeFacePhaseAmplitude, runtimeFaceRetainedAmplitude,
    runtimeFaceCenteredAmplitude, face.phaseWhole_eq,
    face.retained_eq, face.centeredTrace_eq]
  change normalizedPairSkew (stageSqrtScaleUnit face.stage)
      (installedRuntimeEffectValueAt
        observation nontrivial face.stage).phase =
    normalizedPairSkew (stageSqrtScaleUnit face.stage)
        (installedRuntimeEffectValueAt
          observation nontrivial face.stage).retained +
      normalizedPairSkew (stageSqrtScaleUnit face.stage)
        (installedRuntimeEffectValueAt
          observation nontrivial face.stage).centeredTrace
  rw [installedRuntimeEffectValueAt_conservation]
  simp [normalizedPairSkew, pairSkew]
  ring

def runtimeFaceEulerWeight
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (prime : Nat.Primes) (exponent : Nat) : ℝ :=
  face.eulerCoefficients (thetaDistributionPrimePower prime exponent)

def primePowerRuntimeWholeQuadratic
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (prime : Nat.Primes) (exponent : Nat) : ℝ :=
  runtimeFaceEulerWeight face prime exponent *
    ‖runtimeFacePhaseAmplitude face‖ ^ 2

def primePowerRuntimeRetainedQuadratic
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (prime : Nat.Primes) (exponent : Nat) : ℝ :=
  runtimeFaceEulerWeight face prime exponent *
    ‖runtimeFaceRetainedAmplitude face‖ ^ 2

/-- The centered remainder is a generated polarization coordinate. -/
def centeredRuntimeQuadraticResidual
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (prime : Nat.Primes) (exponent : Nat) : ℝ :=
  runtimeFaceEulerWeight face prime exponent *
    (2 * RCLike.re (inner ℂ (runtimeFaceRetainedAmplitude face)
        (runtimeFaceCenteredAmplitude face)) +
      ‖runtimeFaceCenteredAmplitude face‖ ^ 2)

theorem primePowerRuntimeWholeQuadratic_decomposition
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (prime : Nat.Primes) (exponent : Nat) :
    primePowerRuntimeWholeQuadratic face prime exponent =
      primePowerRuntimeRetainedQuadratic face prime exponent +
        centeredRuntimeQuadraticResidual face prime exponent := by
  rw [primePowerRuntimeWholeQuadratic,
    primePowerRuntimeRetainedQuadratic,
    centeredRuntimeQuadraticResidual,
    runtimeFacePhaseAmplitude_eq_retained_add_centered,
    norm_add_sq (𝕜 := ℂ)]
  ring_nf

end
end Quadratic
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
