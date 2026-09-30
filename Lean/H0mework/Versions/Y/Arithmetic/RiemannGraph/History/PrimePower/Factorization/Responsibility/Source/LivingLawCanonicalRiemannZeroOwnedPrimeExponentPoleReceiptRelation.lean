import H0mework.Versions.Y.Arithmetic.PrimeLeakage.ZeroOwnedPrimePowerWeilBoundaryOccurrence
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.LivingLawCanonicalRiemannPrimeExponentPoleReceiptRelation
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.Measurement.LivingLawCanonicalRiemannRuntimeMuntzPrimePowerConductorPairReadback

/-!
# Zero-owned source face of one prime-exponent receipt relation

The actual prime-power boundary payload already stores both the unnormalized
Mellin boundary state and its density-normalized Euler-character boundary.
They are kept as distinct sibling coordinates.  The unnormalized boundary,
the Riesz energy, and the vertical trace specialize at the exact root to the
three fields of the installed receipt relation.

No equality between the normalized and unnormalized boundaries is assumed:
their affine half-density conversion is generated from the same payload.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Source

open Character.GlobalCoPoissonCurrent
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open PrimePower.Occurrence
open PrimePower.Source
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
open SourceGeneratedPositiveRealCharacter
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence

noncomputable section

def zeroOwnedReceiptSelectedState
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) : JointGraphTarget :=
  source.1.1.2.selectedSpectralState

/-- Unnormalized Mellin boundary read from the actual joint boundary state. -/
def zeroOwnedReceiptRawBoundary
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) : QRich.ClozelJPair :=
  runtimeJointMeasurementFace source.2.boundaryState

/-- Density-normalized Euler boundary stored by the same payload.  It is
`1 - character`, not the character target or the raw Mellin boundary. -/
def zeroOwnedReceiptNormalizedBoundary
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) : QRich.ClozelJPair :=
  (source.2.selectedRead, source.2.reversalRead)

def zeroOwnedReceiptRieszEnergy
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) : QRich.ClozelJPair :=
  (inner ℂ (zeroOwnedReceiptSelectedState source).fst
      (selectedPrimeExponentPolePositiveEnergyMap observation nontrivial
        (factorizationBoundaryValue ⟨prime, ⟨exponent, positive⟩⟩)),
    inner ℂ source.1.1.2.reversalSpectralState.fst
      (reversalPrimeExponentPolePositiveEnergyMap observation nontrivial
        (factorizationBoundaryValue ⟨prime, ⟨exponent, positive⟩⟩)))

def zeroOwnedReceiptVerticalTrace
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) : QRich.ClozelJPair :=
  (inner ℂ (zeroOwnedReceiptSelectedState source).snd
      (zeroOwnedReceiptRawBoundary source).1,
    inner ℂ source.1.1.2.reversalSpectralState.snd
      (zeroOwnedReceiptRawBoundary source).2)

def zeroOwnedReceiptRoleValue
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) :
    PrimeExponentPoleReceiptRole → QRich.ClozelJPair
  | .retained => zeroOwnedReceiptRawBoundary source
  | .energy => zeroOwnedReceiptRieszEnergy source
  | .vertical => zeroOwnedReceiptVerticalTrace source

theorem zeroOwnedReceiptRawBoundary_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    zeroOwnedReceiptRawBoundary
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root =
      pairedPrimeExponentPoleBoundaryMellin observation nontrivial
        ⟨prime, ⟨exponent, positive⟩⟩ := by
  change runtimeJointMeasurementFace
      (primePowerBoundaryStateFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).root
          prime exponent) = _
  rw [primePowerBoundaryStateFromSource_root_eq]
  unfold primePowerBoundaryState
  rw [runtimeJointSourceBoundary_measurement_eq_installedRetained,
    pairedPrimeExponentPoleBoundaryMellin_eq_installedRetained,
    ← installedRuntimeEffectValueAt_retained_eq_jointIncidence]

theorem zeroOwnedReceiptNormalizedBoundary_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    zeroOwnedReceiptNormalizedBoundary
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root =
      pairedOne - normalizedRetainedPair observation nontrivial
        (primePowerUnit prime exponent) := by
  apply Prod.ext
  · change (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        prime exponent positive).root.2.selectedRead = _
    rw [(zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).root.2.selectedRead_eq]
    change primePowerSelectedCharacterReadFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).root
        prime exponent = _
    rw [primePowerSelectedCharacterReadFromSource_root_eq]
    change 1 - complexPowerCharacter observation.coordinate
        (primePowerUnit prime exponent) =
      1 - (normalizedRetainedPair observation nontrivial
        (primePowerUnit prime exponent)).1
    rw [normalizedRetainedPair_fst_eq_complexPower]
    all_goals exact positive
  · change (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        prime exponent positive).root.2.reversalRead = _
    rw [(zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
      prime exponent positive).root.2.reversalRead_eq]
    change primePowerReversalCharacterReadFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial).root
        prime exponent = _
    rw [primePowerReversalCharacterReadFromSource_root_eq]
    change 1 - complexPowerCharacter
        (CanonicalUnitArithmeticCoordinateProjectionObstruction.coordinateReversal
          observation.coordinate) (primePowerUnit prime exponent) =
      1 - (normalizedRetainedPair observation nontrivial
        (primePowerUnit prime exponent)).2
    rw [normalizedRetainedPair_snd_eq_complexPower]
    all_goals exact positive

/-- Exact affine half-density conversion between the two source-owned
boundary coordinates. -/
theorem zeroOwnedReceipt_halfDensity_normalization_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    zeroOwnedReceiptNormalizedBoundary
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root =
      pairedOne -
        (positiveMellinQuarterDilationWeight
          (scaleSquare (primePowerUnit prime exponent)))⁻¹ •
          (pairedOne -
            zeroOwnedReceiptRawBoundary
              (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
                prime exponent positive).root) := by
  rw [zeroOwnedReceiptNormalizedBoundary_root observation nontrivial
      prime exponent positive,
    normalizedRetainedPair,
    zeroOwnedReceiptRawBoundary_root observation nontrivial
      prime exponent positive,
    pairedPrimeExponentPoleBoundaryMellin_eq_incidence]

theorem zeroOwnedReceiptRieszEnergy_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    zeroOwnedReceiptRieszEnergy
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root =
      pairedPrimeExponentPoleBoundaryRieszEnergy observation nontrivial
        ⟨prime, ⟨exponent, positive⟩⟩ := by
  rfl

theorem zeroOwnedReceiptVerticalTrace_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    zeroOwnedReceiptVerticalTrace
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root =
      pairedPrimeExponentPoleBoundaryVerticalTrace observation nontrivial
        ⟨prime, ⟨exponent, positive⟩⟩ := by
  have retainedEq := zeroOwnedReceiptRawBoundary_root observation nontrivial
    prime exponent positive
  apply Prod.ext
  · change inner ℂ
        (zeroOwnedReceiptSelectedState
          (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
            prime exponent positive).root).snd
        (zeroOwnedReceiptRawBoundary
          (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
            prime exponent positive).root).1 =
      inner ℂ (selectedPrimeExponentPoleRootSpectralState
          observation nontrivial).snd
        (selectedPrimeExponentPoleMellinMap observation nontrivial
          (factorizationBoundaryValue ⟨prime, ⟨exponent, positive⟩⟩))
    rw [retainedEq]
    rfl
  · change inner ℂ
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root.1.1.2.reversalSpectralState.snd
        (zeroOwnedReceiptRawBoundary
          (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
            prime exponent positive).root).2 =
      inner ℂ (reversalPrimeExponentPoleRootSpectralState
          observation nontrivial).snd
        (reversalPrimeExponentPoleMellinMap observation nontrivial
          (factorizationBoundaryValue ⟨prime, ⟨exponent, positive⟩⟩))
    rw [retainedEq]
    rfl

theorem zeroOwnedReceiptRelation_root
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    zeroOwnedReceiptRoleValue
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root .retained =
      zeroOwnedReceiptRoleValue
          (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
            prime exponent positive).root .energy +
        zeroOwnedReceiptRoleValue
          (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
            prime exponent positive).root .vertical := by
  change zeroOwnedReceiptRawBoundary
      (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        prime exponent positive).root =
    zeroOwnedReceiptRieszEnergy
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root +
      zeroOwnedReceiptVerticalTrace
        (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
          prime exponent positive).root
  rw [zeroOwnedReceiptRawBoundary_root observation nontrivial
      prime exponent positive,
    zeroOwnedReceiptRieszEnergy_root observation nontrivial
      prime exponent positive,
    zeroOwnedReceiptVerticalTrace_root observation nontrivial
      prime exponent positive]
  exact pairedPrimeExponentPoleBoundaryMellin_verticalSplit
    observation nontrivial ⟨prime, ⟨exponent, positive⟩⟩

/-- Generated coordinate face over the entire source occurrence.  The
relation itself is asserted only at the exact root, where its Riesz readback
has been proved; arbitrary branches are not silently upgraded. -/
structure GeneratedZeroOwnedReceiptCoordinateFaceAt
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) where
  private mk ::
  roleValue : PrimeExponentPoleReceiptRole → QRich.ClozelJPair
  normalizedBoundary : QRich.ClozelJPair
  roleValue_eq : roleValue = zeroOwnedReceiptRoleValue source
  normalizedBoundary_eq : normalizedBoundary =
    zeroOwnedReceiptNormalizedBoundary source

def generateZeroOwnedReceiptCoordinateFace
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {prime : Nat.Primes} {exponent : Nat} {positive : 0 < exponent}
    (source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      prime exponent positive) :
    GeneratedZeroOwnedReceiptCoordinateFaceAt source :=
  ⟨zeroOwnedReceiptRoleValue source,
    zeroOwnedReceiptNormalizedBoundary source, rfl, rfl⟩

abbrev ZeroOwnedReceiptCoordinatePayload
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :=
  Σ source : ZeroOwnedPrimePowerWeilBoundaryPayload observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor),
    GeneratedZeroOwnedReceiptCoordinateFaceAt source

def zeroOwnedReceiptCoordinateOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    RootedAccountedUnfolding
      (ZeroOwnedReceiptCoordinatePayload observation nontrivial cursor) :=
  (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
    (scheduledPrime cursor) (scheduledExponent cursor)
      (scheduledExponent_positive cursor)).map fun source =>
        ⟨source, generateZeroOwnedReceiptCoordinateFace source⟩

theorem zeroOwnedReceiptCoordinateOccurrence_projects_boundary
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    (zeroOwnedReceiptCoordinateOccurrence observation nontrivial cursor).map
        Sigma.fst =
      zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        (scheduledPrime cursor) (scheduledExponent cursor)
          (scheduledExponent_positive cursor) := by
  rw [zeroOwnedReceiptCoordinateOccurrence, RootedAccountedUnfolding.map_map]
  change (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
    (scheduledPrime cursor) (scheduledExponent cursor)
      (scheduledExponent_positive cursor)).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem zeroOwnedReceiptCoordinateOccurrence_projects_allPrime
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    ((zeroOwnedReceiptCoordinateOccurrence observation nontrivial cursor).map
        Sigma.fst).map Sigma.fst =
      zeroOwnedAllPrimeWeilQuadraticOccurrence observation nontrivial := by
  rw [zeroOwnedReceiptCoordinateOccurrence_projects_boundary,
    zeroOwnedPrimePowerWeilBoundaryOccurrence_projects]

theorem zeroOwnedReceiptCoordinateOccurrence_root_specializes
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    (zeroOwnedReceiptCoordinateOccurrence observation nontrivial
        cursor).root.2.roleValue role =
      receiptRoleValue observation nontrivial cursor role := by
  change zeroOwnedReceiptRoleValue
      (zeroOwnedPrimePowerWeilBoundaryOccurrence observation nontrivial
        (scheduledPrime cursor) (scheduledExponent cursor)
          (scheduledExponent_positive cursor)).root role = _
  cases role
  · exact zeroOwnedReceiptRawBoundary_root observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor)
  · exact zeroOwnedReceiptRieszEnergy_root observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor)
  · exact zeroOwnedReceiptVerticalTrace_root observation nontrivial
      (scheduledPrime cursor) (scheduledExponent cursor)
        (scheduledExponent_positive cursor)

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Source
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
