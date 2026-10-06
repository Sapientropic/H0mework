import H0mework.Realization.Integral.GroupRingPairing
import H0mework.Arithmetic.RiemannRuntime.PairedOmegaJointRelationOccurrence

/-!
# Stage-zero integral boundary readback

The actual runtime scale produces the integral boundary between the identity
event and its translated successor.  The canonical Kronecker pairing detects
that boundary before any coherent or measurement projection.  Its selected
and reversal measurements are the already installed retained incidence, while
the full-joint evolved/source roles preserve the boundary and the incidence
role has zero integral projection.

The identity coefficient is exactly one, so no rational prime divides this
boundary and every prime residual class is nonzero.
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
namespace IntegralGraphJointAction

open Character.GlobalCoPoissonCurrent
open SourceGeneratedFaithfulIntegralFace
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentJointAction
open SourceGeneratedIntegralGroupRingPerfectPair
open ThetaJRoleRepresentation

noncomputable section

/-- Actual stage-zero scale used by the full-joint runtime occurrence. -/
abbrev stageZeroIntegralScale : Units NNReal :=
  stageSqrtScaleUnit 0

/-- Integral source-to-successor boundary at the runtime stage-zero scale. -/
def stageZeroIntegralBoundary : IntegralScaleCarrier :=
  delta 1 -
    (leftTranslation stageZeroIntegralScale).toLinearMap (delta 1)

theorem stageZeroIntegralBoundary_eq_delta_sub_delta :
    stageZeroIntegralBoundary =
      delta 1 - delta stageZeroIntegralScale := by
  simp [stageZeroIntegralBoundary]

theorem stageZeroIntegralScale_ne_one :
    stageZeroIntegralScale ≠ 1 := by
  intro scale_eq_one
  have square_eq := congrArg scaleSquare scale_eq_one
  rw [stageSqrtScaleUnit_square_eq_rootScale] at square_eq
  norm_num [scaleSquare, scaleValue,
    QRich.blockQRichSuccessorScale_eq_stage_add_three] at square_eq

/-- Every basis detector reads the literal two-term boundary coefficient. -/
theorem stageZeroIntegralBoundary_basisCoefficient (element : Units NNReal) :
    evaluation stageZeroIntegralBoundary (delta element) =
      (if element = 1 then 1 else 0) -
        (if element = stageZeroIntegralScale then 1 else 0) := by
  rw [evaluation_apply_delta,
    stageZeroIntegralBoundary_eq_delta_sub_delta]
  simp [delta, Finsupp.single_apply, eq_comm]

theorem stageZeroIntegralBoundary_identityCoefficient :
    evaluation stageZeroIntegralBoundary (delta 1) = 1 := by
  rw [stageZeroIntegralBoundary_basisCoefficient]
  simp [Ne.symm stageZeroIntegralScale_ne_one]

theorem stageZeroIntegralBoundary_scaleCoefficient :
    evaluation stageZeroIntegralBoundary
        (delta stageZeroIntegralScale) = -1 := by
  rw [stageZeroIntegralBoundary_basisCoefficient]
  simp [stageZeroIntegralScale_ne_one]

theorem stageZeroIntegralBoundary_ne_zero :
    stageZeroIntegralBoundary ≠ 0 := by
  intro boundary_zero
  have identityCoefficient := stageZeroIntegralBoundary_identityCoefficient
  rw [boundary_zero, map_zero] at identityCoefficient
  norm_num at identityCoefficient

/-- Every prime sees the same nondivisible boundary, witnessed by its identity
coefficient `1`. -/
theorem stageZeroIntegralBoundary_not_prime_divisible (prime : Nat.Primes) :
    ¬ ∃ divided : IntegralScaleCarrier,
      prime.1 • divided = stageZeroIntegralBoundary := by
  rintro ⟨divided, equality⟩
  have atIdentity := congrArg
    (fun value : IntegralScaleCarrier => value.coeff (1 : Units NNReal)) equality
  simp only [MonoidAlgebra.coeff_smul_apply] at atIdentity
  have boundaryCoefficient : stageZeroIntegralBoundary.coeff 1 = 1 := by
    simpa only [evaluation_apply_delta] using
      stageZeroIntegralBoundary_identityCoefficient
  rw [boundaryCoefficient] at atIdentity
  change (prime.1 : ℤ) * divided.coeff 1 = 1 at atIdentity
  have dividesOne : (prime.1 : ℤ) ∣ 1 :=
    ⟨divided.coeff 1, atIdentity.symm⟩
  have unit : IsUnit (prime.1 : ℤ) :=
    (isUnit_iff_dvd_one).2 dividesOne
  rcases Int.isUnit_iff.mp unit with primeOne | primeNegOne
  · have primeNatOne : prime.1 = 1 := by exact_mod_cast primeOne
    exact prime.property.ne_one primeNatOne
  · have primePositive : (0 : ℤ) < prime.1 := by
      exact_mod_cast prime.property.pos
    omega

def stageZeroIntegralBoundaryPrimeResidualCoordinate (prime : Nat.Primes) :
    PrimeResidualCoordinate (L := IntegralScaleCarrier) prime where
  representative := stageZeroIntegralBoundary
  not_divisible := stageZeroIntegralBoundary_not_prime_divisible prime

theorem stageZeroIntegralBoundary_residualClass_ne_zero
    (prime : Nat.Primes) :
    residualClass (L := IntegralScaleCarrier) prime
        stageZeroIntegralBoundary ≠ 0 :=
  (stageZeroIntegralBoundaryPrimeResidualCoordinate prime).class_ne_zero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial :
  ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))

theorem selectedStageZeroIntegralBoundary_measurement :
    selectedGraphMeasurementRead observation nontrivial
        stageZeroIntegralBoundary =
      (selectedOwnerFreeCouplingResidual observation nontrivial
        stageZeroIntegralScale (delta 1)).snd := by
  rw [stageZeroIntegralBoundary, map_sub]
  rw [selectedOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

theorem reversalStageZeroIntegralBoundary_measurement :
    reversalGraphMeasurementRead observation nontrivial
        stageZeroIntegralBoundary =
      (reversalOwnerFreeCouplingResidual observation nontrivial
        stageZeroIntegralScale (delta 1)).snd := by
  rw [stageZeroIntegralBoundary, map_sub]
  rw [reversalOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

/-- The paired integral boundary is measured as the existing raw incidence. -/
theorem pairedStageZeroIntegralBoundary_measurement :
    pairedGraphMeasurementRead observation nontrivial
        stageZeroIntegralBoundary =
      pairedOmegaMeasurementResidual observation nontrivial
        stageZeroIntegralScale := by
  rw [pairedOmegaMeasurementResidual_eq]
  apply Prod.ext
  · exact selectedStageZeroIntegralBoundary_measurement
      observation nontrivial
  · exact reversalStageZeroIntegralBoundary_measurement
      observation nontrivial

/-- The same paired measurement is the installed stage-zero retained effect. -/
theorem pairedStageZeroIntegralBoundary_measurement_eq_installedRetained :
    pairedGraphMeasurementRead observation nontrivial
        stageZeroIntegralBoundary =
      (installedRuntimeEffectValueAt observation nontrivial 0).retained := by
  rw [pairedStageZeroIntegralBoundary_measurement]
  exact (installedRuntimeEffectValueAt_retained_eq_jointIncidence
    observation nontrivial 0).symm

/-- Integral coordinate exposed by one full-joint relation role. -/
def stageZeroJointRoleIntegral (role : RuntimeJointRelationRole) :
    IntegralScaleCarrier :=
  runtimeJointIntegralFace
    (runtimeJointRelationGeneratorValue observation nontrivial (0, role))

theorem evolvedRole_preserves_stageZeroIntegralBoundary :
    delta 1 - stageZeroJointRoleIntegral observation nontrivial
        .evolvedSeed = stageZeroIntegralBoundary := by
  rfl

theorem sourceActionRole_preserves_stageZeroIntegralBoundary :
    delta 1 - stageZeroJointRoleIntegral observation nontrivial
        .sourceActionSeed = stageZeroIntegralBoundary := by
  rfl

/-- The new dedicated role exposes the boundary itself, not only its scalar
measurement shadow. -/
theorem sourceBoundaryRole_integral_eq_stageZeroIntegralBoundary :
    stageZeroJointRoleIntegral observation nontrivial .sourceBoundary =
      stageZeroIntegralBoundary := by
  rfl

theorem sourceBoundaryRole_measurement_eq_installedRetained :
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (0, .sourceBoundary)) =
      (installedRuntimeEffectValueAt observation nontrivial 0).retained :=
  runtimeJointSourceBoundary_measurement_eq_installedRetained
    observation nontrivial 0

/-- The joint incidence is deliberately vertical: its integral projection is
zero even though the source-to-successor boundary above is nonzero. -/
theorem incidenceRole_integral_eq_zero :
    stageZeroJointRoleIntegral observation nontrivial .incidence = 0 := by
  change (runtimeJointInputAt observation nontrivial 0).integralFace
    ((runtimeJointInputAt observation nontrivial 0).incidenceResidual
      (delta 1)) = 0
  exact Input.incidenceResidual_integralFace _ _

end


end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
