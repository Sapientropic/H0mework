import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaJointRelationCoverage
import H0mework.Versions.Y.Arithmetic.RiemannGraph.StageZeroIntegralBoundaryReadback
import H0mework.Versions.Y.Arithmetic.RiemannGraph.ExpandingRieszClosedRangeAdmission

/-!
# Quarter-scale runtime readback

The stage-zero quarter-scale rows installed in the fixed-root history are the
actual integral source boundary and paired Riesz incidence.  The boundary is
nonzero in every prime residual quotient.  Off center, the occurrence-selected
incidence is internal to the already generated topological orbit closure, so
the corresponding external defect is zero.  No finite-range lift or
separator-zero premise is introduced.
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

/-- Integral source-to-successor boundary at the actual quarter scale. -/
def stageZeroQuarterIntegralBoundary : IntegralScaleCarrier :=
  delta 1 -
    (leftTranslation stageZeroQuarterScaleUnit).toLinearMap (delta 1)

theorem stageZeroQuarterIntegralBoundary_eq_delta_sub_delta :
    stageZeroQuarterIntegralBoundary =
      delta 1 - delta stageZeroQuarterScaleUnit := by
  simp [stageZeroQuarterIntegralBoundary]

theorem stageZeroQuarterScaleUnit_ne_one :
    stageZeroQuarterScaleUnit ≠ 1 := by
  intro scale_eq_one
  have square_eq := congrArg scaleSquare scale_eq_one
  rw [stageZeroQuarterScaleUnit_square] at square_eq
  have : stageZeroSqrtScale = 1 := by
    simpa [scaleSquare, scaleValue] using square_eq
  exact (ne_of_gt stageZeroSqrtScale_one_lt) this

theorem stageZeroQuarterIntegralBoundary_identityCoefficient :
    evaluation stageZeroQuarterIntegralBoundary (delta 1) = 1 := by
  rw [evaluation_apply_delta,
    stageZeroQuarterIntegralBoundary_eq_delta_sub_delta]
  simp [delta, Ne.symm stageZeroQuarterScaleUnit_ne_one]

theorem stageZeroQuarterIntegralBoundary_ne_zero :
    stageZeroQuarterIntegralBoundary ≠ 0 := by
  intro boundary_zero
  have identityCoefficient :=
    stageZeroQuarterIntegralBoundary_identityCoefficient
  rw [boundary_zero, map_zero] at identityCoefficient
  norm_num at identityCoefficient

/-- The actual quarter boundary cannot be removed by division by any rational
prime; the identity basis coefficient remains exactly one. -/
theorem stageZeroQuarterIntegralBoundary_not_prime_divisible
    (prime : Nat.Primes) :
    ¬ ∃ divided : IntegralScaleCarrier,
      prime.1 • divided = stageZeroQuarterIntegralBoundary := by
  rintro ⟨divided, equality⟩
  have atIdentity := congrArg
    (fun value : IntegralScaleCarrier => value.coeff (1 : Units NNReal))
    equality
  simp only [MonoidAlgebra.coeff_smul_apply] at atIdentity
  have boundaryCoefficient :
      stageZeroQuarterIntegralBoundary.coeff 1 = 1 := by
    simpa only [evaluation_apply_delta] using
      stageZeroQuarterIntegralBoundary_identityCoefficient
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

def stageZeroQuarterIntegralBoundaryPrimeResidualCoordinate
    (prime : Nat.Primes) :
    PrimeResidualCoordinate (L := IntegralScaleCarrier) prime where
  representative := stageZeroQuarterIntegralBoundary
  not_divisible :=
    stageZeroQuarterIntegralBoundary_not_prime_divisible prime

theorem stageZeroQuarterIntegralBoundary_residualClass_ne_zero
    (prime : Nat.Primes) :
    residualClass (L := IntegralScaleCarrier) prime
        stageZeroQuarterIntegralBoundary ≠ 0 :=
  (stageZeroQuarterIntegralBoundaryPrimeResidualCoordinate prime).class_ne_zero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial :
  ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))

/-- The named quarter-boundary role is the literal integral boundary. -/
theorem runtimeQuarterSourceBoundary_integral_readback :
    runtimeJointIntegralFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (0, .quarterSourceBoundary)) =
      stageZeroQuarterIntegralBoundary := by
  change
    (runtimeJointQuarterInputAt observation nontrivial 0).integralFace
        ((runtimeJointQuarterInputAt observation nontrivial 0).sourceBoundary
          (delta 1)) = stageZeroQuarterIntegralBoundary
  rw [Input.sourceBoundary_integralFace]
  change delta 1 -
      (leftTranslation (runtimeJointQuarterScaleUnit 0)).toLinearMap
        (delta 1) = stageZeroQuarterIntegralBoundary
  rw [runtimeJointQuarterScaleUnit_zero]
  rfl

/-- The named quarter-incidence role is the existing selected/reversal raw
Riesz incidence pair, not a new scalar comparator. -/
theorem runtimeQuarterIncidence_coherent_readback :
    runtimeJointCoherentFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (0, .quarterIncidence)) =
      (selectedOwnerFreeCouplingResidual observation nontrivial
          stageZeroQuarterScaleUnit (delta 1),
        reversalOwnerFreeCouplingResidual observation nontrivial
          stageZeroQuarterScaleUnit (delta 1)) := by
  change
    (runtimeJointQuarterInputAt observation nontrivial 0).coherentFace
        ((runtimeJointQuarterInputAt observation nontrivial 0
          ).incidenceResidual (delta 1)) = _
  unfold runtimeJointQuarterInputAt
  rw [paired_incidence_coherent_readback]
  rw [runtimeJointQuarterScaleUnit_zero]

/-- The measurement face of the installed quarter incidence is the retained
coordinate of the existing quarter-scale root effect. -/
theorem runtimeQuarterIncidence_measurement_eq_retained (stage : Nat) :
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (stage, .quarterIncidence)) =
      runtimeJointQuarterRetainedAt observation nontrivial stage := by
  change
    (runtimeJointQuarterInputAt observation nontrivial stage).measurementFace
        ((runtimeJointQuarterInputAt observation nontrivial stage
          ).incidenceResidual (delta 1)) + 0 = _
  rw [add_zero]
  rfl

/-- Existing residual conservation projected onto the named quarter-scale
runtime incidence. -/
theorem runtimeQuarterEffect_eq_incidence_add_centeredTrace (stage : Nat) :
    runtimeJointBalanceFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (stage, .quarterPhase)) =
      runtimeJointMeasurementFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (stage, .quarterIncidence)) +
        runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (stage, .quarterCenteredTrace)) := by
  change runtimeJointQuarterPhaseAt observation nontrivial stage =
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (stage, .quarterIncidence)) +
      runtimeJointQuarterCenteredTraceAt observation nontrivial stage
  rw [runtimeQuarterIncidence_measurement_eq_retained]
  exact runtimeJointQuarterEffect_conservation
    observation nontrivial stage

/-- Off center, the actual runtime quarter-incidence chooses the expanding
sibling and lies in that sibling's source-generated topological orbit closure. -/
theorem offCenter_runtimeQuarterIncidence_mem_actualOrbitClosure
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (observation.coordinate.re < 1 / 2 ∧
      (runtimeJointCoherentFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (0, .quarterIncidence))).1 ∈
        selectedStageZeroOrbitClosedRange observation nontrivial) ∨
    (1 / 2 < observation.coordinate.re ∧
      (runtimeJointCoherentFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (0, .quarterIncidence))).2 ∈
        reversalStageZeroOrbitClosedRange observation nontrivial) := by
  rcases lt_or_gt_of_ne offCenter with left | right
  · refine Or.inl ⟨left, ?_⟩
    rw [runtimeQuarterIncidence_coherent_readback]
    rw [selectedRawIncidence_eq_measurementOnly_smul observation nontrivial
      (selectedRieszEnergy_eq_zero_of_re_lt_half
        observation nontrivial left)
      (selectedStageZeroJointState_snd_ne_zero observation nontrivial)]
    exact (selectedStageZeroOrbitClosedRange observation nontrivial).smul_mem _
      (selectedExpandingRieszState_mem_complexifiedOrbitClosure
        observation nontrivial left)
  · refine Or.inr ⟨right, ?_⟩
    rw [runtimeQuarterIncidence_coherent_readback]
    rw [reversalRawIncidence_eq_measurementOnly_smul observation nontrivial
      (reversalRieszEnergy_eq_zero_of_half_lt_re
        observation nontrivial right)
      (reversalStageZeroJointState_snd_ne_zero observation nontrivial)]
    exact (reversalStageZeroOrbitClosedRange observation nontrivial).smul_mem _
      (reversalExpandingRieszState_mem_complexifiedOrbitClosure
        observation nontrivial right)

/-- Direct fixed-root consumer.  Both actual quarter-scale rows are present in
the emitted stage-zero history; the integral write stays prime-visible, while
the off-center coherent write is internal to the corresponding complete
topological carrier and has zero external defect. -/
theorem offCenter_runtimeQuarterScale_rootedDisposition
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    runtimeJointQuarterIncidencePresentedEvent 0 ∈
        ((runtimeJointFaithfulStepAt observation nontrivial 0
          ).history.observation 0).trace ∧
      runtimeJointQuarterSourceBoundaryPresentedEvent 0 ∈
        ((runtimeJointFaithfulStepAt observation nontrivial 0
          ).history.observation 0).trace ∧
      runtimeJointQuarterBalancePresentedEvent 0 ∈
        ((runtimeJointFaithfulStepAt observation nontrivial 0
          ).history.observation 0).trace ∧
      runtimeJointBalanceFace
          (runtimeJointRelationGeneratorValue observation nontrivial
            (0, .quarterPhase)) =
        runtimeJointMeasurementFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterIncidence)) +
          runtimeJointBalanceFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterCenteredTrace)) ∧
      (∀ prime : Nat.Primes,
        residualClass (L := IntegralScaleCarrier) prime
          (runtimeJointIntegralFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterSourceBoundary))) ≠ 0) ∧
      ((observation.coordinate.re < 1 / 2 ∧
          (runtimeJointCoherentFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterIncidence))).1 ∈
            selectedStageZeroOrbitClosedRange observation nontrivial ∧
          SourceGeneratedCompressedUnitaryDefectPort.externalDefect
              (selectedStageZeroOrbitClosedRange observation nontrivial)
              stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
              (selectedStageZeroOrbitIdentitySeed observation nontrivial) = 0) ∨
        (1 / 2 < observation.coordinate.re ∧
          (runtimeJointCoherentFace
            (runtimeJointRelationGeneratorValue observation nontrivial
              (0, .quarterIncidence))).2 ∈
            reversalStageZeroOrbitClosedRange observation nontrivial ∧
          SourceGeneratedCompressedUnitaryDefectPort.externalDefect
              (reversalStageZeroOrbitClosedRange observation nontrivial)
              stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
              (reversalStageZeroOrbitIdentitySeed observation nontrivial) = 0)) := by
  refine ⟨runtimeJointFaithfulObservation_quarterIncidence_mem
      observation nontrivial 0 0, ?_⟩
  refine ⟨runtimeJointFaithfulObservation_quarterSourceBoundary_mem
      observation nontrivial 0 0, ?_⟩
  refine ⟨runtimeJointFaithfulObservation_quarterBalance_mem
      observation nontrivial 0 0, ?_⟩
  refine ⟨runtimeQuarterEffect_eq_incidence_add_centeredTrace
      observation nontrivial 0, ?_⟩
  refine ⟨?_, ?_⟩
  · intro prime
    rw [runtimeQuarterSourceBoundary_integral_readback]
    exact stageZeroQuarterIntegralBoundary_residualClass_ne_zero prime
  · rcases offCenter_runtimeQuarterIncidence_mem_actualOrbitClosure
        observation nontrivial offCenter with selected | reversal
    · exact Or.inl ⟨selected.1, selected.2,
        selectedExpandingActualOrbit_externalDefect_zero
          observation nontrivial selected.1⟩
    · exact Or.inr ⟨reversal.1, reversal.2,
        reversalExpandingActualOrbit_externalDefect_zero
          observation nontrivial reversal.1⟩

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
