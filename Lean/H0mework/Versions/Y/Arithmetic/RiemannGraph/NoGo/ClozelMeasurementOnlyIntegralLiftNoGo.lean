import H0mework.Versions.Y.Arithmetic.RiemannGraph.PerfectRealization.ClozelIntegralGraphPerfectRealization
import H0mework.Versions.Y.Arithmetic.RiemannGraph.StageZeroOrbitClosedDefectPort
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedRieszEnergySupportResidual
import H0mework.Versions.Y.Arithmetic.RiemannGraph.IntegralGraphKernelCompatibility
/-!
# Measurement-only integral lift no-go

Perfect-carrier and literal integral point lifts are equivalent; complexified
and closed-range lifts are only one-way extensions.  Off center, the expanding
side requires an explicit vertical integral event.  A global section from the
complex graph target back to the integral carrier is impossible, but no
pointwise lift is declared impossible.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open Character.GlobalCoPoissonCurrent
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentCompletion
open SourceGeneratedIntegralEquivariantPerfectRealization
open SourceGeneratedIntegralGroupRingPerfectPair
open SourceGeneratedIntegralOrbitClosedDefectPort
open ThetaJRoleRepresentation
noncomputable section
universe r c p h

structure PointLift
    {R : Type r} [Semiring R]
    {C : Type c} {H : Type h}
    [AddCommMonoid C] [Module R C]
    [AddCommMonoid H] [Module R H]
    (map : C →ₗ[R] H) (target : H) where
  source : C
  readback : map source = target

private theorem pointLift_comp_surjective_iff
    {R : Type r} [Semiring R]
    {C : Type c} {P : Type p} {H : Type h}
    [AddCommMonoid C] [Module R C]
    [AddCommMonoid P] [Module R P]
    [AddCommMonoid H] [Module R H]
    (quotientMap : C →ₗ[R] P) (surjective : Function.Surjective quotientMap)
    (readout : P →ₗ[R] H) (feature : C →ₗ[R] H)
    (sourceReadback : readout.comp quotientMap = feature) (target : H) :
    Nonempty (PointLift readout target) ↔
      Nonempty (PointLift feature target) := by
  constructor
  · rintro ⟨⟨point, pointReadback⟩⟩
    obtain ⟨source, rfl⟩ := surjective point
    exact ⟨⟨source,
      (LinearMap.congr_fun sourceReadback source).symm.trans pointReadback⟩⟩
  · rintro ⟨⟨source, pointReadback⟩⟩
    exact ⟨⟨quotientMap source,
      (LinearMap.congr_fun sourceReadback source).trans pointReadback⟩⟩

private theorem pointLift_nonempty_iff_rangeClass_zero
    {R : Type r} [CommRing R]
    {C : Type c} {H : Type h}
    [AddCommGroup C] [Module R C]
    [AddCommGroup H] [Module R H]
    (map : C →ₗ[R] H) (target : H) :
    Nonempty (PointLift map target) ↔
      (Submodule.Quotient.mk target : H ⧸ LinearMap.range map) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨⟨source, readback⟩⟩
    exact ⟨source, readback⟩
  · rintro ⟨source, readback⟩
    exact ⟨⟨source, readback⟩⟩

abbrev SelectedPerfectCarrierPointLift
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  PointLift
    (selectedIntegralGraphPerfectFace observation nontrivial
      stageZeroQuarterScaleUnit).readout
    (selectedStageZeroJointState observation nontrivial)

abbrev ReversalPerfectCarrierPointLift
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  PointLift
    (reversalIntegralGraphPerfectFace observation nontrivial
      stageZeroQuarterScaleUnit).readout
    (reversalStageZeroJointState observation nontrivial)

abbrev SelectedIntegralOrbitPointLift
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  PointLift (selectedIntegralGraphOrbit observation nontrivial)
    (selectedStageZeroJointState observation nontrivial)

abbrev ReversalIntegralOrbitPointLift
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  PointLift (reversalIntegralGraphOrbit observation nontrivial)
    (reversalStageZeroJointState observation nontrivial)

theorem selectedPerfectCarrierPointLift_iff_integralOrbitPointLift
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (SelectedPerfectCarrierPointLift observation nontrivial) ↔
      Nonempty (SelectedIntegralOrbitPointLift observation nontrivial) :=
  pointLift_comp_surjective_iff
    (SourceGeneratedScalarPerfectification.canonicalMap
      integralScalePerfectEvaluation)
    (Submodule.mkQ_surjective (LinearMap.ker integralScalePerfectEvaluation))
    (selectedIntegralGraphPerfectFace observation nontrivial
      stageZeroQuarterScaleUnit).readout
    (selectedIntegralGraphOrbit observation nontrivial)
    (selectedIntegralGraphPerfectFace observation nontrivial
      stageZeroQuarterScaleUnit).source_readback _

theorem reversalPerfectCarrierPointLift_iff_integralOrbitPointLift
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (ReversalPerfectCarrierPointLift observation nontrivial) ↔
      Nonempty (ReversalIntegralOrbitPointLift observation nontrivial) :=
  pointLift_comp_surjective_iff
    (SourceGeneratedScalarPerfectification.canonicalMap
      integralScalePerfectEvaluation)
    (Submodule.mkQ_surjective (LinearMap.ker integralScalePerfectEvaluation))
    (reversalIntegralGraphPerfectFace observation nontrivial
      stageZeroQuarterScaleUnit).readout
    (reversalIntegralGraphOrbit observation nontrivial)
    (reversalIntegralGraphPerfectFace observation nontrivial
      stageZeroQuarterScaleUnit).source_readback _

theorem selectedPerfectCarrierPointLift_iff_integralRangeClass_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (SelectedPerfectCarrierPointLift observation nontrivial) ↔
      (Submodule.Quotient.mk (selectedStageZeroJointState observation nontrivial) :
        JointGraphTarget ⧸ LinearMap.range
          (selectedIntegralGraphOrbit observation nontrivial)) = 0 := by
  rw [selectedPerfectCarrierPointLift_iff_integralOrbitPointLift]
  exact pointLift_nonempty_iff_rangeClass_zero _ _

theorem reversalPerfectCarrierPointLift_iff_integralRangeClass_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (ReversalPerfectCarrierPointLift observation nontrivial) ↔
      (Submodule.Quotient.mk (reversalStageZeroJointState observation nontrivial) :
        JointGraphTarget ⧸ LinearMap.range
          (reversalIntegralGraphOrbit observation nontrivial)) = 0 := by
  rw [reversalPerfectCarrierPointLift_iff_integralOrbitPointLift]
  exact pointLift_nonempty_iff_rangeClass_zero _ _

structure MeasurementOnlyIntegralEvent
    (feature : IntegralScaleCarrier →ₗ[ℤ] JointGraphTarget)
    (measurement : ℂ) where
  event : IntegralScaleCarrier
  energy_zero : (feature event).fst = 0
  measurement_readback : (feature event).snd = measurement
  measurement_ne_zero : measurement ≠ 0

private theorem pointLift_iff_measurementOnlyIntegralEvent
    (feature : IntegralScaleCarrier →ₗ[ℤ] JointGraphTarget)
    (state : JointGraphTarget) (energy_zero : state.fst = 0)
    (measurement_ne_zero : state.snd ≠ 0) :
    Nonempty (PointLift feature state) ↔
      Nonempty (MeasurementOnlyIntegralEvent feature state.snd) := by
  constructor
  · rintro ⟨⟨event, readback⟩⟩
    exact ⟨⟨event, by simpa [readback] using energy_zero,
      by simp [readback], measurement_ne_zero⟩⟩
  · rintro ⟨⟨event, eventEnergy, eventMeasurement, _⟩⟩
    refine ⟨⟨event, ?_⟩⟩
    apply (WithLp.linearEquiv 2 ℂ
      (PositiveMellinQuarterEnergy × ℂ)).injective
    exact Prod.ext (eventEnergy.trans energy_zero.symm) eventMeasurement

theorem offCenter_expandingSide_verticalIntegralEvent_iff
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (observation.coordinate.re < 1 / 2 ∧
      (Nonempty (SelectedPerfectCarrierPointLift observation nontrivial) ↔
        Nonempty (MeasurementOnlyIntegralEvent
          (selectedIntegralGraphOrbit observation nontrivial)
          (selectedStageZeroJointState observation nontrivial).snd))) ∨
    (1 / 2 < observation.coordinate.re ∧
      (Nonempty (ReversalPerfectCarrierPointLift observation nontrivial) ↔
        Nonempty (MeasurementOnlyIntegralEvent
          (reversalIntegralGraphOrbit observation nontrivial)
          (reversalStageZeroJointState observation nontrivial).snd))) := by
  by_cases left : observation.coordinate.re < 1 / 2
  · exact Or.inl ⟨left,
      (selectedPerfectCarrierPointLift_iff_integralOrbitPointLift
        observation nontrivial).trans
        (pointLift_iff_measurementOnlyIntegralEvent _ _
          (selectedRieszEnergy_eq_zero_of_re_lt_half
            observation nontrivial left)
          (selectedStageZeroJointState_snd_ne_zero observation nontrivial))⟩
  · have right : 1 / 2 < observation.coordinate.re :=
      lt_of_le_of_ne (le_of_not_gt left) (Ne.symm offCenter)
    exact Or.inr ⟨right,
      (reversalPerfectCarrierPointLift_iff_integralOrbitPointLift
        observation nontrivial).trans
        (pointLift_iff_measurementOnlyIntegralEvent _ _
          (reversalRieszEnergy_eq_zero_of_half_lt_re
            observation nontrivial right)
          (reversalStageZeroJointState_snd_ne_zero observation nontrivial))⟩

/-- The expanding selected Riesz state cannot be one literal integral event:
the actual source-test kernel law would kill its nonzero measurement. -/
theorem selectedIntegralOrbitPointLift_isEmpty_of_re_lt_half
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    IsEmpty (SelectedIntegralOrbitPointLift observation nontrivial) := by
  refine ⟨?_⟩
  intro lift
  have sourceEnergyZero :
      (selectedIntegralGraphOrbit observation nontrivial lift.source).fst = 0 := by
    calc
      (selectedIntegralGraphOrbit observation nontrivial lift.source).fst =
          (selectedStageZeroJointState observation nontrivial).fst :=
        congrArg (fun value : JointGraphTarget => value.fst) lift.readback
      _ = 0 := selectedRieszEnergy_eq_zero_of_re_lt_half
        observation nontrivial left
  have sourceMeasurementZero :=
    selectedIntegralGraphOrbit_energy_zero_imp_measurement_zero
      observation nontrivial lift.source sourceEnergyZero
  apply selectedStageZeroJointState_snd_ne_zero observation nontrivial
  calc
    (selectedStageZeroJointState observation nontrivial).snd =
        (selectedIntegralGraphOrbit observation nontrivial lift.source).snd :=
      congrArg (fun value : JointGraphTarget => value.snd) lift.readback.symm
    _ = 0 := sourceMeasurementZero

theorem reversalIntegralOrbitPointLift_isEmpty_of_half_lt_re
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    IsEmpty (ReversalIntegralOrbitPointLift observation nontrivial) := by
  refine ⟨?_⟩
  intro lift
  have sourceEnergyZero :
      (reversalIntegralGraphOrbit observation nontrivial lift.source).fst = 0 := by
    calc
      (reversalIntegralGraphOrbit observation nontrivial lift.source).fst =
          (reversalStageZeroJointState observation nontrivial).fst :=
        congrArg (fun value : JointGraphTarget => value.fst) lift.readback
      _ = 0 := reversalRieszEnergy_eq_zero_of_half_lt_re
        observation nontrivial right
  have sourceMeasurementZero :=
    reversalIntegralGraphOrbit_energy_zero_imp_measurement_zero
      observation nontrivial lift.source sourceEnergyZero
  apply reversalStageZeroJointState_snd_ne_zero observation nontrivial
  calc
    (reversalStageZeroJointState observation nontrivial).snd =
        (reversalIntegralGraphOrbit observation nontrivial lift.source).snd :=
      congrArg (fun value : JointGraphTarget => value.snd) lift.readback.symm
    _ = 0 := sourceMeasurementZero

theorem selectedPerfectCarrierPointLift_isEmpty_of_re_lt_half
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    IsEmpty (SelectedPerfectCarrierPointLift observation nontrivial) := by
  refine ⟨?_⟩
  intro lift
  obtain ⟨integralLift⟩ :=
    (selectedPerfectCarrierPointLift_iff_integralOrbitPointLift
      observation nontrivial).1 ⟨lift⟩
  exact (selectedIntegralOrbitPointLift_isEmpty_of_re_lt_half
    observation nontrivial left).false integralLift

theorem reversalPerfectCarrierPointLift_isEmpty_of_half_lt_re
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    IsEmpty (ReversalPerfectCarrierPointLift observation nontrivial) := by
  refine ⟨?_⟩
  intro lift
  obtain ⟨integralLift⟩ :=
    (reversalPerfectCarrierPointLift_iff_integralOrbitPointLift
      observation nontrivial).1 ⟨lift⟩
  exact (reversalIntegralOrbitPointLift_isEmpty_of_half_lt_re
    observation nontrivial right).false integralLift

theorem selectedIntegralRangeClass_ne_zero_of_re_lt_half
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left : observation.coordinate.re < 1 / 2) :
    (Submodule.Quotient.mk (selectedStageZeroJointState observation nontrivial) :
      JointGraphTarget ⧸ LinearMap.range
        (selectedIntegralGraphOrbit observation nontrivial)) ≠ 0 := by
  intro classZero
  obtain ⟨lift⟩ :=
    (selectedPerfectCarrierPointLift_iff_integralRangeClass_zero
      observation nontrivial).2 classZero
  exact (selectedPerfectCarrierPointLift_isEmpty_of_re_lt_half
    observation nontrivial left).false lift

theorem reversalIntegralRangeClass_ne_zero_of_half_lt_re
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (right : 1 / 2 < observation.coordinate.re) :
    (Submodule.Quotient.mk (reversalStageZeroJointState observation nontrivial) :
      JointGraphTarget ⧸ LinearMap.range
        (reversalIntegralGraphOrbit observation nontrivial)) ≠ 0 := by
  intro classZero
  obtain ⟨lift⟩ :=
    (reversalPerfectCarrierPointLift_iff_integralRangeClass_zero
      observation nontrivial).2 classZero
  exact (reversalPerfectCarrierPointLift_isEmpty_of_half_lt_re
    observation nontrivial right).false lift

/-- Off center, the expanding involutive side has a certified nonzero
algebraic range class; no branch premise is supplied by a caller. -/
theorem offCenter_expandingSide_integralRangeClass_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (offCenter : observation.coordinate.re ≠ 1 / 2) :
    (observation.coordinate.re < 1 / 2 ∧
      (Submodule.Quotient.mk
        (selectedStageZeroJointState observation nontrivial) :
        JointGraphTarget ⧸ LinearMap.range
          (selectedIntegralGraphOrbit observation nontrivial)) ≠ 0) ∨
    (1 / 2 < observation.coordinate.re ∧
      (Submodule.Quotient.mk
        (reversalStageZeroJointState observation nontrivial) :
        JointGraphTarget ⧸ LinearMap.range
          (reversalIntegralGraphOrbit observation nontrivial)) ≠ 0) := by
  by_cases left : observation.coordinate.re < 1 / 2
  · exact Or.inl ⟨left,
      selectedIntegralRangeClass_ne_zero_of_re_lt_half
        observation nontrivial left⟩
  · have right : 1 / 2 < observation.coordinate.re :=
      lt_of_le_of_ne (le_of_not_gt left) (Ne.symm offCenter)
    exact Or.inr ⟨right,
      reversalIntegralRangeClass_ne_zero_of_half_lt_re
        observation nontrivial right⟩

def integralPointLiftToComplexified
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : IntegralScaleCarrier →ₗ[ℤ] H) (target : H)
    (lift : PointLift feature target) :
    PointLift (complexifiedFeature feature) target :=
  ⟨1 ⊗ₜ[ℤ] lift.source, by simpa using lift.readback⟩

def complexifiedPointLiftToClosed
    {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (feature : IntegralScaleCarrier →ₗ[ℤ] H) (target : H)
    (lift : PointLift (complexifiedFeature feature) target) :
    {value : orbitClosedRange feature // (value : H) = target} :=
  ⟨⟨target, (LinearMap.range (complexifiedFeature feature)).le_topologicalClosure
    ⟨lift.source, lift.readback⟩⟩, rfl⟩

theorem selectedIntegral_to_complexified_to_closed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (SelectedIntegralOrbitPointLift observation nontrivial) →
      Nonempty (PointLift
        (complexifiedFeature (selectedIntegralGraphOrbit observation nontrivial))
        (selectedStageZeroJointState observation nontrivial)) ∧
      Nonempty {value : selectedStageZeroOrbitClosedRange observation nontrivial //
        (value : JointGraphTarget) = selectedStageZeroJointState observation nontrivial} := by
  rintro ⟨lift⟩
  let complexLift := integralPointLiftToComplexified _ _ lift
  exact ⟨⟨complexLift⟩, ⟨complexifiedPointLiftToClosed _ _ complexLift⟩⟩

theorem reversalIntegral_to_complexified_to_closed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nonempty (ReversalIntegralOrbitPointLift observation nontrivial) →
      Nonempty (PointLift
        (complexifiedFeature (reversalIntegralGraphOrbit observation nontrivial))
        (reversalStageZeroJointState observation nontrivial)) ∧
      Nonempty {value : reversalStageZeroOrbitClosedRange observation nontrivial //
        (value : JointGraphTarget) = reversalStageZeroJointState observation nontrivial} := by
  rintro ⟨lift⟩
  let complexLift := integralPointLiftToComplexified _ _ lift
  exact ⟨⟨complexLift⟩, ⟨complexifiedPointLiftToClosed _ _ complexLift⟩⟩

private theorem globalAmbientLift_isEmpty
    (feature : IntegralScaleCarrier →ₗ[ℤ] JointGraphTarget) :
    IsEmpty (SourceGeneratedPerfectification.SourceGeneratedAmbientLift
      integralScalePerfectEvaluation feature) := by
  refine ⟨?_⟩
  intro ambient
  let point := feature (delta 1)
  let halfPoint : JointGraphTarget := (2 : ℂ)⁻¹ • point
  have doubledHalf : (2 : ℤ) • halfPoint = point := by
    simp [halfPoint, two_zsmul, ← two_smul ℂ, smul_smul]
  have commutesAt := LinearMap.congr_fun ambient.commutes (delta 1)
  have divisible :
      SourceGeneratedPerfectification.canonicalMap
          integralScalePerfectEvaluation (delta 1) =
        (2 : ℤ) • ambient.lift halfPoint := by
    rw [← commutesAt]
    change ambient.lift point = _
    rw [← doubledHalf, map_smul]
  have coefficientEquality := congrArg
    (fun value => SourceGeneratedPerfectification.dualEmbedding
      integralScalePerfectEvaluation value (delta 1)) divisible
  have leftCoefficient :
      SourceGeneratedPerfectification.dualEmbedding
          integralScalePerfectEvaluation
          (SourceGeneratedPerfectification.canonicalMap
            integralScalePerfectEvaluation (delta 1)) (delta 1) = 1 := by
    change integralScalePerfectEvaluation (delta 1) (delta 1) = 1
    rw [evaluation_apply_delta]
    simp [delta]
  rw [leftCoefficient] at coefficientEquality
  simp only [map_smul] at coefficientEquality
  change 1 = (2 : ℤ) * SourceGeneratedPerfectification.dualEmbedding
    integralScalePerfectEvaluation (ambient.lift halfPoint) (delta 1)
    at coefficientEquality
  omega

theorem selectedGlobalAmbientLift_isEmpty
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceGeneratedPerfectification.SourceGeneratedAmbientLift
      integralScalePerfectEvaluation
      (selectedIntegralGraphOrbit observation nontrivial)) :=
  globalAmbientLift_isEmpty _

theorem reversalGlobalAmbientLift_isEmpty
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceGeneratedPerfectification.SourceGeneratedAmbientLift
      integralScalePerfectEvaluation
      (reversalIntegralGraphOrbit observation nontrivial)) :=
  globalAmbientLift_isEmpty _

end
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
