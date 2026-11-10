import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeJointPreparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead
open CanonicalGradedSpatialSource GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open ActualCompositeFieldCurrent ActualCompositeJointPreparation CanonicalGradedCharge
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumFullElectricWard
open PreparationVacuumActionFieldLift PreparationVacuumRawJointFeedback
open ActualCompositeGaugeBand FullYSourceResolventGraphSplice SourceScalarPairedTransport
open scoped InnerProductSpace
attribute [local irreducible] preparedInput compositeInput compositeResponse compositeResolvent
  compositeUnitLeg ActualCompositeFieldCurrent.compositeCurrent rawForm

def preparedProbeEndpoint (leg : CompositeLeg) : QuantumTest :=
  ((‖embed (compositeInput leg)‖ : ℂ)/(‖embed (compositeResponse leg)‖ : ℂ)) •
    compositeResolvent leg (preparedInput leg.dual)

theorem prepared_probe_endpoint_original (leg : CompositeLeg) :
    preparedProbeEndpoint leg = compositeUnitLeg leg :=
  (prepared_response_unit leg).symm

structure PreparedProbe (leg : CompositeLeg) : Prop where
  input_unit : ‖embed (preparedInput leg.dual)‖ = 1
  input_charge : chargeReader sourcePhaseGaugeLie (embed (preparedInput leg.dual)) =
    (if leg.dual then (-1 : ℂ) else 1) • embed (preparedInput leg.dual)
  endpoint_generated : preparedProbeEndpoint leg = compositeUnitLeg leg
  endpoint_unit : ‖embed (preparedProbeEndpoint leg)‖ = 1
  full_source : leg.sharp = false →
    (GaussFullHamiltonian.fullAction-leg.energy • (1 : Module.End ℂ QuantumTest))
      (preparedProbeEndpoint leg) =
        ((‖embed (compositeResponse leg)‖ : ℂ)⁻¹) • compositeInput leg+
          defectAction leg.frame (preparedProbeEndpoint leg)
  sharp_source : leg.sharp = true →
    (GaussFullHamiltonian.sharpAction-leg.energy • (1 : Module.End ℂ QuantumTest))
      (preparedProbeEndpoint leg) =
        ((‖embed (compositeResponse leg)‖ : ℂ)⁻¹) • compositeInput leg+
          defectAction leg.frame (preparedProbeEndpoint leg)

theorem actual_prepared_probe (leg : CompositeLeg) : PreparedProbe leg := by
  refine ⟨prepared_input_norm leg.dual, prepared_input_completed_charge leg.dual,
    prepared_probe_endpoint_original leg, ?_, ?_, ?_⟩
  · rw [prepared_probe_endpoint_original]
    exact composite_unit_norm leg
  · intro full
    rw [prepared_probe_endpoint_original]
    exact composite_unit_full_source leg full
  · intro sharp
    rw [prepared_probe_endpoint_original]
    exact composite_unit_sharp_source leg sharp

def preparedProbeCurrent (p : PhysicalMomentum) (left right : CompositeLeg) : Fin 289 → ℂ :=
  fun i => -rawForm (fieldUnit i) p (preparedProbeEndpoint left) (preparedProbeEndpoint right) 0

theorem prepared_probe_current_original (p : PhysicalMomentum) (left right : CompositeLeg) :
    preparedProbeCurrent p left right = ActualCompositeFieldCurrent.compositeCurrent p left right := by
  funext i
  exact (prepared_current_generated p left right i).symm

theorem actual_probe_current_generated (p : PhysicalMomentum) (left right : CompositeLeg) :
    PreparedProbe left ∧ PreparedProbe right ∧
      (∀ i : Fin 289, ActualCompositeFieldCurrent.compositeCurrent p left right i =
        -rawForm (fieldUnit i) p (preparedProbeEndpoint left) (preparedProbeEndpoint right) 0) :=
  ⟨actual_prepared_probe left, actual_prepared_probe right, prepared_current_generated p left right⟩

end LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead

#print axioms LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.actual_prepared_probe
#print axioms LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.actual_probe_current_generated
