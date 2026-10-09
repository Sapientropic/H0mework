import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBoundary

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoether
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open ActualDressedFullCoulomb ActualEMCauchyDynamic MeasureTheory Filter
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] originalJacobi originalReadback originalChange originalInverse
  sourceGreen PreparationVacuumOriginalGreenFeedback.sourceField originalReader36

/-- The generated Cauchy histories pay every smoothness and time-jet input of the actual quantum co-source. -/
theorem dressed_voltage_quantum_cosources (event : DressedEvent) (transfer : PhysicalMomentum)
    (imaginary : Bool) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum (physicalSpatial transfer) lambda)*ᵥ
      dressedNoetherForcing event transfer (voltageNativeTimeJet (physicalSpatial transfer) imaginary) lambda T) row=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*
        dressedNoetherTimeSource event transfer (voltageNativeTimeJet (physicalSpatial transfer) imaginary) t row)-
      (dressedNoetherBoundary event transfer (voltageNativeTimeJet (physicalSpatial transfer) imaginary) lambda T row-
        dressedNoetherBoundary event transfer (voltageNativeTimeJet (physicalSpatial transfer) imaginary) lambda 0 row) := by
  exact dressed_noether_readback event transfer _ (voltage_timejet_continuous _ imaginary)
    (voltage_timejet_generated _ imaginary) lambda T row

/-- The same original Cauchy field, its nine null data, and the actual creation/background quantum update share one carrier. -/
theorem dressed_voltage_update_split (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : physicalSpectralDomain transfer) (T : ℝ) :
    dressedVoltageUpdate event transfer lambda T=
      voltageWindowField (physicalSpatial transfer) lambda.val T-
        originalChange (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
          (nullProjection*ᵥ(originalInverse (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
            voltageWindowField (physicalSpatial transfer) lambda.val T))+
      dressedNoetherField event transfer (voltageNativeTimeJet (physicalSpatial transfer) false) lambda T+
      Complex.I • dressedNoetherField event transfer (voltageNativeTimeJet (physicalSpatial transfer) true) lambda T := by
  have original:=voltage_window_green (physicalSpatial transfer) lambda.val T lambda.property
  unfold dressedVoltageUpdate dressedVoltageForcing dressedNoetherField
  simp only [PreparationVacuumOriginalGreenFeedback.sourceField,Matrix.mulVec_add,Matrix.mulVec_smul]
  simpa only [PreparationVacuumOriginalGreenFeedback.sourceField,add_assoc] using!
    congrArg (fun field=>field+
      sourceGreen ⟨fullMomentum (physicalSpatial transfer) lambda.val,lambda.property⟩*ᵥ
        dressedNoetherForcing event transfer (voltageNativeTimeJet (physicalSpatial transfer) false) lambda.val T+
      Complex.I • (sourceGreen ⟨fullMomentum (physicalSpatial transfer) lambda.val,lambda.property⟩*ᵥ
        dressedNoetherForcing event transfer (voltageNativeTimeJet (physicalSpatial transfer) true) lambda.val T)) original

/-- All36 original curvature rows observe the complete actual update, including its null and quantum returns. -/
theorem dressed_voltage_curvature_update (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : physicalSpectralDomain transfer) (T : ℝ) :
    originalReader36 (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥdressedVoltageUpdate event transfer lambda T=
      originalReader36 (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
        voltageWindowField (physicalSpatial transfer) lambda.val T-
      originalReader36 (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
        (originalChange (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
          (nullProjection*ᵥ(originalInverse (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
            voltageWindowField (physicalSpatial transfer) lambda.val T)))+
      originalReader36 (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
        dressedNoetherField event transfer (voltageNativeTimeJet (physicalSpatial transfer) false) lambda T+
      Complex.I • (originalReader36 (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
        dressedNoetherField event transfer (voltageNativeTimeJet (physicalSpatial transfer) true) lambda T) := by
  rw [dressed_voltage_update_split]
  simp only [Matrix.mulVec_add,Matrix.mulVec_sub,Matrix.mulVec_smul]

end LowEnergy.GaussComposite.ActualDressedNoether
