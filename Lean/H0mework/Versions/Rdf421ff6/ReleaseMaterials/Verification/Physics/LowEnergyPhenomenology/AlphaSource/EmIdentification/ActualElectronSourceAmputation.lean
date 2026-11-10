import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronNoetherCalibration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronPhysicalNormalization
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource SourceQuantumFockGauge GaussCoreHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates GaussCoreDifferential
open ActualCompositeFieldCurrent ActualCompositeGaugeBand
open FullYDynamicSource FullYSourceResolventGraphSplice GeneralThreeParticleResponse
open SourceScalarPairedTransport
open scoped InnerProductSpace

theorem actual_electron_source_amputation (leg : CompositeLeg) :
    compositeShift leg (compositeResponse leg)=compositeInput leg := by
  cases hs : leg.sharp
  · simpa only [compositeShift,compositeResponse,hs,Bool.false_eq_true,if_false,
      Module.End.mul_apply,Module.End.one_apply] using
      LinearMap.congr_fun (literal_core_right_inverse leg.frame leg.energy leg.nonreal) (compositeInput leg)
  · simpa only [compositeShift,compositeResponse,hs,if_true,
      Module.End.mul_apply,Module.End.one_apply] using
      LinearMap.congr_fun (literal_sharp_right_inverse leg.frame leg.energy leg.nonreal) (compositeInput leg)

theorem actual_electron_input_nonzero (leg : CompositeLeg) :
    embed (compositeInput leg)≠0 := by
  intro zero
  have input : compositeInput leg=0 := embed_injective zero
  have inverse : compositeResolvent leg*compositeShift leg=1 := by
    cases hs : leg.sharp
    · simpa only [compositeResolvent,compositeShift,hs,Bool.false_eq_true,if_false] using
        literal_core_left_inverse leg.frame leg.energy leg.nonreal
    · simpa only [compositeResolvent,compositeShift,hs,if_true] using
        literal_sharp_left_inverse leg.frame leg.energy leg.nonreal
  have result := LinearMap.congr_fun inverse (compositeResponse leg)
  simp only [Module.End.mul_apply,Module.End.one_apply] at result
  rw [actual_electron_source_amputation,input,map_zero] at result
  exact composite_response_nonzero leg result.symm

def actualElectronInputInverseNorm (leg : CompositeLeg) : ℂ :=
  (‖embed (compositeInput leg)‖:ℂ)⁻¹

/-- The actual complete resolvent output is amputated by its own source shift before normalization. -/
def actualElectronAmputatedLeg (leg : CompositeLeg) : QuantumTest :=
  actualElectronInputInverseNorm leg • compositeShift leg (compositeResponse leg)

theorem actual_electron_amputated_source (leg : CompositeLeg) :
    actualElectronAmputatedLeg leg=
      actualElectronInputInverseNorm leg • compositeInput leg := by
  rw [actualElectronAmputatedLeg,actual_electron_source_amputation]

theorem actual_electron_amputated_norm (leg : CompositeLeg) :
    ‖embed (actualElectronAmputatedLeg leg)‖=1 := by
  rw [actual_electron_amputated_source,map_smul,norm_smul,
    actualElectronInputInverseNorm,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr (actual_electron_input_nonzero leg))]

theorem actual_electron_amputated_nonzero (leg : CompositeLeg) :
    embed (actualElectronAmputatedLeg leg)≠0 := by
  exact norm_ne_zero_iff.mp (by rw [actual_electron_amputated_norm]; exact one_ne_zero)

/-- This returns to the same normalized complete output; no source one-particle leg is substituted. -/
theorem actual_electron_amputate_unit_output (leg : CompositeLeg) :
    actualElectronAmputatedLeg leg=
      (actualElectronInputInverseNorm leg*(‖embed (compositeResponse leg)‖:ℂ)) •
        compositeShift leg (compositeUnitLeg leg) := by
  have nz : (‖embed (compositeResponse leg)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (fun zero=>composite_response_nonzero leg (embed_injective zero)))
  rw [compositeUnitLeg,map_smul,smul_smul]
  rw [mul_assoc,mul_inv_cancel₀ nz,mul_one]
  rfl

theorem actual_electron_full_amputation_defect (leg : CompositeLeg) (full : leg.sharp=false) :
    actualElectronAmputatedLeg leg=actualElectronInputInverseNorm leg •
      ((GaussFullHamiltonian.fullAction-leg.energy • (1 : Module.End ℂ QuantumTest))
        (compositeResponse leg)-defectAction leg.frame (compositeResponse leg)) := by
  rw [actual_electron_amputated_source,composite_full_source_return leg full,add_sub_cancel_right]

theorem actual_electron_sharp_amputation_defect (leg : CompositeLeg) (sharp : leg.sharp=true) :
    actualElectronAmputatedLeg leg=actualElectronInputInverseNorm leg •
      ((GaussFullHamiltonian.sharpAction-leg.energy • (1 : Module.End ℂ QuantumTest))
        (compositeResponse leg)-defectAction leg.frame (compositeResponse leg)) := by
  rw [actual_electron_amputated_source,composite_sharp_source_return leg sharp,add_sub_cancel_right]

end LowEnergy.GaussComposite.ActualElectronPhysicalNormalization
