import H0mework.Versions.AB.Physics.MotherSource.TemporalGauge.Matter

/-! Exact complete-U density for every P286 temporal potential. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineDiracDualFormNativeMotherAction
open StageNineFormNativeP286GaugeYangMillsReadout StageNineFormNativeMotherAction
open Stage9C.Material.SpinPair
noncomputable section

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

theorem primitive_zero : primitive (fun _ => 0) = Stage10.Runtime.configuration := by
  apply StageNineHolonomicConfiguration.ext <;>
    simp only [primitive, ite_self, add_zero]

theorem configuration_zero : configuration (fun _ => 0) = Stage10.Runtime.configuration := by
  unfold configuration
  rw [primitive_zero, Stage10.Runtime.source_eq, Stage10.Runtime.configuration_eq]
  symm
  apply (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout
    positiveSmoothUnifiedSource actual actual_nondegenerate).mp
  intro point
  exact (Stage9G.Foundation.actualConstitutive_solves point).symm

theorem original_gauge_density (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings Stage10.Runtime.source)
      (toContinuumPointField Stage10.Runtime.configuration point) = -lapse⁻¹ * squared magnetic := by
  have zero := gauge_density (fun _ => 0) point
  rw [configuration_zero] at zero
  simpa [electric, derivative, fieldDirectionalDerivative, bracket_zero_left, squared,
    StageNineFormNativeGaugeWedge.formNativeP286LiePairing,
    specialUnitaryLiePairing, hyperchargeLiePairing] using zero

/-- The full source temporal response, including every covariant derivative cross term. -/
def quadraticDensity (potential : Potential) (point : BasePoint) : ℝ :=
  lapse * squared (electric potential point) -
    scalarCoordinateSquaredNorm (scalarCharge (potential point)) / (2*lapse)

theorem mother_density_shift (potential : Potential) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (configuration potential) point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) + quadraticDensity potential point := by
  have matter : generatedDiracDualFormNativeMatterDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (configuration potential) point) =
      generatedDiracDualFormNativeMatterDensity Stage10.Runtime.source 0 point
        (toContinuumPointField Stage10.Runtime.configuration point) -
      scalarCoordinateSquaredNorm (scalarCharge (potential point)) / (2*lapse) := by
    have scalarShift := scalar_density_shift potential point
    have diracShift := dirac_density_preserved potential point
    rw [Stage10.Runtime.source_eq] at scalarShift diracShift ⊢
    simp only [configuration, Stage10.Runtime.source_eq]
    rw [HyperchargeResponse.constitutive_matter_preserved]
    unfold generatedDiracDualFormNativeMatterDensity
    rw [scalarShift, diracShift]
    ring
  have gravity : generatedFormNativeGravityBFDensity
      (toContinuumPointField (configuration potential) point) =
      generatedFormNativeGravityBFDensity
        (toContinuumPointField Stage10.Runtime.configuration point) := by
    simp only [generatedFormNativeGravityBFDensity, toContinuumPointField,
      configuration, formNativeP286GaugeConstitutiveReadout, primitive]
    rfl
  have constraint : generatedFormNativeGravityConstraintDensity
      (toContinuumPointField (configuration potential) point) =
      generatedFormNativeGravityConstraintDensity
        (toContinuumPointField Stage10.Runtime.configuration point) := by
    simp only [generatedFormNativeGravityConstraintDensity,
      generatedGravitySimplicityResidual, toContinuumPointField,
      configuration, formNativeP286GaugeConstitutiveReadout, primitive]
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [gravity, constraint, gauge_density, original_gauge_density, matter]
  unfold quadraticDensity
  ring

end
end SaturationMonoid.PhysicsCore.Stage10.TemporalGauge
