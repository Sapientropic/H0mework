import H0mework.Versions.AB.Physics.MotherSource.GaugeHamiltonian.Action

/-! The electric energy comes from the complete source action's temporal connection momentum. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.GaugeHamiltonian
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open StageNineFormNativeMotherAction StageNineFormNativeGaugeWedge
open StageNineP286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator
open Stage9C.Material.SpinPair TemporalGauge
open SU7MotherLieAlgebra
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

private theorem gauge_normal (source : SmoothUnifiedSource)
    (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField (p286ConnectionRelativeScalarNormalConstraintCauchyDevelopmentOperator background) point) =
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField background point) := rfl

/-- Legendre pairing in the covariant electric velocity. The ordinary-time Hamiltonian also contains the temporal connection constraint. -/
def covariantEnergy (potential : Potential) (point : BasePoint) : ℝ :=
  momentum potential point (electric potential point) -
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings Stage10.Runtime.source)
      (toContinuumPointField (CanonicalGauss.configuration potential) point)

theorem source_covariant_energy (potential : Potential) (point : BasePoint) :
    covariantEnergy potential point =
      lapse*squared (electric potential point) + lapse⁻¹*squared magnetic := by
  unfold covariantEnergy
  rw [momentum_readout, CanonicalGauss.configuration, Stage10.Runtime.source_eq, gauge_normal]
  have gauge := gauge_density potential point
  rw [Stage10.Runtime.source_eq] at gauge
  rw [gauge]
  unfold squared
  ring

def electricEnergy (potential : Potential) (point : BasePoint) : ℝ :=
  covariantEnergy potential point - lapse⁻¹*squared magnetic

theorem electric_energy (potential : Potential) (point : BasePoint) :
    electricEnergy potential point = lapse*squared (electric potential point) := by
  rw [electricEnergy, source_covariant_energy]
  ring

theorem electric_energy_nonnegative (potential : Potential) (point : BasePoint) :
    0 ≤ electricEnergy potential point := by
  rw [electric_energy]
  exact mul_nonneg lapse_pos.le (squared_nonnegative _)

theorem electric_energy_zero_iff (potential : Potential) (point : BasePoint) :
    electricEnergy potential point = 0 ↔ electric potential point = 0 := by
  rw [electric_energy, mul_eq_zero, squared_zero_iff]
  simp [lapse_pos.ne']

theorem source_abelian_energy (potential : BasePoint → ℝ) (point : BasePoint)
    (regular : DifferentiableAt ℝ potential point) :
    electricEnergy (CanonicalGauss.abelianPotential potential) point =
      lapse*∑ axis : Fin 3, (fieldDirectionalDerivative potential point axis.succ)^2 := by
  rw [electric_energy]
  unfold squared
  simp only [CanonicalGauss.electric_abelian potential point regular,
    formNativeP286LiePairing_smul_left, formNativeP286LiePairing_smul_right]
  have pairing : formNativeP286LiePairing HyperchargeResponse.chargeDirection
      HyperchargeResponse.chargeDirection = 1 := CanonicalGauss.charge_pairing
  rw [pairing]
  congr 1
  apply Finset.sum_congr rfl
  intro axis _
  ring


end
end SaturationMonoid.PhysicsCore.Stage10.GaugeHamiltonian
