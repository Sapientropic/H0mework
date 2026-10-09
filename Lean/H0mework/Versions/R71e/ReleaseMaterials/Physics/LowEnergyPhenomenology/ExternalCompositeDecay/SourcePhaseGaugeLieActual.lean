import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterNativeCarrier
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCharge

set_option autoImplicit false
noncomputable section
namespace LowEnergy.PreparationPhysicalPhaseGaugeRealization
open GaussComposite

/-- Literal Lie direction owned by `SourcePhaseGaugeGenerator.sourcePhaseGaugeLie`.
This small owner preserves that expression without importing its field-response spine. -/
def actualSourcePhaseGaugeLie : SourceQuantumScalarChart.NativeLie :=
  -SourceQuantumResidualGaugeSlice.colorGenerator 2-(1/2:ℝ) • nativeY

theorem actualSourcePhaseGaugeLie_literal : actualSourcePhaseGaugeLie =
  -SourceQuantumResidualGaugeSlice.colorGenerator 2-(1/2:ℝ) • nativeY := rfl

end LowEnergy.PreparationPhysicalPhaseGaugeRealization
