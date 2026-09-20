import H0mework.Physics.CartanReduction.P286Dynamics

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Reduction

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineGlobalBundle StageNineHolonomicField
open StageNineFormNativeMotherAction StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity StageNineDiracKineticLocalSpinDensity
open StageNineScalarLocalSpinDensity

noncomputable section

/-- The repaired epoch changes only the Yukawa summand. Its difference is
blind to all gauge and derivative fields that a P286 path writes. -/
theorem diracDual_densityDifference_eq_of_material
    (source : SmoothUnifiedSource) (chart : StageNineChart) (point : BasePoint)
    (before after : StageNineContinuumPointField)
    (coframe : after.coframe = before.coframe)
    (scalar : after.scalar = before.scalar)
    (matter : after.matter = before.matter)
    (conjugate : after.conjugateMatter = before.conjugateMatter) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point after -
        sourceGeneratedFormNativeUnifiedLocalDensity source chart point after =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point before -
        sourceGeneratedFormNativeUnifiedLocalDensity source chart point before := by
  simp only [sourceGeneratedDiracDualFormNativeUnifiedLocalDensity,
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary,
    sourceGeneratedFormNativeUnifiedLocalDensity,
    generatedFormNativeUnifiedLocalDensityAtBoundary,
    generatedDiracDualFormNativeMatterDensity,
    generatedDensitizedContinuumDiracDualMatterDensity,
    generatedDensitizedContinuumScalarDensity,
    generatedDensitizedContinuumMatterKineticDensity,
    generatedDensitizedContinuumDiracDualYukawaDensity,
    generatedFormNativeMatterDensity, generatedContinuumMatterDensity,
    generatedContinuumMatterVector, generatedContinuumMatterKineticVector,
    StageNineMatterCovariantDerivativeAffine.matterCovariantDerivativeVariationVector,
    StageNineMatterCovariantDerivativeAffine.matterCovariantDerivativeKineticSum,
    map_add, Complex.add_re]
  ring_nf
  unfold generatedVolumeDensity generatedContinuumDiracDualYukawaVector
  rw [coframe, scalar, matter, conjugate]

theorem diracDual_densityIncrement_eq_of_material
    (source : SmoothUnifiedSource) (chart : StageNineChart) (point : BasePoint)
    (before after : StageNineContinuumPointField)
    (coframe : after.coframe = before.coframe)
    (scalar : after.scalar = before.scalar)
    (matter : after.matter = before.matter)
    (conjugate : after.conjugateMatter = before.conjugateMatter) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point after -
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point before =
      sourceGeneratedFormNativeUnifiedLocalDensity source chart point after -
        sourceGeneratedFormNativeUnifiedLocalDensity source chart point before := by
  linarith [diracDual_densityDifference_eq_of_material source chart point
    before after coframe scalar matter conjugate]

end
end SaturationMonoid.PhysicsCore.Stage9C.Reduction
