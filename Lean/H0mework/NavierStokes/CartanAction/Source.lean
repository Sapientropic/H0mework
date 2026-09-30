import H0mework.NavierStokes.MaterialAction.SourceAdjoint
import H0mework.Physics.CartanAction.CartanConnectionActualization

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeSourceCartan

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineLorentzConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineCoframeLocalDifferentiability StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineFormNativeMatterSpinThreeForm
open StageNineMatterVariation StageNineFormNativeLorentzGeometricFirstVariation
open StageNineMatterCovariantDerivativeAffine StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalGravityCurvatureVariancePairing StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalLorentzThreeFormDualInverse
open StageNineCartanContorsionTorsionEquiv StageNineCartanTorsionThreeFormEquiv
open StageNineCartanAffineConnectionActualization StageNineCartanTorsionThreeFormCoordinates
open StageNineCoframeFirstJet StageNineIIPlusRestriction
open StageNineDiracDualFormNativeCartanConnectionActualization
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliCoframeAction NativeMaterialJetAction NativeMaterialAdjointPrincipal NativeMaterialMomentumJet

noncomputable section

def bivectorConnectionLinear : LorentzBivectorOneForm →ₗ[ℝ] PointwiseLorentzSpinConnection where
  toFun := lorentzSkewConnectionOfBivectorOneForm
  map_add' := lorentzSkewConnectionOfBivectorOneForm_add
  map_smul' := lorentzSkewConnectionOfBivectorOneForm_smul

def spinMatrixResponse (velocity : PhysicalSpace) (direction : Fin 4) : DiracMatrix →ₗ[ℝ] ℝ where
  toFun matrix := volumeFactor velocity * (NativeCanonicalFluidCoframe.dual velocity
    (principal velocity direction (diracMatrixMatterAction matrix (NativeCanonicalFluidCoframe.matter velocity)))).re
  map_add' := by
    intro first second
    simp only [coframeDiracMatrixMatterAction_add_matrix, map_add, Complex.add_re, mul_add]
  map_smul' := by
    intro scalar matrix
    rw [diracMatrixMatterAction_real_smul_matrix_local]
    change volumeFactor velocity * (NativeCanonicalFluidCoframe.dual velocity
      (principal velocity direction ((scalar : ℂ) • diracMatrixMatterAction matrix (NativeCanonicalFluidCoframe.matter velocity)))).re =
      scalar * (volumeFactor velocity * (NativeCanonicalFluidCoframe.dual velocity
        (principal velocity direction (diracMatrixMatterAction matrix (NativeCanonicalFluidCoframe.matter velocity)))).re)
    simp only [map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring

def spinLinear (velocity : PhysicalSpace) : LorentzBivectorOneForm →ₗ[ℝ] ℝ :=
  ∑ direction, (spinMatrixResponse velocity direction).comp
    ((diracSpinConnectionLiftLinear direction).comp bivectorConnectionLinear)

def spinCLM (velocity : PhysicalSpace) : LorentzBivectorOneForm →L[ℝ] ℝ :=
  (spinLinear velocity).toContinuousLinearMap

theorem spinCLM_apply (velocity : PhysicalSpace) (direction : LorentzBivectorOneForm) :
    spinCLM velocity direction = volumeFactor velocity * (NativeCanonicalFluidCoframe.dual velocity
      (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (fun index =>
        diracMatrixMatterAction (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm direction) index)
          (NativeCanonicalFluidCoframe.matter velocity)))).re := by
  change spinLinear velocity direction = _
  simp only [spinLinear, LinearMap.sum_apply,
    LinearMap.comp_apply, diracSpinConnectionLiftLinear_apply, bivectorConnectionLinear,
    spinMatrixResponse, principal, LinearMap.smul_apply, gaugeVectorAt,
    Finset.smul_sum, map_sum, Complex.re_sum, Finset.mul_sum]
  rfl

theorem spinCLM_eq_mother (velocity : PhysicalSpace) (source : SmoothUnifiedSource)
    (point : ProofFreeRicherAnholonomicSource.BasePoint) (field : StageNineContinuumPointField)
    (frame : field.coframe = NativeCanonicalFluidCoframe.coframe velocity)
    (matter : field.matter = NativeCanonicalFluidCoframe.matter velocity)
    (dual : field.conjugateMatter = NativeCanonicalFluidCoframe.dual velocity) :
    spinCLM velocity = formNativeLorentzMatterFirstContinuousLinearMap source 0 point field := by
  ext direction
  simp only [spinCLM_apply, formNativeLorentzMatterFirstContinuousLinearMap_apply,
    formNativeLorentzMatterFirstCoefficient, generatedVolumeDensity,
    matterCovariantDerivativeFirstVariationDensity, matterDualFrameRelative_zeroChart,
    matterCovariantDerivativeVariationVector, matterCovariantDerivativeKineticSum,
    matterDerivativeFrameRelative_zeroChart, pointwiseMatterLorentzConnectionVariation,
    frame, matter, dual, volumeFactor, gaugeVectorAt]

def spinResponse (velocity : PhysicalSpace) : PhysicalBivectorThreeForm :=
  -lorentzOneFormContinuousDualThreeForm (spinCLM velocity)

theorem spinResponse_eq_mother (velocity : PhysicalSpace) (source : SmoothUnifiedSource)
    (point : ProofFreeRicherAnholonomicSource.BasePoint) (field : StageNineContinuumPointField)
    (frame : field.coframe = NativeCanonicalFluidCoframe.coframe velocity)
    (matter : field.matter = NativeCanonicalFluidCoframe.matter velocity)
    (dual : field.conjugateMatter = NativeCanonicalFluidCoframe.dual velocity) :
    spinResponse velocity = formNativePhysicalSpinCurrentThreeForm source 0 point field := by
  rw [spinResponse, spinCLM_eq_mother velocity source point field frame matter dual]
  rfl

def torsion (velocity : PhysicalSpace) : PointwiseCartanTorsionTwoForm :=
  cartanTorsionOfThreeForm (NativeCanonicalFluidCoframe.coframe velocity) (spinResponse velocity)

def contorsion (velocity : PhysicalSpace) : LorentzBivectorOneForm :=
  contorsionOfCartanTorsion (NativeCanonicalFluidCoframe.coframe velocity) (torsion velocity)

def connection (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) : PointwiseLorentzSpinConnection :=
  cartanAffineSpinConnection (geometry velocity derivative) (contorsion velocity)

/-- The original KIN-3 inverse consumes the same action-signed W13 response. -/
theorem torsion_response (velocity : PhysicalSpace) :
    cartanTorsionThreeForm (NativeCanonicalFluidCoframe.coframe velocity) (torsion velocity) = spinResponse velocity := by
  simpa only [torsion] using cartanTorsionOfThreeForm_rightInverse
    (NativeCanonicalFluidCoframe.coframe velocity) (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity) (spinResponse velocity)

/-- The actual torsion of the produced connection is the source action's typed torsion. -/
theorem connection_torsion (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    actualPointwiseCartanTorsionTwoForm (geometry velocity derivative) (connection velocity derivative) = torsion velocity := by
  have nondegenerate : Matrix.det (geometry velocity derivative).coframe ≠ 0 :=
    NativeCanonicalFluidCoframe.coframe_nondegenerate velocity
  have actual := actualPointwiseCartanTorsionTwoForm_cartanAffineSpinConnection
    (geometry velocity derivative) nondegenerate (contorsion velocity)
  rw [show (geometry velocity derivative).coframe = NativeCanonicalFluidCoframe.coframe velocity from rfl] at actual
  have inverse := contorsionOfCartanTorsion_rightInverse (NativeCanonicalFluidCoframe.coframe velocity)
    (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity) (torsion velocity)
  exact actual.trans inverse

/-- Exact agreement with the original repaired-action Cartan producer on every full-field extension of this source jet. -/
theorem connection_eq_mother (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (source : SmoothUnifiedSource) (configuration : StageNineHolonomicConfiguration)
    (point : ProofFreeRicherAnholonomicSource.BasePoint)
    (frameJet : holonomicCoframeFirstJetAt configuration.coframe point = geometry velocity derivative)
    (matter : configuration.matter point = NativeCanonicalFluidCoframe.matter velocity)
    (dual : configuration.conjugateMatter point = NativeCanonicalFluidCoframe.dual velocity) :
    connection velocity derivative = diracDualFormNativeActionCartanConnectionAt source configuration point := by
  have frame : configuration.coframe point = NativeCanonicalFluidCoframe.coframe velocity :=
    congrArg PointwiseLorentzianCoframeJet.coframe frameJet
  have spin : spinResponse velocity = diracDualFormNativeActionSpinResponseAt source configuration point := by
    exact spinResponse_eq_mother velocity source point
      (toContinuumPointField (restrictHolonomicConfigurationToIIPlus configuration) point) frame matter dual
  simp only [connection, contorsion, torsion, diracDualFormNativeActionCartanConnectionAt,
    diracDualFormNativeActionCartanContorsionAt, diracDualFormNativeActionCartanTorsionAt,
    frameJet, frame, ← spin]

end
end SaturationMonoid.NavierStokes.NativeSourceCartan
