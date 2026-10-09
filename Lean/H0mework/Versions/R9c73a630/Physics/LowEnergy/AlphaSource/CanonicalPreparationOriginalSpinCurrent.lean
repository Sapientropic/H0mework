import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalGaussKinetic
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationMovingNoetherLegendre

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeQuantumCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineMatterCovariantDerivativeAffine StageNineDynamicBreakingVacuum
open StageNineFormNativeMatterSpinThreeForm StageNineLorentzConnectionVariation DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeLegendreSource
open PreparationVacuumNoetherChart PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert PreparationVacuumMixedFieldReturn
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator

abbrev Mother:=YangMills.FullPairing.Mother

def sourceSpinField (u : JointParameter) (e : LorentzianCoframe) : StageNineContinuumPointField:=
  toContinuumPointField (sourceConnectionConfiguration u e 0) 0

def sourceSpinIncrementMother (e : LorentzianCoframe) (i : LorentzIndex) : Mother:=
  Complex.I • ∑mu : Fin 4,
    (diracMatrixMatterAction (inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu)).comp
      ((diracExteriorMatterGaugeRepresentation (generatedScalarFrame positiveSmoothUnifiedSource 0 0)⁻¹).comp
        (diracMatrixMatterAction
          (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm (sourceConnectionBasis i)) mu)))

theorem sourceSpinIncrementMother_original (u : JointParameter) (e : LorentzianCoframe) (i : LorentzIndex) :
    sourceSpinIncrementMother e i (sourceSpinField u e).matter=
      matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 0 (sourceSpinField u e)
        (pointwiseMatterLorentzConnectionVariation (sourceSpinField u e) (sourceConnectionBasis i)):=by
  simp only [sourceSpinIncrementMother,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    matterCovariantDerivativeVariationVector,matterCovariantDerivativeKineticSum,
    matterDerivativeFrameRelative,matterFrameRelative,pointwiseMatterLorentzConnectionVariation,
    sourceSpinField,toContinuumPointField,sourceConnectionConfiguration]

def sourceSpinIndependentDual (u : JointParameter) (e : LorentzianCoframe) : Module.Dual ℂ DiracExteriorMatterCarrier:=
  matterDualFrameRelative positiveSmoothUnifiedSource 0 0 (sourceSpinField u e).conjugateMatter

theorem sourceSpinLoad_original (u : JointParameter) (e : LorentzianCoframe) (i : LorentzIndex) :
    sourceLorentzSpinLoad u e i=generatedVolumeDensity (sourceSpinField u e)*
      (sourceSpinIndependentDual u e (sourceSpinIncrementMother e i (sourceSpinField u e).matter)).re:=by
  rw [sourceSpinIncrementMother_original]
  rfl

def sourceSpinMomentum (u : JointParameter) (s : ActionState) : Module.Dual ℂ DiracExteriorMatterCarrier:=
  legendreDual s (sourceSpinIndependentDual u s.1)

def sourceSpinMomentumMother (s : ActionState) (i : LorentzIndex) : Mother:=
  (inverseMomentumMother s).comp (sourceSpinIncrementMother s.1 i)

theorem sourceSpinLoad_momentum (u : JointParameter) (s : ActionState) (valid : s∈validStates) (i : LorentzIndex) :
    sourceLorentzSpinLoad u s.1 i=generatedVolumeDensity (sourceSpinField u s.1)*
      (sourceSpinMomentum u s (sourceSpinMomentumMother s i (sourceSpinField u s.1).matter)).re:=by
  rw [sourceSpinLoad_original]
  have actual:=LinearMap.congr_fun (densityDual_legendre s valid (sourceSpinIndependentDual u s.1))
    (sourceSpinIncrementMother s.1 i (sourceSpinField u s.1).matter)
  change sourceSpinMomentum u s (sourceSpinMomentumMother s i (sourceSpinField u s.1).matter)=
    sourceSpinIndependentDual u s.1 (sourceSpinIncrementMother s.1 i (sourceSpinField u s.1).matter) at actual
  rw [actual]

theorem sourceSpinLoad_sourceMomentum (f : Field289) (z : physicalChart) (i : LorentzIndex) :
    sourceLorentzSpinLoad (f,z.val) (sourceState z.val).1 i=
      generatedVolumeDensity (sourceSpinField (f,z.val) (sourceState z.val).1)*
        (sourceSpinMomentum (f,z.val) (sourceState z.val)
          (sourceSpinMomentumMother (sourceState z.val) i
            (sourceSpinField (f,z.val) (sourceState z.val).1).matter)).re:=by
  have valid : sourceState z.val∈validStates:=
    ⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  exact sourceSpinLoad_momentum (f,z.val) (sourceState z.val) valid i

end LowEnergy.PreparationVacuumCoframeQuantumCurrent
