import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeLocalAction
import H0mework.Versions.R2.Physics.Homogeneous.CartanActual
import H0mework.Versions.R2.Physics.SpinPair.GaugeField

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationMotherEulerKernel
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineLorentzConnectionVariation StageNineDiracDualFormNativeMotherAction
open StageNineFormNativeMotherAction StageNineScalarLocalSpinDensity
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart StageNineBlockwiseConstitutive
open Stage9C.Material.SpinPair Stage9C.Reduction SourcePropagationNativeActionHessian
open PreparationVacuumMixedFieldReturn
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
attribute [local irreducible] SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual
local instance : Module.Finite ℝ SU7MotherLieAlgebra.P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem anchoredInsertion_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Field289 →L[ℝ] E) (point : BasePoint) (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (fun x => C (anchoredSignal point jet x)) point mu = C (jet.2 mu) := by
  have derivative := C.hasFDerivAt.comp point (anchoredSignal_hasFDerivAt point jet point)
  change HasFDerivAt (fun x => C (anchoredSignal point jet x)) (C.comp (jetDerivative jet.2)) point at derivative
  rw [fieldDirectionalDerivative,derivative.fderiv]
  change C (jetDerivative jet.2 (coordinateDirection mu)) = _
  apply congrArg C
  simpa only [fieldDirectionalDerivative,(affineSignal_hasFDerivAt jet 0).fderiv] using
    affineSignal_directionalDerivative jet mu

private theorem anchoredGaugeConnectionDerivative (point : BasePoint) (jet : NativeFirstJet)
    (mu nu : Fin 4) :
    p286ConnectionDerivative (nativeConfiguration (anchoredSignal point jet)) point mu nu =
      p286CoordinateEquiv.symm (fieldGauge (jet.2 mu) nu) := by
  unfold p286ConnectionDerivative
  have values : (fun x => p286CoordinateEquiv
      ((nativeConfiguration (anchoredSignal point jet)).gaugeConnection x nu)) =
      fun x => p286CoordinateEquiv (actual.gaugeConnection 0 nu) +
        gaugeCoordinateCLM nu (anchoredSignal point jet x) := by
    funext x
    simp only [nativeConfiguration,actual_gaugeConnection,map_add,LinearEquiv.apply_symm_apply]
    rfl
  rw [values]
  have derivative := ((gaugeCoordinateCLM nu).hasFDerivAt.comp point
    (anchoredSignal_hasFDerivAt point jet point)).const_add
      (p286CoordinateEquiv (actual.gaugeConnection 0 nu))
  change HasFDerivAt (fun x => p286CoordinateEquiv (actual.gaugeConnection 0 nu) + gaugeCoordinateCLM nu (anchoredSignal point jet x)) ((gaugeCoordinateCLM nu).comp (jetDerivative jet.2)) point at derivative
  rw [fieldDirectionalDerivative,derivative.fderiv]
  change p286CoordinateEquiv.symm (fieldGauge (jetDerivative jet.2 (coordinateDirection mu)) nu) = _
  have value : jetDerivative jet.2 (coordinateDirection mu) = jet.2 mu := by
    simpa only [fieldDirectionalDerivative,(affineSignal_hasFDerivAt jet 0).fderiv] using
      affineSignal_directionalDerivative jet mu
  rw [value]

theorem nativeLocalGaugeCurvature_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).gaugeCurvature = (nativeJetPoint jet).gaugeCurvature := by
  change holonomicGaugeCurvature (nativeConfiguration (anchoredSignal point jet)) point = nativeGaugeCurvature jet
  rw [←nativeGaugeCurvature_generated]
  funext pair
  have atZero (mu nu : Fin 4) :
      p286ConnectionDerivative (nativeConfiguration (affineSignal jet)) 0 mu nu =
        p286CoordinateEquiv.symm (fieldGauge (jet.2 mu) nu) := by
    simpa only [anchoredSignal_at_zero] using anchoredGaugeConnectionDerivative 0 jet mu nu
  unfold holonomicGaugeCurvature
  rw [anchoredGaugeConnectionDerivative,anchoredGaugeConnectionDerivative,atZero,atZero]
  simp only [nativeConfiguration,anchoredSignal_value,affineSignal_zero,actual_gaugeConnection]

theorem nativeLocalScalarCovariant_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).scalarCovariantDerivative =
      (nativeJetPoint jet).scalarCovariantDerivative := by
  change holonomicScalarCovariantDerivative (nativeConfiguration (anchoredSignal point jet)) point = nativeScalarCovariant jet
  funext mu
  unfold holonomicScalarCovariantDerivative nativeScalarCovariant
  have values : (nativeConfiguration (anchoredSignal point jet)).scalar =
      fun x => actual.scalar 0 + scalarInsertionCLM (anchoredSignal point jet x) := by
    funext x
    simp only [nativeConfiguration,actual_scalar]
    rfl
  have derivative : fieldDirectionalDerivative
      (nativeConfiguration (anchoredSignal point jet)).scalar point mu = fieldScalar (jet.2 mu) := by
    rw [values]
    have generated := (scalarInsertionCLM.hasFDerivAt.comp point
      (anchoredSignal_hasFDerivAt point jet point)).const_add (actual.scalar 0)
    change HasFDerivAt (fun x => actual.scalar 0 + scalarInsertionCLM (anchoredSignal point jet x)) (scalarInsertionCLM.comp (jetDerivative jet.2)) point at generated
    rw [fieldDirectionalDerivative,generated.fderiv]
    change fieldScalar (jetDerivative jet.2 (coordinateDirection mu)) = _
    apply congrArg fieldScalar
    simpa only [fieldDirectionalDerivative,(affineSignal_hasFDerivAt jet 0).fderiv] using
      affineSignal_directionalDerivative jet mu
  rw [derivative]
  simp only [nativeConfiguration,anchoredSignal_value,actual_scalar,actual_gaugeConnection]

private theorem anchoredGravityConnectionDerivative (point : BasePoint) (jet : NativeFirstJet)
    (mu nu a b : Fin 4) :
    gravityConnectionDerivative (nativeConfiguration (anchoredSignal point jet)) point mu nu a b =
      lorentzInsertionCLM (jet.2 mu) nu a b := by
  have insertion := lorentzInsertionCLM.hasFDerivAt.comp point
    (anchoredSignal_hasFDerivAt point jet point)
  let evaluation : PointwiseLorentzSpinConnection →ₗ[ℝ] ℝ :=
    { toFun := fun w => w nu a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have entry := evaluation.toContinuousLinearMap.hasFDerivAt.comp point insertion
  have values : (fun x => (nativeConfiguration (anchoredSignal point jet)).gravityConnection x nu a b) =
      fun x => actual.gravityConnection 0 nu a b + evaluation.toContinuousLinearMap
        (lorentzInsertionCLM (anchoredSignal point jet x)) := by
    funext x
    simp only [nativeConfiguration,actual_gravityConnection]
    rfl
  have derivative := entry.const_add (actual.gravityConnection 0 nu a b)
  change HasFDerivAt (fun x => actual.gravityConnection 0 nu a b + evaluation.toContinuousLinearMap (lorentzInsertionCLM (anchoredSignal point jet x))) _ point at derivative
  unfold gravityConnectionDerivative
  rw [values,derivative.fderiv]
  change lorentzInsertionCLM (jetDerivative jet.2 (coordinateDirection mu)) nu a b = _
  have value : jetDerivative jet.2 (coordinateDirection mu) = jet.2 mu := by
    simpa only [fieldDirectionalDerivative,(affineSignal_hasFDerivAt jet 0).fderiv] using
      affineSignal_directionalDerivative jet mu
  rw [value]

theorem nativeLocalGravityCurvature_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).gravityCurvature = (nativeJetPoint jet).gravityCurvature := by
  change holonomicGravityCurvature (nativeConfiguration (anchoredSignal point jet)) point = nativeGravityCurvature jet
  rw [←nativeGravityCurvature_generated]
  funext internal pair
  have atZero (mu nu a b : Fin 4) :
      gravityConnectionDerivative (nativeConfiguration (affineSignal jet)) 0 mu nu a b =
        lorentzInsertionCLM (jet.2 mu) nu a b := by
    simpa only [anchoredSignal_at_zero] using anchoredGravityConnectionDerivative 0 jet mu nu a b
  unfold holonomicGravityCurvature
  dsimp only
  rw [anchoredGravityConnectionDerivative,anchoredGravityConnectionDerivative,atZero,atZero]
  simp only [nativeConfiguration,anchoredSignal_value,affineSignal_zero,actual_gravityConnection]

private theorem actualGravityAuxiliary_at (point : BasePoint) :
    actual.gravityAuxiliary point = actual.gravityAuxiliary 0 := by
  unfold actual algebraicCartanReduction
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary]
  rfl

theorem nativeLocalGravityAuxiliary_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).gravityAuxiliary = (nativeJetPoint jet).gravityAuxiliary := by
  change actual.gravityAuxiliary point + fieldGravityB (anchoredSignal point jet point) = _
  rw [anchoredSignal_value,actualGravityAuxiliary_at]
  rfl

theorem nativeLocalGravityMultiplier_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).gravitySimplicityMultiplier = (nativeJetPoint jet).gravitySimplicityMultiplier := by
  change actual.gravitySimplicityMultiplier point + fieldMultiplier (anchoredSignal point jet point) = _
  dsimp only [nativeJetPoint]
  rw [anchoredSignal_value,actual_gravitySimplicityMultiplier]

theorem nativeLocalGaugeAuxiliary_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).gaugeAuxiliary = (nativeJetPoint jet).gaugeAuxiliary := by
  funext pair
  change actual.gaugeAuxiliary point pair + gaugeBInsertion (anchoredSignal point jet point) pair = _
  dsimp only [nativeJetPoint]
  rw [anchoredSignal_value,actual_gaugeAuxiliary]

theorem nativeLocalGravityBF_generated (point : BasePoint) (jet : NativeFirstJet) :
    generatedFormNativeGravityBFDensity (nativeLocalPoint point jet) =
      generatedFormNativeGravityBFDensity (nativeJetPoint jet) := by
  unfold generatedFormNativeGravityBFDensity
  rw [nativeLocalGravityAuxiliary_generated,nativeLocalGravityCurvature_generated]

theorem nativeLocalGravityConstraint_generated (point : BasePoint) (jet : NativeFirstJet) :
    generatedFormNativeGravityConstraintDensity (nativeLocalPoint point jet) =
      generatedFormNativeGravityConstraintDensity (nativeJetPoint jet) := by
  unfold generatedFormNativeGravityConstraintDensity generatedGravitySimplicityResidual
  rw [nativeLocalGravityMultiplier_generated,nativeLocalGravityAuxiliary_generated,nativeLocalCoframe_generated]

theorem nativeLocalGaugeDensity_generated (point : BasePoint) (jet : NativeFirstJet) :
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (nativeLocalPoint point jet) =
    generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (nativeJetPoint jet) := by
  unfold generatedFormNativeGaugeDensityAtBoundary
  rw [nativeLocalCoframe_generated,nativeLocalGaugeCurvature_generated,nativeLocalGaugeAuxiliary_generated]

theorem nativeLocalScalarDensity_generated (point : BasePoint) (jet : NativeFirstJet) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 point (nativeLocalPoint point jet) =
      generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet) := by
  unfold generatedDensitizedContinuumScalarDensity generatedVolumeDensity generatedScalarKineticDensity
    scalarFrameRelativeCovariantDerivative generatedScalarPotential
  simp only [scalarFrameRelativeCoordinates_zeroChart,nativeLocalCoframe_generated,
    nativeLocalScalarCovariant_generated,nativeLocalScalar_generated]

end LowEnergy.SourcePropagationMotherEulerKernel
