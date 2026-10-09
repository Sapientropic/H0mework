import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeLocalDiracJets

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationMotherEulerKernel
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineLorentzConnectionVariation StageNineDiracDualFormNativeMotherAction
open StageNineDiracMatterCoordinateCalculus StageNineMatterVariation
open DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair ActiveGauge SourcePropagationNativeActionHessian
open PreparationVacuumMixedFieldReturn
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
attribute [local irreducible] SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual
attribute [local irreducible] nativeConfiguration nativePoint nativeLocalPoint nativeJetPoint nativeDensity
local instance : Module.Finite ℝ SU7MotherLieAlgebra.P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-- The value and four actual directional derivatives at the same spacetime occurrence. -/
def signalFirstJet (signal : BasePoint → Field289) (point : BasePoint) : NativeFirstJet :=
  (signal point,fun mu => fieldDirectionalDerivative signal point mu)

private theorem coordinate_reconstruction (vector : BasePoint) :
    vector = ∑ mu : Fin 4,vector mu • coordinateDirection mu := by
  ext nu
  simp [coordinateDirection,PiLp.single_apply,Pi.single_apply]

theorem signalFirstJet_derivative (signal : BasePoint → Field289) (point : BasePoint) :
    jetDerivative (signalFirstJet signal point).2 = fderiv ℝ signal point := by
  apply ContinuousLinearMap.ext
  intro vector
  simp only [jetDerivative,sum_apply,ContinuousLinearMap.smulRight_apply]
  change (∑ mu : Fin 4,vector mu • fieldDirectionalDerivative signal point mu) =
    fderiv ℝ signal point vector
  conv_rhs => rw [coordinate_reconstruction vector]
  simp only [map_sum,map_smul,fieldDirectionalDerivative]

theorem signalFirstJet_hasFDerivAt (signal : BasePoint → Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) :
    HasFDerivAt signal (jetDerivative (signalFirstJet signal point).2) point := by
  rw [signalFirstJet_derivative]
  exact differentiable.hasFDerivAt

private theorem linearSignal_firstGerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Field289 →L[ℝ] E) (background : BasePoint → E) (point : BasePoint)
    (backgroundDerivative : DifferentiableAt ℝ background point)
    (signal : BasePoint → Field289) (differentiable : DifferentiableAt ℝ signal point) :
    fderiv ℝ (fun x => background x + C (signal x)) point =
      fderiv ℝ (fun x => background x + C (anchoredSignal point (signalFirstJet signal point) x)) point := by
  have left := backgroundDerivative.hasFDerivAt.add
    (C.hasFDerivAt.comp point (signalFirstJet_hasFDerivAt signal point differentiable))
  have right := backgroundDerivative.hasFDerivAt.add
    (C.hasFDerivAt.comp point (anchoredSignal_hasFDerivAt point (signalFirstJet signal point) point))
  change HasFDerivAt (fun x => background x + C (signal x)) _ point at left
  change HasFDerivAt (fun x => background x + C (anchoredSignal point (signalFirstJet signal point) x)) _ point at right
  rw [left.fderiv,right.fderiv]

private theorem signalGravity_firstGerm (signal : BasePoint → Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (mu nu a b : Fin 4) :
    gravityConnectionDerivative (nativeConfiguration signal) point mu nu a b =
      gravityConnectionDerivative (nativeConfiguration (anchoredSignal point (signalFirstJet signal point)))
        point mu nu a b := by
  let evaluation : PointwiseLorentzSpinConnection →ₗ[ℝ] ℝ :=
    { toFun := fun w => w nu a b,map_add' := fun _ _ => rfl,map_smul' := fun _ _ => rfl }
  let C := evaluation.toContinuousLinearMap.comp lorentzInsertionCLM
  have background : DifferentiableAt ℝ (fun x : BasePoint => actual.gravityConnection x nu a b) point :=
    ((actual_smooth.2.1 nu a b).differentiable (by simp)).differentiableAt
  have generated := linearSignal_firstGerm C (fun x => actual.gravityConnection x nu a b)
    point background signal differentiable
  unfold gravityConnectionDerivative nativeConfiguration
  change (fderiv ℝ (fun x => actual.gravityConnection x nu a b+C (signal x)) point) (coordinateDirection mu) =
    (fderiv ℝ (fun x => actual.gravityConnection x nu a b+C (anchoredSignal point (signalFirstJet signal point) x)) point) (coordinateDirection mu)
  rw [generated]

private theorem signalGauge_firstGerm (signal : BasePoint → Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (mu nu : Fin 4) :
    p286ConnectionDerivative (nativeConfiguration signal) point mu nu =
      p286ConnectionDerivative (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))) point mu nu := by
  have background : DifferentiableAt ℝ
      (fun x => p286CoordinateEquiv (actual.gaugeConnection x nu)) point :=
    ((actual_smooth.2.2.2.2.1 nu).differentiable (by simp)).differentiableAt
  have values (signal : BasePoint → Field289) :
      (fun x => p286CoordinateEquiv ((nativeConfiguration signal).gaugeConnection x nu)) =
        fun x => p286CoordinateEquiv (actual.gaugeConnection x nu)+gaugeCoordinateCLM nu (signal x) := by
    funext x
    simp only [nativeConfiguration,map_add,LinearEquiv.apply_symm_apply]
    rfl
  unfold p286ConnectionDerivative fieldDirectionalDerivative
  rw [values,values,linearSignal_firstGerm (gaugeCoordinateCLM nu) _ point background signal differentiable]

private theorem signalScalar_firstGerm (signal : BasePoint → Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (mu : Fin 4) :
    fieldDirectionalDerivative (nativeConfiguration signal).scalar point mu =
      fieldDirectionalDerivative (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))).scalar point mu := by
  have background : DifferentiableAt ℝ actual.scalar point :=
    (actual_smooth.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  unfold fieldDirectionalDerivative nativeConfiguration
  change (fderiv ℝ (fun x => actual.scalar x+scalarInsertionCLM (signal x)) point) (coordinateDirection mu) =
    (fderiv ℝ (fun x => actual.scalar x+scalarInsertionCLM (anchoredSignal point (signalFirstJet signal point) x)) point) (coordinateDirection mu)
  rw [linearSignal_firstGerm scalarInsertionCLM actual.scalar point background signal differentiable]

private theorem signalMatter_coordinates (signal : BasePoint → Field289) :
    (fun x => matterCoordinateEquiv ((nativeConfiguration signal).matter x)) =
      fun x => diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation x)
        (matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal x)) := by
  funext x
  rw [nativeMatter_family_rotated,diracMatrixMatterCoordinateRealBilinear_apply]
  have value : matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (signal x) =
      matterCoordinateEquiv (actual.matter 0+primalInsertion (signal x)) := by
    rw [map_add]
    rfl
  rw [value,LinearEquiv.symm_apply_apply]

private theorem bilinearSignal_firstGerm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (matrix : BasePoint → E) (point : BasePoint)
    (matrixDerivative : DifferentiableAt ℝ matrix point) (C : Field289 →L[ℝ] F) (initial : F)
    (signal : BasePoint → Field289) (differentiable : DifferentiableAt ℝ signal point) :
    fderiv ℝ (fun x => B (matrix x) (initial+C (signal x))) point =
      fderiv ℝ (fun x => B (matrix x) (initial+C (anchoredSignal point (signalFirstJet signal point) x))) point := by
  have left := (C.hasFDerivAt.comp point
    (signalFirstJet_hasFDerivAt signal point differentiable)).const_add initial
  have right := (C.hasFDerivAt.comp point
    (anchoredSignal_hasFDerivAt point (signalFirstJet signal point) point)).const_add initial
  change HasFDerivAt (fun x => initial+C (signal x)) _ point at left
  change HasFDerivAt (fun x => initial+C (anchoredSignal point (signalFirstJet signal point) x)) _ point at right
  rw [B.fderiv_of_bilinear matrixDerivative left.differentiableAt,
    B.fderiv_of_bilinear matrixDerivative right.differentiableAt,left.fderiv,right.fderiv,
    anchoredSignal_value]
  rfl

private theorem signalMatter_firstGerm (signal : BasePoint → Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) (mu : Fin 4) :
    fieldDirectionalDerivative (fun x => matterCoordinateEquiv ((nativeConfiguration signal).matter x)) point mu =
      fieldDirectionalDerivative
        (fun x => matterCoordinateEquiv
          ((nativeConfiguration (anchoredSignal point (signalFirstJet signal point))).matter x)) point mu := by
  rw [signalMatter_coordinates,signalMatter_coordinates]
  have matrixDerivative : DifferentiableAt ℝ ActiveGauge.rotation point :=
    (rotation_source_smooth.differentiable (by simp)).differentiableAt
  have generated := bilinearSignal_firstGerm
    diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap ActiveGauge.rotation point
      matrixDerivative primalInsertionCLM (matterCoordinateEquiv (actual.matter 0)) signal differentiable
  unfold fieldDirectionalDerivative
  exact congrArg (fun derivative => derivative (coordinateDirection mu)) generated

/-- The complete original point field factors through the signal's actual first germ. -/
theorem nativePoint_signalFirstJet (signal : BasePoint → Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) :
    nativePoint signal point = nativeLocalPoint point (signalFirstJet signal point) := by
  unfold nativeLocalPoint nativePoint
  apply StageNineContinuumPointField.ext
  · simp only [toContinuumPointField,nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · change holonomicGravityCurvature (nativeConfiguration signal) point =
      holonomicGravityCurvature (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))) point
    funext internal pair
    unfold holonomicGravityCurvature
    dsimp only
    rw [signalGravity_firstGerm signal point differentiable,signalGravity_firstGerm signal point differentiable]
    simp only [nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · simp only [toContinuumPointField,nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · simp only [toContinuumPointField,nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · change holonomicGaugeCurvature (nativeConfiguration signal) point =
      holonomicGaugeCurvature (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))) point
    funext pair
    unfold holonomicGaugeCurvature
    rw [signalGauge_firstGerm signal point differentiable,signalGauge_firstGerm signal point differentiable]
    simp only [nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · simp only [toContinuumPointField,nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · simp only [toContinuumPointField,nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · change holonomicScalarCovariantDerivative (nativeConfiguration signal) point =
      holonomicScalarCovariantDerivative (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))) point
    funext mu
    unfold holonomicScalarCovariantDerivative
    rw [signalScalar_firstGerm signal point differentiable]
    simp only [nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · simp only [toContinuumPointField,nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · change holonomicMatterCovariantDerivative (nativeConfiguration signal) point =
      holonomicMatterCovariantDerivative (nativeConfiguration (anchoredSignal point (signalFirstJet signal point))) point
    funext mu
    unfold holonomicMatterCovariantDerivative
    rw [signalMatter_firstGerm signal point differentiable]
    simp only [nativeConfiguration,anchoredSignal_value,signalFirstJet]
  · simp only [toContinuumPointField,nativeConfiguration,anchoredSignal_value,signalFirstJet]

theorem nativeDensity_signalFirstJet (signal : BasePoint → Field289) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ signal point) :
    nativeDensity signal point = nativeJetDensity (signalFirstJet signal point) := by
  have density : nativeDensity signal point = nativeLocalAction point (signalFirstJet signal point) := by
    unfold nativeLocalAction nativeDensity
    rw [nativePoint_signalFirstJet signal point differentiable]
    unfold nativeLocalPoint
    rfl
  exact density.trans (nativeLocalAction_pointfree point (signalFirstJet signal point))

end LowEnergy.SourcePropagationMotherEulerKernel
