import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeLocalAction
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeLocalBosonJets
import H0mework.Versions.R2.Physics.Homogeneous.CartanActual

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherEulerKernel
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineDiracKineticLocalSpinDensity StageNineMatterVariation
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineDiracMatterCoordinateCalculus StageNineMatterCovariantDerivativeAffine StageNineCoframeLocalDifferentiability
open Stage9C.Material.SpinPair ActiveGauge SourcePropagationNativeActionHessian
open StageNineConjugateMatterVariation StageNineCoframeVariation
open StageNineP286GaugeConnectionVariationDensity
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction PreparationVacuumLowerClassical
open Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
attribute [local irreducible] nativeConfiguration nativeLocalPoint nativeJetPoint nativeMatterCovariant nativeMatterValue nativeDualValue

private theorem matrix_matter_comp (A B : DiracMatrix) (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction A (diracMatrixMatterAction B matter)=diracMatrixMatterAction (A*B) matter := by
  funext row
  change (∑ col,A row col • ∑ other,B col other • matter other)=
    ∑ other,(∑ col,A row col*B col other) • matter other
  simp only [Finset.smul_sum,Finset.sum_smul,smul_smul]
  rw [Finset.sum_comm]

private theorem coordinate_matrix_comp (A B : DiracMatrix) (coordinates : MatterCoordinateCarrier) :
    diracMatrixMatterCoordinateRealBilinear A (diracMatrixMatterCoordinateRealBilinear B coordinates)=
      diracMatrixMatterCoordinateRealBilinear (A*B) coordinates := by
  simp only [diracMatrixMatterCoordinateRealBilinear_apply,LinearEquiv.symm_apply_apply]
  exact congrArg matterCoordinateEquiv (matrix_matter_comp A B _)

private theorem coordinate_matrix_one (coordinates : MatterCoordinateCarrier) :
    diracMatrixMatterCoordinateRealBilinear 1 coordinates=coordinates := by
  rw [diracMatrixMatterCoordinateRealBilinear_apply]
  have identity (matter : DiracExteriorMatterCarrier) : diracMatrixMatterAction 1 matter=matter := by
    funext row
    simp [diracMatrixMatterAction,Matrix.one_apply]
  rw [identity,LinearEquiv.apply_symm_apply]

theorem rotation_source_smooth : ContDiff ℝ ∞ (ActiveGauge.rotation : BasePoint→DiracMatrix) := by
  apply contDiff_pi.2
  intro row
  apply contDiff_pi.2
  intro col
  by_cases same : row=col
  · subst col
    have value : (fun point : BasePoint=>ActiveGauge.rotation point row row)=fun point=>phaseComponents point row := by
      simp [ActiveGauge.rotation,phaseComponents]
    rw [value]
    exact phaseComponents_smooth row
  · have value : (fun point : BasePoint=>ActiveGauge.rotation point row col)=fun _=>(0 : ℂ) := by
      simp only [ActiveGauge.rotation,Matrix.diagonal_apply,if_neg same]
    rw [value]
    exact contDiff_const

theorem rotation_first_source (point : BasePoint) (mu : Fin 4) :
    fieldDirectionalDerivative ActiveGauge.rotation point mu=if mu=0 then rotationVelocity point else 0 := by
  let read (row col : Fin 4) : DiracMatrix→ₗ[ℝ] ℂ :=
    {toFun:=fun matrix=>matrix row col,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
  have derivative (row col : Fin 4) := (read row col).toContinuousLinearMap.hasFDerivAt.comp point
    (rotation_source_smooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt)
  ext row col
  have entry : fieldDirectionalDerivative (fun position=>ActiveGauge.rotation position row col) point mu=
      (fieldDirectionalDerivative ActiveGauge.rotation point mu) row col := by
    have generated:=derivative row col
    change HasFDerivAt (fun position=>ActiveGauge.rotation position row col) _ point at generated
    rw [fieldDirectionalDerivative,generated.fderiv,fieldDirectionalDerivative]
    rfl
  rw [←entry,rotation_entry_derivative]
  by_cases time : mu=0
  · simp [time,rotationVelocity,Matrix.smul_apply,smul_eq_mul]
  · simp [time]

theorem rotation_velocity_source (point : BasePoint) :
    rotationVelocity point=ActiveGauge.rotation point*rotationVelocity 0 := by
  have commute : diracGammaFive*ActiveGauge.rotation point=ActiveGauge.rotation point*diracGammaFive := by
    simp only [diracGammaFive,ActiveGauge.rotation,Matrix.diagonal_mul_diagonal]
    congr 1
    funext row
    exact mul_comm _ _
  simp only [rotationVelocity,rotation_zero,Matrix.mul_one,Matrix.mul_smul]
  rw [commute]

theorem anchoredSignal_smooth (point : BasePoint) (jet : NativeFirstJet) : ContDiff ℝ ∞ (anchoredSignal point jet) := by
  have value : anchoredSignal point jet=fun position=>affineSignal jet position-∑ mu : Fin 4,point mu • jet.2 mu := by
    funext position
    simp only [anchoredSignal,affineSignal,sub_smul,Finset.sum_sub_distrib]
    abel
  rw [value]
  exact (affineSignal_smooth jet).sub contDiff_const

def unrotatedMatterCoordinates (point : BasePoint) (jet : NativeFirstJet) (position : BasePoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv (actual.matter 0)+primalInsertionCLM (anchoredSignal point jet position)

theorem unrotatedMatterCoordinates_smooth (point : BasePoint) (jet : NativeFirstJet) :
    ContDiff ℝ ∞ (unrotatedMatterCoordinates point jet) :=
  contDiff_const.add (primalInsertionCLM.contDiff.comp (anchoredSignal_smooth point jet))

theorem unrotatedMatterCoordinates_value (point : BasePoint) (jet : NativeFirstJet) :
    unrotatedMatterCoordinates point jet point=matterCoordinateEquiv (nativeMatterValue jet) := by
  rw [unrotatedMatterCoordinates,anchoredSignal_value]
  unfold nativeMatterValue
  simp only [map_add]
  rfl

theorem unrotatedMatterCoordinates_derivative (point : BasePoint) (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (unrotatedMatterCoordinates point jet) point mu=primalInsertionCLM (jet.2 mu) := by
  have generated:=(primalInsertionCLM.hasFDerivAt.comp point (anchoredSignal_hasFDerivAt point jet point)).const_add
    (matterCoordinateEquiv (actual.matter 0))
  change HasFDerivAt (unrotatedMatterCoordinates point jet) _ point at generated
  rw [fieldDirectionalDerivative,generated.fderiv]
  change primalInsertionCLM (jetDerivative jet.2 (coordinateDirection mu))=_
  have value : jetDerivative jet.2 (coordinateDirection mu)=jet.2 mu := by
    simpa only [fieldDirectionalDerivative,(affineSignal_hasFDerivAt jet 0).fderiv] using affineSignal_directionalDerivative jet mu
  rw [value]

theorem nativeMatter_family_rotated (signal : BasePoint→Field289) (point : BasePoint) :
    (nativeConfiguration signal).matter point=
      diracMatrixMatterAction (ActiveGauge.rotation point) (actual.matter 0+primalInsertion (signal point)) := by
  unfold nativeConfiguration
  change actual.matter point+diracMatrixMatterAction (ActiveGauge.rotation point) (primalInsertion (signal point))=_
  rw [map_add,original_matter_rotation,original_matter_rotation 0,rotation_zero]
  have identity (matter : DiracExteriorMatterCarrier) : diracMatrixMatterAction 1 matter=matter := by
    funext row
    simp [diracMatrixMatterAction,Matrix.one_apply]
  rw [identity]

theorem nativeMatter_coordinates_rotated (point : BasePoint) (jet : NativeFirstJet) :
    (fun position=>matterCoordinateEquiv ((nativeConfiguration (anchoredSignal point jet)).matter position))=
      fun position=>diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation position)
        (unrotatedMatterCoordinates point jet position) := by
  funext position
  rw [nativeMatter_family_rotated,diracMatrixMatterCoordinateRealBilinear_apply]
  have unrotated : unrotatedMatterCoordinates point jet position=
      matterCoordinateEquiv (actual.matter 0+primalInsertion (anchoredSignal point jet position)) := by
    simp only [unrotatedMatterCoordinates,map_add]
    rfl
  rw [unrotated,LinearEquiv.symm_apply_apply]

theorem nativeMatter_point_derivative (point : BasePoint) (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative
      (fun position=>matterCoordinateEquiv ((nativeConfiguration (anchoredSignal point jet)).matter position)) point mu=
      diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation point)
        (fieldDirectionalDerivative
          (fun position=>matterCoordinateEquiv ((nativeConfiguration (affineSignal jet)).matter position)) 0 mu) := by
  rw [nativeMatter_coordinates_rotated]
  have base : (fun position=>matterCoordinateEquiv ((nativeConfiguration (affineSignal jet)).matter position))=
      fun position=>diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation position)
        (unrotatedMatterCoordinates 0 jet position) := by
    rw [←anchoredSignal_at_zero]
    exact nativeMatter_coordinates_rotated 0 jet
  rw [base,fieldDirectionalDerivative_diracMatrixMatterCoordinate _ _ rotation_source_smooth (unrotatedMatterCoordinates_smooth point jet),
    fieldDirectionalDerivative_diracMatrixMatterCoordinate _ _ rotation_source_smooth (unrotatedMatterCoordinates_smooth 0 jet)]
  rw [unrotatedMatterCoordinates_value,unrotatedMatterCoordinates_value,
    unrotatedMatterCoordinates_derivative,unrotatedMatterCoordinates_derivative,rotation_first_source,rotation_first_source,rotation_zero,
    map_add,coordinate_matrix_one]
  by_cases time : mu=0
  · simp only [if_pos time]
    rw [rotation_velocity_source point,coordinate_matrix_comp]
  · simp only [if_neg time,map_zero]
    simp

theorem rotation_spin_source (point : BasePoint) (connection : PointwiseLorentzSpinConnection) (mu : Fin 4) :
    ActiveGauge.rotation point*diracSpinConnectionLift connection mu=
      diracSpinConnectionLift connection mu*ActiveGauge.rotation point := by
  unfold diracSpinConnectionLift
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro pair _
  rw [rotation_spin_commutes]

private theorem spin_source_rotated (point : BasePoint) (connection : PointwiseLorentzSpinConnection)
    (mu : Fin 4) (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (diracSpinConnectionLift connection mu) (diracMatrixMatterAction (ActiveGauge.rotation point) matter)=
      diracMatrixMatterAction (ActiveGauge.rotation point) (diracMatrixMatterAction (diracSpinConnectionLift connection mu) matter) := by
  rw [matrix_matter_comp,matrix_matter_comp,rotation_spin_source]

private theorem gauge_source_rotated (point : BasePoint) (matrix : SU7MotherLieAlgebra.SU7MotherLieMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction matrix (diracMatrixMatterAction (ActiveGauge.rotation point) matter)=
      diracMatrixMatterAction (ActiveGauge.rotation point) (diracExteriorMotherLieAction matrix matter) := by
  exact congrArg (fun f : Module.End ℂ DiracExteriorMatterCarrier=>f matter)
    (diracMatrixMatterAction_commutes_internal (ActiveGauge.rotation point) (exteriorSpinorMotherLieAction matrix)).symm

theorem nativeLocalMatterCovariant_rotated (point : BasePoint) (jet : NativeFirstJet) (mu : Fin 4) :
    (nativeLocalPoint point jet).matterCovariantDerivative mu=
      diracMatrixMatterAction (ActiveGauge.rotation point) (nativeMatterCovariant jet mu) := by
  rw [←nativeMatterCovariant_generated]
  have derivative:=nativeMatter_point_derivative point jet mu
  have gravity : (nativeConfiguration (anchoredSignal point jet)).gravityConnection point=
      (nativeConfiguration (affineSignal jet)).gravityConnection 0 := by
    unfold nativeConfiguration
    change actual.gravityConnection point+StageNineLorentzConnectionVariation.lorentzSkewConnectionOfBivectorOneForm
      (fieldLorentz (anchoredSignal point jet point))=_
    simp only [anchoredSignal_value,affineSignal_zero,actual_gravityConnection]
  have gauge : (nativeConfiguration (anchoredSignal point jet)).gaugeConnection point=
      (nativeConfiguration (affineSignal jet)).gaugeConnection 0 := by
    unfold nativeConfiguration
    funext direction
    change actual.gaugeConnection point direction+p286CoordinateEquiv.symm (fieldGauge (anchoredSignal point jet point) direction)=_
    simp only [anchoredSignal_value,affineSignal_zero,actual_gaugeConnection]
  unfold nativeLocalPoint nativePoint toContinuumPointField
  change holonomicMatterCovariantDerivative (nativeConfiguration (anchoredSignal point jet)) point mu=_
  unfold holonomicMatterCovariantDerivative
  rw [derivative,gravity,gauge]
  have values : (nativeConfiguration (anchoredSignal point jet)).matter point=
      diracMatrixMatterAction (ActiveGauge.rotation point) ((nativeConfiguration (affineSignal jet)).matter 0) := by
    rw [nativeMatter_family_rotated,nativeMatterValue_generated]
    rw [anchoredSignal_value]
    unfold nativeMatterValue
    rfl
  rw [values,spin_source_rotated,gauge_source_rotated,map_add,map_add]
  have coordinate (v : MatterCoordinateCarrier) :
      matterCoordinateEquiv.symm (diracMatrixMatterCoordinateRealBilinear (ActiveGauge.rotation point) v)=
        diracMatrixMatterAction (ActiveGauge.rotation point) (matterCoordinateEquiv.symm v) := by
    rw [diracMatrixMatterCoordinateRealBilinear_apply,LinearEquiv.symm_apply_apply]
  rw [coordinate]

theorem rotation_coframe_gamma (point : BasePoint) (coframe : SaturationMonoid.PhysicsCore.LorentzianCoframe)
    (mu : Fin 4) :
    ActiveGauge.rotation point*inverseCoframeDiracGamma {coframe:=coframe,derivative:=0} mu*
      ActiveGauge.rotation point=inverseCoframeDiracGamma {coframe:=coframe,derivative:=0} mu := by
  unfold inverseCoframeDiracGamma
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro internal _
  rw [rotation_gamma_rotation]

theorem nativeLocalKineticPair_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).conjugateMatter
      (generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 point (nativeLocalPoint point jet))=
        (nativeJetPoint jet).conjugateMatter
          (generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)) := by
  rw [nativeLocalDual_rotated]
  have dual : (nativeJetPoint jet).conjugateMatter=nativeDualValue jet := by
    unfold nativeJetPoint
    rfl
  rw [dual]
  have covariant : (nativeJetPoint jet).matterCovariantDerivative=nativeMatterCovariant jet := by
    unfold nativeJetPoint
    rfl
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart,LinearMap.comp_apply,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  rw [nativeLocalMatterCovariant_rotated,nativeLocalCoframe_generated,matrix_matter_comp,matrix_matter_comp]
  rw [rotation_coframe_gamma,covariant]

theorem nativeLocalKineticDensity_generated (point : BasePoint) (jet : NativeFirstJet) :
    generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point (nativeLocalPoint point jet)=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet) := by
  unfold generatedDensitizedContinuumMatterKineticDensity
  simp only [matterDualFrameRelative_zeroChart,nativeLocalKineticPair_generated]
  congr 1
  unfold generatedVolumeDensity
  rw [nativeLocalCoframe_generated]

private theorem dual_rotated_yukawa_zero (force : Field289) (matrix : DiracMatrix)
    (scalar : SU7ExteriorBreakingYukawa.ExteriorBreakingScalarCarrier) (matter : DiracExteriorMatterCarrier) :
    dualInsertion force (diracMatrixMatterAction matrix
      (StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction scalar matter))=0 := by
  change (∑ spin : Fin 4,∑ color : Fin 3,fieldDualComplex force spin color*
    sourceTripletRead (diracMatrixMatterAction matrix
      (StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction scalar matter) spin) color)=0
  apply Finset.sum_eq_zero
  intro spin _
  apply Finset.sum_eq_zero
  intro color _
  have coefficient : sourceTripletRead (diracMatrixMatterAction matrix
      (StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction scalar matter) spin) color=0 := by
    change sourceTripletRead (∑ other : Fin 4,matrix spin other •
      (StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction scalar matter other)) color=0
    unfold sourceTripletRead
    simp only [Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,
      Response.Yukawa.output_degree_two_zero,smul_zero,map_zero,Finsupp.zero_apply,Finset.sum_const_zero]
  rw [coefficient,mul_zero]

theorem nativeLocalYukawaDensity_zero (point : BasePoint) (jet : NativeFirstJet) :
    StageNineDiracDualYukawaLocalSpinDensity.generatedDensitizedContinuumDiracDualYukawaDensity
      positiveSmoothUnifiedSource 0 point (nativeLocalPoint point jet)=0 := by
  unfold StageNineDiracDualYukawaLocalSpinDensity.generatedDensitizedContinuumDiracDualYukawaDensity
    StageNineDiracDualYukawaLocalSpinDensity.generatedContinuumDiracDualYukawaVector
  simp only [matterDualFrameRelative_zeroChart,scalarFrameRelativeCoordinates_zeroChart,matterFrameRelative_zeroChart]
  have dual : (nativeLocalPoint point jet).conjugateMatter=
      actual.conjugateMatter point+(dualInsertion jet.1).comp (diracMatrixMatterAction (ActiveGauge.rotation point)) := by
    unfold nativeLocalPoint nativePoint toContinuumPointField nativeConfiguration
    change actual.conjugateMatter point+(dualInsertion (anchoredSignal point jet point)).comp
      (diracMatrixMatterAction (ActiveGauge.rotation point))=_
    rw [anchoredSignal_value]
  rw [dual,LinearMap.add_apply,actual_conjugateMatter,LinearMap.comp_apply,
    spinPairDual_yukawa_annihilates,dual_rotated_yukawa_zero]
  simp

/-- The same repaired mother density is autonomous in the actual co-rotating full-field coordinates. -/
theorem nativeLocalAction_pointfree (point : BasePoint) (jet : NativeFirstJet) :
    nativeLocalAction point jet=nativeJetDensity jet := by
  rw [nativeLocalAction_original,nativeJetDensity_original,←nativePoint,nativeJetPoint_generated]
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [nativeLocalGravityBF_generated,nativeLocalGravityConstraint_generated,nativeLocalGaugeDensity_generated,
    nativeLocalScalarDensity_generated,nativeLocalKineticDensity_generated,nativeLocalYukawaDensity_zero,nativeYukawaDensity_zero]

theorem nativeLocalAction_family (jet : NativeFirstJet) : (fun point=>nativeLocalAction point jet)=fun _=>nativeJetDensity jet :=
  funext (fun point=>nativeLocalAction_pointfree point jet)

theorem nativeLocalAction_smooth : ContDiffAt ℝ ∞ (fun data : BasePoint×NativeFirstJet=>nativeLocalAction data.1 data.2) 0 := by
  have value : (fun data : BasePoint×NativeFirstJet=>nativeLocalAction data.1 data.2)=fun data=>nativeJetDensity data.2 :=
    funext (fun data=>nativeLocalAction_pointfree data.1 data.2)
  rw [value]
  exact nativeJetDensity_smooth.comp (f:=fun data : BasePoint×NativeFirstJet=>data.2) 0 contDiffAt_snd

theorem nativeLocalAction_atPoint (point : BasePoint) : nativeLocalAction point=nativeJetDensity :=
  funext (fun jet=>nativeLocalAction_pointfree point jet)

/-- The mixed explicit-spacetime momentum term vanishes by the actual source density identity. -/
theorem nativeLocalMomentum_spacetime (jet : NativeFirstJet) (index : NativeJetIndex) (point : BasePoint) :
    HasFDerivAt (𝕜:=ℝ) (fun position=>fderiv ℝ (nativeLocalAction position) jet (nativeJetBasis index)) 0 point := by
  simp only [nativeLocalAction_atPoint]
  exact hasFDerivAt_const _ _

end LowEnergy.SourcePropagationMotherEulerKernel
