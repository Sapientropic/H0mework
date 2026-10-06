import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationActualNativeHistoryReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherEulerKernel
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeJointResidualCarrier SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory
open PreparationVacuumMixedFieldReturn
open DiracExteriorMatterAction Stage9C.Material.SpinPair SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge
open scoped BigOperators Topology ContDiff
attribute [local irreducible] nativeDensity nativeConfiguration nativePoint nativeEuler

/-- The same physical first jet, centered at the actual spacetime occurrence. -/
def anchoredSignal (point : BasePoint) (jet : NativeFirstJet) (position : BasePoint) : Field289 :=
  jet.1+∑ mu : Fin 4,(position mu-point mu) • jet.2 mu

theorem anchoredSignal_value (point : BasePoint) (jet : NativeFirstJet) : anchoredSignal point jet point=jet.1 := by
  simp only [anchoredSignal,sub_self,zero_smul,Finset.sum_const_zero,add_zero]

theorem anchoredSignal_at_zero (jet : NativeFirstJet) : anchoredSignal 0 jet=affineSignal jet := by
  funext point
  simp [anchoredSignal,affineSignal]

theorem anchoredSignal_hasFDerivAt (point : BasePoint) (jet : NativeFirstJet) (position : BasePoint) :
    HasFDerivAt (anchoredSignal point jet) (jetDerivative jet.2) position := by
  have original:=(affineSignal_hasFDerivAt jet position).sub_const (∑ mu : Fin 4,point mu • jet.2 mu)
  convert! original using 1
  funext p
  simp only [anchoredSignal,affineSignal,sub_smul,Finset.sum_sub_distrib]
  abel

theorem anchoredSignal_directionalDerivative (point : BasePoint) (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (anchoredSignal point jet) point mu=jet.2 mu := by
  rw [fieldDirectionalDerivative,(anchoredSignal_hasFDerivAt point jet point).fderiv]
  simpa only [fieldDirectionalDerivative,(affineSignal_hasFDerivAt jet 0).fderiv] using
    affineSignal_directionalDerivative jet mu

/-- All native value and first-derivative slots still come from the original nine-group lift. -/
def nativeLocalPoint (point : BasePoint) (jet : NativeFirstJet) : StageNineContinuumPointField :=
  nativePoint (anchoredSignal point jet) point

def nativeLocalAction (point : BasePoint) (jet : NativeFirstJet) : ℝ :=
  nativeDensity (anchoredSignal point jet) point

theorem nativeLocalAction_original (point : BasePoint) (jet : NativeFirstJet) :
    nativeLocalAction point jet=generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      positiveSmoothUnifiedSource (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 0 point
        (nativeLocalPoint point jet) := by
  unfold nativeLocalAction nativeLocalPoint nativePoint
  exact nativeDensity_original _ _

theorem nativeLocalAction_zero (jet : NativeFirstJet) : nativeLocalAction 0 jet=nativeJetDensity jet := by
  rw [nativeLocalAction,anchoredSignal_at_zero]
  rfl

def localNativeActionJet (point : BasePoint) (jet : NativeFirstJet) : DiracDualFormNativePointwiseActionJetCarrier :=
  nativeActionJet (anchoredSignal point jet) point

def localNativeJointEuler (point : BasePoint) (jet : NativeFirstJet) : DiracDualFormNativePointwiseJointResidualCarrier :=
  nativeEuler (anchoredSignal point jet) point

theorem localNativeJointEuler_original (point : BasePoint) (jet : NativeFirstJet) :
    localNativeJointEuler point jet=diracDualFormNativePointwiseJointResidual
      positiveSmoothUnifiedSource (nativeConfiguration (anchoredSignal point jet)) point :=
  nativeEuler_original _ _

theorem localNativeActionJet_point (point : BasePoint) (jet : NativeFirstJet) :
    (localNativeActionJet point jet).pointField=nativeLocalPoint point jet :=
  nativeActionJet_pointField _ _

private theorem matrix_one_matter (field : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction 1 field=field := by
  funext spin
  simp [diracMatrixMatterAction,Matrix.one_apply]

theorem nativeLocalMatter_rotated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).matter=diracMatrixMatterAction (SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation point) (nativeMatterValue jet) := by
  unfold nativeLocalPoint nativePoint toContinuumPointField nativeConfiguration
  change actual.matter point+diracMatrixMatterAction (SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation point) (primalInsertion (anchoredSignal point jet point))=_
  rw [anchoredSignal_value,nativeMatterValue,map_add,original_matter_rotation,original_matter_rotation 0,rotation_zero,matrix_one_matter]

theorem nativeLocalDual_rotated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).conjugateMatter=(nativeDualValue jet).comp (diracMatrixMatterAction (SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation point)) := by
  unfold nativeLocalPoint nativePoint toContinuumPointField nativeConfiguration
  change actual.conjugateMatter point+(dualInsertion (anchoredSignal point jet point)).comp (diracMatrixMatterAction (SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation point))=_
  rw [anchoredSignal_value,nativeDualValue,original_dual_rotation,original_dual_rotation 0,rotation_zero]
  apply LinearMap.ext
  intro field
  simp only [LinearMap.comp_apply,LinearMap.add_apply,matrix_one_matter]

theorem nativeLocalCoframe_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).coframe=(nativeJetPoint jet).coframe := by
  unfold nativeLocalPoint nativePoint toContinuumPointField nativeConfiguration
  dsimp only [nativeJetPoint]
  rw [anchoredSignal_value,actual_coframe]

theorem nativeLocalScalar_generated (point : BasePoint) (jet : NativeFirstJet) :
    (nativeLocalPoint point jet).scalar=(nativeJetPoint jet).scalar := by
  unfold nativeLocalPoint nativePoint toContinuumPointField nativeConfiguration
  dsimp only [nativeJetPoint]
  rw [anchoredSignal_value,actual_scalar]

theorem phaseComponents_first_at (point : BasePoint) (spin : Fin 4) :
    HasFDerivAt (fun x : BasePoint=>phaseComponents x spin)
      ((EuclideanSpace.proj (0 : Fin 4) : BasePoint→L[ℝ] ℝ).smulRight
        (phaseComponents point spin*phaseComponentVelocity spin)) point := by
  fin_cases spin
  · simpa [phaseComponents,phaseComponentVelocity,upperPhase] using phase_hasFDerivAt frequency point
  · simpa [phaseComponents,phaseComponentVelocity,upperPhase] using phase_hasFDerivAt frequency point
  · simpa [phaseComponents,phaseComponentVelocity,lowerPhase] using phase_hasFDerivAt (-frequency) point
  · simpa [phaseComponents,phaseComponentVelocity,lowerPhase] using phase_hasFDerivAt (-frequency) point

def anchoredRotatedPrimalCoordinates (point : BasePoint) (jet : NativeFirstJet) (position : BasePoint) :
    MatterCoordinateCarrier :=
  ∑ spin : Fin 4,∑ color : Fin 3,
    (phaseComponents position spin*primalCoefficientCLM spin color (anchoredSignal point jet position)) •
      matterCoordinateEquiv (PreparationVacuumNativeSourceRestriction.sourceTripletLeg spin color)

theorem anchoredRotatedPrimal_source (point : BasePoint) (jet : NativeFirstJet) (position : BasePoint) :
    anchoredRotatedPrimalCoordinates point jet position=matterCoordinateEquiv
      (diracMatrixMatterAction (SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation position) (primalInsertion (anchoredSignal point jet position))) := by
  unfold anchoredRotatedPrimalCoordinates
  simp only [←map_smul,←map_sum]
  apply congrArg matterCoordinateEquiv
  funext row
  simp [diracMatrixMatterAction,SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge.rotation,phaseComponents,primalInsertion,
    PreparationVacuumNativeSourceRestriction.sourceTripletLeg,Pi.single_apply,Finset.sum_apply,Matrix.diagonal_apply,
    smul_smul,primalCoefficientCLM,primalCoefficientLinear]
  apply Finset.sum_congr rfl
  intro color _
  rw [mul_comm]

theorem anchoredRotatedPrimal_first (point : BasePoint) (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (anchoredRotatedPrimalCoordinates point jet) point mu=
      ∑ spin : Fin 4,∑ color : Fin 3,
        (phaseComponents point spin*((if mu=0 then phaseComponentVelocity spin else 0)*
          fieldPrimalComplex jet.1 spin color+fieldPrimalComplex (jet.2 mu) spin color)) •
          matterCoordinateEquiv (PreparationVacuumNativeSourceRestriction.sourceTripletLeg spin color) := by
  have each (spin : Fin 4) (color : Fin 3) :=
    ((phaseComponents_first_at point spin).mul ((primalCoefficientCLM spin color).hasFDerivAt.comp point
      (anchoredSignal_hasFDerivAt point jet point))).smul_const
        (matterCoordinateEquiv (PreparationVacuumNativeSourceRestriction.sourceTripletLeg spin color))
  have derivative:=HasFDerivAt.fun_sum (u:=Finset.univ) (fun spin _=>
    HasFDerivAt.fun_sum (u:=Finset.univ) (fun color _=>each spin color))
  change HasFDerivAt (anchoredRotatedPrimalCoordinates point jet) _ point at derivative
  rw [fieldDirectionalDerivative,derivative.fderiv]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro spin _
  apply Finset.sum_congr rfl
  intro color _
  have value : jetDerivative jet.2 (coordinateDirection mu)=jet.2 mu := by
    simpa only [fieldDirectionalDerivative,(affineSignal_hasFDerivAt jet 0).fderiv] using affineSignal_directionalDerivative jet mu
  have coefficient (f : Field289) : primalCoefficientCLM spin color f=fieldPrimalComplex f spin color := rfl
  have projected : (EuclideanSpace.proj (0 : Fin 4) : BasePoint→L[ℝ] ℝ) (coordinateDirection mu)=
      if mu=0 then 1 else 0 := by
    change (coordinateDirection mu) 0=if mu=0 then 1 else 0
    simp [coordinateDirection,eq_comm]
  simp only [ContinuousLinearMap.smulRight_apply,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    Function.comp_apply,anchoredSignal_value,value,coefficient,projected,smul_eq_mul]
  congr 1
  by_cases time : mu=0
  · subst mu
    simp
    ring
  · simp [time]


end LowEnergy.SourcePropagationMotherEulerKernel
