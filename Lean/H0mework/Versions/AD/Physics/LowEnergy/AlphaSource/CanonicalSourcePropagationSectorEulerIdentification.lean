import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationMotherResidualPullback
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationMotherAlgebraicDirections

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationMotherResidualDirections
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeMatterVariation StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineScalarVariation StageNineScalarPointwiseEquation StageNineMatterVariation StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine StageNineConjugateMatterVariation StageNineGlobalIntegratedAction
open StageNineScalarLocalSpinDensity StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineFormNativeGravityMultiplierAuxiliaryVariation StageNineFormNativeGaugeAuxiliaryVariation
open StageNineTopologicalFourFormPairing StageNineFormNativeGaugeWedge
open DiracExteriorMatterAction SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction
open scoped Topology ContDiff BigOperators
attribute [local irreducible] nativeEuler nativeConfiguration nativePoint nativeActionJet

def motherDensityAt (point : BasePoint) (field : StageNineContinuumPointField) : ℝ :=
  generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary positiveSmoothUnifiedSource
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 0 point field

private theorem affineDerivative (base first : ℝ) :
    HasDerivAt (fun a : ℝ=>base+a*first) first 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const first).const_add base

private theorem quadraticDerivative (base first second : ℝ) :
    HasDerivAt (fun a : ℝ=>base+a*first+a^2*second) first 0 := by
  have generated := (((hasDerivAt_id (0 : ℝ)).mul_const first).const_add base).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const second)
  convert! generated using 1
  simp

private theorem matterRealZero (value : DiracExteriorMatterCarrier) : (0 : ℝ) • value=0 := by
  change (0 : ℂ) • value=0
  exact zero_smul ℂ value

/-- The scalar direction retains its actual gauge-covariant derivative direction. -/
def motherScalarCurve (signal : BasePoint→Field289) (point : BasePoint)
    (value : ScalarCoordinateCarrier) (slope : LorentzianIndex→ScalarCoordinateCarrier) (a : ℝ) : ℝ :=
  motherDensityAt point (withScalarJets (nativePoint signal point)
    ((nativePoint signal point).scalar+a • value)
    ((nativePoint signal point).scalarCovariantDerivative+a • slope))

theorem motherScalarCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (value : ScalarCoordinateCarrier) (slope : LorentzianIndex→ScalarCoordinateCarrier) :
    HasDerivAt (motherScalarCurve signal point value slope)
      (diracDualScalarFirstVariationDensity positiveSmoothUnifiedSource point
        (nativePoint signal point) value slope) 0 := by
  have source := fun a : ℝ=>generatedDiracDualFormNativeUnifiedLocalDensity_withScalarJets_quadratic
    positiveSmoothUnifiedSource point (nativePoint signal point) value slope a
  have law : motherScalarCurve signal point value slope=(fun a : ℝ=>
      motherDensityAt point (nativePoint signal point)+a*diracDualScalarFirstVariationDensity positiveSmoothUnifiedSource
        point (nativePoint signal point) value slope+a^2*scalarSecondVariationDensity positiveSmoothUnifiedSource
        point (nativePoint signal point) value slope) := by
    funext a
    exact source a
  rw [law]
  exact quadraticDerivative _ _ _

/-- The primal direction is independent of the supplied dual; its complete repaired Yukawa and kinetic legs stay in the same density. -/
def motherPrimalCurve (signal : BasePoint→Field289) (point : BasePoint)
    (value : DiracExteriorMatterCarrier) (slope : LorentzianIndex→DiracExteriorMatterCarrier) (a : ℝ) : ℝ :=
  motherDensityAt point (withMatterJets (nativePoint signal point)
    ((nativePoint signal point).matter+a • value)
    ((nativePoint signal point).matterCovariantDerivative+a • slope))

theorem motherPrimalCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (value : DiracExteriorMatterCarrier) (slope : LorentzianIndex→DiracExteriorMatterCarrier) :
    HasDerivAt (motherPrimalCurve signal point value slope)
      (diracDualMatterFirstVariationDensity positiveSmoothUnifiedSource point
        (nativePoint signal point) value slope) 0 := by
  have law : motherPrimalCurve signal point value slope=(fun a : ℝ=>
      motherDensityAt point (nativePoint signal point)+a*diracDualMatterFirstVariationDensity positiveSmoothUnifiedSource
        point (nativePoint signal point) value slope) := by
    funext a
    exact generatedDiracDualFormNativeUnifiedLocalDensity_withMatterJets_affine positiveSmoothUnifiedSource
      point (nativePoint signal point) value slope a
  rw [law]
  exact affineDerivative _ _

def motherIndependentDualCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) (a : ℝ) : ℝ :=
  motherDensityAt point (withConjugateMatter (nativePoint signal point)
    ((nativePoint signal point).conjugateMatter+a • matterDualOfCoordinates direction))

theorem motherIndependentDualCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) :
    HasDerivAt (motherIndependentDualCurve signal point direction)
      ((nativeEuler signal point).conjugateMatter direction) 0 := by
  have law : motherIndependentDualCurve signal point direction=(fun a : ℝ=>
      motherDensityAt point (nativePoint signal point)+a*(generatedVolumeDensity (nativePoint signal point)*
        (matterDualOfCoordinates direction (generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource
          0 point (nativePoint signal point))).re)) := by
    funext a
    exact generatedDiracDualFormNativeUnifiedLocalDensity_withConjugateMatter_affine positiveSmoothUnifiedSource
      point (nativePoint signal point) direction a
  rw [law]
  convert! affineDerivative _ _ using 1
  unfold nativeEuler nativeActionJet diracDualFormNativeJointResidualOfActionJet generatedDiracDualFormNativePointwiseActionJet
    nativePoint
  rfl

def motherScalarAlgebraicCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : ScalarCoordinateCarrier) : ℝ→ℝ :=
  motherScalarCurve signal point direction (pointwiseScalarVariationAlgebraicDirection
    (nativeActionJet signal point).p286GaugeConnection direction)

theorem motherScalarAlgebraicCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    HasDerivAt (motherScalarAlgebraicCurve signal point direction)
      (pointwiseDiracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource point
        (nativeActionJet signal point) direction) 0 := by
  have source := motherScalarCurve_generated signal point direction (pointwiseScalarVariationAlgebraicDirection
    (nativeActionJet signal point).p286GaugeConnection direction)
  convert! source using 1
  unfold pointwiseDiracDualScalarAlgebraicDirectionalCoefficient diracDualScalarFirstVariationDensity
  rw [nativeActionJet_pointField]

def motherPrimalAlgebraicCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) : ℝ→ℝ :=
  motherPrimalCurve signal point (matterCoordinateEquiv.symm direction)
    (pointwiseMatterVariationAlgebraicDirection (nativeActionJet signal point).gravityConnection
      (nativeActionJet signal point).p286GaugeConnection direction)

theorem motherPrimalAlgebraicCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) :
    HasDerivAt (motherPrimalAlgebraicCurve signal point direction)
      (pointwiseDiracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource point
        (nativeActionJet signal point) direction) 0 := by
  have source := motherPrimalCurve_generated signal point (matterCoordinateEquiv.symm direction)
    (pointwiseMatterVariationAlgebraicDirection (nativeActionJet signal point).gravityConnection
      (nativeActionJet signal point).p286GaugeConnection direction)
  convert! source using 1
  unfold pointwiseDiracDualMatterAlgebraicDirectionalCoefficient diracDualMatterFirstVariationDensity
  rw [nativeActionJet_pointField]

def motherScalarMomentumCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : ScalarCoordinateCarrier) (mu : LorentzianIndex) : ℝ→ℝ :=
  motherScalarCurve signal point 0 (scalarVariationDifferentialDirection direction mu)

theorem motherScalarMomentumCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : ScalarCoordinateCarrier) (mu : LorentzianIndex) :
    HasDerivAt (motherScalarMomentumCurve signal point direction mu)
      (scalarDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal) direction mu point) 0 := by
  have source := motherScalarCurve_generated signal point 0 (scalarVariationDifferentialDirection direction mu)
  convert! source using 1
  unfold scalarDifferentialMomentum diracDualScalarFirstVariationDensity
  simp only [scalarPotentialFirstVariation_zero,diracDualScalarYukawaFirstVariationDensity_zero,sub_zero,add_zero,nativePoint]

def motherPrimalMomentumCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) (mu : LorentzianIndex) : ℝ→ℝ :=
  motherPrimalCurve signal point 0 (fun nu=>if nu=mu then matterCoordinateEquiv.symm direction else 0)

theorem motherPrimalMomentumCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) (mu : LorentzianIndex) :
    HasDerivAt (motherPrimalMomentumCurve signal point direction mu)
      (matterDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal) direction mu point) 0 := by
  have source := motherPrimalCurve_generated signal point 0
    (fun nu=>if nu=mu then matterCoordinateEquiv.symm direction else 0)
  convert! source using 1
  have variation : (fun nu : LorentzianIndex=>if nu=mu then matterCoordinateEquiv.symm direction else 0)=
      (fun nu=>(if nu=mu then (1 : ℝ) else 0) • matterCoordinateEquiv.symm direction) := by
    funext nu
    by_cases h : nu=mu
    · simp only [if_pos h,one_smul]
    · simp only [if_neg h,matterRealZero]
  have kinetic := matterCovariantDerivativeVariationVector_coordinateDerivativeDirections positiveSmoothUnifiedSource
    point (nativePoint signal point) direction (fun nu=>if nu=mu then 1 else 0)
  have vector : diracDualMatterFieldVariationVector positiveSmoothUnifiedSource point (nativePoint signal point) 0
      (fun nu=>if nu=mu then matterCoordinateEquiv.symm direction else 0)=
      matterDifferentialVariationVector positiveSmoothUnifiedSource point (nativePoint signal point) direction mu := by
    unfold diracDualMatterFieldVariationVector
    rw [variation,kinetic]
    simp only [ite_smul,one_smul,matterRealZero,Finset.sum_ite_eq',Finset.mem_univ,if_true,map_zero,add_zero]
  unfold matterDifferentialMomentum diracDualMatterFirstVariationDensity
  rw [vector]
  unfold nativePoint
  rfl

/-- The scalar raw residual is the actual mother value coefficient minus its full four-direction momentum divergence. -/
theorem motherScalarEuler_action (signal : BasePoint→Field289) (point : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    (nativeEuler signal point).scalar direction=
      deriv (motherScalarAlgebraicCurve signal point direction) 0-
        ∑ mu : LorentzianIndex,fieldDirectionalDerivative
          (fun position=>deriv (motherScalarMomentumCurve signal position direction mu) 0) point mu := by
  rw [(motherScalarAlgebraicCurve_generated signal point direction).deriv]
  have slope (mu : LorentzianIndex) : (fun position=>deriv (motherScalarMomentumCurve signal position direction mu) 0)=
      scalarDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal) direction mu := by
    funext position
    exact (motherScalarMomentumCurve_generated signal position direction mu).deriv
  simp only [slope]
  unfold nativeEuler diracDualFormNativeJointResidualOfActionJet nativeActionJet generatedDiracDualFormNativePointwiseActionJet
    scalarDifferentialMomentumDivergence
  rfl

theorem motherPrimalEuler_action (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) :
    (nativeEuler signal point).matter direction=
      deriv (motherPrimalAlgebraicCurve signal point direction) 0-
        ∑ mu : LorentzianIndex,fieldDirectionalDerivative
          (fun position=>deriv (motherPrimalMomentumCurve signal position direction mu) 0) point mu := by
  rw [(motherPrimalAlgebraicCurve_generated signal point direction).deriv]
  have slope (mu : LorentzianIndex) : (fun position=>deriv (motherPrimalMomentumCurve signal position direction mu) 0)=
      matterDifferentialMomentum positiveSmoothUnifiedSource (nativeConfiguration signal) direction mu := by
    funext position
    exact (motherPrimalMomentumCurve_generated signal position direction mu).deriv
  simp only [slope]
  unfold nativeEuler diracDualFormNativeJointResidualOfActionJet nativeActionJet generatedDiracDualFormNativePointwiseActionJet
    matterDifferentialMomentumDivergence
  rfl

theorem motherIndependentDualEuler_action (signal : BasePoint→Field289) (point : BasePoint)
    (direction : MatterCoordinateCarrier) :
    (nativeEuler signal point).conjugateMatter direction=deriv (motherIndependentDualCurve signal point direction) 0 :=
  (motherIndependentDualCurve_generated signal point direction).deriv.symm

def motherMultiplierCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : PhysicalBivector) (a : ℝ) : ℝ :=
  motherDensityAt point (withFormNativeGravityMultiplier (nativePoint signal point)
    ((nativePoint signal point).gravitySimplicityMultiplier+a • direction))

theorem motherMultiplierCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : PhysicalBivector) :
    HasDerivAt (motherMultiplierCurve signal point direction)
      (gravityTopologicalWedgeCoefficient direction (nativeEuler signal point).gravityMultiplier) 0 := by
  have source := motherMultiplier_hasDerivAt positiveSmoothUnifiedSource
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 0 point (nativePoint signal point) direction
  convert! source using 1
  unfold nativeEuler nativeActionJet diracDualFormNativeJointResidualOfActionJet generatedDiracDualFormNativePointwiseActionJet
    nativePoint
  rfl

def motherGravityAuxiliaryCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : PhysicalBivector) (a : ℝ) : ℝ :=
  motherDensityAt point (withFormNativeGravityAuxiliary (nativePoint signal point)
    ((nativePoint signal point).gravityAuxiliary+a • direction))

theorem motherGravityAuxiliaryCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : PhysicalBivector) :
    HasDerivAt (motherGravityAuxiliaryCurve signal point direction)
      (gravityTopologicalWedgeCoefficient direction (nativeEuler signal point).gravityAuxiliary) 0 := by
  have source := motherGravityAuxiliary_hasDerivAt positiveSmoothUnifiedSource
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 0 point (nativePoint signal point) direction
  convert! source using 1
  unfold nativeEuler nativeActionJet diracDualFormNativeJointResidualOfActionJet generatedDiracDualFormNativePointwiseActionJet
    nativePoint
  rfl

def motherGaugeAuxiliaryCurve (signal : BasePoint→Field289) (point : BasePoint)
    (direction : FormNativeP286GaugeTwoForm) (a : ℝ) : ℝ :=
  motherDensityAt point (withFormNativeP286GaugeAuxiliary (nativePoint signal point)
    ((nativePoint signal point).gaugeAuxiliary+a • direction))

theorem motherGaugeAuxiliaryCurve_generated (signal : BasePoint→Field289) (point : BasePoint)
    (direction : FormNativeP286GaugeTwoForm) (nondegenerate : Matrix.det (nativePoint signal point).coframe≠0) :
    HasDerivAt (motherGaugeAuxiliaryCurve signal point direction)
      (formNativeP286GaugeWedgeCoefficient direction (nativeEuler signal point).p286GaugeAuxiliary) 0 := by
  have source := motherGaugeAuxiliary_hasDerivAt positiveSmoothUnifiedSource
    (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 0 point (nativePoint signal point) nondegenerate direction
  convert! source using 1
  unfold nativeEuler nativeActionJet diracDualFormNativeJointResidualOfActionJet generatedDiracDualFormNativePointwiseActionJet
    nativePoint
  rfl

end LowEnergy.SourcePropagationMotherResidualDirections
