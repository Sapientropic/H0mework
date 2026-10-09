import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceTemporalEulerCharge

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalTemporalConstraintObserver
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationPhysicalResponseChargeGrading PreparationVacuumLorentzFieldInjection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalPoleChargeMatrix
open GaussFockLift GaussCoreHilbert PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalNativePhaseChargeInventory
open scoped InnerProductSpace

open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice CanonicalGradedCharge GaussCoreDifferential GaussQuantumMultiplier
open GaussFockPair GaussLiveMomentum GaussNativePotential
open scoped ContDiff

open NativeHistoryGrade GaussUnitaryHistory CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation PreparationPhysicalChargedScatteringPoleReturn
open GaussFockWeights GaussDensityCore MeasureTheory PreparationVacuumFieldConstraintResponse PreparationVacuumYukawaTransport
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent actualC gradedTest

open PreparationPhysicalFirstGaugeMaterialDifference PreparationPhysicalActualUnitFourPointReturn
open PreparationPhysicalActualPolarizationResponse PreparationVacuumFullFieldRiesz

open PreparationPhysicalFirstChargeFourPointReturn PreparationPhysicalFirstTemporalChargeReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumSpatialDensityTransport
open PreparationVacuumHalfDensityFiber PreparationVacuumSourceActionJets PreparationVacuumGradedTransport


open PreparationPhysicalUnitCurrentFieldReturn PreparationPhysicalTemporalNumberOneReturn
open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalFeedback

/-- The moving detector uses its own physical momenta and the original independently normalized Gauss legs. -/
def sourceMovingUnitFieldRead (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) : ℂ :=
  -sourceUnitRead q sL eL sR eR (sourceActualPreparedKernel q (q.p+q.k) q.p lambda T V)

private theorem kernel_current (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (age : ℝ) (i : Fin 289) :
    -sourceUnitRead q sL eL sR eR (actualJointKernel q (q.p+q.k) q.p age i)=
      sourceUnitEulerCurrent q sL eL sR eR age 0 i := by
  have momentum : (q.p+q.k)-q.p=q.k := by abel
  rw [←actualJointKernel_original,momentum]
  rfl

private theorem kernel_integrable (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ)
    (i : Fin 289) (left : q.z.im≠0) (right : q.w.im≠0) :
    IntervalIntegrable (fun t=>laplaceWeight lambda t • actualJointKernel q (q.p+q.k) q.p t i) volume 0 T := by
  have arguments : Continuous (fun t : ℝ=>(q.p+q.k,q.p,t)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have kernel := (actualJointKernel_continuous q i left right).comp arguments
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight; fun_prop
  exact (weight.smul kernel).intervalIntegrable _ _

/-- The independently prepared current and detector are restrictions of the same original five-factor operator at their actual momenta. -/
theorem sourceMovingUnitFieldRead_current (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceMovingUnitFieldRead q sL eL sR eR lambda T V=
      ∑i : Fin 289,sourceUnitCurrentWindow q sL eL sR eR lambda T i*V i := by
  have expanded : sourceActualPreparedKernel q (q.p+q.k) q.p lambda T V=
      ∑i : Fin 289,V i • ∫t in (0:ℝ)..T,laplaceWeight lambda t • actualJointKernel q (q.p+q.k) q.p t i := by
    unfold sourceActualPreparedKernel
    simp only [Finset.smul_sum,smul_comm (laplaceWeight lambda _) (V _)]
    have exchange := intervalIntegral.integral_finsetSum (s:=Finset.univ)
      (f:=fun i t=>V i • (laplaceWeight lambda t • actualJointKernel q (q.p+q.k) q.p t i))
      (fun i _=>(kernel_integrable q lambda T i left right).smul (V i))
    simpa only [intervalIntegral.integral_smul] using exchange
  rw [sourceMovingUnitFieldRead,expanded,map_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  have exchange := (sourceUnitRead q sL eL sR eR).intervalIntegral_comp_comm
    (kernel_integrable q lambda T i left right)
  rw [←exchange,sourceUnitCurrentWindow_actual]
  simp only [map_smul,smul_eq_mul]
  have same : (fun t : ℝ=> -(laplaceWeight lambda t*sourceUnitRead q sL eL sR eR
      (actualJointKernel q (q.p+q.k) q.p t i)))=
      fun t=>laplaceWeight lambda t*sourceUnitEulerCurrent q sL eL sR eR t 0 i := by
    funext t
    rw [←kernel_current q sL eL sR eR t i,mul_neg]
  have integralSame := congrArg (fun f : ℝ→ℂ=>∫t in (0:ℝ)..T,f t) same
  rw [intervalIntegral.integral_neg] at integralSame
  rw [←integralSame]
  ring

/-- Original moving prepared detector, actual norm and every independent leg correction remain visible. -/
theorem sourceMovingUnitFieldRead_material (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceMovingUnitFieldRead q sL eL sR eR lambda T V=
      sourceActualLegNormalization q sL eL sR eR*
        (sourceActualPreparedDetector q (q.p+q.k) q.p sL eL sR eR lambda T V-
          sourceActualLegCorrection q sL eL sR eR
            (sourceActualPreparedKernel q (q.p+q.k) q.p lambda T V)) := by
  rw [sourceMovingUnitFieldRead,sourceUnitRead_original,sourceActualUnitLegRead_return,
    sourceActualPreparedDetector_action q (q.p+q.k) q.p sL eL sR eR lambda T V left right]
  ring

/-- A full field generated by one physical preparation is read by the other actual preparation. -/
def sourceMatchedUnitResponse (detector source : SourceUnitFieldLeg) : ℂ :=
  sourceMovingUnitFieldRead detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
    detector.frequency.val detector.T (sourceUnitCompleteField source)

/-- This is the complete current-current tensor through the original 289 Green matrix, with the physical source and detector windows unchanged. -/
theorem sourceMatchedUnitResponse_tensor (detector source : SourceUnitFieldLeg) :
    sourceMatchedUnitResponse detector source=
      ∑i : Fin 289,∑j : Fin 289,sourceUnitRawForcing detector i*
        sourceGreen (sourceUnitFieldPoint source) i j*sourceUnitRawForcing source j := by
  rw [sourceMatchedUnitResponse,sourceMovingUnitFieldRead_current _ _ _ _ _ _ _ _ detector.nonrealL detector.nonrealR]
  simp only [sourceUnitCompleteField,PreparationVacuumOriginalGreenFeedback.sourceField,
    Matrix.mulVec,dotProduct,Finset.mul_sum,sourceUnitRawForcing,mul_assoc]

/-- The returned current tensor is attached to the same generated nine-row compatibility repair and exact full Jacobi equation. -/
theorem sourceMatchedUnitResponse_field (detector source : SourceUnitFieldLeg) :
    originalJacobi (sourceUnitFieldPoint source).val*ᵥsourceUnitCompleteField source=
      sourceUnitRawForcing source+sourceUnitConstraintSupplement source ∧
    sourceMatchedUnitResponse detector source=
      sourceActualLegNormalization detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR*
        (sourceActualPreparedDetector detector.q (detector.q.p+detector.q.k) detector.q.p
          detector.sideL detector.edgeL detector.sideR detector.edgeR detector.frequency.val detector.T
          (sourceUnitCompleteField source)-
        sourceActualLegCorrection detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
          (sourceActualPreparedKernel detector.q (detector.q.p+detector.q.k) detector.q.p
            detector.frequency.val detector.T (sourceUnitCompleteField source))) := by
  exact ⟨sourceUnitCompleteField_equation source,
    sourceMovingUnitFieldRead_material _ _ _ _ _ _ _ _ detector.nonrealL detector.nonrealR⟩

/-- The temporal row of this same observer is the computed weighted charge, not the null slot of the reduced Hamiltonian Hessian. -/
theorem sourceMatchedTemporal_charge (detector : SourceUnitFieldLeg) :
    sourceMovingUnitFieldRead detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
      detector.frequency.val detector.T (fun i=>(sourceTemporalAxis i:ℂ))=
      ∫t in (0:ℝ)..detector.T,laplaceWeight detector.frequency.val t*
        (-sourceTemporalN1UnitSandwich detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
          (physicalTime (detector.q.p+detector.q.k) detector.q.F (-t) 0*
            jointResolvent (detector.q.p+detector.q.k) detector.q.F detector.q.z 0)
          (jointResolvent detector.q.p detector.q.F detector.q.w 0*physicalTime detector.q.p detector.q.F t 0)) := by
  rw [sourceMovingUnitFieldRead_current _ _ _ _ _ _ _ _ detector.nonrealL detector.nonrealR]
  rw [show (∑i : Fin 289,sourceUnitCurrentWindow detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
      detector.frequency.val detector.T i*(sourceTemporalAxis i:ℂ))=
      ∑i : Fin 289,(sourceTemporalAxis i:ℂ)*sourceUnitCurrentWindow detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
        detector.frequency.val detector.T i from Finset.sum_congr rfl (fun i _=>mul_comm _ _)]
  rw [sourceTemporalWindow_charge _ _ _ _ _ _ _ detector.nonrealL detector.nonrealR]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  exact congrArg (fun z : ℂ=>laplaceWeight detector.frequency.val t*z)
    (sourceTemporalEulerCharge_numberOne _ _ _ _ _ t detector.nonrealR)

end LowEnergy.PreparationPhysicalTemporalConstraintObserver
