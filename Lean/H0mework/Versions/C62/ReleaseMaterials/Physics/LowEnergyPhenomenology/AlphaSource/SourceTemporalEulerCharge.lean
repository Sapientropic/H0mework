import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceTemporalSliceKernel
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceUnitCompatibleField
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceTemporalN1Observation

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


open PreparationPhysicalUnitCurrentFieldReturn PreparationVacuumFixedMomentumActionReturn
open PreparationPhysicalTemporalNumberOneReturn PreparationVacuumPhysicalN1WardCollapse

private theorem field_basis (f : Field289) : f=∑i : Fin 289,f i • fieldUnit i := by
  funext j
  simp [fieldUnit,Finset.sum_apply,Pi.single_apply]

private theorem reader_basis (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    PreparationVacuumRawJointFeedback.rawReader f p F 0=
      ∑i : Fin 289,f i • PreparationVacuumRawJointFeedback.rawReader (fieldUnit i) p F 0 := by
  rw [←sourceMatterActionOperator_gradient]
  conv_lhs => rw [field_basis f]
  simp only [map_sum,map_smul,sourceMatterActionOperator_gradient]

private theorem ordered_sum {A : Type*} [Ring A] [Algebra ℝ A]
    (L G R T : A) (r : Fin 289→ℝ) (C : Fin 289→A) :
    L*G*(∑i : Fin 289,r i • C i)*R*T=∑i : Fin 289,r i • (L*G*C i*R*T) := by
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]

/-- The original fixed-pi action derivative assembles the full Euler covector on the actual temporal column. -/
theorem sourceTemporalEuler_contract (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (age : ℝ) :
    (∑i : Fin 289,(sourceTemporalAxis i:ℂ)*sourceUnitEulerCurrent q sL eL sR eR age 0 i)=
      sourceUnitTimeCurrent q sL eL sR eR sourceTemporalAxis age 0 := by
  have kernel : fiveKernel sourceTemporalAxis q.p q.k q.F q.z q.w age 0=
      ∑i : Fin 289,sourceTemporalAxis i • fiveKernel (fieldUnit i) q.p q.k q.F q.z q.w age 0 := by
    rw [fiveKernel,reader_basis]
    exact ordered_sum _ _ _ _ _ _
  rw [sourceUnitTimeCurrent,kernel,map_sum]
  simp only [sourceUnitEulerCurrent,sourceUnitTimeCurrent,Finset.sum_neg_distrib,
    mul_neg,←Complex.real_smul]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  exact (((sourceUnitRead q sL eL sR eR).restrictScalars ℝ).map_smul (sourceTemporalAxis i)
    (fiveKernel (fieldUnit i) q.p q.k q.F q.z q.w age 0)).symm

/-- These are the original two physical-time legs around the actual weighted charge density. -/
def sourceTemporalEulerCharge (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (age : ℝ) : ℂ :=
  -sourceTemporalUnitSandwich q sL eL sR eR
    (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0)
    (jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0)

open Lean Elab Term Meta in
elab "paidTemporalSandwich%" : term => do
  let wanted:=`LowEnergy.PreparationPhysicalFirstTemporalChargeReturn.unit_sandwich
  let names:=(←getEnv).constants.toList.filterMap fun (n,_)=>
    if n.toString.startsWith "_private.H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstTemporalUnitResponse." && privateToUserName n==wanted then some n else none
  match names with
  | [name]=>
    logInfo m!"Original temporal sandwich payer: {name}"
    mkConstWithFreshMVarLevels name
  | _=>throwError "Expected unique original temporal sandwich payer, found {names}"

/-- Full material, equal/off-energy, raw-frame and normal-order terms stay inside the original time-prepared Green legs. -/
theorem sourceTemporalEulerCharge_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (age : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    (∑i : Fin 289,(sourceTemporalAxis i:ℂ)*sourceUnitEulerCurrent q sL eL sR eR age 0 i)=
      sourceTemporalEulerCharge q sL eL sR eR age := by
  rw [sourceTemporalEuler_contract,sourceUnitTimeCurrent,fiveKernel,
    sourceTemporalChargeReader_original]
  have paid := (paidTemporalSandwich%) q sL eL sR eR
    (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0)
    (jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0) left right
  simpa only [sourceTemporalEulerCharge,sourceTemporalUnitSandwich,mul_assoc] using congrArg Neg.neg paid

private theorem apply_range (A : H→L[ℂ]H)
    (paid : sourceN1Projection*A*sourceN1Projection=A*sourceN1Projection) (v : H)
    (fixed : sourceN1Projection v=v) : sourceN1Projection (A v)=A v := by
  have read:=congrArg (fun B : H→L[ℂ]H=>B v) paid
  simpa only [mul_apply_eq_comp,fixed] using read

/-- Actual number-one transport removes both quartic terms from the temporal Euler observer while preserving its two source-frame charge defects. -/
theorem sourceTemporalEulerCharge_numberOne (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (age : ℝ) (right : q.w.im≠0) :
    sourceTemporalEulerCharge q sL eL sR eR age=
      -sourceTemporalN1UnitSandwich q sL eL sR eR
        (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0)
        (jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0) := by
  let y:=jointResolvent 0 q.F q.w 0 (sourceChargedGaussPrepared q.epsilon q.precision sR eR)
  have seed : sourceN1Projection y=y:=sourceTemporalGreen_N1 q 0 sR eR q.w right
  have time := apply_range _ (actualTime_sourceN1_range q.p q.F age) y seed
  have green := apply_range _ (sourceTemporalGreen_range q.p q.F q.w right) _ time
  unfold sourceTemporalEulerCharge sourceTemporalUnitSandwich sourceTemporalN1UnitSandwich
  rw [sourceTemporalSpectralPair_N1 q.F _ _]
  simpa only [mul_apply_eq_comp,y] using green

private theorem current_continuous (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (i : Fin 289) :
    Continuous (fun t=>sourceUnitEulerCurrent q sL eL sR eR t 0 i) := by
  exact (sourceUnitCurrentJet_continuous q sL eL sR eR i).1.congr
    (fun t=>sourceUnitCurrentJet_value q sL eL sR eR t i)

/-- The physical finite window contains the computed weighted source charge, with no exchange of the observation limits. -/
theorem sourceTemporalWindow_charge (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    (∑i : Fin 289,(sourceTemporalAxis i:ℂ)*sourceUnitCurrentWindow q sL eL sR eR lambda T i)=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceTemporalEulerCharge q sL eL sR eR t := by
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight; fun_prop
  have each (i : Fin 289) : IntervalIntegrable
      (fun t=>laplaceWeight lambda t*sourceUnitEulerCurrent q sL eL sR eR t 0 i) volume 0 T :=
    (weight.mul (current_continuous q sL eL sR eR i)).intervalIntegrable _ _
  simp only [sourceUnitCurrentWindow_actual,←intervalIntegral.integral_const_mul]
  rw [←intervalIntegral.integral_finsetSum (s:=Finset.univ) (fun i _=>(each i).const_mul _)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [←sourceTemporalEulerCharge_generated q sL eL sR eR t left right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The temporal force restriction of the original physical response is evaluated without deleting its density current. -/
theorem sourceTemporalResponse_slot (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (j : Fin 4) (age : ℝ) :
    sourceUnitTimeSlope q sL eL sR eR (sourceEnergyAxisField 1 j) sourceTemporalAxis age=0 := by
  simp only [sourceUnitTimeSlope,sourceTemporalFiveForce_zero,map_zero,neg_zero]

end LowEnergy.PreparationPhysicalTemporalConstraintObserver
