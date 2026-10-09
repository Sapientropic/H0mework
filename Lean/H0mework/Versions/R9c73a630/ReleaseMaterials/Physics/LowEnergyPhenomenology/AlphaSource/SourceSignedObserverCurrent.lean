import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedCurrentGram

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalSignedCurrentPoleObserver
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

open PreparationPhysicalTemporalConstraintObserver PreparationPhysicalSignedVolumeWeightReturn
open PreparationPhysicalTemporalNumberOneReturn PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalFeedback

open PreparationPhysicalUnitCurrentFieldReturn PreparationVacuumPhysicalTailPrice

/-- Every coefficient is the computed signed-volume source Gram between the actual independent time-prepared legs. -/
def sourceSignedUnitRead (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f : Field289) (p : PhysicalMomentum) (L R : H→L[ℂ]H) : ℂ :=
  ∑i : FrameIndex q.F,∑j : FrameIndex q.F,
    sourceActualUnitDual q sL eL q.z (L (frameVector q.F i))*
      sourceSignedCurrentForm f p (frameTest q.F i) (frameTest q.F j)*
        inner ℂ (frameVector q.F j) (R (sourceActualUnitPrimal q sR eR q.w))

theorem sourceSignedUnitRead_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f : Field289) (p : PhysicalMomentum) (L R : H→L[ℂ]H) :
    sourceUnitRead q sL eL sR eR (L*sourceSignedCurrentReader f p q.F*R)=
      sourceSignedUnitRead q sL eL sR eR f p L R := by
  simp only [sourceUnitRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    sourceSignedCurrentReader,finiteRiesz,mul_apply_eq_comp,sum_apply,smul_apply,
    InnerProductSpace.rankOne_apply,map_sum,map_smul,smul_eq_mul,sourceSignedUnitRead]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full source current has the Euler minus and the computed negative raw action, leaving this positive signed-volume read. -/
def sourceSignedUnitCurrent (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f : Field289) (age : ℝ) : ℂ :=
  sourceSignedUnitRead q sL eL sR eR f q.p
    (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0)
    (jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0)

private theorem negative_middle {A : Type*} [Ring A] (a b c d e : A) :
    a*b*(-c)*d*e= -((a*b)*c*(d*e)) := by
  simp only [mul_neg,neg_mul,mul_assoc]

theorem sourceSignedUnitCurrent_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f : Field289) (age : ℝ) :
    sourceUnitTimeCurrent q sL eL sR eR f age 0=sourceSignedUnitCurrent q sL eL sR eR f age := by
  have kernel : fiveKernel f q.p q.k q.F q.z q.w age 0=
      -((physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0)*
        sourceSignedCurrentReader f q.p q.F*(jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0)) := by
    rw [fiveKernel,sourceSignedCurrentReader_actual]
    exact negative_middle _ _ _ _ _
  rw [sourceUnitTimeCurrent,kernel,map_neg,neg_neg]
  exact sourceSignedUnitRead_generated q sL eL sR eR f q.p _ _

theorem sourceSignedUnitCurrent_price (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f : Field289) (eta age : ℝ) (positive : 0<eta) (future : 0≤age)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceSignedUnitCurrent q sL eL sR eR f age‖≤rawCoefficient q f eta*Real.exp (4*eta*age) := by
  rw [←sourceSignedUnitCurrent_generated,sourceUnitTimeCurrent,norm_neg,sourceUnitRead_original]
  exact (sourceActualUnitLegRead_bound q sL eL sR eR left right _).trans
    (rawKernel_price q f eta age positive future)

/-- The full289 source, not a chosen scalar charge profile, is integrated in the original finite clock window. -/
def sourceSignedCurrentWindow (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceSignedUnitCurrent q sL eL sR eR (fieldUnit i) t

theorem sourceSignedCurrentWindow_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) :
    sourceSignedCurrentWindow q sL eL sR eR lambda T=sourceUnitCurrentWindow q sL eL sR eR lambda T := by
  funext i
  rw [sourceUnitCurrentWindow_actual]
  simp only [sourceSignedCurrentWindow,sourceUnitEulerCurrent,sourceSignedUnitCurrent_generated]

private theorem current_continuous (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (i : Fin 289) :
    Continuous (fun t=>sourceSignedUnitCurrent q sL eL sR eR (fieldUnit i) t) := by
  have paid:=(sourceUnitCurrentJet_continuous q sL eL sR eR i).1
  apply paid.congr
  intro t
  rw [sourceUnitCurrentJet_value,sourceUnitEulerCurrent,sourceSignedUnitCurrent_generated]

theorem sourceSignedCurrentWindow_integrable (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    IntervalIntegrable (fun t=>laplaceWeight lambda t*sourceSignedUnitCurrent q sL eL sR eR (fieldUnit i) t)
      volume 0 T := by
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight; fun_prop
  exact (weight.mul (current_continuous q sL eL sR eR i)).intervalIntegrable _ _

/-- The source-generated finite window is continuous through the damping boundary; no half-axis limit is interchanged. -/
theorem sourceSignedCurrentWindow_continuous (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (T : ℝ) :
    Continuous (fun lambda=>sourceSignedCurrentWindow q sL eL sR eR lambda T) := by
  apply continuous_pi
  intro i
  have joint : Continuous (fun u : ℂ×ℝ=>laplaceWeight u.1 u.2*
      sourceSignedUnitCurrent q sL eL sR eR (fieldUnit i) u.2) := by
    have weight : Continuous (fun u : ℂ×ℝ=>laplaceWeight u.1 u.2) := by unfold laplaceWeight; fun_prop
    exact weight.mul ((current_continuous q sL eL sR eR i).comp continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' joint 0 T

/-- Both independently prepared currents of the previous complete observer are now evaluated configuration Grams. -/
theorem sourceSignedCurrent_tensor (detector source : SourceUnitFieldLeg) :
    sourceMatchedUnitResponse detector source=
      ∑i : Fin 289,∑j : Fin 289,
        sourceSignedCurrentWindow detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
          detector.frequency.val detector.T i*sourceGreen (sourceUnitFieldPoint source) i j*
        sourceSignedCurrentWindow source.q source.sideL source.edgeL source.sideR source.edgeR
          source.frequency.val source.T j := by
  simpa only [sourceSignedCurrentWindow_generated,sourceUnitRawForcing] using
    sourceMatchedUnitResponse_tensor detector source

end LowEnergy.PreparationPhysicalSignedCurrentPoleObserver
