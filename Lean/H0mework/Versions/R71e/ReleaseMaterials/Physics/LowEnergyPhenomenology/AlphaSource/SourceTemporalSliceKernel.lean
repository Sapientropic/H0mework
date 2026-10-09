import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstUnitFourPointReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstTemporalUnitResponse

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

/-- The same full literal temporal column is retained; only its actual slice restriction is evaluated. -/
abbrev sourceTemporalAxis : Field289 := sourceEnergyAxisField 1 0

theorem sourceTemporalAmbient_zero : fieldAmbient sourceTemporalAxis=0 := by
  apply Prod.ext
  · exact (sourceFirstGauge_sectors 0).2.1
  · apply PiLp.ext
    intro i
    change fieldGauge sourceTemporalAxis i.succ=0
    rw [sourceFirstGauge_generated,sourceFirstTemporal_connection,if_neg (Fin.succ_ne_zero i)]

theorem sourceTemporalVector_zero (z : SourceCoordinateSlice) : fieldVector sourceTemporalAxis z=0 := by
  have coframe : coframeSliceDirection sourceTemporalAxis z=0 := by
    rw [coframeSliceDirection,coframeResidual,normalizedCoframe,(sourceFirstGauge_sectors 0).1,
      Matrix.zero_mul,map_zero,sub_self,Matrix.zero_mul,map_zero]
  simp only [fieldVector,gaugeParameters,sourceTemporalAmbient_zero,map_zero,coframe,Prod.snd_zero,Prod.mk_zero_zero]

private theorem curve_congr (f g : Field289) (same : fieldVector f=fieldVector g) :
    fieldCoordinateCurve f=fieldCoordinateCurve g := by
  funext r z
  simp only [fieldCoordinateCurve,same]

private theorem half_congr (f g : Field289) (same : fieldVector f=fieldVector g) (N : ℕ) :
    halfRatio f N=halfRatio g N := by
  funext z r
  simp only [halfRatio,curve_congr f g same]

private theorem correction_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (u : PreparationVacuumSourceActionJets.Parameter) (v : SourceCoordinateSlice) :
    spatialCorrection f u v=spatialCorrection g u v := by
  apply congrArg GaussFockWeights.weight
  funext N
  simp only [spatialRatio,half_congr f g same N]

private theorem native_sample_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (a b : QuantumTest) (u : PreparationVacuumSourceActionJets.Parameter) :
    nativeFixedSample f a b u=nativeFixedSample g a b u := by
  simp only [nativeFixedSample,basePair,correctedMomentum,correctedDerivative,
    curve_congr f g same,correction_congr f g same]

private theorem coframe_sample_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (a b : QuantumTest) (u : PreparationVacuumSourceActionJets.Parameter) :
    coframeFixedSample f a b u=coframeFixedSample g a b u := by
  simp only [coframeFixedSample,mixedFixedSample,basePair,correctedCoframe,correctedDerivative,
    curve_congr f g same,correction_congr f g same]

private theorem form_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (p : PhysicalMomentum) (a b : QuantumTest) : jointForm p a b f=jointForm p a b g := by
  simp only [jointForm,nativeFixedIntegral,coframeFixedIntegral,fixedFiber,fixedSample,
    native_sample_congr f g same,coframe_sample_congr f g same,curve_congr f g same]

private theorem uncut_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (phi : CanonicalGradedLocalCurrent.Localizer) : uncutOperator f phi 1=uncutOperator g phi 1 := by
  apply GaussYukawaGrade.core_ext
  intro a
  rw [uncutOperator_core,uncutOperator_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change ((phi z:ℂ) • GaussYukawaCoefficient.sourceMap
      (GaussNativePotential.scalarField (fieldCoordinateCurve f 1 z))) (a z)=
    ((phi z:ℂ) • GaussYukawaCoefficient.sourceMap
      (GaussNativePotential.scalarField (fieldCoordinateCurve g 1 z))) (a z)
  rw [curve_congr f g same]

private theorem generator_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator p F z f=jointGenerator p F z g := by
  have compression : jointCompression p F f=jointCompression p F g := by
    unfold jointCompression
    apply congrArg (sourceAssembly p F)
    funext i j
    exact form_congr f g same p _ _
  have yukawa : jointY (finiteRetainer p F) f=jointY (finiteRetainer p F) g := by
    rw [jointY_source,jointY_source]
    exact uncut_congr f g same _
  simp only [jointGenerator,compression,yukawa]

/-- Exact invariance of the original reduced configuration family, rather than deletion of the full ambient temporal column. -/
theorem sourceTemporalGenerator_invariant (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (h : Field289) (r : ℝ) :
    jointGenerator p F z (h+r • sourceTemporalAxis)=jointGenerator p F z h := by
  apply generator_congr
  funext x
  change PreparationVacuumFieldCovector.tangentLinear x (h+r • sourceTemporalAxis)=PreparationVacuumFieldCovector.tangentLinear x h
  rw [map_add,map_smul]
  change fieldVector h x+r • fieldVector sourceTemporalAxis x=fieldVector h x
  rw [sourceTemporalVector_zero,smul_zero,add_zero]

private theorem null_direction {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : E→V) (h v : E)
    (same : ∀r : ℝ,f (h+r • v)=f h) : fderiv ℝ f h v=0 := by
  by_cases differentiable : DifferentiableAt ℝ f h
  · have line : HasDerivAt (fun r : ℝ=>h+r • v) v 0 := by
      convert ((hasDerivAt_id (0:ℝ)).smul_const v).const_add h using 1
      all_goals first | rfl | simp only [one_smul]
    have generated:=differentiable.hasFDerivAt.comp_hasDerivAt_of_eq 0 line
      (by simp only [zero_smul,add_zero])
    have constant : HasDerivAt (fun r : ℝ=>f (h+r • v)) 0 0 :=
      (hasDerivAt_const (0:ℝ) (f h)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall same)
    exact generated.unique constant
  · rw [fderiv_zero_of_not_differentiableAt differentiable,zero_apply]

/-- The original slice current has an exact temporal null slot; the full raw charge reader is evaluated separately below. -/
theorem sourceTemporalCurrent_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (h : Field289) : jointCurrent p F z h sourceTemporalAxis=0 := by
  exact null_direction (jointGenerator p F z) h sourceTemporalAxis
    (sourceTemporalGenerator_invariant p F z h)

private theorem derivative_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ→V) (v : V) (paid : HasDerivAt f v 0) (zero : ∀r,f r=0) : v=0 :=
  paid.unique ((hasDerivAt_const (0:ℝ) (0:V)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall zero))

theorem sourceTemporalHessian_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (f : Field289) : jointHessian p F z sourceTemporalAxis f=0 := by
  exact (jointHessian_symmetric p F z sourceTemporalAxis f).trans
    (derivative_zero _ _ (current_direction p F z f sourceTemporalAxis)
      (fun r=>sourceTemporalCurrent_zero p F z (r • f)))

theorem sourceTemporalTimeSlope_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    timeSlope sourceTemporalAxis p F t=0 := by
  simp only [timeSlope,sourceTemporalCurrent_zero,CanonicalGradedVariation.variation,
    CanonicalGradedVariation.variationBetween,smul_zero,mul_zero,zero_mul,intervalIntegral.integral_zero]

/-- Both orderings and the true Hessian consume the same evaluated slice-null force slot. -/
theorem sourceTemporalMixedVertex_zero (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z w : ℂ) (f : Field289) : mixedVertex sourceTemporalAxis f p k F z w=0 := by
  simp only [mixedVertex,sourceTemporalCurrent_zero,sourceTemporalHessian_zero,mul_zero,zero_mul,zero_add,sub_zero]

/-- This is an evaluated temporal-force restriction of the original five terms, not a statement that the temporal density or the full field vanishes. -/
theorem sourceTemporalFiveForce_zero (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z w : ℂ) (j : Fin 4) (age : ℝ) :
    fiveDerivative (sourceEnergyAxisField 1 j) sourceTemporalAxis p k F z w age=0 := by
  simp only [fiveDerivative,sourceTemporalTimeSlope_zero,sourceTemporalCurrent_zero,
    sourcePolarizationAxis_readerContact,mul_zero,zero_mul,neg_zero,zero_add]

/-- The same full ambient direction has its source-generated charge symbol and actual weighted density. -/
theorem sourceTemporalAmbient_charge (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    symbolFirst p s (fieldDirection sourceTemporalAxis)=sourceFirstChargeMatrix ∧
      rawActionSymbol sourceTemporalAxis p s=sourceFirstTemporalWeight s*sourceFirstChargeMatrix :=
  ⟨sourceFirstTemporal_symbol s valid p,sourceFirstTemporal_raw s valid p⟩

end LowEnergy.PreparationPhysicalTemporalConstraintObserver
