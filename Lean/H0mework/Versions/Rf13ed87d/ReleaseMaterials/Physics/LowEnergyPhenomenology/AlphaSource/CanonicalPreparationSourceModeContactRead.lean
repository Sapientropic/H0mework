import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceModeNativeSymbol

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalModeContact
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation

def sourceDeviationSample (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  pairSample z (a z) (quantizer (sourceModeDeviationSymbol p z) (b z))

def sourceDeviationForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,sourceDeviationSample p a b z ∂GaussHistoryHilbert.configurationMeasure

private theorem pair_real_linear (z : SourceCoordinateSlice) (u v w : FockFiber) (c : ℝ) :
    pairSample z u (c • v+w)=c • pairSample z u v+pairSample z u w := by
  simp only [pairSample,WithLp.ofLp_add,WithLp.ofLp_smul,Pi.add_apply,Pi.smul_apply,Complex.real_smul,mul_add,Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem sourceNativeSample_mode (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,z)=
      -(gaugeScale/2 : ℝ) • (rawSample (gaugeField 1 0) p a b (0,z)-rawSample (gaugeField 2 1) p a b (0,z))+
        sourceDeviationSample p a b z := by
  by_cases inside : z∈tsupport a
  · have h:=congrArg (quantizer.restrictScalars ℝ) (sourceNativeContactSymbol_generated p ⟨z,a.tsupport_subset inside⟩)
    simp only [map_add,map_smul] at h
    change quantizer (sourceNativeContactSymbol p z)=-(gaugeScale/2 : ℝ) • quantizer (sourceModeSymbol (sourceState z))+quantizer (sourceModeDeviationSymbol p z) at h
    have mode:=sourceModeSymbol_generated p (sourceState z) (coframe_nondegenerate ⟨z,a.tsupport_subset inside⟩)
    have converted:=congrArg quantizer mode
    simp only [map_sub,rawActionSymbol_actual] at converted
    rw [PreparationVacuumNativeLocalWard.nativeSample,nativeJointFiber,nativeNoetherFiber,ambientState_zero,nativeNoether_source]
    change pairSample z (a z) (quantizer (sourceNativeContactSymbol p z) (b z))=_
    rw [h,←converted]
    change pairSample z (a z) (-(gaugeScale/2 : ℝ) •
      (rawStateFiber (gaugeField 1 0) p (sourceState z) (b z)-rawStateFiber (gaugeField 2 1) p (sourceState z) (b z))+
        quantizer (sourceModeDeviationSymbol p z) (b z))=_
    rw [pair_real_linear]
    unfold sourceDeviationSample rawSample
    rw [rawFiber_zero,rawFiber_zero]
    simp only [pairSample,WithLp.ofLp_sub,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  · rw [PreparationVacuumNativeLocalWard.nativeSample_zero _ _ _ _ _ _ _ _ inside,
      rawSample_zero _ _ _ _ _ _ inside,rawSample_zero _ _ _ _ _ _ inside]
    simp only [sub_self,smul_zero,zero_add,sourceDeviationSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

private theorem raw_integrable (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (fun z=>rawSample reader p a b (0,z)) GaussHistoryHilbert.configurationMeasure :=
  parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
    (fun z=>rawSample_near_smooth reader p a b 0 z (by simpa only [norm_zero] using ambientRadius_positive a))
    (rawSample_zero reader p a b)

private theorem native_integrable (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (fun z=>PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,z))
      GaussHistoryHilbert.configurationMeasure :=
  parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
    (fun z=>nativeSample_near_smooth _ _ _ p a b 0 z (by simpa only [norm_zero] using ambientRadius_positive a))
    (PreparationVacuumNativeLocalWard.nativeSample_zero _ _ _ p a b)

private theorem deviation_integrable (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (sourceDeviationSample p a b) GaussHistoryHilbert.configurationMeasure := by
  have h:=((native_integrable p a b).sub ((raw_integrable (gaugeField 1 0) p a b).sub
    (raw_integrable (gaugeField 2 1) p a b) |>.smul (-(gaugeScale/2 : ℝ))))
  exact h.congr (Eventually.of_forall (fun z=>by simp only [Pi.sub_apply,Pi.smul_apply]; rw [sourceNativeSample_mode];abel))

theorem sourceNativeForm_mode (p : PhysicalMomentum) (a b : QuantumTest) :
    PreparationVacuumNativeLocalWard.nativeForm (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b 0=
      -(gaugeScale/2 : ℝ) • (rawForm (gaugeField 1 0) p a b 0-rawForm (gaugeField 2 1) p a b 0)+sourceDeviationForm p a b := by
  unfold PreparationVacuumNativeLocalWard.nativeForm rawForm sourceDeviationForm
  simp_rw [sourceNativeSample_mode]
  have h : Integrable (fun z=>-(gaugeScale/2 : ℝ) • (rawSample (gaugeField 1 0) p a b (0,z)-rawSample (gaugeField 2 1) p a b (0,z))) GaussHistoryHilbert.configurationMeasure := by
    simp only [Complex.real_smul]
    exact ((raw_integrable (gaugeField 1 0) p a b).sub (raw_integrable (gaugeField 2 1) p a b)).const_mul _
  rw [integral_add h (deviation_integrable p a b),
    integral_smul,integral_sub (raw_integrable (gaugeField 1 0) p a b) (raw_integrable (gaugeField 2 1) p a b)]


def sourceDeviationReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  finiteRiesz F (fun i j=>sourceDeviationForm p (frameTest F i) (frameTest F j))

private theorem sum_mode {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℂ M]
    (n x y d : ι→ι→ℂ) (v : ι→ι→M) (c : ℂ)
    (h : ∀ i j,n i j=c*(x i j-y i j)+d i j) :
    (∑ i,∑ j,n i j • v i j)=c • ((∑ i,∑ j,x i j • v i j)-(∑ i,∑ j,y i j • v i j))+
      (∑ i,∑ j,d i j • v i j) := by
  simp only [smul_sub,Finset.smul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h]
  simp only [add_smul,sub_smul,smul_sub,mul_smul]

attribute [local irreducible] frameVector frameTest rawForm sourceDeviationForm sourceDeviationReader
  PreparationVacuumNativeLocalWard.nativeReader PreparationVacuumNativeLocalWard.nativeForm

theorem sourceNativeReader_mode (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    PreparationVacuumNativeLocalWard.nativeReader (Fin.castAdd 6 (2:Fin 3)) 1 0 p F 0=
      (-(gaugeScale/2 : ℝ) : ℂ) • (PreparationVacuumRawJointFeedback.rawReader (gaugeField 1 0) p F 0-
        PreparationVacuumRawJointFeedback.rawReader (gaugeField 2 1) p F 0)+sourceDeviationReader p F := by
  unfold PreparationVacuumNativeLocalWard.nativeReader PreparationVacuumRawJointFeedback.rawReader sourceDeviationReader finiteRiesz
  exact sum_mode (ι:=FrameIndex F) (M:=H→L[ℂ] H)
    (fun i j=>PreparationVacuumNativeLocalWard.nativeForm (Fin.castAdd 6 (2:Fin 3)) 1 0 p (frameTest F i) (frameTest F j) 0)
    (fun i j=>rawForm (gaugeField 1 0) p (frameTest F i) (frameTest F j) 0)
    (fun i j=>rawForm (gaugeField 2 1) p (frameTest F i) (frameTest F j) 0)
    (fun i j=>sourceDeviationForm p (frameTest F i) (frameTest F j))
    (fun i j=>InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
    (-(gaugeScale/2 : ℝ) : ℂ)
    (fun i j=>by simpa only [Complex.real_smul,Complex.ofReal_neg] using sourceNativeForm_mode p (frameTest F i) (frameTest F j))

def sourceContactKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  SourceFiniteUnitary.time (actualC pL q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*
    PreparationVacuumNativeLocalWard.nativeReader (Fin.castAdd 6 (2:Fin 3)) 1 0 pR q.F 0*
      CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*SourceFiniteUnitary.time (actualC pR q.F) t

def sourceDeviationKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  SourceFiniteUnitary.time (actualC pL q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*
    sourceDeviationReader pR q.F*CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w*
      SourceFiniteUnitary.time (actualC pR q.F) t

theorem sourceContactKernel_mode (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    sourceContactKernel q pL pR t=
      (-(gaugeScale/2 : ℝ) : ℂ) • (sourceGaugeZeroHistoryKernel q pL pR 1 0 t-
        sourceGaugeZeroHistoryKernel q pL pR 2 1 t)+sourceDeviationKernel q pL pR t := by
  unfold sourceContactKernel sourceDeviationKernel sourceGaugeZeroHistoryKernel
  rw [sourceNativeReader_mode]
  simp only [mul_add,add_mul,mul_sub,sub_mul,smul_sub,smul_mul_assoc,mul_smul_comm]

private theorem mode_read_balance {B : Type*} [AddCommGroup B] [Module ℂ B]
    (L : B→ₗ[ℂ] ℂ) (c : ℂ) (N X Y D : B) (source : N=(-c) • (X-Y)+D) :
    c • (-L X-(-L Y))=L N-L D := by
  rw [source,map_add,map_smul,map_sub]
  simp only [smul_eq_mul]
  ring

theorem sourceActualMode_contact_deviation (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (gaugeScale/2 : ℝ) • (sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)-
      sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1))=
      sourcePoleRead q.epsilon q.precision pL pR left right (sourceContactKernel q pL pR t)-
        sourcePoleRead q.epsilon q.precision pL pR left right (sourceDeviationKernel q pL pR t) := by
  rw [sourceGaugeCurrent_zeroHistory q pL pR left right 1 0 t nonrealL nonrealR,
    sourceGaugeCurrent_zeroHistory q pL pR left right 2 1 t nonrealL nonrealR]
  simp only [Complex.real_smul]
  exact mode_read_balance (sourcePoleRead q.epsilon q.precision pL pR left right).toLinearMap
    _ _ _ _ _ (by simpa only [Complex.ofReal_neg] using sourceContactKernel_mode q pL pR t)

end LowEnergy.PreparationVacuumPhysicalModeContact
