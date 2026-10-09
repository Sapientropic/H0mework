import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedGTVertexReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeResidueReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPoleFrameReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalDressedPhotonCouplingReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalDressedGTVertexReturn PreparationPhysicalDressedSpinChargeReturn
open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalFirstGaugeBackgroundReturn
open PreparationVacuumSourceActionJets PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization
open PreparationVacuumActionDecomposition PreparationVacuumActionFieldLift
open PreparationVacuumFieldConstraintResponse PreparationVacuumFieldCovector
open PreparationVacuumNativeFieldInjection PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumFullFieldRiesz
open PreparationVacuumSourcePreparedResponse
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open GaussHistoryHilbert GaussFockLift GaussFockPair GaussDensityCore CanonicalGradedSpatialSource CanonicalPhysicalYResolvent
open GaussComposite GaussComposite.SourceGraph MeasureTheory Filter Set
open GaussUnitaryHistory (Index)
open scoped BigOperators InnerProductSpace ContDiff Topology Matrix Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- The harmonic orbit, its generated gradient, and all nine remaining source fields. -/
def sourcePhotonModeMother (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (z : SourceCoordinateSlice) : FullMatrix :=
  sourceFirstGaugeQuadrature imaginary omega k 0 • sourceFirstBackgroundFullAd (sourceSymbol p (sourceState z))-
    symbolFirst p (sourceState z) (sourceFirstModeGradient imaginary omega k 0)+
    symbolFirst p (sourceState z) (sourceFirstModeRemainderState imaginary omega k (emitter z) 0)

theorem sourcePhotonModeMother_generated (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (z : physicalChart) :
    symbolFirst p (sourceState z.val) (fieldDirection (sourceFirstModeField imaginary omega k 0))=
      sourcePhotonModeMother imaginary omega k p z.val := by
  simpa only [configurationState_emitter,sourcePhotonModeMother] using
    sourceFirstModeSymbol_return imaginary omega k (emitter z.val) 0 p (sourceState_valid z)

/-- Density and complement remain alongside the calculated G+R matrix. -/
def sourcePhotonModeMatter (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  densityCurrent (sourceFirstModeField imaginary omega k 0) p a b z+
    pairSample z (a z) (quantizer (sourcePhotonModeMother imaginary omega k p z) (b z))-
    pairSample z (a z) (quantizer (symbolFirst p (sourceState z)
      (complement (sourceFirstModeField imaginary omega k 0) z)) (b z))

theorem sourcePhotonModeMatter_sample (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (a b : QuantumTest) (z : physicalChart) :
    sampleCurrent (fiberSample (actualFiber p) a b) (sourceFirstModeField imaginary omega k 0) z.val=
      sourcePhotonModeMatter imaginary omega k p a b z.val := by
  have whole:=fiber_sample_mother_balance (sourceFirstModeField imaginary omega k 0) p a b z
  have matrix:=symbolFirst_actual (sourceFirstModeField imaginary omega k 0) p z
  rw [sourcePhotonModeMother_generated] at matrix
  have pair:=congrArg (fun A : PreparationVacuumSourceFieldFamily.FiberMap=>pairSample z.val (a z.val) (A (b z.val))) matrix
  simp only [neg_apply,pairSample,PiLp.neg_apply,mul_neg,Finset.sum_neg_distrib] at pair
  change pairSample z.val (a z.val) (quantizer (sourcePhotonModeMother imaginary omega k p z.val) (b z.val))=
    -pairSample z.val (a z.val) (fiberFamily (sourceFirstModeField imaginary omega k 0) p z.val (b z.val)) at pair
  change _=densityCurrent _ p a b z.val+pairSample z.val (a z.val)
    (quantizer (sourcePhotonModeMother imaginary omega k p z.val) (b z.val))-_
  rw [pair]
  linear_combination whole

private theorem matter_parameter (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (z : SourceCoordinateSlice) :
    parameterCurrent (fiberSample (actualFiber p) a b) f z=
      sampleCurrent (fiberSample (actualFiber p) a b) f z :=
  parameterCurrent_eq (fiberSample (actualFiber p) a b) a
    (fun g r z hz hx=>fiberSample_param (actualFiber p) (actualFiber_smooth p) a b
      (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd (r,z) hx
      (field_curve_smooth g r ⟨z,hz⟩) contDiffAt_snd)
    (fun z=>(fiberSample_param (actualFiber p) (actualFiber_smooth p) a b id (fun _=>z.val)
      z.val z.property contDiffAt_id contDiffAt_const).differentiableAt (by simp))
    (fiberSample_zero_outside (actualFiber p) a b) f z

private theorem matter_integrable (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (parameterCurrent (fiberSample (actualFiber p) a b) f) GaussHistoryHilbert.configurationMeasure :=
  parameterCurrent_integrable (fiberSample (actualFiber p) a b) a
    (fun g r z hz hx=>fiberSample_param (actualFiber p) (actualFiber_smooth p) a b
      (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd (r,z) hx
      (field_curve_smooth g r ⟨z,hz⟩) contDiffAt_snd)
    (fiberSample_zero_outside (actualFiber p) a b) f

private theorem mode_parameter (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (a b : QuantumTest) (z : SourceCoordinateSlice) :
    parameterCurrent (fiberSample (actualFiber p) a b) (sourceFirstModeField imaginary omega k 0) z=
      sourcePhotonModeMatter imaginary omega k p a b z := by
  rw [matter_parameter]
  by_cases inside : z∈tsupport a
  · exact sourcePhotonModeMatter_sample imaginary omega k p a b ⟨z,a.tsupport_subset inside⟩
  · have zero : a z=0:=image_eq_zero_of_notMem_tsupport inside
    have same : fiberSample (actualFiber p) a b z=fun _=>0 :=
      funext (fun x=>fiberSample_zero_outside (actualFiber p) a b z x inside)
    simp only [sampleCurrent,same,fderiv_const_apply,zero_apply]
    simp only [sourcePhotonModeMatter,densityCurrent,zero,pairSample,PiLp.zero_apply,star_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,add_zero,sub_zero]

theorem sourcePhotonModeMatter_integrable (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (a b : QuantumTest) :
    Integrable (sourcePhotonModeMatter imaginary omega k p a b) GaussHistoryHilbert.configurationMeasure := by
  have same:=funext (mode_parameter imaginary omega k p a b)
  rw [←same]
  exact matter_integrable _ p a b

/-- The complete first jet keeps its native, coframe and retained-Y pieces; only its actual matter symbol is evaluated. -/
def sourcePhotonModeConfiguration (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (a b : QuantumTest) : ℂ :=
  (nativeFieldJets (sourceFirstModeField imaginary omega k 0) a b).first 0+
  (coframeFieldJets (sourceFirstModeField imaginary omega k 0) a b).first 0+
  (∫z,sourcePhotonModeMatter imaginary omega k p a b z ∂GaussHistoryHilbert.configurationMeasure)-
  (fiberFieldJets (sourceFirstModeField imaginary omega k 0) retainedCoefficient retainedCoefficient_smooth a b).first 0

theorem sourcePhotonModeConfiguration_generated (imaginary : Bool) (omega : ℝ) (k p : PhysicalMomentum)
    (a b : QuantumTest) :
    (fieldJets (sourceFirstModeField imaginary omega k 0) p a b).first 0=
      sourcePhotonModeConfiguration imaginary omega k p a b := by
  change _+_+(∫z,parameterCurrent (fiberSample (actualFiber p) a b)
    (sourceFirstModeField imaginary omega k 0) z ∂GaussHistoryHilbert.configurationMeasure)-_=_
  unfold sourcePhotonModeConfiguration
  rw [funext (mode_parameter imaginary omega k p a b)]

/-- This uses the actual source profile and both original inverses, without replacing either leg by a bare pole state. -/
theorem sourcePhotonModePrepared_generated (epsilon : ℝ) (precision : 0<epsilon)
    (imaginary : Bool) (omega : ℝ) (modeMomentum p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    preparedCurrent epsilon precision (sourceFirstModeField imaginary omega modeMomentum 0)
      p k F n z w left right a s b t=
    sourcePhotonModeConfiguration imaginary omega modeMomentum p
      (sourceTestApprox F ((finiteFull (p+k) F n z).adjoint (completedLeg left a s (sourceProfile epsilon precision))))
      (sourceTestApprox F (finiteFull p F n w (completedLeg right b t (sourceProfile epsilon precision)))) := by
  rw [preparedCurrent_source]
  exact sourcePhotonModeConfiguration_generated imaginary omega modeMomentum p _ _

end LowEnergy.PreparationPhysicalDressedPhotonCouplingReturn
