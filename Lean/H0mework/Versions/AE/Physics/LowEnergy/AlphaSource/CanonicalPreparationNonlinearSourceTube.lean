import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFieldLocalized
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNonlinearFieldCurve
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal StageNineCoframeVariation
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization PreparationVacuumSourceFieldFamily
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

def validStates : Set ActionState :=
  {s | s.1.det≠0 ∧ coframeTemporalPrincipalScalar s.1≠0}

theorem temporalScalar_smooth (e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    ContDiffAt ℝ ∞ coframeTemporalPrincipalScalar e := by
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.mul
    ((contDiffAt_pi.mp (contDiffAt_pi.mp (coframe_inv_contDiffAt e nondegenerate) 0) i).pow 2)

theorem validStates_open : IsOpen validStates := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have det : ContinuousAt (fun w : ActionState=>w.1.det) s :=
    coframe_det_contDiff.continuous.continuousAt.comp continuous_fst.continuousAt
  have temporal : ContinuousAt (fun w : ActionState=>coframeTemporalPrincipalScalar w.1) s :=
    (temporalScalar_smooth s.1 hs.1).continuousAt.comp continuous_fst.continuousAt
  have first : ∀ᶠ w : ActionState in 𝓝 s,w.1.det≠0 := det.eventually (isOpen_compl_singleton.mem_nhds hs.1)
  have second : ∀ᶠ w : ActionState in 𝓝 s,coframeTemporalPrincipalScalar w.1≠0 :=
    temporal.eventually (isOpen_compl_singleton.mem_nhds hs.2)
  filter_upwards [first,second] with w hw1 hw2
  exact ⟨hw1,hw2⟩

abbrev ParameterPoint := ℝ×SourceCoordinateSlice

def statePath (g : Field289) (psi : Localizer) (x : ParameterPoint) : ActionState :=
  sourceState x.2+(x.1*psi x.2) • fieldDirection g

theorem statePath_smooth (g : Field289) (psi : Localizer) : ContDiff ℝ ∞ (statePath g psi) :=
  (sourceState_smooth.comp contDiff_snd).add
    ((contDiff_fst.mul (psi.contDiff.comp contDiff_snd)).smul contDiff_const)

def curveDomain (g : Field289) (psi : Localizer) : Set ParameterPoint :=
  statePath g psi ⁻¹' validStates

theorem curveDomain_open (g : Field289) (psi : Localizer) : IsOpen (curveDomain g psi) :=
  validStates_open.preimage (statePath_smooth g psi).continuous

theorem sourceState_valid (z : physicalChart) : sourceState z.val∈validStates :=
  ⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩

theorem source_tube_exists (g : Field289) (psi : Localizer) :
    ∃ radius : ℝ,0<radius ∧ ∀ r z,|r| ≤ radius → z∈tsupport psi → (r,z)∈curveDomain g psi := by
  have base : ({0}:Set ℝ) ×ˢ tsupport psi⊆curveDomain g psi := by
    rintro ⟨r,z⟩ ⟨hr,hz⟩
    have zero : r=0 := hr
    subst r
    change sourceState z+(0*psi z) • fieldDirection g∈validStates
    rw [zero_mul,zero_smul,add_zero]
    exact sourceState_valid ⟨z,psi.tsupport_subset hz⟩
  obtain ⟨u,v,hu,_hv,hzero,hcover,hproduct⟩:=generalized_tube_lemma (isCompact_singleton (x:=(0:ℝ)))
    psi.hasCompactSupport (curveDomain_open g psi) base
  obtain ⟨epsilon,positive,hball⟩:=Metric.mem_nhds_iff.mp (hu.mem_nhds (hzero (by rfl)))
  refine ⟨epsilon/2,by positivity,?_⟩
  intro r z hr hz
  apply hproduct
  refine ⟨hball ?_,hcover hz⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero]
  exact hr.trans_lt (by linarith)

def fieldRadius (g : Field289) (psi : Localizer) : ℝ := (source_tube_exists g psi).choose

theorem fieldRadius_pos (g : Field289) (psi : Localizer) : 0 < fieldRadius g psi :=
  (source_tube_exists g psi).choose_spec.1

theorem fieldRadius_valid (g : Field289) (psi : Localizer) (r : ℝ) (z : SourceCoordinateSlice)
    (small : |r| ≤ fieldRadius g psi) (inside : z∈tsupport psi) : (r,z)∈curveDomain g psi :=
  (source_tube_exists g psi).choose_spec.2 r z small inside

def sourceTube (g : Field289) (psi : Localizer) : Set ParameterPoint :=
  Icc (-fieldRadius g psi) (fieldRadius g psi) ×ˢ tsupport psi

theorem sourceTube_compact (g : Field289) (psi : Localizer) : IsCompact (sourceTube g psi) :=
  isCompact_Icc.prod psi.hasCompactSupport

theorem sourceTube_valid (g : Field289) (psi : Localizer) : sourceTube g psi⊆curveDomain g psi := by
  rintro ⟨r,z⟩ ⟨hr,hz⟩
  exact fieldRadius_valid g psi r z (abs_le.mpr hr) hz

def hamiltonianQuantizer (p : PhysicalMomentum) : (Fin 4→SourceMatrix) →L[ℝ] FiberMap :=
  (quantizer.toContinuousLinearMap.restrictScalars ℝ).comp (fourierLinear p).toContinuousLinearMap

def rawCurve (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint) : FiberMap :=
  quantizer (fourierLinear p (stateHamiltonian (statePath g psi x)))

theorem rawCurve_smooth (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint)
    (valid : x∈curveDomain g psi) : ContDiffAt ℝ ∞ (rawCurve g psi p) x := by
  have stateSmooth : ContDiffAt ℝ ∞ stateHamiltonian (statePath g psi x) :=
    contDiffAt_pi.mpr (fun i=>stateHamiltonian_smooth _ valid.1 valid.2 i)
  exact (hamiltonianQuantizer p).contDiff.contDiffAt.comp x
    (stateSmooth.comp x (statePath_smooth g psi).contDiffAt)

def parameterDirection : ParameterPoint := (1,0)
def curveFirst (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint) : FiberMap :=
  fderiv ℝ (rawCurve g psi p) x parameterDirection

def curveSecond (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint) : FiberMap :=
  fderiv ℝ (curveFirst g psi p) x parameterDirection

theorem curveFirst_smooth (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint)
    (valid : x∈curveDomain g psi) : ContDiffAt ℝ ∞ (curveFirst g psi p) x :=
  ((rawCurve_smooth g psi p x valid).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem curveSecond_smooth (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (x : ParameterPoint)
    (valid : x∈curveDomain g psi) : ContDiffAt ℝ ∞ (curveSecond g psi p) x :=
  ((curveFirst_smooth g psi p x valid).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem source_second_bound_exists (g : Field289) (psi : Localizer) (p : PhysicalMomentum) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ x∈sourceTube g psi,‖curveSecond g psi p x‖ ≤ M := by
  have continuous : ContinuousOn (curveSecond g psi p) (sourceTube g psi) := fun x hx=>
    (curveSecond_smooth g psi p x (sourceTube_valid g psi hx)).continuousAt.continuousWithinAt
  obtain ⟨C,bound⟩:=(sourceTube_compact g psi).exists_bound_of_continuousOn continuous
  exact ⟨max 0 C,le_max_left _ _,fun x hx=>(bound x hx).trans (le_max_right _ _)⟩

def secondBound (g : Field289) (psi : Localizer) (p : PhysicalMomentum) : ℝ :=
  (source_second_bound_exists g psi p).choose

theorem secondBound_nonneg (g : Field289) (psi : Localizer) (p : PhysicalMomentum) : 0 ≤ secondBound g psi p :=
  (source_second_bound_exists g psi p).choose_spec.1

theorem secondBound_controls (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (z : SourceCoordinateSlice) (small : |r| ≤ fieldRadius g psi) (inside : z∈tsupport psi) :
    ‖curveSecond g psi p (r,z)‖ ≤ secondBound g psi p :=
  (source_second_bound_exists g psi p).choose_spec.2 (r,z) ⟨abs_le.mp small,inside⟩

private theorem parameter_path (r : ℝ) (z : SourceCoordinateSlice) :
    HasDerivAt (fun t : ℝ=>(t,z)) parameterDirection r :=
  (hasDerivAt_id r).prodMk (hasDerivAt_const r z)

theorem rawCurve_parameter_derivative (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (z : SourceCoordinateSlice) (valid : (r,z)∈curveDomain g psi) :
    HasDerivAt (fun t : ℝ=>rawCurve g psi p (t,z)) (curveFirst g psi p (r,z)) r := by
  have hf : HasFDerivAt (rawCurve g psi p) (fderiv ℝ (rawCurve g psi p) (r,z)) (r,z) :=
    ((rawCurve_smooth g psi p (r,z) valid).differentiableAt (by simp)).hasFDerivAt
  convert! hf.comp_hasDerivAt r (parameter_path r z) using 1

theorem curveFirst_parameter_derivative (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (z : SourceCoordinateSlice) (valid : (r,z)∈curveDomain g psi) :
    HasDerivAt (fun t : ℝ=>curveFirst g psi p (t,z)) (curveSecond g psi p (r,z)) r := by
  have hf : HasFDerivAt (curveFirst g psi p) (fderiv ℝ (curveFirst g psi p) (r,z)) (r,z) :=
    ((curveFirst_smooth g psi p (r,z) valid).differentiableAt (by simp)).hasFDerivAt
  convert! hf.comp_hasDerivAt r (parameter_path r z) using 1

def coefficientCurve (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (z : SourceCoordinateSlice) : FiberMap := rawCurve g psi p (r,z)-rawCurve g psi p (0,z)

theorem coefficientCurve_original (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (z : SourceCoordinateSlice) : coefficientCurve g psi p r z=
      quantizer (fourierLinear p (stateHamiltonian (sourceState z+(r*psi z) • fieldDirection g)-stateHamiltonian (sourceState z))) := by
  simp only [coefficientCurve,rawCurve,statePath,zero_mul,zero_smul,add_zero,map_sub]

end LowEnergy.PreparationVacuumNonlinearFieldCurve
