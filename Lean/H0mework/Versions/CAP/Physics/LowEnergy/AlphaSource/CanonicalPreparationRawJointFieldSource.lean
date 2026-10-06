import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationJointMixedResponse

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumRawJointFeedback
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreHilbert GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumNonlinearFieldCurve PreparationVacuumActualFieldQuantization
open PreparationVacuumActionFieldLift PreparationVacuumGradedTransport PreparationVacuumJointFieldResponse
open PreparationVacuumHalfDensityFiber PreparationVacuumSourceActionJets
open PreparationVacuumGaugeSourceInjection PreparationVacuumFieldConstraintResponse
open StageNineHolonomicField FullQuantum.StateGreen
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
abbrev FiberMap:=CanonicalGradedLocalCurrent.FiberMap

/-- The two source restrictions sit in one emitted mother-state square. -/
def ambientState (u : JointParameter) : ActionState:=sourceState u.2+fieldDirectionLinear u.1

theorem ambientState_zero (z : SourceCoordinateSlice) : ambientState (0,z)=sourceState z :=by
  simp only [ambientState,map_zero,add_zero]

theorem ambientState_ray (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) :
    ambientState (r • f,z)=stateSquare f z r r :=by
  rw [stateSquare_ambient]
  simp only [ambientState,map_smul]
  rfl

theorem ambientState_coordinate (h : Field289) (z : SourceCoordinateSlice) :
    ambientState (h,z)=sourceState (jointCurve (h,z))+complement h z :=by
  change sourceState z+fieldDirection h=sourceState (z+fieldVector h z)+complement h z
  have affine:=sourceState_affine z (fieldVector h z) 1
  simp only [one_smul] at affine
  rw [affine,complement]
  abel

theorem ambientState_smooth : ContDiff ℝ ∞ ambientState :=
  (sourceState_smooth.comp contDiff_snd).add
    (fieldDirectionLinear.toContinuousLinearMap.contDiff.comp contDiff_fst)

theorem sourceState_valid (z : SourceCoordinateSlice) (hz : z∈physicalChart) : sourceState z∈validStates:=
  ⟨coframe_nondegenerate ⟨z,hz⟩,temporal_noncharacteristic ⟨z,hz⟩⟩

theorem ambient_tube_exists (a : QuantumTest) :
    ∃R : ℝ,0<R ∧ ∀h z,‖h‖≤ R→z∈tsupport a→ambientState (h,z)∈validStates :=by
  let U : Set JointParameter:=ambientState ⁻¹' validStates
  have op : IsOpen U:=validStates_open.preimage ambientState_smooth.continuous
  have base : ({0}:Set Field289) ×ˢ tsupport a⊆U :=by
    rintro ⟨h,z⟩ ⟨hh,hz⟩
    have h0 : h=0:=hh
    subst h
    change ambientState (0,z)∈validStates
    rw [ambientState_zero]
    exact sourceState_valid z (a.tsupport_subset hz)
  obtain ⟨u,v,hu,_hv,hzero,hcover,hproduct⟩:=generalized_tube_lemma (isCompact_singleton (x:=(0:Field289))) a.hasCompactSupport op base
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp (hu.mem_nhds (hzero (by rfl)))
  refine ⟨e/2,by positivity,?_⟩
  intro h z hh hz
  apply hproduct
  refine ⟨hball ?_,hcover hz⟩
  rw [Metric.mem_ball,dist_zero_right]
  linarith

def ambientRadius (a : QuantumTest) : ℝ:=(ambient_tube_exists a).choose

theorem ambientRadius_positive (a : QuantumTest) : 0<ambientRadius a:=(ambient_tube_exists a).choose_spec.1

theorem ambientRadius_valid (a : QuantumTest) (h : Field289) (z : SourceCoordinateSlice)
    (small : ‖h‖≤ ambientRadius a) (inside : z∈tsupport a) : ambientState (h,z)∈validStates:=
  (ambient_tube_exists a).choose_spec.2 h z small inside

def rawFiber (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) : FiberMap:=
  quantizer (rawActionSymbol reader p (ambientState u))

def rawContact (reader force : Field289) (p : PhysicalMomentum) (u : JointParameter) : FiberMap:=
  quantizer (rawActionContact reader p (ambientState u) (fieldDirection force))

theorem rawFiber_zero (reader : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    rawFiber reader p (0,z)=rawStateFiber reader p (sourceState z) :=by
  rw [rawFiber,ambientState_zero,rawActionSymbol_actual]

theorem rawContact_zero (reader force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    rawContact reader force p (0,z.val)=rawContactFiber reader force p z.val :=by
  rw [rawContact,ambientState_zero,rawActionContact_actual]

theorem rawFiber_source (reader : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (valid : ambientState u∈validStates) :
    rawFiber reader p u=quantizer (-(4:ℂ) • (sourceActionWeight (ambientState u)*
      symbolFirst p (ambientState u) (fieldDirection reader))) :=by
  rw [rawFiber,rawActionSymbol_source reader p _ valid]

theorem rawContact_source (reader force : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (valid : ambientState u∈validStates) :
    rawContact reader force p u=quantizer (-(4:ℂ) •
      (actionWeightFirst (ambientState u) (fieldDirection force)*symbolFirst p (ambientState u) (fieldDirection reader)+
        sourceActionWeight (ambientState u)*symbolSecond p (ambientState u) (fieldDirection reader) (fieldDirection force))) :=by
  rw [rawContact,rawActionContact_generated reader p _ _ valid]

theorem rawFiber_smooth (reader : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (valid : ambientState u∈validStates) : ContDiffAt ℝ ∞ (rawFiber reader p) u :=
  (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((rawActionSymbol_smooth reader p _ valid).comp u ambientState_smooth.contDiffAt)

theorem rawFiber_direction (reader force : Field289) (p : PhysicalMomentum) (h : Field289)
    (z : SourceCoordinateSlice) (valid : ambientState (h,z)∈validStates) :
    HasDerivAt (fun r : ℝ=>rawFiber reader p (h+r • force,z)) (rawContact reader force p (h,z)) 0 :=by
  have hs:=(rawActionSymbol_smooth reader p _ valid).differentiableAt (by simp) |>.hasFDerivAt
  have line:=hs.comp_hasDerivAt_of_eq 0 (state_line (ambientState (h,z)) (fieldDirection force)) (by simp)
  have quantified:=(quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 line
  have same (r : ℝ) : ambientState (h+r • force,z)=ambientState (h,z)+r • fieldDirection force :=by
    simp only [ambientState,map_add,map_smul,add_assoc]
    rfl
  change HasDerivAt (fun r : ℝ=>quantizer (rawActionSymbol reader p (ambientState (h,z)+r • fieldDirection force)))
    (quantizer (rawActionContact reader p (ambientState (h,z)) (fieldDirection force))) 0 at quantified
  simpa only [rawFiber,rawContact,same] using quantified

def rawSample (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) : ℂ:=
  pairSample u.2 (a u.2) (rawFiber reader p u (b u.2))

theorem rawSample_zero (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport a) : rawSample reader p a b (h,z)=0 :=by
  simp only [rawSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

theorem rawSample_smooth (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter)
    (base : u.2∈physicalChart) (valid : ambientState u∈validStates) : ContDiffAt ℝ ∞ (rawSample reader p a b) u :=by
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have coefficient:=R.contDiff.contDiffAt.comp u (rawFiber_smooth reader p u valid)
  exact pairSample_param Prod.snd _ _ u base contDiffAt_snd (a.contDiff.contDiffAt.comp u contDiffAt_snd)
    (coefficient.clm_apply (b.contDiff.contDiffAt.comp u contDiffAt_snd))

theorem rawSample_near_smooth (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    ContDiffAt ℝ ∞ (rawSample reader p a b) (h,z) :=by
  by_cases inside : z∈tsupport a
  · exact rawSample_smooth reader p a b (h,z) (a.tsupport_subset inside) (ambientRadius_valid a h z small.le inside)
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact rawSample_zero reader p a b u.1 u.2 hu

def rawForm (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  ∫z,rawSample reader p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

theorem rawForm_C2 (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (rawForm reader p a b) 0 :=
  source_integral_C2 _ (tsupport a) a.hasCompactSupport (ambientRadius a) (ambientRadius_positive a)
    (rawSample_near_smooth reader p a b) (rawSample_zero reader p a b)


def rawContactSample (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) : ℂ:=
  pairSample z (a z) (rawContact reader force p (h,z) (b z))

theorem rawSample_direction (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (valid : ambientState (h,z)∈validStates) :
    HasDerivAt (fun r : ℝ=>rawSample reader p a b (h+r • force,z))
      (rawContactSample reader force p a b h z) 0 :=by
  let E:=(ContinuousLinearMap.apply ℂ FockFiber (b z)).restrictScalars ℝ
  let P:=(pairRight z (a z)).restrictScalars ℝ
  have applied:=E.hasFDerivAt.comp_hasDerivAt 0 (rawFiber_direction reader force p h z valid)
  exact P.hasFDerivAt.comp_hasDerivAt 0 applied

def rawContactForm (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ:=
  ∫z,rawContactSample reader force p a b 0 z ∂GaussHistoryHilbert.configurationMeasure

attribute [local irreducible] rawSample rawContactSample rawFiber rawContact

theorem rawPartial_source (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (z : SourceCoordinateSlice) :
    parameterPartial (rawSample reader p a b) (0,z) force=rawContactSample reader force p a b 0 z :=by
  by_cases inside : z∈tsupport a
  · have smooth:=rawSample_near_smooth reader p a b 0 z (by simpa using ambientRadius_positive a)
    have differential:=parameterPartial_derivative (rawSample reader p a b) 0 z smooth
    have first:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
    have original:=rawSample_direction reader force p a b 0 z
      (by rw [ambientState_zero];exact sourceState_valid z (a.tsupport_subset inside))
    have second : HasDerivAt (fun r : ℝ=>rawSample reader p a b (r • force,z))
        (rawContactSample reader force p a b 0 z) 0:=by
      simpa only [zero_add] using original
    exact first.unique second
  · rw [parameterPartial_zero _ (tsupport a) (isClosed_tsupport a) (rawSample_zero reader p a b) 0 z inside]
    simp only [zero_apply,rawContactSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem rawForm_direction (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fun r : ℝ=>rawForm reader p a b (r • force)) (rawContactForm reader force p a b) 0 :=by
  have zero:=(rawSample_zero reader p a b)
  have positive:=ambientRadius_positive a
  have derivative:=source_integral_fderivative (rawSample reader p a b) (tsupport a) a.hasCompactSupport
    (ambientRadius a) positive (rawSample_near_smooth reader p a b) zero 0 (by simp;positivity)
  have integral : Integrable (fun z=>parameterPartial (rawSample reader p a b) (0,z)) GaussHistoryHilbert.configurationMeasure:=
    parameter_slice_integrable _ (tsupport a) a.hasCompactSupport 0
      (fun z=>parameterPartial_smooth _ _ (rawSample_near_smooth reader p a b 0 z (by simpa using positive)))
      (parameterPartial_zero _ (tsupport a) (isClosed_tsupport a) zero)
  have first:=derivative.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have value : (∫z,parameterPartial (rawSample reader p a b) (0,z) ∂GaussHistoryHilbert.configurationMeasure) force=
      rawContactForm reader force p a b :=by
    rw [ContinuousLinearMap.integral_apply integral]
    exact integral_congr_ae (Filter.Eventually.of_forall (rawPartial_source reader force p a b))
  exact first.congr_deriv value

end LowEnergy.PreparationVacuumRawJointFeedback
