import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTransportedGraded

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldCovector
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussFockWeights GaussQuantumMultiplier
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionDecomposition PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceActionJets SourceQuantumScalarChart GaussLiveMomentum
open PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearFieldCurve
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open CanonicalGradedLocalCurrent Filter Set
abbrev Localizer:=CanonicalGradedLocalCurrent.Localizer
abbrev FiberMap:=CanonicalGradedLocalCurrent.FiberMap
open GaussUnitaryHistory (Index)
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators Distributions InnerProductSpace Interval
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

def fieldAmbientLinear : Field289 →ₗ[ℝ] Ambient where
  toFun:=fieldAmbient
  map_add' f g:=by
    apply Prod.ext
    · change fieldScalar (f+g)=fieldScalar f+fieldScalar g
      simp only [fieldScalar,Pi.add_apply,add_smul,Finset.sum_add_distrib]
    · apply PiLp.ext;intro i
      change fieldGauge (f+g) i.succ=fieldGauge f i.succ+fieldGauge g i.succ
      simp only [fieldGauge,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r f:=by
    apply Prod.ext
    · change fieldScalar (r • f)=r • fieldScalar f
      simp only [fieldScalar,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]
    · apply PiLp.ext;intro i
      change fieldGauge (r • f) i.succ=r • fieldGauge f i.succ
      simp only [fieldGauge,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

def fieldCoframeLinear : Field289 →ₗ[ℝ] LorentzianCoframe where
  toFun:=fieldCoframe
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def tangentLinear (z : SourceCoordinateSlice) : Field289 →ₗ[ℝ] SourceCoordinateSlice where
  toFun f:=fieldVector f z
  map_add' f g:=by
    apply Prod.ext
    · change lowerCoordinates (coframeResidual (f+g) z)=lowerCoordinates (coframeResidual f z)+lowerCoordinates (coframeResidual g z)
      rw [←map_add]
      congr 1
      have fc : fieldCoframe (f+g)=fieldCoframe f+fieldCoframe g:=fieldCoframeLinear.map_add f g
      unfold coframeResidual normalizedCoframe
      rw [fc,Matrix.add_mul,map_add]
      simp only [Matrix.sub_mul,Matrix.add_mul]
      abel
    · change (inverseL z (fieldAmbientLinear (f+g))).2=_
      rw [map_add,map_add];rfl
  map_smul' r f:=by
    apply Prod.ext
    · change lowerCoordinates (((fieldCoframeLinear (r • f))*(CanonicalGradedSpatialSource.sourceCoframe z)⁻¹-
        lorentzPart (fieldCoframeLinear (r • f)*(CanonicalGradedSpatialSource.sourceCoframe z)⁻¹))*CanonicalGradedSpatialSource.sourceCoframe z)=
        r • lowerCoordinates (coframeResidual f z)
      rw [map_smul,Matrix.smul_mul,map_smul,←smul_sub,Matrix.smul_mul,map_smul]
      rfl
    · change (inverseL z (fieldAmbientLinear (r • f))).2=_
      rw [map_smul,map_smul];rfl

def fieldBasis (i : Fin 289) : Field289:=Pi.single i 1

theorem field_coordinates (f : Field289) : f=∑i : Fin 289,f i • fieldBasis i :=by
  funext j
  simp [fieldBasis,Pi.single_apply,Finset.sum_apply]

theorem tangent_coordinates (f : Field289) (z : SourceCoordinateSlice) :
    fieldVector f z=∑i : Fin 289,f i • fieldVector (fieldBasis i) z :=by
  change tangentLinear z f=∑i : Fin 289,f i • tangentLinear z (fieldBasis i)
  calc
    _=tangentLinear z (∑i : Fin 289,f i • fieldBasis i):=congrArg (tangentLinear z) (field_coordinates f)
    _=_:=by simp only [map_sum,map_smul]

def sampleCurrent (S : SourceCoordinateSlice→SourceCoordinateSlice→ℂ) (f : Field289) (z : SourceCoordinateSlice) : ℂ:=
  fderiv ℝ (S z) z (fieldVector f z)

theorem sampleCurrent_coordinates (S : SourceCoordinateSlice→SourceCoordinateSlice→ℂ) (f : Field289) (z : SourceCoordinateSlice) :
    sampleCurrent S f z=∑i : Fin 289,(f i:ℂ)*sampleCurrent S (fieldBasis i) z :=by
  rw [sampleCurrent,tangent_coordinates,map_sum]
  apply Finset.sum_congr rfl;intro i _
  rw [map_smul];rfl

theorem sampleCurrent_parameter (S : SourceCoordinateSlice→SourceCoordinateSlice→ℂ) (f : Field289) (z : SourceCoordinateSlice)
    (joint : ContDiffAt ℝ ∞ (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (0,z))
    (slot : DifferentiableAt ℝ (S z) z) :
    parameterJet (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (0,z)=sampleCurrent S f z :=by
  have h:=partial_parameter _ 0 z joint
  have line : HasDerivAt (fun r : ℝ=>fieldCoordinateCurve f r z) (fieldVector f z) 0 :=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const (fieldVector f z)).const_add z using 1
    simp
  have ss : HasFDerivAt (S z) (fderiv ℝ (S z) z) (fieldCoordinateCurve f 0 z) :=by
    simpa only [fieldCoordinateCurve,zero_smul,add_zero] using slot.hasFDerivAt
  have s:=ss.comp_hasDerivAt 0 line
  exact h.unique s


open MeasureTheory

def parameterCurrent (S : SourceCoordinateSlice→SourceCoordinateSlice→ℂ) (f : Field289) (z : SourceCoordinateSlice) : ℂ:=
  parameterJet (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (0,z)

section Sample
variable (S : SourceCoordinateSlice→SourceCoordinateSlice→ℂ) (test : QuantumTest)
  (smooth : ∀f r z,z∈physicalChart→fieldCoordinateCurve f r z∈physicalChart→
    ContDiffAt ℝ ∞ (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (r,z))
  (slot : ∀z : physicalChart,DifferentiableAt ℝ (S z.val) z.val)
  (zero : ∀z x,z∉tsupport test→S z x=0)

include test zero in
theorem parameterCurrent_zero (f : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport test) :
    parameterCurrent S f z=0 :=
  partial_zero_outside _ (tsupport test) (isClosed_tsupport test)
    (fun r z hz=>zero z (fieldCoordinateCurve f r z) hz) 0 z outside

include test smooth slot zero in
theorem parameterCurrent_eq (f : Field289) (z : SourceCoordinateSlice) :
    parameterCurrent S f z=sampleCurrent S f z :=by
  by_cases hz : z∈tsupport test
  · have chart:=test.tsupport_subset hz
    exact sampleCurrent_parameter S f z
      (smooth f 0 z chart (by rw [PreparationVacuumGradedTransport.curve_zero];exact chart)) (slot ⟨z,chart⟩)
  · rw [parameterCurrent_zero S test zero f z hz]
    have same : S z=fun _=>0:=funext (fun x=>zero z x hz)
    rw [sampleCurrent,same,fderiv_const_apply]
    rfl

include test smooth zero in
theorem parameterCurrent_continuous (f : Field289) : Continuous (parameterCurrent S f) :=by
  apply continuous_iff_continuousAt.mpr;intro z
  by_cases hz : z∈tsupport test
  · have chart:=test.tsupport_subset hz
    have hs:=partial_smooth _ (0,z) (smooth f 0 z chart (by rw [PreparationVacuumGradedTransport.curve_zero];exact chart))
    exact hs.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport test).isOpen_compl.mem_nhds hz] with y hy
    exact parameterCurrent_zero S test zero f y hy

include test smooth zero in
theorem parameterCurrent_integrable (f : Field289) :
    Integrable (parameterCurrent S f) GaussHistoryHilbert.configurationMeasure :=by
  apply (parameterCurrent_continuous S test smooth zero f).integrable_of_hasCompactSupport
  apply test.hasCompactSupport.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_tsupport test)
  intro z hz;by_contra outside
  exact hz (parameterCurrent_zero S test zero f z outside)

include slot in
theorem sample_first_coordinates (f : Field289) :
    (fieldSampleJets S f test (smooth f) zero).first 0=
      ∑i : Fin 289,(f i:ℂ)*(fieldSampleJets S (fieldBasis i) test (smooth (fieldBasis i)) zero).first 0 :=by
  change (∫z,parameterCurrent S f z ∂GaussHistoryHilbert.configurationMeasure)=
    ∑i : Fin 289,(f i:ℂ)*(∫z,parameterCurrent S (fieldBasis i) z ∂GaussHistoryHilbert.configurationMeasure)
  have pointwise : parameterCurrent S f=fun z=>∑i : Fin 289,(f i:ℂ)*parameterCurrent S (fieldBasis i) z :=by
    funext z
    simp only [parameterCurrent_eq S test smooth slot zero]
    exact sampleCurrent_coordinates S f z
  rw [pointwise,integral_finsetSum]
  · apply Finset.sum_congr rfl;intro i _
    exact integral_const_mul _ _
  · intro i _
    exact (parameterCurrent_integrable S test smooth zero (fieldBasis i)).const_mul _

end Sample

theorem native_first_coordinates (f : Field289) (a b : QuantumTest) :
    (nativeFieldJets f a b).first 0=∑i : Fin 289,(f i:ℂ)*(nativeFieldJets (fieldBasis i) a b).first 0 :=
  sample_first_coordinates (nativeSample a b) a
    (fun g r z hz hx=>nativeSample_param a b (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth g r ⟨z,hz⟩) contDiffAt_snd)
    (fun z=>(nativeSample_param a b id (fun _=>z.val) z.val z.property contDiffAt_id contDiffAt_const).differentiableAt (by simp))
    (nativeSample_zero_outside a b) f

end LowEnergy.PreparationVacuumFieldCovector
