import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeReferenceWard

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedLockedWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
abbrev Operator:=H→L[ℂ] H
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

def nativeDeviationSample (n : Fin 9) (theta : ℝ) (p : PhysicalMomentum)
    (a b : QuantumTest) (u : JointParameter) : ℂ :=
  pairSample u.2 (a u.2)
    (quantizer (nativeDeviationNoether n theta p (sourceState u.2) (ambientState u)) (b u.2))

def nativeDeviationForm (n : Fin 9) (theta : ℝ) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) : ℂ :=
  ∫z,nativeDeviationSample n theta p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

private theorem pair_matrix_sub (z : SourceCoordinateSlice) (a b : FockFiber) (A B : FullMatrix) :
    pairSample z a (quantizer (A-B) b)=
      pairSample z a (quantizer A b)-pairSample z a (quantizer B b) := by
  change (pairRight z a) (quantizer (A-B) b)=
    (pairRight z a) (quantizer A b)-(pairRight z a) (quantizer B b)
  rw [map_sub,sub_apply,map_sub]

private theorem sample_reference (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    noetherSample (nativeSourceColumn n theta gradient) p a b (h,z)=
      nativeSample n theta gradient p a b (h,z)-nativeDeviationSample n theta p a b (h,z) := by
  by_cases inside : z∈tsupport a
  · have valid:=ambientRadius_valid a h z small.le inside
    change pairSample z (a z)
      (quantizer (transportedRawSymbol (nativeSourceColumn n theta gradient) (sourceState z) (ambientState (h,z)) p) (b z))=_
    rw [native_reference_transport n theta gradient p (sourceState z) (ambientState (h,z)) valid,pair_matrix_sub]
    rfl
  · rw [noetherSample_zero _ p a b h z inside,nativeSample_zero n theta gradient p a b h z inside]
    simp only [nativeDeviationSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,sub_zero]

/-- The original dense tests generate integrable deviation forms; no completed-state regularity is required as a premise. -/
theorem native_reference_forms (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (small : ‖h‖<ambientRadius a) :
    noetherForm (nativeSourceColumn n theta gradient) p a b h=
      PreparationVacuumNativeLocalWard.nativeForm n theta gradient p a b h-nativeDeviationForm n theta p a b h := by
  have ni:=parameter_slice_integrable (nativeSample n theta gradient p a b) (tsupport a) a.hasCompactSupport h
    (fun z=>nativeSample_near_smooth n theta gradient p a b h z small)
    (nativeSample_zero n theta gradient p a b)
  have qi:=parameter_slice_integrable (noetherSample (nativeSourceColumn n theta gradient) p a b)
    (tsupport a) a.hasCompactSupport h
    (fun z=>noetherSample_near_smooth (nativeSourceColumn n theta gradient) p a b h z small)
    (noetherSample_zero (nativeSourceColumn n theta gradient) p a b)
  have same (z : SourceCoordinateSlice) : nativeSample n theta gradient p a b (h,z)-
      noetherSample (nativeSourceColumn n theta gradient) p a b (h,z)=nativeDeviationSample n theta p a b (h,z) := by
    rw [sample_reference n theta gradient p a b h z small]
    abel
  have di : Integrable (fun z=>nativeDeviationSample n theta p a b (h,z)) GaussHistoryHilbert.configurationMeasure :=
    (ni.sub qi).congr (Eventually.of_forall same)
  unfold noetherForm PreparationVacuumNativeLocalWard.nativeForm nativeDeviationForm
  rw [←integral_sub ni di]
  exact integral_congr_ae (Eventually.of_forall (fun z=>sample_reference n theta gradient p a b h z small))

def nativeDeviationReader (n : Fin 9) (theta : ℝ) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (h : Field289) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>nativeDeviationForm n theta p (frameTest F i) (frameTest F j) h)

private theorem riesz_sub (F : GaussUnitaryHistory.Index) (a b : FrameIndex F→FrameIndex F→ℂ) :
    finiteRiesz F (fun i j=>a i j-b i j)=finiteRiesz F a-finiteRiesz F b := by
  simp only [finiteRiesz,sub_smul,Finset.sum_sub_distrib]

/-- The actual fixed-F reader germ is paid by the same source tests and their source-owned compact chart radius. -/
theorem native_reference_reader_germ (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (nativeSourceColumn n theta gradient) p F=ᶠ[𝓝 0]
      fun h=>nativeReader n theta gradient p F h-nativeDeviationReader n theta p F h := by
  have entries : ∀ᶠh : Field289 in 𝓝 0,∀i j : FrameIndex F,
      noetherForm (nativeSourceColumn n theta gradient) p (frameTest F i) (frameTest F j) h=
        PreparationVacuumNativeLocalWard.nativeForm n theta gradient p (frameTest F i) (frameTest F j) h-
          nativeDeviationForm n theta p (frameTest F i) (frameTest F j) h := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have near : ∀ᶠh : Field289 in 𝓝 0,‖h‖<ambientRadius (frameTest F i) :=
      (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using ambientRadius_positive (frameTest F i)))
    exact near.mono (fun h small=>native_reference_forms n theta gradient p (frameTest F i) (frameTest F j) h small)
  filter_upwards [entries] with h paid
  unfold noetherReader nativeReader nativeDeviationReader
  simp_rw [paid]
  exact riesz_sub F _ _

theorem native_reference_reader (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (nativeSourceColumn n theta gradient) p F 0=
      nativeReader n theta gradient p F 0-nativeDeviationReader n theta p F 0 :=
  (native_reference_reader_germ n theta gradient p F).self_of_nhds

private theorem deviation_reader_germ (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    nativeDeviationReader n theta p F=ᶠ[𝓝 0]
      fun h=>nativeReader n theta gradient p F h-noetherReader (nativeSourceColumn n theta gradient) p F h := by
  filter_upwards [native_reference_reader_germ n theta gradient p F] with h paid
  rw [paid]
  abel

private theorem deviation_reader_differentiable (n : Fin 9) (theta : ℝ) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : DifferentiableAt ℝ (nativeDeviationReader n theta p F) 0 := by
  have source:=(nativeReader_C2 n theta (0:Fin 4→ℝ) p F).sub
    (noetherReader_C2 (nativeSourceColumn n theta 0) p F)
  have same:=deviation_reader_germ n theta (0:Fin 4→ℝ) p F
  exact (source.differentiableAt (by norm_num)).congr_of_eventuallyEq same

/-- This contact is the derivative of the generated deviation integral itself. -/
def nativeDeviationReaderContact (n : Fin 9) (theta : ℝ) (force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : H→L[ℂ]H := fderiv ℝ (nativeDeviationReader n theta p F) 0 force

theorem native_deviation_reader_generated (n : Fin 9) (theta : ℝ) (force : Field289)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (fun r : ℝ=>nativeDeviationReader n theta p F (r • force)) (nativeDeviationReaderContact n theta force p F) 0 :=
  (deviation_reader_differentiable n theta p F).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (fieldRay_derivative force 0) (by simp)

/-- The original mixed Noether contact retains the same complete native and configuration/preparation pieces. -/
theorem native_reference_reader_contact (n : Fin 9) (theta : ℝ) (gradient : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact (nativeSourceColumn n theta gradient) force p F=
      nativeReaderContact n theta gradient force p F-nativeDeviationReaderContact n theta force p F := by
  have source:=(nativeReader_generated n theta gradient force p F).sub
    (noetherReader_generated (nativeSourceColumn n theta gradient) force p F)
  have same : (fun r : ℝ=>nativeDeviationReader n theta p F (r • force))=ᶠ[𝓝 0]
      fun r=>nativeReader n theta gradient p F (r • force)-noetherReader (nativeSourceColumn n theta gradient) p F (r • force) :=
    (deviation_reader_germ n theta gradient p F).comp_tendsto
      (by simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto)
  have generated:=source.congr_of_eventuallyEq same
  have contact:=(native_deviation_reader_generated n theta force p F).unique generated
  rw [contact]
  abel

end LowEnergy.GaussComposite.ActualDressedLockedWard
