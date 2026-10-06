import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawJointFieldSource

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumRawJointFeedback
open GaussCoreHilbert GaussHistoryHilbert GaussCoreDifferential CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumGradedTransport PreparationVacuumJointFieldResponse PreparationVacuumFullFieldRiesz
open PreparationVacuumUncutYukawa PreparationVacuumHalfDensityFiber PreparationVacuumActionFieldLift
open PreparationVacuumSourceActionJets
open Filter Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace BigOperators
abbrev Index:=GaussUnitaryHistory.Index
abbrev Op:=H→L[ℂ] H
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointCurrent rawForm rawContactForm

/-- Both frame labels remain free: raw readers retain grade-changing matrix entries. -/
def rawReader (reader : Field289) (p : PhysicalMomentum) (F : Index) (h : Field289) : Op:=
  finiteRiesz F (fun i j=>rawForm reader p (frameTest F i) (frameTest F j) h)

def rawReaderContact (reader force : Field289) (p : PhysicalMomentum) (F : Index) : Op:=
  finiteRiesz F (fun i j=>rawContactForm reader force p (frameTest F i) (frameTest F j))

theorem rawReader_C2 (reader : Field289) (p : PhysicalMomentum) (F : Index) :
    ContDiffAt ℝ 2 (rawReader reader p F) 0 :=by
  apply ContDiffAt.sum;intro i _
  apply ContDiffAt.sum;intro j _
  exact (rawForm_C2 reader p (frameTest F i) (frameTest F j)).smul contDiffAt_const

theorem rawReader_direction (reader force : Field289) (p : PhysicalMomentum) (F : Index) :
    HasDerivAt (fun r : ℝ=>rawReader reader p F (r • force)) (rawReaderContact reader force p F) 0 :=by
  apply HasDerivAt.fun_sum;intro i _
  apply HasDerivAt.fun_sum;intro j _
  exact (rawForm_direction reader force p (frameTest F i) (frameTest F j)).smul_const
    (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))

theorem rawReader_pair (reader : Field289) (p : PhysicalMomentum) (F : Index) (h : Field289) (x y : H) :
    inner ℂ x (rawReader reader p F h y)=
      ∑i : FrameIndex F,∑j : FrameIndex F,star (inner ℂ (frameVector F i) x)*
        rawForm reader p (frameTest F i) (frameTest F j) h*inner ℂ (frameVector F j) y :=
by
  have pairing:=finiteRiesz_pair F (fun i j=>rawForm reader p (frameTest F i) (frameTest F j) h) x y
  change inner ℂ x (finiteRiesz F (fun i j=>rawForm reader p (frameTest F i) (frameTest F j) h) y)=_
  exact pairing

theorem rawForm_original (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm reader p a b 0=∫z,pairSample z (a z) (rawStateFiber reader p (sourceState z) (b z))
      ∂configurationMeasure :=by
  simp only [rawForm,rawSample,rawFiber_zero]

theorem rawContactForm_original (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    rawContactForm reader force p a b=∫z,pairSample z (a z) (rawContactFiber reader force p z (b z))
      ∂configurationMeasure :=by
  unfold rawContactForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall;intro z
  by_cases inside : z∈tsupport a
  · rw [rawContactSample,rawContact_zero reader force p ⟨z,a.tsupport_subset inside⟩]
  · simp only [rawContactSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

/-- Spectral subtraction is absent from the physical time generator. -/
def physicalTime (p : PhysicalMomentum) (F : Index) (age : ℝ) (h : Field289) : Op:=
  SourceFiniteUnitary.time (jointGenerator p F 0 h) age

def timeSlope (force : Field289) (p : PhysicalMomentum) (F : Index) (age : ℝ) : Op:=
  CanonicalGradedVariation.variation (jointGenerator p F 0 0) (jointCurrent p F 0 0 force) age

attribute [local irreducible] physicalTime timeSlope

theorem physicalTime_direction (force : Field289) (p : PhysicalMomentum) (F : Index) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>physicalTime p F age (r • force)) (timeSlope force p F age) 0 :=by
  have inner:=(jointGenerator_ray_derivative force p F 0).self_of_nhds
  simp only [zero_smul] at inner
  have h:=PreparationVacuumActionDecomposition.nonlinear_time_derivative
    (jointGenerator p F 0 0) (jointCurrent p F 0 0 force)
    (fun r : ℝ=>jointGenerator p F 0 (r • force)-jointGenerator p F 0 0)
    (by simp only [zero_smul,sub_self]) (inner.sub_const _) age
  simpa only [add_sub_cancel,physicalTime,timeSlope] using h

theorem physicalTime_source (force : Field289) (p : PhysicalMomentum) (F : Index) (age : ℝ) :
    (fun r : ℝ=>physicalTime p F age (r • force))=ᶠ[𝓝 0]
      (fun r=>SourceFiniteUnitary.time (transportedCompression force p F r+
        uncutOperator force (PreparationVacuumYukawaTransport.finiteRetainer p F) r) age) :=by
  filter_upwards [jointGenerator_ray force p F 0] with r hr
  unfold physicalTime
  change SourceFiniteUnitary.time (jointGenerator p F 0 (r • force)) age=_
  rw [hr]
  change SourceFiniteUnitary.time (transportedCompression force p F r+
    uncutOperator force (PreparationVacuumYukawaTransport.finiteRetainer p F) r-(0:ℂ) • (1:Op)) age=_
  have zero : (0:ℂ) • (1:Op)=0:=by
    apply ContinuousLinearMap.ext;intro x
    exact zero_smul ℂ x
  rw [zero,sub_zero]

theorem physicalTime_inverse (p : PhysicalMomentum) (F : Index) (age : ℝ) (h : Field289) :
    physicalTime p F (-age) h*physicalTime p F age h=1 ∧
    physicalTime p F age h*physicalTime p F (-age) h=1 :=by
  constructor
  · rw [physicalTime,physicalTime,←SourceFiniteUnitary.time_add,neg_add_cancel,SourceFiniteUnitary.time_zero]
  · rw [physicalTime,physicalTime,←SourceFiniteUnitary.time_add,add_neg_cancel,SourceFiniteUnitary.time_zero]

theorem physicalTime_initial (p : PhysicalMomentum) (F : Index) (h : Field289) : physicalTime p F 0 h=1 :=by
  unfold physicalTime
  exact SourceFiniteUnitary.time_zero _

theorem timeSlope_initial (force : Field289) (p : PhysicalMomentum) (F : Index) : timeSlope force p F 0=0 :=by
  simp only [timeSlope,CanonicalGradedVariation.variation,CanonicalGradedVariation.variationBetween,
    intervalIntegral.integral_same]

end LowEnergy.PreparationVacuumRawJointFeedback
