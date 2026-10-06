import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldCoframeTangent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldConstraintResponse
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

open GaussNativePotential GaussNativeMatter
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair PointwiseDiracSpinConnectionLift

open GaussCoreHilbert GaussCoreDifferential
open PreparationVacuumNonlinearFieldCurve
open SU7ExteriorBreakingYukawa GaussNativeEnergy StageNineCoframeLocalDifferentiability
open StageNineP286GaugeConnectionVariationDensity

open SourceQuantumScalarChart
open GaussLiveMomentum GaussDensityCore GaussFockPair GaussMomentumAdjoint
open MeasureTheory
open scoped Distributions InnerProductSpace

open PreparationVacuumSourceActionJets StageNineCoframeGravityGaugeRegularity

open StageNineLorentzConnectionVariation ProofFreeRicherAnholonomicSource
open PointwiseLorentzianCoframeJet

open PreparationVacuumActionDecomposition PreparationVacuumSourceActionJets
open GaussCoframeForm GaussUnitaryHistory GaussDiagonalHistory
open GaussComposite GaussComposite.SourceGraph

def fieldCoordinateCurve (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  z+r • fieldVector f z

theorem field_curve_smooth (f : Field289) (r : ℝ) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) (r,z.val) :=
  contDiffAt_snd.add (contDiffAt_fst.smul ((fieldVector_smooth f z).comp (r,z.val) contDiffAt_snd))

theorem field_tube_exists (f : Field289) (test : QuantumTest) :
    ∃R : ℝ,0<R ∧ ∀r z,|r|  ≤  R  →  z∈tsupport test  →  fieldCoordinateCurve f r z∈physicalChart := by
  let U : Set Parameter:={u | u.2∈physicalChart ∧ fieldCoordinateCurve f u.1 u.2∈physicalChart}
  have op : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro u hu
    have start:=continuous_snd.continuousAt.preimage_mem_nhds (physicalChart.isOpen.mem_nhds hu.1)
    have finish:=(field_curve_smooth f u.1 ⟨u.2,hu.1⟩).continuousAt.preimage_mem_nhds
      (physicalChart.isOpen.mem_nhds hu.2)
    exact Filter.inter_mem start finish
  have base : ({0}:Set ℝ) ×ˢ tsupport test⊆U := by
    rintro ⟨r,z⟩ ⟨hr,hz⟩
    have hz0 : r=0:=hr
    subst r
    change z∈physicalChart ∧ z+(0:ℝ) • fieldVector f z∈physicalChart
    rw [zero_smul,add_zero]
    constructor <;> convert! test.tsupport_subset hz using 1
  obtain ⟨u,v,hu,_hv,hzero,hcover,hproduct⟩:=generalized_tube_lemma (isCompact_singleton (x:=(0:ℝ)))
    test.hasCompactSupport op base
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp (hu.mem_nhds (hzero (by rfl)))
  refine ⟨e/2,by positivity,?_⟩
  intro r z hr hz
  have member : (r,z)∈u ×ˢ v := by
    refine ⟨hball ?_,hcover hz⟩
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact hr.trans_lt (by linarith)
  exact (hproduct member).2

def fieldRadius (f : Field289) (test : QuantumTest) : ℝ:=(field_tube_exists f test).choose

theorem fieldRadius_positive (f : Field289) (test : QuantumTest) : 0<fieldRadius f test:=
  (field_tube_exists f test).choose_spec.1

theorem fieldRadius_chart (f : Field289) (test : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice)
    (small : |r|  ≤  fieldRadius f test) (inside : z∈tsupport test) : fieldCoordinateCurve f r z∈physicalChart:=
  (field_tube_exists f test).choose_spec.2 r z small inside

def fieldSampleJets (S : SourceCoordinateSlice  →  SourceCoordinateSlice  →  ℂ) (f : Field289) (test : QuantumTest)
    (smooth : ∀r z,z∈physicalChart  →  fieldCoordinateCurve f r z∈physicalChart  →
      ContDiffAt ℝ ∞ (fun u : Parameter=>S u.2 (fieldCoordinateCurve f u.1 u.2)) (r,z))
    (zero : ∀z x,z∉tsupport test  →  S z x=0) :
    TwoJets (fun r=>∫ z,S z (fieldCoordinateCurve f r z) ∂GaussHistoryHilbert.configurationMeasure) := by
  let F : Parameter  →  ℂ:=fun u=>S u.2 (fieldCoordinateCurve f u.1 u.2)
  have full (r : ℝ) (z : SourceCoordinateSlice) (small : |r|<fieldRadius f test) : ContDiffAt ℝ ∞ F (r,z) := by
    by_cases inside : z∈tsupport test
    · exact smooth r z (test.tsupport_subset inside) (fieldRadius_chart f test r z small.le inside)
    · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (isClosed_tsupport test |>.isOpen_compl.mem_nhds inside)] with u hu
      exact zero u.2 (fieldCoordinateCurve f u.1 u.2) hu
  exact integralJets F (tsupport test) test.hasCompactSupport (fieldRadius f test) (fieldRadius_positive f test)
    full (fun r z hz=>zero z (fieldCoordinateCurve f r z) hz)

def nativeFieldForm (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ:=
  ∫ z,nativeSample a b z (fieldCoordinateCurve f r z) ∂GaussHistoryHilbert.configurationMeasure

def nativeFieldJets (f : Field289) (a b : QuantumTest) : TwoJets (nativeFieldForm f a b) :=
  fieldSampleJets (nativeSample a b) f a
    (fun r z hz hx=>nativeSample_param a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (nativeSample_zero_outside a b)

def rowFieldForm (f : Field289) (c : SourceCoordinateSlice  →  ℝ) (a b : QuantumTest) (r : ℝ) : ℂ:=
  ∫ z,rowSample c a b z (fieldCoordinateCurve f r z) ∂GaussHistoryHilbert.configurationMeasure

def rowFieldJets (f : Field289) (c : SourceCoordinateSlice  →  ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (a b : QuantumTest) : TwoJets (rowFieldForm f c a b) :=
  fieldSampleJets (rowSample c a b) f a
    (fun r z hz hx=>rowSample_param c hc a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (rowSample_zero_outside c a b)

def fiberFieldForm (f : Field289) (A : SourceCoordinateSlice  →  FiberMap) (a b : QuantumTest) (r : ℝ) : ℂ:=
  ∫ z,fiberSample A a b z (fieldCoordinateCurve f r z) ∂GaussHistoryHilbert.configurationMeasure

def fiberFieldJets (f : Field289) (A : SourceCoordinateSlice  →  FiberMap)
    (hA : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) (a b : QuantumTest) : TwoJets (fiberFieldForm f A a b) :=
  fieldSampleJets (fiberSample A a b) f a
    (fun r z hz hx=>fiberSample_param A hA a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (fiberSample_zero_outside A a b)

def mixedFieldForm (f : Field289) (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice  →  ℝ)
    (a b : QuantumTest) (r : ℝ) : ℂ:=
  (1/2:ℂ)*(rowFieldForm f c (GaussCoframeSpin.current k a) (GaussCoframeCore.momentum i b) r+
    rowFieldForm f c (GaussCoframeCore.momentum i a) (GaussCoframeSpin.current k b) r)

def mixedFieldJets (f : Field289) (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice  →  ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (a b : QuantumTest) : TwoJets (mixedFieldForm f i k c a b) :=
  TwoJets.scale (1/2:ℂ) ((rowFieldJets f c hc (GaussCoframeSpin.current k a) (GaussCoframeCore.momentum i b)).add
    (rowFieldJets f c hc (GaussCoframeCore.momentum i a) (GaussCoframeSpin.current k b)))

def coframeFieldForm (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ:=
  (∑ i : Fin 6,∑ j : Fin 6,rowFieldForm f (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeCore.momentum i a) (GaussCoframeCore.momentum j b) r)+
  (mixedFieldForm f 1 5 (currentCoefficient 0) a b r+mixedFieldForm f 3 3 (currentCoefficient 1) a b r+
   mixedFieldForm f 3 4 (fun z=>-currentCoefficient 0 z) a b r+mixedFieldForm f 4 3 (currentCoefficient 2) a b r)+
  (∑ k : Fin 7,(spinWeight k:ℂ)*rowFieldForm f inverseVolume (GaussCoframeSpin.current k a) (GaussCoframeSpin.current k b) r)+
  (1/2:ℂ)*(rowFieldForm f numberCoefficient (number a) b r+rowFieldForm f numberCoefficient a (number b) r)+
  rowFieldForm f volumePotential a b r

def coframeFieldJets (f : Field289) (a b : QuantumTest) : TwoJets (coframeFieldForm f a b) := by
  let kin:=sumJets fun i : Fin 6=>sumJets fun j : Fin 6=>rowFieldJets f (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j) (GaussCoframeCore.momentum i a) (GaussCoframeCore.momentum j b)
  let cur:=(((mixedFieldJets f 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0) a b).add
    (mixedFieldJets f 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1) a b)).add
    (mixedFieldJets f 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg) a b)).add
    (mixedFieldJets f 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2) a b)
  let spin:=sumJets fun k : Fin 7=>TwoJets.scale (spinWeight k:ℂ) (rowFieldJets f inverseVolume inverseVolume_smooth
    (GaussCoframeSpin.current k a) (GaussCoframeSpin.current k b))
  let num:=TwoJets.scale (1/2:ℂ) ((rowFieldJets f numberCoefficient numberCoefficient_smooth (number a) b).add
    (rowFieldJets f numberCoefficient numberCoefficient_smooth a (number b)))
  exact (((kin.add cur).add spin).add num).add (rowFieldJets f volumePotential volumePotential_smooth a b)

def fieldForm (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (r : ℝ) : ℂ:=
  nativeFieldForm f a b r+coframeFieldForm f a b r+fiberFieldForm f (actualFiber p) a b r-
    fiberFieldForm f retainedCoefficient a b r

def fieldJets (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : TwoJets (fieldForm f p a b) :=
  (((nativeFieldJets f a b).add (coframeFieldJets f a b)).add
    (fiberFieldJets f (actualFiber p) (actualFiber_smooth p) a b)).sub
    (fiberFieldJets f retainedCoefficient retainedCoefficient_smooth a b)

theorem fieldForm_source (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    fieldForm f p a b 0=sourcePair a ((CanonicalPhysicalSpatial.physicalAction p+GaussYukawaOperator.originalAction) b) := by
  have same : fieldForm f p a b 0=totalForm p a b 0 0 := by
    simp only [fieldForm,totalForm,nativeFieldForm,nativeForm,coframeFieldForm,coframeForm,
      mixedFieldForm,mixedForm,rowFieldForm,rowForm,fiberFieldForm,fiberForm,fieldCoordinateCurve,zero_smul,add_zero]
  exact same.trans (total_form_source p a b 0)

theorem fieldForm_two_jets (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fieldForm f p a b) ((fieldJets f p a b).first 0) 0 ∧
      HasDerivAt (deriv (fieldForm f p a b)) (fieldJets f p a b).second 0 := (fieldJets f p a b).actual

-- The complementary original channels remain attached to the same field direction.
structure RemainingFieldChannels where
  time : Fin 4  →  ℝ
  frame : LorentzianCoframe
  gaugeOrbit : NativeLie
  temporalGauge : NativeLie
  lorentz : LorentzBivectorOneForm
  primal : Fin 2  →  Fin 4  →  Fin 3  →  ℝ
  dual : Fin 2  →  Fin 4  →  Fin 3  →  ℝ
  gravityB : Fin 6  →  Fin 6  →  ℝ
  multiplier : Fin 6  →  Fin 6  →  ℝ
  gaugeB : Fin 6  →  Fin 12  →  ℝ

def remainingChannels (f : Field289) (z : SourceCoordinateSlice) : RemainingFieldChannels where
  time:=coframeTimeDirection f z
  frame:=lorentzPart (normalizedCoframe f z)
  gaugeOrbit:=gaugeOrbitParameter f z
  temporalGauge:=fieldGauge f 0
  lorentz:=fieldLorentz f
  primal:=fieldPrimal f
  dual:=fieldDual f
  gravityB:=fieldGravityB f
  multiplier:=fieldMultiplier f
  gaugeB:=fieldGaugeB f

-- Exact literal rows of the already-generated ordinary source curvature reader.
-- The paired real/imaginary inputs retain every original 289-field slot.
def originalReader36 (p : Fin 4  →  ℂ) (row : Fin 36) (column : Fin 289) : ℂ:=
  match row.val,column.val with
  | 0,15 => ((-3)*(p 1))
  | 0,16 => ((-3)*(p 1))
  | 0,27 => (3*(p 0))
  | 0,28 => (3*(p 0))
  | 1,15 => ((-3)*(p 2))
  | 1,16 => ((-3)*(p 2))
  | 1,39 => (3*(p 0))
  | 1,40 => (3*(p 0))
  | 2,15 => ((-3)*(p 3))
  | 2,16 => ((-3)*(p 3))
  | 2,51 => (3*(p 0))
  | 2,52 => (3*(p 0))
  | 3,39 => ((-3)*(p 3))
  | 3,40 => ((-3)*(p 3))
  | 3,51 => (3*(p 2))
  | 3,52 => (3*(p 2))
  | 4,27 => (3*(p 3))
  | 4,28 => (3*(p 3))
  | 4,51 => ((-3)*(p 1))
  | 4,52 => ((-3)*(p 1))
  | 5,27 => ((-3)*(p 2))
  | 5,28 => ((-3)*(p 2))
  | 5,39 => (3*(p 1))
  | 5,40 => (3*(p 1))
  | 6,17 => ((-2)*(p 1))
  | 6,29 => (2*(p 0))
  | 7,17 => ((-2)*(p 2))
  | 7,41 => (2*(p 0))
  | 8,17 => ((-2)*(p 3))
  | 8,53 => (2*(p 0))
  | 9,41 => ((-2)*(p 3))
  | 9,53 => (2*(p 2))
  | 10,29 => (2*(p 3))
  | 10,53 => ((-2)*(p 1))
  | 11,29 => ((-2)*(p 2))
  | 11,41 => (2*(p 1))
  | 12,18 => ((-2)*(p 1))
  | 12,30 => (2*(p 0))
  | 13,18 => ((-2)*(p 2))
  | 13,42 => (2*(p 0))
  | 14,18 => ((-2)*(p 3))
  | 14,54 => (2*(p 0))
  | 15,42 => ((-2)*(p 3))
  | 15,54 => (2*(p 2))
  | 16,30 => (2*(p 3))
  | 16,54 => ((-2)*(p 1))
  | 17,30 => ((-2)*(p 2))
  | 17,42 => (2*(p 1))
  | 18,19 => ((-2)*(p 1))
  | 18,31 => (2*(p 0))
  | 19,19 => ((-2)*(p 2))
  | 19,43 => (2*(p 0))
  | 20,19 => ((-2)*(p 3))
  | 20,55 => (2*(p 0))
  | 21,43 => ((-2)*(p 3))
  | 21,55 => (2*(p 2))
  | 22,31 => (2*(p 3))
  | 22,55 => ((-2)*(p 1))
  | 23,31 => ((-2)*(p 2))
  | 23,43 => (2*(p 1))
  | 24,20 => (-(p 1))
  | 24,32 => (p 0)
  | 25,20 => (-(p 2))
  | 25,44 => (p 0)
  | 26,20 => (-(p 3))
  | 26,56 => (p 0)
  | 27,44 => (-(p 3))
  | 27,56 => (p 2)
  | 28,32 => (p 3)
  | 28,56 => (-(p 1))
  | 29,32 => (-(p 2))
  | 29,44 => (p 1)
  | 30,9 => (((-25)*(p 3))/18)
  | 30,10 => ((5*(Real.sqrt 2:ℂ))/3)
  | 30,15 => ((25*(p 2))/36)
  | 30,16 => (((-25)*(p 2))/36)
  | 30,39 => (((-25)*(p 0))/36)
  | 30,40 => ((25*(p 0))/36)
  | 30,45 => ((25*(p 0))/18)
  | 31,9 => ((5*(Real.sqrt 2:ℂ))/3)
  | 31,10 => ((25*(p 3))/18)
  | 31,15 => (((-25)*(p 1))/36)
  | 31,16 => ((25*(p 1))/36)
  | 31,27 => ((25*(p 0))/36)
  | 31,28 => (((-25)*(p 0))/36)
  | 31,46 => (((-25)*(p 0))/18)
  | 32,9 => ((25*(p 1))/18)
  | 32,10 => (((-25)*(p 2))/18)
  | 32,15 => ((5*(Real.sqrt 2:ℂ))/6)
  | 32,16 => (((-5)*(Real.sqrt 2:ℂ))/6)
  | 32,21 => (((-25)*(p 0))/18)
  | 32,34 => ((25*(p 0))/18)
  | 33,21 => (((-25)*(p 2))/18)
  | 33,27 => (((-25)*(p 3))/36)
  | 33,28 => ((25*(p 3))/36)
  | 33,33 => ((25*(p 1))/18)
  | 33,39 => ((5*(Real.sqrt 2:ℂ))/12)
  | 33,40 => (((-5)*(Real.sqrt 2:ℂ))/12)
  | 33,45 => (((-5)*(Real.sqrt 2:ℂ))/6)
  | 33,51 => ((25*(p 1))/36)
  | 33,52 => (((-25)*(p 1))/36)
  | 33,68 => (1/2)
  | 33,71 => ((-1)/2)
  | 33,85 => (1/2)
  | 33,89 => ((-1)/2)
  | 33,91 => (1/2)
  | 33,95 => ((-1)/2)
  | 34,22 => ((25*(p 2))/18)
  | 34,27 => (((-5)*(Real.sqrt 2:ℂ))/12)
  | 34,28 => ((5*(Real.sqrt 2:ℂ))/12)
  | 34,34 => (((-25)*(p 1))/18)
  | 34,39 => (((-25)*(p 3))/36)
  | 34,40 => ((25*(p 3))/36)
  | 34,46 => ((5*(Real.sqrt 2:ℂ))/6)
  | 34,51 => ((25*(p 2))/36)
  | 34,52 => (((-25)*(p 2))/36)
  | 34,64 => ((-1)/2)
  | 34,70 => (1/2)
  | 34,73 => (1/2)
  | 34,77 => (1/2)
  | 34,79 => (1/2)
  | 34,83 => (1/2)
  | 35,21 => ((5*(Real.sqrt 2:ℂ))/6)
  | 35,22 => ((25*(p 3))/18)
  | 35,33 => ((25*(p 3))/18)
  | 35,34 => (((-5)*(Real.sqrt 2:ℂ))/6)
  | 35,45 => (((-25)*(p 2))/18)
  | 35,46 => (((-25)*(p 1))/18)
  | 35,63 => (1/2)
  | 35,66 => ((-1)/2)
  | 35,86 => ((-1)/2)
  | 35,88 => ((-1)/2)
  | 35,92 => ((-1)/2)
  | 35,94 => ((-1)/2)
  | _,_=>0

def readerReal (p : Fin 4  →  ℂ) (row : Fin 36) : Field289:=fun j=>(originalReader36 p row j).re
def readerImag (p : Fin 4  →  ℂ) (row : Fin 36) : Field289:=fun j=>(originalReader36 p row j).im

theorem original_reader_complex (p : Fin 4  →  ℂ) (row : Fin 36) (j : Fin 289) :
    (readerReal p row j:ℂ)+Complex.I*(readerImag p row j:ℂ)=originalReader36 p row j := by
  simpa only [readerReal,readerImag,mul_comm] using Complex.re_add_im (originalReader36 p row j)

theorem curvature_primal_retained (p : Fin 4  →  ℂ) (z : SourceCoordinateSlice) :
    (remainingChannels (readerReal p 33) z).primal 1 0 0=1/2 := by
  change (1/2:ℂ).re=(1/2:ℝ)
  norm_num

local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

def sourceApprox (F : Index) : H  →L[ℂ] H :=
  ∑ label : NativeHistoryGrade.Label,NativeHistoryGrade.projection label*
    (FiniteCoreEvolution.coreSpan diagonal F).starProjection*NativeHistoryGrade.projection label

theorem sourceApprox_apply (F : Index) (x : H) : sourceApprox F x=
    ∑ label : NativeHistoryGrade.Label,NativeHistoryGrade.projection label
      ((FiniteCoreEvolution.coreSpan diagonal F).starProjection (NativeHistoryGrade.projection label x)) := by
  simp only [sourceApprox,sum_apply,mul_apply_eq_comp]

theorem sourceApprox_mem_core (F : Index) (x : H) : sourceApprox F x∈Core := by
  rw [sourceApprox_apply]
  apply Submodule.sum_mem
  intro label _
  let y : Core:=⟨((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto
    (NativeHistoryGrade.projection label x)).val,FiniteCoreEvolution.coreSpan_le diagonal F
      ((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto (NativeHistoryGrade.projection label x)).property⟩
  exact GaussDiagonalGrade.stable label y

theorem sourceApprox_blocks (F : Index) (label : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection label) (sourceApprox F) := by
  have left : NativeHistoryGrade.projection label*sourceApprox F=
      NativeHistoryGrade.projection label*(FiniteCoreEvolution.coreSpan diagonal F).starProjection*
        NativeHistoryGrade.projection label := by
    simp only [sourceApprox,Finset.mul_sum,←mul_assoc]
    simp [NativeHistoryGrade.projection_product,ite_mul]
  have right : sourceApprox F*NativeHistoryGrade.projection label=
      NativeHistoryGrade.projection label*(FiniteCoreEvolution.coreSpan diagonal F).starProjection*
        NativeHistoryGrade.projection label := by
    simp only [sourceApprox,Finset.sum_mul,mul_assoc]
    simp [NativeHistoryGrade.projection_product,mul_ite]
  exact left.trans right.symm

def sourceCoreApprox (F : Index) (x : H) : Core:=⟨sourceApprox F x,sourceApprox_mem_core F x⟩
def sourceTestApprox (F : Index) (x : H) : QuantumTest:=coreEquiv.symm (sourceCoreApprox F x)

theorem sourceTestApprox_embed (F : Index) (x : H) : embed (sourceTestApprox F x)=sourceApprox F x :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply (sourceCoreApprox F x))

theorem same_source_approximation (x : H) :
    Tendsto (fun F : Index=>embed (sourceTestApprox F x)) sourceFilter (𝓝 x) := by
  simp only [sourceTestApprox_embed,sourceApprox_apply]
  have each (label : NativeHistoryGrade.Label) :=
    (NativeHistoryGrade.projection label).continuous.tendsto (NativeHistoryGrade.projection label x) |>.comp
      ((FiniteCoreEvolution.projection_tendsto diagonal diagonal_dense (NativeHistoryGrade.projection label x)).mono_left
        (WeakCoreEvolution.sourceFilter_cofinal diagonal))
  have total:=tendsto_finsetSum Finset.univ (fun label _=>each label)
  simp only [GaussGradedCompression.projection_idempotent] at total
  have resolution : (∑ label : NativeHistoryGrade.Label,NativeHistoryGrade.projection label x)=x := by
    rw [←sum_apply,NativeHistoryGrade.projection_resolution,one_apply_eq_self]
  rw [resolution] at total
  exact total

theorem sourceTestApprox_eventually_core (test : QuantumTest) :
    ∀ᶠ F in sourceFilter,sourceTestApprox F (embed test)=test := by
  filter_upwards [GaussGradedCompression.eventually_contains (coreEquiv test)] with F contains
  have each (label : NativeHistoryGrade.Label) :
      (FiniteCoreEvolution.coreSpan diagonal F).starProjection (NativeHistoryGrade.projection label (embed test))=
        NativeHistoryGrade.projection label (embed test) := by
    apply Submodule.starProjection_eq_self_iff.mpr
    exact FiniteCoreEvolution.mem_coreSpan diagonal F (GaussGradedCompression.piece label (coreEquiv test)) (contains label)
  have value : sourceApprox F (embed test)=embed test := by
    rw [sourceApprox_apply]
    simp_rw [each,GaussGradedCompression.projection_idempotent]
    rw [←sum_apply,NativeHistoryGrade.projection_resolution,one_apply_eq_self]
  apply coreEquiv.injective
  apply Subtype.ext
  change embed (sourceTestApprox F (embed test))=embed test
  rw [sourceTestApprox_embed,value]

theorem sourceApprox_norm_bound (F : Index) (x : H) :
    ‖sourceApprox F x‖ ≤ ∑ label : NativeHistoryGrade.Label,‖NativeHistoryGrade.projection label x‖ := by
  rw [sourceApprox_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro label _
  exact (NativeHistoryGrade.piece_bound label _).trans
    ((FiniteCoreEvolution.coreSpan diagonal F).norm_starProjection_apply_le (NativeHistoryGrade.projection label x))

def finitePreparedForm (f : Field289) (p : PhysicalMomentum) (F : Index)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) (r : ℝ) : ℂ:=
  fieldForm f p (sourceTestApprox F (completedLeg left lc ls u))
    (sourceTestApprox F (completedLeg right rc rs v)) r

theorem finite_prepared_form_jets (f : Field289) (p : PhysicalMomentum) (F : Index)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    Nonempty (TwoJets (finitePreparedForm f p F left right lc ls rc rs u v)) :=
  ⟨fieldJets f p _ _⟩

def curvatureReducedPreparedCurve (sourceMomentum : Fin 4  →  ℂ) (row : Fin 36) (p : PhysicalMomentum) (F : Index)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) (r : ℝ) : ℂ:=
  finitePreparedForm (readerReal sourceMomentum row) p F left right lc ls rc rs u v r+
    Complex.I*(finitePreparedForm (readerImag sourceMomentum row) p F left right lc ls rc rs u v r-
      finitePreparedForm (readerImag sourceMomentum row) p F left right lc ls rc rs u v 0)

theorem original_curvature_reduced_prepared_first (sourceMomentum : Fin 4  →  ℂ) (row : Fin 36) (p : PhysicalMomentum) (F : Index)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    HasDerivAt (curvatureReducedPreparedCurve sourceMomentum row p F left right lc ls rc rs u v)
      (((fieldJets (readerReal sourceMomentum row) p (sourceTestApprox F (completedLeg left lc ls u))
          (sourceTestApprox F (completedLeg right rc rs v))).first 0)+
        Complex.I*((fieldJets (readerImag sourceMomentum row) p (sourceTestApprox F (completedLeg left lc ls u))
          (sourceTestApprox F (completedLeg right rc rs v))).first 0)) 0 := by
  have realJet:=(fieldJets (readerReal sourceMomentum row) p (sourceTestApprox F (completedLeg left lc ls u))
    (sourceTestApprox F (completedLeg right rc rs v))).actual.1
  have imagJet:=(fieldJets (readerImag sourceMomentum row) p (sourceTestApprox F (completedLeg left lc ls u))
    (sourceTestApprox F (completedLeg right rc rs v))).actual.1
  exact realJet.add ((imagJet.sub_const _).const_mul Complex.I)

end LowEnergy.PreparationVacuumFieldConstraintResponse
