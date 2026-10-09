import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeFormJets

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceActionJets
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

open GaussCoframeCore GaussCoframeForm

def rowSample (c : SourceCoordinateSlice→ℝ) (f g : QuantumTest) (z x : SourceCoordinateSlice) : ℂ :=
  pairSample x (f z) ((c x:ℂ) • g z)

def rowForm (c : SourceCoordinateSlice→ℝ) (f g : QuantumTest) (h : SourceCoordinateSlice) (r : ℝ) : ℂ :=
  ∫ z,rowSample c f g z (z+r • h) ∂GaussHistoryHilbert.configurationMeasure

theorem rowSample_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : SourceCoordinateSlice→ℝ) (hc : ∀x : physicalChart,ContDiffAt ℝ ∞ c x.val)
    (f g : QuantumTest) (X Z : E→SourceCoordinateSlice) (w : E)
    (hx : X w∈physicalChart) (hX : ContDiffAt ℝ ∞ X w) (hZ : ContDiffAt ℝ ∞ Z w) :
    ContDiffAt ℝ ∞ (fun u=>rowSample c f g (Z u) (X u)) w :=
  pairSample_param X _ _ w hx hX (f.contDiff.contDiffAt.comp w hZ)
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp w ((hc ⟨X w,hx⟩).comp w hX)).smul
      (g.contDiff.contDiffAt.comp w hZ))

theorem rowSample_zero_outside (c : SourceCoordinateSlice→ℝ) (f g : QuantumTest)
    (z x : SourceCoordinateSlice) (outside : z∉tsupport f) : rowSample c f g z x=0 := by
  rw [rowSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

theorem row_form_source (c : SourceCoordinateSlice→ℝ)
    (hc : ∀x : physicalChart,ContDiffAt ℝ ∞ c x.val) (f g : QuantumTest) (h : SourceCoordinateSlice) :
    rowForm c f g h 0=sourcePair f (GaussNativeForm.multiply c hc g) := by
  rw [rowForm,sourcePair_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [zero_smul,add_zero,rowSample]
    rw [←pairSample_source]
    rfl

def mixedForm (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (f g : QuantumTest) (h : SourceCoordinateSlice) (r : ℝ) : ℂ :=
  (1/2:ℂ)*(rowForm c (GaussCoframeSpin.current a f) (GaussCoframeCore.momentum i g) h r+
    rowForm c (GaussCoframeCore.momentum i f) (GaussCoframeSpin.current a g) h r)

def coframeForm (f g : QuantumTest) (h : SourceCoordinateSlice) (r : ℝ) : ℂ :=
  (∑ i : Fin 6,∑ j : Fin 6,rowForm (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeCore.momentum i f) (GaussCoframeCore.momentum j g) h r)+
  (mixedForm 1 5 (currentCoefficient 0) f g h r+
   mixedForm 3 3 (currentCoefficient 1) f g h r+
   mixedForm 3 4 (fun z=>-currentCoefficient 0 z) f g h r+
   mixedForm 4 3 (currentCoefficient 2) f g h r)+
  (∑ a : Fin 7,(spinWeight a:ℂ)*rowForm inverseVolume (GaussCoframeSpin.current a f)
    (GaussCoframeSpin.current a g) h r)+
  (1/2:ℂ)*(rowForm numberCoefficient (number f) g h r+rowForm numberCoefficient f (number g) h r)+
  rowForm volumePotential f g h r

theorem sourcePair_add (f g h : QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]

theorem sourcePair_smul (c : ℂ) (f g : QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

theorem sourcePair_sum {ι : Type*} [Fintype ι] (f : QuantumTest) (g : ι→QuantumTest) :
    sourcePair f (∑ i,g i)=∑ i,sourcePair f (g i) := by
  simp only [sourcePair,map_sum,inner_sum]

theorem mixed_form_source (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (hc : ∀x : physicalChart,ContDiffAt ℝ ∞ c x.val) (f g : QuantumTest) (h : SourceCoordinateSlice) :
    mixedForm i a c f g h 0=sourcePair f (mixed i a c hc g) := by
  rw [mixedForm,row_form_source c hc,row_form_source c hc]
  simp only [mixed,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,
    sourcePair_smul,sourcePair_add]
  rw [GaussCoframeSpin.current_pair,GaussCoframeKinetic.adjoint_pair]

theorem coframe_form_source (f g : QuantumTest) (h : SourceCoordinateSlice) :
    coframeForm f g h 0=sourcePair f (coframeAction g) := by
  have kinetic i j : rowForm (GaussCoframeKinetic.coefficient i j)
      (GaussCoframeCore.momentum i f) (GaussCoframeCore.momentum j g) h 0=
      sourcePair f (GaussCoframeKinetic.term i j g) := by
    rw [row_form_source _ (GaussCoframeKinetic.coefficient_smooth i j)]
    exact (GaussCoframeKinetic.adjoint_pair i f _).symm
  have spin a : (spinWeight a:ℂ)*rowForm inverseVolume (GaussCoframeSpin.current a f)
      (GaussCoframeSpin.current a g) h 0=sourcePair f (spinSquare a g) := by
    rw [row_form_source _ inverseVolume_smooth]
    simp only [spinSquare,LinearMap.smul_apply,LinearMap.comp_apply,sourcePair_smul]
    rw [GaussCoframeSpin.current_pair]
  have shifted : (1/2:ℂ)*(rowForm numberCoefficient (number f) g h 0+
      rowForm numberCoefficient f (number g) h 0)=sourcePair f (numberShift g) := by
    rw [row_form_source _ numberCoefficient_smooth,row_form_source _ numberCoefficient_smooth]
    simp only [numberShift,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,
      sourcePair_smul,sourcePair_add]
    rw [number_pair]
  unfold coframeForm
  simp_rw [kinetic,spin,mixed_form_source _ _ _ (currentCoefficient_smooth _),
    mixed_form_source 3 4 _ (fun z=>(currentCoefficient_smooth 0 z).neg)]
  rw [shifted,row_form_source _ volumePotential_smooth]
  simp only [coframeAction,currentAction,GaussCoframeKinetic.kinetic,LinearMap.add_apply,
    LinearMap.sum_apply,sourcePair_add,sourcePair_sum]

open PreparationVacuumActionDecomposition

def fiberSample (A : SourceCoordinateSlice→FiberMap) (f g : QuantumTest) (z x : SourceCoordinateSlice) : ℂ :=
  pairSample x (f z) (A x (g z))

def fiberForm (A : SourceCoordinateSlice→FiberMap) (f g : QuantumTest) (h : SourceCoordinateSlice) (r : ℝ) : ℂ :=
  ∫ z,fiberSample A f g z (z+r • h) ∂GaussHistoryHilbert.configurationMeasure

theorem fiberSample_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : SourceCoordinateSlice→FiberMap) (hA : ∀x : physicalChart,ContDiffAt ℝ ∞ A x.val)
    (f g : QuantumTest) (X Z : E→SourceCoordinateSlice) (w : E)
    (hx : X w∈physicalChart) (hX : ContDiffAt ℝ ∞ X w) (hZ : ContDiffAt ℝ ∞ Z w) :
    ContDiffAt ℝ ∞ (fun u=>fiberSample A f g (Z u) (X u)) w := by
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have ha:=R.contDiff.contDiffAt.comp w ((hA ⟨X w,hx⟩).comp w hX)
  exact pairSample_param X _ _ w hx hX (f.contDiff.contDiffAt.comp w hZ)
    (ha.clm_apply (g.contDiff.contDiffAt.comp w hZ))

theorem fiberSample_zero_outside (A : SourceCoordinateSlice→FiberMap) (f g : QuantumTest)
    (z x : SourceCoordinateSlice) (outside : z∉tsupport f) : fiberSample A f g z x=0 := by
  rw [fiberSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

def retainedCoefficient (x : SourceCoordinateSlice) : FiberMap :=
  actualFiber 0 x-GaussYukawaCoefficient.sourceMap (scalarField x)-
    ∑ i : Fin 3,∑ b : Fin 3,quantized (GaussMatterCore.localMatrix i b x)

theorem retainedCoefficient_smooth (x : physicalChart) : ContDiffAt ℝ ∞ retainedCoefficient x.val :=
  ((actualFiber_smooth 0 x).sub
    (GaussYukawaCoefficient.sourceMap.contDiff.contDiffAt.comp x.val scalarField_smooth.contDiffAt)).sub
      (ContDiffAt.sum fun i _=>ContDiffAt.sum fun b _=>GaussMatterCore.local_smooth i b x)

theorem retainedCoefficient_source (x : physicalChart) :
    retainedCoefficient x.val=quantized (SourceRealScalarFock.branches (retainedConnection x.val)) := by
  rw [retainedCoefficient,actualFiber_components]
  simp only [CanonicalGradedSpatial.sourceMomentum,momentumMatrix_zero,quantized_zero]
  abel

theorem retainedCoefficient_core (g : QuantumTest) (z : SourceCoordinateSlice) :
    retainedCoefficient z (g z)=retainedCore g z := by
  simp only [retainedCoefficient,sub_apply,sum_apply,retainedCore,LinearMap.sub_apply,
    GaussMatterCore.matterAction,LinearMap.sum_apply]
  rfl

theorem actual_fiber_form_source (p : PhysicalMomentum) (f g : QuantumTest) (h : SourceCoordinateSlice) :
    fiberForm (actualFiber p) f g h 0=sourcePair f (actualCore p g) := by
  rw [fiberForm,sourcePair_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [zero_smul,add_zero,fiberSample]
    rw [←pairSample_source]
    rfl

theorem retained_form_source (f g : QuantumTest) (h : SourceCoordinateSlice) :
    fiberForm retainedCoefficient f g h 0=sourcePair f (retainedCore g) := by
  rw [fiberForm,sourcePair_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [zero_smul,add_zero,fiberSample,retainedCoefficient_core]
    exact pairSample_source _ _ z

end LowEnergy.PreparationVacuumSourceActionJets
