import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCoframeFormJets
import Mathlib.Analysis.Calculus.ParametricIntegral

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

open Set Filter

abbrev Parameter := ℝ×SourceCoordinateSlice

def parameterJet (F : Parameter → ℂ) (u : Parameter) : ℂ := fderiv ℝ F u (1,0)

theorem partial_smooth (F : Parameter → ℂ) (u : Parameter) (hF : ContDiffAt ℝ ∞ F u) :
    ContDiffAt ℝ ∞ (parameterJet F) u :=
  (hF.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem partial_parameter (F : Parameter → ℂ) (r : ℝ) (z : SourceCoordinateSlice)
    (hF : ContDiffAt ℝ ∞ F (r,z)) :
    HasDerivAt (fun t=>F (t,z)) (parameterJet F (r,z)) r :=
  hF.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r z))

theorem partial_zero_outside (F : Parameter → ℂ) (K : Set SourceCoordinateSlice) (closed : IsClosed K)
    (zero : ∀r z,z∉K → F (r,z)=0) (r : ℝ) (z : SourceCoordinateSlice) (outside : z∉K) :
    parameterJet F (r,z)=0 := by
  have localZero : F =ᶠ[𝓝 (r,z)] fun _=>0 := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (closed.isOpen_compl.mem_nhds outside)] with w hw
    exact zero w.1 w.2 hw
  rw [parameterJet,localZero.fderiv_eq,fderiv_const_apply]
  rfl

theorem slice_support (F : Parameter → ℂ) (K : Set SourceCoordinateSlice) (closed : IsClosed K)
    (zero : ∀r z,z∉K → F (r,z)=0) (r : ℝ) : tsupport (fun z=>F (r,z))⊆K := by
  apply closure_minimal _ closed
  intro z hz
  by_contra outside
  exact hz (zero r z outside)

theorem integral_partial_at (F : Parameter → ℂ) (K : Set SourceCoordinateSlice) (compact : IsCompact K)
    (R : ℝ) (positive : 0<R)
    (smooth : ∀r z,|r|<R → ContDiffAt ℝ ∞ F (r,z))
    (zero : ∀r z,z∉K → F (r,z)=0) (s : ℝ) (small : |s|<R/2) :
    HasDerivAt (fun r=>∫ z,F (r,z) ∂GaussHistoryHilbert.configurationMeasure)
      (∫ z,parameterJet F (s,z) ∂GaussHistoryHilbert.configurationMeasure) s := by
  have inner {r : ℝ} (hr : r∈Icc (-(R/2)) (R/2)) : |r|<R := by
    have h:=abs_le.mpr hr
    linarith
  have pSmooth (r : ℝ) (z : SourceCoordinateSlice) (hr : |r|<R) :=partial_smooth F (r,z) (smooth r z hr)
  have pZero:=partial_zero_outside F K compact.isClosed zero
  have integrable (r : ℝ) (hr : |r|<R) :
      Integrable (fun z=>F (r,z)) GaussHistoryHilbert.configurationMeasure :=
    (continuous_iff_continuousAt.mpr fun z=>(smooth r z hr).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).integrable_of_hasCompactSupport
      (compact.of_isClosed_subset isClosed_closure (slice_support F K compact.isClosed zero r))
  have pIntegrable (r : ℝ) (hr : |r|<R) :
      Integrable (fun z=>parameterJet F (r,z)) GaussHistoryHilbert.configurationMeasure :=
    (continuous_iff_continuousAt.mpr fun z=>(pSmooth r z hr).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).integrable_of_hasCompactSupport
      (compact.of_isClosed_subset isClosed_closure (slice_support (parameterJet F) K compact.isClosed pZero r))
  have cOn : ContinuousOn (parameterJet F) (Icc (-(R/2)) (R/2) ×ˢ K) :=
    fun u hu=>(pSmooth u.1 u.2 (inner hu.1)).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod compact).exists_bound_of_continuousOn cOn
  let majorant : SourceCoordinateSlice → ℝ:=K.indicator (fun _=>max 0 C)
  have bi : Integrable majorant GaussHistoryHilbert.configurationMeasure := by
    apply (integrable_indicator_iff compact.measurableSet).mpr
    exact integrableOn_const compact.measure_lt_top.ne
  have hs : s∈Ioo (-(R/2)) (R/2) :=abs_lt.mp small
  have domain : Ioo (-(R/2)) (R/2)∈𝓝 s :=isOpen_Ioo.mem_nhds hs
  have hbound : ∀ᵐ z ∂GaussHistoryHilbert.configurationMeasure,∀r∈Ioo (-(R/2)) (R/2),‖parameterJet F (r,z)‖ ≤ majorant z := by
    apply Filter.Eventually.of_forall
    intro z r hr
    by_cases hz : z∈K
    · change ‖parameterJet F (r,z)‖ ≤ K.indicator (fun _=>max 0 C) z
      rw [Set.indicator_of_mem hz]
      exact (hC (r,z) ⟨⟨hr.1.le,hr.2.le⟩,hz⟩).trans (le_max_right _ _)
    · change ‖parameterJet F (r,z)‖ ≤ K.indicator (fun _=>max 0 C) z
      rw [pZero r z hz,Set.indicator_of_notMem hz,norm_zero]
  have sInside : |s|<R :=inner ⟨hs.1.le,hs.2.le⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le domain
    (by filter_upwards [domain] with r hr; exact (integrable r (inner ⟨hr.1.le,hr.2.le⟩)).aestronglyMeasurable)
    (integrable s sInside) (pIntegrable s sInside).aestronglyMeasurable hbound bi
    (Filter.Eventually.of_forall fun z r hr=>partial_parameter F r z (smooth r z (inner ⟨hr.1.le,hr.2.le⟩)))).2

structure TwoJets (F : ℝ → ℂ) where
  first : ℝ → ℂ
  second : ℂ
  derivative_near : ∀ᶠr in 𝓝 0,HasDerivAt F (first r) r
  second_derivative : HasDerivAt first second 0

def integralJets (F : Parameter → ℂ) (K : Set SourceCoordinateSlice) (compact : IsCompact K)
    (R : ℝ) (positive : 0<R)
    (smooth : ∀r z,|r|<R → ContDiffAt ℝ ∞ F (r,z))
    (zero : ∀r z,z∉K → F (r,z)=0) : TwoJets (fun r=>∫ z,F (r,z) ∂GaussHistoryHilbert.configurationMeasure) where
  first r:=∫ z,parameterJet F (r,z) ∂GaussHistoryHilbert.configurationMeasure
  second:=∫ z,parameterJet (parameterJet F) (0,z) ∂GaussHistoryHilbert.configurationMeasure
  derivative_near:=by
    filter_upwards [Ioo_mem_nhds (show -(R/2)<(0:ℝ) by linarith) (show (0:ℝ)<R/2 by positivity)] with r hr
    exact integral_partial_at F K compact R positive smooth zero r (abs_lt.mpr hr)
  second_derivative:=integral_partial_at (parameterJet F) K compact R positive
    (fun r z hr=>partial_smooth F (r,z) (smooth r z hr))
    (partial_zero_outside F K compact.isClosed zero) 0 (by simp; positivity)

theorem TwoJets.actual {F : ℝ → ℂ} (jet : TwoJets F) :
    HasDerivAt F (jet.first 0) 0 ∧ HasDerivAt (deriv F) jet.second 0 := by
  have atZero:=jet.derivative_near.self_of_nhds
  refine ⟨atZero,?_⟩
  apply jet.second_derivative.congr_of_eventuallyEq
  exact jet.derivative_near.mono fun r hr=>hr.deriv

theorem coordinate_tube_exists (h : SourceCoordinateSlice) (test : QuantumTest) :
    ∃R : ℝ,0<R ∧ ∀r z,|r| ≤ R → z∈tsupport test → z+r • h∈physicalChart := by
  let U : Set Parameter:={u | u.2+u.1 • h∈physicalChart}
  have op : IsOpen U:=physicalChart.isOpen.preimage (by fun_prop)
  have base : ({0}:Set ℝ) ×ˢ tsupport test⊆U := by
    rintro ⟨r,z⟩ ⟨hr,hz⟩
    have hz0 : r=0:=hr
    subst r
    change z+(0:ℝ) • h∈physicalChart
    rw [zero_smul,add_zero]
    convert! test.tsupport_subset hz using 1
  obtain ⟨u,v,hu,_hv,hzero,hcover,hproduct⟩:=generalized_tube_lemma (isCompact_singleton (x:=(0:ℝ)))
    test.hasCompactSupport op base
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp (hu.mem_nhds (hzero (by rfl)))
  refine ⟨e/2,by positivity,?_⟩
  intro r z hr hz
  change (r,z)∈U
  apply hproduct
  refine ⟨hball ?_,hcover hz⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero]
  exact hr.trans_lt (by linarith)

def coordinateRadius (h : SourceCoordinateSlice) (test : QuantumTest) : ℝ:=
  (coordinate_tube_exists h test).choose

theorem coordinateRadius_pos (h : SourceCoordinateSlice) (test : QuantumTest) : 0<coordinateRadius h test:=
  (coordinate_tube_exists h test).choose_spec.1

theorem coordinateRadius_valid (h : SourceCoordinateSlice) (test : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice)
    (small : |r| ≤ coordinateRadius h test) (inside : z∈tsupport test) : z+r • h∈physicalChart:=
  (coordinate_tube_exists h test).choose_spec.2 r z small inside

def TwoJets.add {F G : ℝ → ℂ} (jf : TwoJets F) (jg : TwoJets G) : TwoJets (fun r=>F r+G r) where
  first r:=jf.first r+jg.first r
  second:=jf.second+jg.second
  derivative_near:=by
    filter_upwards [jf.derivative_near,jg.derivative_near] with r hf hg
    exact hf.add hg
  second_derivative:=jf.second_derivative.add jg.second_derivative

def TwoJets.sub {F G : ℝ → ℂ} (jf : TwoJets F) (jg : TwoJets G) : TwoJets (fun r=>F r-G r) where
  first r:=jf.first r-jg.first r
  second:=jf.second-jg.second
  derivative_near:=by
    filter_upwards [jf.derivative_near,jg.derivative_near] with r hf hg
    exact hf.sub hg
  second_derivative:=jf.second_derivative.sub jg.second_derivative

def TwoJets.scale {F : ℝ → ℂ} (c : ℂ) (jet : TwoJets F) : TwoJets (fun r=>c*F r) where
  first r:=c*jet.first r
  second:=c*jet.second
  derivative_near:=jet.derivative_near.mono fun _r hr=>hr.const_mul c
  second_derivative:=jet.second_derivative.const_mul c

def sumJets {ι : Type*} [Fintype ι] {F : ι → ℝ → ℂ} (J : ∀i,TwoJets (F i)) :
    TwoJets (fun r=>∑ i,F i r) where
  first r:=∑ i,(J i).first r
  second:=∑ i,(J i).second
  derivative_near:=by
    have e : ∀ᶠr in 𝓝 (0:ℝ),∀i,HasDerivAt (F i) ((J i).first r) r :=
      Filter.eventually_all.mpr (fun i=>(J i).derivative_near)
    filter_upwards [e] with r hr
    exact HasDerivAt.fun_sum (fun i _=>hr i)
  second_derivative:=HasDerivAt.fun_sum (fun i _=>(J i).second_derivative)

def sampleFamily (S : SourceCoordinateSlice → SourceCoordinateSlice → ℂ) (h : SourceCoordinateSlice)
    (u : Parameter) : ℂ:=S u.2 (u.2+u.1 • h)

def sourceSampleJets (S : SourceCoordinateSlice → SourceCoordinateSlice → ℂ) (test : QuantumTest)
    (h : SourceCoordinateSlice)
    (smooth : ∀r z,z+r • h∈physicalChart → ContDiffAt ℝ ∞ (sampleFamily S h) (r,z))
    (zero : ∀z x,z∉tsupport test → S z x=0) :
    TwoJets (fun r=>∫ z,S z (z+r • h) ∂GaussHistoryHilbert.configurationMeasure) := by
  let R:=coordinateRadius h test
  have full (r : ℝ) (z : SourceCoordinateSlice) (small : |r|<R) :
      ContDiffAt ℝ ∞ (sampleFamily S h) (r,z) := by
    by_cases inside : z∈tsupport test
    · exact smooth r z (coordinateRadius_valid h test r z small.le inside)
    · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (isClosed_tsupport test |>.isOpen_compl.mem_nhds inside)] with u hu
      exact zero u.2 (u.2+u.1 • h) hu
  exact integralJets (sampleFamily S h) (tsupport test) test.hasCompactSupport R (coordinateRadius_pos h test)
    full (fun r z hz=>zero z (z+r • h) hz)

def nativeForm (f g : QuantumTest) (h : SourceCoordinateSlice) (r : ℝ) : ℂ:=
  ∫ z,nativeSample f g z (z+r • h) ∂GaussHistoryHilbert.configurationMeasure

def nativeJets (f g : QuantumTest) (h : SourceCoordinateSlice) : TwoJets (nativeForm f g h) :=
  sourceSampleJets (nativeSample f g) f h
    (fun r z hx=>nativeSample_param f g (fun u : Parameter=>u.2+u.1 • h) Prod.snd (r,z) hx (by fun_prop) contDiffAt_snd)
    (nativeSample_zero_outside f g)

def rowJets (c : SourceCoordinateSlice → ℝ) (hc : ∀x : physicalChart,ContDiffAt ℝ ∞ c x.val)
    (f g : QuantumTest) (h : SourceCoordinateSlice) : TwoJets (rowForm c f g h) :=
  sourceSampleJets (rowSample c f g) f h
    (fun r z hx=>rowSample_param c hc f g (fun u : Parameter=>u.2+u.1 • h) Prod.snd (r,z) hx (by fun_prop) contDiffAt_snd)
    (rowSample_zero_outside c f g)

def fiberJets (A : SourceCoordinateSlice → FiberMap) (hA : ∀x : physicalChart,ContDiffAt ℝ ∞ A x.val)
    (f g : QuantumTest) (h : SourceCoordinateSlice) : TwoJets (fiberForm A f g h) :=
  sourceSampleJets (fiberSample A f g) f h
    (fun r z hx=>fiberSample_param A hA f g (fun u : Parameter=>u.2+u.1 • h) Prod.snd (r,z) hx (by fun_prop) contDiffAt_snd)
    (fiberSample_zero_outside A f g)

def mixedJets (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀x : physicalChart,ContDiffAt ℝ ∞ c x.val) (f g : QuantumTest) (h : SourceCoordinateSlice) :
    TwoJets (mixedForm i a c f g h) :=
  TwoJets.scale (1/2:ℂ) ((rowJets c hc (GaussCoframeSpin.current a f) (GaussCoframeCore.momentum i g) h).add
    (rowJets c hc (GaussCoframeCore.momentum i f) (GaussCoframeSpin.current a g) h))

def coframeJets (f g : QuantumTest) (h : SourceCoordinateSlice) : TwoJets (coframeForm f g h) := by
  let kinetic:=sumJets fun i : Fin 6=>sumJets fun j : Fin 6=>rowJets (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j) (GaussCoframeCore.momentum i f) (GaussCoframeCore.momentum j g) h
  let currents:=(((mixedJets 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0) f g h).add
    (mixedJets 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1) f g h)).add
    (mixedJets 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg) f g h)).add
    (mixedJets 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2) f g h)
  let spins:=sumJets fun a : Fin 7=>TwoJets.scale (spinWeight a:ℂ) (rowJets inverseVolume inverseVolume_smooth
    (GaussCoframeSpin.current a f) (GaussCoframeSpin.current a g) h)
  let numbers:=TwoJets.scale (1/2:ℂ) ((rowJets numberCoefficient numberCoefficient_smooth (number f) g h).add
    (rowJets numberCoefficient numberCoefficient_smooth f (number g) h))
  exact (((kinetic.add currents).add spins).add numbers).add (rowJets volumePotential volumePotential_smooth f g h)

open PreparationVacuumActionDecomposition

def totalForm (p : PhysicalMomentum) (f g : QuantumTest) (h : SourceCoordinateSlice) (r : ℝ) : ℂ:=
  nativeForm f g h r+coframeForm f g h r+fiberForm (actualFiber p) f g h r-
    fiberForm retainedCoefficient f g h r

def totalJets (p : PhysicalMomentum) (f g : QuantumTest) (h : SourceCoordinateSlice) : TwoJets (totalForm p f g h) :=
  (((nativeJets f g h).add (coframeJets f g h)).add (fiberJets (actualFiber p) (actualFiber_smooth p) f g h)).sub
    (fiberJets retainedCoefficient retainedCoefficient_smooth f g h)

theorem total_form_source (p : PhysicalMomentum) (f g : QuantumTest) (h : SourceCoordinateSlice) :
    totalForm p f g h 0=sourcePair f ((CanonicalPhysicalSpatial.physicalAction p+GaussYukawaOperator.originalAction) g) := by
  simp only [totalForm,nativeForm,zero_smul,add_zero,native_form_source,coframe_form_source,
    actual_fiber_form_source,retained_form_source]
  rw [physical_action_decomposition]
  simp only [LinearMap.sub_apply,LinearMap.add_apply,sourcePair,map_add,map_sub,inner_add_right,inner_sub_right]

theorem total_form_two_jets (p : PhysicalMomentum) (f g : QuantumTest) (h : SourceCoordinateSlice) :
    HasDerivAt (totalForm p f g h) ((totalJets p f g h).first 0) 0 ∧
    HasDerivAt (deriv (totalForm p f g h)) (totalJets p f g h).second 0 := (totalJets p f g h).actual

theorem sourceState_coordinate_first (h : SourceCoordinateSlice) (x : SourceCoordinateSlice) :
    HasDerivAt (fun r : ℝ=>sourceState (x+r • h)) (fderiv ℝ sourceState x h) 0 := by
  have path : HasDerivAt (fun r : ℝ=>x+r • h) h 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const h) using 1
    simp only [zero_add,one_smul]
  exact (sourceState_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 path (by simp)

end LowEnergy.PreparationVacuumSourceActionJets
