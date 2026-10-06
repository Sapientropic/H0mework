import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationJointParameterIntegral

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumJointFieldResponse
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

open PreparationVacuumGradedTransport GaussDensityCore GaussYukawaCoefficient GaussNativePotential
open MeasureTheory

open CanonicalPreparationCore PreparationVacuumHalfDensityFiber

open PreparationVacuumFieldCovector PreparationVacuumSpatialDensityTransport
open PreparationVacuumUncutYukawa PreparationVacuumYukawaTransport
open GaussNativeMatter GaussCoframeForm GaussNativeEnergy

abbrev FiberMap:=CanonicalGradedLocalCurrent.FiberMap
abbrev Localizer:=CanonicalGradedLocalCurrent.Localizer
attribute [local irreducible] fieldVector coreHalfDensity

def jointCurve (u : JointParameter) : SourceCoordinateSlice:=u.2+fieldVector u.1 u.2

def jointJacobian (u : JointParameter) (v : SourceCoordinateSlice) : SourceCoordinateSlice:=
  v+fderiv ℝ (fieldVector u.1) u.2 v

theorem jointVector_smooth (u : JointParameter) (base : u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (fun w : JointParameter=>fieldVector w.1 w.2) u :=by
  have term (i : Fin 289) : ContDiffAt ℝ ∞ (fun w : JointParameter=>w.1 i • fieldVector (fieldBasis i) w.2) u :=
    ((contDiffAt_pi.mp (contDiffAt_fst : ContDiffAt ℝ ∞ (Prod.fst : JointParameter→Field289) u)) i).smul
      ((fieldVector_smooth (fieldBasis i) ⟨u.2,base⟩).comp u contDiffAt_snd)
  have generated:=ContDiffAt.sum (s:=Finset.univ) (fun i _=>term i)
  have same : (fun w : JointParameter=>fieldVector w.1 w.2)=fun w=>∑i : Fin 289,w.1 i • fieldVector (fieldBasis i) w.2:=
    funext (fun w=>tangent_coordinates w.1 w.2)
  rw [same];exact generated

theorem jointCurve_smooth (u : JointParameter) (base : u.2∈physicalChart) : ContDiffAt ℝ ∞ jointCurve u :=
  contDiffAt_snd.add (jointVector_smooth u base)

theorem fieldDerivative_coordinates (h : Field289) (z : physicalChart) (v : SourceCoordinateSlice) :
    fderiv ℝ (fieldVector h) z.val v=∑i : Fin 289,h i • fderiv ℝ (fieldVector (fieldBasis i)) z.val v :=by
  have term (i : Fin 289):=((fieldVector_smooth (fieldBasis i) z).differentiableAt (by simp)).hasFDerivAt.const_smul (h i)
  have generated:=HasFDerivAt.fun_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 289)))=>term i)
  have same : (fun x=>∑i : Fin 289,h i • fieldVector (fieldBasis i) x)=fieldVector h:=
    funext (fun x=>(tangent_coordinates h x).symm)
  simp only [Pi.smul_apply] at generated
  rw [same] at generated
  have read:=congrArg (fun D : SourceCoordinateSlice→L[ℝ] SourceCoordinateSlice=>D v) generated.fderiv
  simpa only [sum_apply,smul_apply] using read

theorem jointJacobian_smooth (u : JointParameter) (base : u.2∈physicalChart)
    (V : JointParameter→SourceCoordinateSlice) (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun w=>jointJacobian w (V w)) u :=by
  have term (i : Fin 289) : ContDiffAt ℝ ∞
      (fun w : JointParameter=>w.1 i • fderiv ℝ (fieldVector (fieldBasis i)) w.2 (V w)) u :=by
    have coeff:=(contDiffAt_pi.mp (contDiffAt_fst : ContDiffAt ℝ ∞ (Prod.fst : JointParameter→Field289) u)) i
    have d:=((fieldVector_smooth (fieldBasis i) ⟨u.2,base⟩).fderiv_right (m:=∞) (by simp)).comp u contDiffAt_snd
    exact coeff.smul (d.clm_apply hV)
  have source:=hV.add (ContDiffAt.sum (s:=Finset.univ) (fun i _=>term i))
  apply source.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (physicalChart.isOpen.mem_nhds base)] with w hw
  exact congrArg (fun v=>V w+v) (fieldDerivative_coordinates w.1 ⟨w.2,hw⟩ (V w))

theorem jointCurve_zero (z : SourceCoordinateSlice) : jointCurve (0,z)=z :=by
  have hz : fieldVector 0 z=0:=(tangentLinear z).map_zero
  simp only [jointCurve,hz,add_zero]

theorem jointCurve_ray (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) :
    jointCurve (r • f,z)=fieldCoordinateCurve f r z :=by
  change z+tangentLinear z (r • f)=z+r • tangentLinear z f
  rw [map_smul]

theorem jointJacobian_ray (f : Field289) (r : ℝ) (z : physicalChart) (v : SourceCoordinateSlice) :
    jointJacobian (r • f,z.val) v=shiftedDirection f r z.val v :=by
  have same : fieldVector (r • f)=fun x=>r • fieldVector f x:=funext (fun x=>(tangentLinear x).map_smul r f)
  have generated:=((fieldVector_smooth f z).differentiableAt (by simp)).hasFDerivAt.const_smul r
  change HasFDerivAt (fun x=>r • fieldVector f x) (r • fderiv ℝ (fieldVector f) z.val) z.val at generated
  rw [←same] at generated
  exact congrArg (fun D : SourceCoordinateSlice→L[ℝ] SourceCoordinateSlice=>v+D v) generated.fderiv

theorem jointDomain_near (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    ∀ᶠw in 𝓝 u,w.2∈physicalChart ∧ jointCurve w∈physicalChart :=by
  have hb : ∀ᶠw in 𝓝 u,w.2∈physicalChart:=continuous_snd.continuousAt.preimage_mem_nhds (physicalChart.isOpen.mem_nhds base)
  have hm : ∀ᶠw in 𝓝 u,jointCurve w∈physicalChart:=(jointCurve_smooth u base).continuousAt.preimage_mem_nhds (physicalChart.isOpen.mem_nhds moved)
  exact hb.and hm

def jointRatio (N : ℕ) (u : JointParameter) (v : SourceCoordinateSlice) : ℂ:=
  fderiv ℝ (coreHalfDensity N) u.2 v/coreHalfDensity N u.2-
    fderiv ℝ (coreHalfDensity N) (jointCurve u) (jointJacobian u v)/coreHalfDensity N (jointCurve u)

theorem jointRatio_source (N : ℕ) (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart)
    (v : SourceCoordinateSlice) : jointRatio N u v=spatialRatio u.1 N 1 u.2 v :=by
  rw [spatialRatio_source u.1 N 1 ⟨u.2,base⟩ (by simpa only [jointCurve,fieldCoordinateCurve,one_smul] using moved) v]
  simp only [jointRatio,jointCurve,jointJacobian,shiftedDirection,fieldCoordinateCurve,one_smul]

theorem jointRatio_ray (f : Field289) (N : ℕ) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (v : SourceCoordinateSlice) :
    jointRatio N (r • f,z.val) v=spatialRatio f N r z.val v :=by
  rw [spatialRatio_source f N r z moved v,jointRatio,jointCurve_ray,jointJacobian_ray]

theorem jointRatio_smooth (N : ℕ) (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart)
    (V : JointParameter→SourceCoordinateSlice) (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun w=>jointRatio N w (V w)) u :=by
  have hb:=(coreHalfDensity_smooth N ⟨u.2,base⟩).comp u contDiffAt_snd
  have hx:=(coreHalfDensity_smooth N ⟨_,moved⟩).comp u (jointCurve_smooth u base)
  have db:=((coreHalfDensity_smooth N ⟨u.2,base⟩).fderiv_right (m:=∞) (by simp)).comp u contDiffAt_snd
  have dx:=((coreHalfDensity_smooth N ⟨_,moved⟩).fderiv_right (m:=∞) (by simp)).comp u (jointCurve_smooth u base)
  exact ((db.clm_apply hV).mul (hb.inv (coreHalfDensity_ne_zero N ⟨u.2,base⟩))).sub
    ((dx.clm_apply (jointJacobian_smooth u base V hV)).mul (hx.inv (coreHalfDensity_ne_zero N ⟨_,moved⟩)))

theorem jointCurve_original (u : JointParameter) : fieldCoordinateCurve u.1 1 u.2=jointCurve u :=by
  simp only [fieldCoordinateCurve,jointCurve,one_smul]

theorem jointCorrection_smooth (U : JointParameter→FockFiber) (V : JointParameter→SourceCoordinateSlice)
    (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun w=>spatialCorrection w.1 (1,w.2) (V w) (U w)) u :=by
  apply (contDiffAt_piLp 2).mpr;intro word
  let P : FockFiber→L[ℝ] ℂ:=(PiLp.proj (𝕜:=ℂ) 2 (fun _ : Occupation=>ℂ) word).restrictScalars ℝ
  have source:=(jointRatio_smooth word.card u base moved V hV).mul (P.contDiff.contDiffAt.comp u hU)
  apply source.congr_of_eventuallyEq
  filter_upwards [jointDomain_near u base moved] with w hw
  change spatialRatio w.1 word.card 1 w.2 (V w)*(U w) word=jointRatio word.card w (V w)*(U w) word
  rw [jointRatio_source word.card w hw.1 hw.2]

theorem jointDerivative_smooth (a : QuantumTest) (V : JointParameter→SourceCoordinateSlice)
    (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart)
    (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun w=>correctedDerivative w.1 a (1,w.2) (V w)) u :=by
  have ha:=a.contDiff.contDiffAt.comp u contDiffAt_snd
  have da:=(a.contDiff.fderiv_right (m:=∞) (by simp)).contDiffAt.comp u contDiffAt_snd
  exact (da.clm_apply hV).add (jointCorrection_smooth _ V u base moved ha hV)

theorem jointMomentum_smooth (a : QuantumTest) (v : Ambient) (u : JointParameter)
    (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    ContDiffAt ℝ ∞ (fun w=>correctedMomentum w.1 a v (1,w.2)) u :=by
  have hd:=(direction_smooth v ⟨_,moved⟩).comp u (jointCurve_smooth u base)
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have hc:=R.contDiff.contDiffAt.comp u ((connection_smooth v ⟨_,moved⟩).comp u (jointCurve_smooth u base))
  have source:=((jointDerivative_smooth a _ u base moved hd).add
    (hc.clm_apply (a.contDiff.contDiffAt.comp u contDiffAt_snd))).const_smul (-Complex.I)
  change ContDiffAt ℝ ∞ (fun w : JointParameter=>(-Complex.I) •
    (correctedDerivative w.1 a (1,w.2) (direction v (jointCurve w))+connection v (jointCurve w) (a w.2))) u at source
  simpa only [correctedMomentum,jointCurve_original] using source

theorem jointCoframe_smooth (a : QuantumTest) (i : Fin 6) (u : JointParameter)
    (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    ContDiffAt ℝ ∞ (fun w=>correctedCoframe w.1 a i (1,w.2)) u :=
  (jointDerivative_smooth a _ u base moved contDiffAt_const).const_smul (-Complex.I)

theorem jointSpin_smooth (a : QuantumTest) (k : Fin 7) (u : JointParameter) :
    ContDiffAt ℝ ∞ (fun w : JointParameter=>correctedSpin a k (1,w.2)) u :=by
  have hs:=correctedSpin_smooth a k (1,u.2)
  have hp : ContDiffAt ℝ ∞ (fun w : JointParameter=>((1:ℝ),w.2)) u:=contDiffAt_const.prodMk contDiffAt_snd
  have generated:=hs.comp u hp
  exact generated

theorem jointNumber_smooth (a : QuantumTest) (u : JointParameter) :
    ContDiffAt ℝ ∞ (fun w : JointParameter=>correctedNumber a (1,w.2)) u :=by
  have hs:=correctedNumber_smooth a (1,u.2)
  have hp : ContDiffAt ℝ ∞ (fun w : JointParameter=>((1:ℝ),w.2)) u:=contDiffAt_const.prodMk contDiffAt_snd
  have generated:=hs.comp u hp
  exact generated

theorem jointPair_smooth (U V : JointParameter→FockFiber) (c : SourceCoordinateSlice→ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (u : JointParameter)
    (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun w=>basePair w.1 c (1,w.2) (U w) (V w)) u :=by
  have coeff:=Complex.ofRealCLM.contDiff.contDiffAt.comp u ((hc ⟨_,moved⟩).comp u (jointCurve_smooth u base))
  have source:=pairSample_param Prod.snd U _ u base contDiffAt_snd hU (coeff.smul hV)
  change ContDiffAt ℝ ∞ (fun w : JointParameter=>pairSample w.2 (U w) ((c (jointCurve w):ℂ) • V w)) u at source
  simpa only [basePair,jointCurve_original] using source

theorem jointNative_smooth (a b : QuantumTest) (u : JointParameter) (base : u.2∈physicalChart)
    (moved : jointCurve u∈physicalChart) : ContDiffAt ℝ ∞ (fun w=>nativeFixedSample w.1 a b (1,w.2)) u :=by
  have term (v w : Ambient) (c : SourceCoordinateSlice→ℝ) (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val):=
    jointPair_smooth (fun x=>correctedMomentum x.1 a v (1,x.2)) (fun x=>correctedMomentum x.1 b w (1,x.2)) c hc u base moved
      (jointMomentum_smooth a v u base moved) (jointMomentum_smooth b w u base moved)
  have first:=ContDiffAt.sum (s:=Finset.univ) (fun i _=>term (GaussNativeForm.scalarDirection i) (GaussNativeForm.scalarDirection i) scalarWeight scalarWeight_smooth)
  have second:=ContDiffAt.sum (s:=Finset.univ) (fun j _=>ContDiffAt.sum (s:=Finset.univ) (fun i _=>ContDiffAt.sum (s:=Finset.univ)
    (fun k _=>term (GaussNativeForm.gaugeDirection i j) (GaussNativeForm.gaugeDirection k j)
      (fun z=>gaugeWeight z i k) (gaugeWeight_smooth i k))))
  exact ((contDiffAt_const.mul first).add (contDiffAt_const.mul second)).add
    (jointPair_smooth _ _ potential potential_smooth u base moved (a.contDiff.contDiffAt.comp u contDiffAt_snd) (b.contDiff.contDiffAt.comp u contDiffAt_snd))

theorem jointMixed_smooth (a b : QuantumTest) (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (u : JointParameter)
    (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    ContDiffAt ℝ ∞ (fun w=>mixedFixedSample w.1 a b i k c (1,w.2)) u :=
  contDiffAt_const.mul ((jointPair_smooth _ _ c hc u base moved (jointSpin_smooth a k u) (jointCoframe_smooth b i u base moved)).add
    (jointPair_smooth _ _ c hc u base moved (jointCoframe_smooth a i u base moved) (jointSpin_smooth b k u)))

theorem jointCoframeForm_smooth (a b : QuantumTest) (u : JointParameter) (base : u.2∈physicalChart)
    (moved : jointCurve u∈physicalChart) : ContDiffAt ℝ ∞ (fun w=>coframeFixedSample w.1 a b (1,w.2)) u :=by
  have kin:=ContDiffAt.sum (s:=Finset.univ) (fun i _=>ContDiffAt.sum (s:=Finset.univ) (fun j _=>
    jointPair_smooth _ _ (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j) u base moved
      (jointCoframe_smooth a i u base moved) (jointCoframe_smooth b j u base moved)))
  have cur:=(((jointMixed_smooth a b 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0) u base moved).add
    (jointMixed_smooth a b 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1) u base moved)).add
    (jointMixed_smooth a b 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg) u base moved)).add
    (jointMixed_smooth a b 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2) u base moved)
  have spin:=ContDiffAt.sum (s:=Finset.univ) (fun k _=>(contDiffAt_const (c:=(spinWeight k:ℂ))).mul
    (jointPair_smooth _ _ inverseVolume inverseVolume_smooth u base moved (jointSpin_smooth a k u) (jointSpin_smooth b k u)))
  have num:=(contDiffAt_const (c:=(1/2:ℂ))).mul ((jointPair_smooth _ _ numberCoefficient numberCoefficient_smooth u base moved
    (jointNumber_smooth a u) (b.contDiff.contDiffAt.comp u contDiffAt_snd)).add
    (jointPair_smooth _ _ numberCoefficient numberCoefficient_smooth u base moved (a.contDiff.contDiffAt.comp u contDiffAt_snd) (jointNumber_smooth b u)))
  exact (((kin.add cur).add spin).add num).add (jointPair_smooth _ _ volumePotential volumePotential_smooth u base moved
    (a.contDiff.contDiffAt.comp u contDiffAt_snd) (b.contDiff.contDiffAt.comp u contDiffAt_snd))

theorem jointFiber_smooth (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter)
    (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    ContDiffAt ℝ ∞ (fun w=>fixedSample (diagonalFiber p) w.1 a b (1,w.2)) u :=by
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have coeff:=R.contDiff.contDiffAt.comp u ((diagonalFiber_smooth p ⟨_,moved⟩).comp u (jointCurve_smooth u base))
  have source:=pairSample_param Prod.snd _ _ u base contDiffAt_snd (a.contDiff.contDiffAt.comp u contDiffAt_snd)
    (coeff.clm_apply (b.contDiff.contDiffAt.comp u contDiffAt_snd))
  change ContDiffAt ℝ ∞ (fun w : JointParameter=>pairSample w.2 (a w.2) (diagonalFiber p (jointCurve w) (b w.2))) u at source
  simpa only [fixedSample,jointCurve_original] using source

theorem joint_tube_exists (a : QuantumTest) :
    ∃R : ℝ,0<R ∧ ∀h z,‖h‖≤ R→z∈tsupport a→jointCurve (h,z)∈physicalChart :=by
  let U : Set JointParameter:={u | u.2∈physicalChart ∧ jointCurve u∈physicalChart}
  have op : IsOpen U:=by
    apply isOpen_iff_mem_nhds.mpr;intro u hu
    exact jointDomain_near u hu.1 hu.2
  have base : ({0}:Set Field289) ×ˢ tsupport a⊆U :=by
    rintro ⟨h,z⟩ ⟨hh,hz⟩
    have h0 : h=0:=hh
    subst h
    exact ⟨a.tsupport_subset hz,by rw [jointCurve_zero];exact a.tsupport_subset hz⟩
  obtain ⟨u,v,hu,_hv,hzero,hcover,hproduct⟩:=generalized_tube_lemma (isCompact_singleton (x:=(0:Field289))) a.hasCompactSupport op base
  obtain ⟨e,he,hball⟩:=Metric.mem_nhds_iff.mp (hu.mem_nhds (hzero (by rfl)))
  refine ⟨e/2,by positivity,?_⟩
  intro h z hh hz
  apply (hproduct ?_).2
  refine ⟨hball ?_,hcover hz⟩
  rw [Metric.mem_ball,dist_zero_right]
  linarith

def jointRadius (a : QuantumTest) : ℝ:=(joint_tube_exists a).choose

theorem jointRadius_positive (a : QuantumTest) : 0<jointRadius a:=(joint_tube_exists a).choose_spec.1

theorem jointRadius_valid (a : QuantumTest) (h : Field289) (z : SourceCoordinateSlice)
    (small : ‖h‖≤ jointRadius a) (inside : z∈tsupport a) : jointCurve (h,z)∈physicalChart:=
  (joint_tube_exists a).choose_spec.2 h z small inside

theorem jointIntegral_C2 (S : JointParameter→ℂ) (a : QuantumTest)
    (smooth : ∀u,u.2∈physicalChart→jointCurve u∈physicalChart→ ContDiffAt ℝ ∞ S u)
    (zero : ∀h z,z∉tsupport a→S (h,z)=0) :
    ContDiffAt ℝ 2 (fun h=>∫z,S (h,z) ∂GaussHistoryHilbert.configurationMeasure) 0 :=by
  apply source_integral_C2 S (tsupport a) a.hasCompactSupport (jointRadius a) (jointRadius_positive a) _ zero
  intro h z small
  by_cases inside : z∈tsupport a
  · exact smooth (h,z) (a.tsupport_subset inside) (jointRadius_valid a h z small.le inside)
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact zero u.1 u.2 hu

def jointForm (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  nativeFixedIntegral h a b 1+coframeFixedIntegral h a b 1+fixedFiber (diagonalFiber p) h a b 1

theorem jointForm_C2 (p : PhysicalMomentum) (a b : QuantumTest) : ContDiffAt ℝ 2 (jointForm p a b) 0 :=
  ((jointIntegral_C2 (fun u=>nativeFixedSample u.1 a b (1,u.2)) a (jointNative_smooth a b)
    (fun h z hz=>nativeFixedSample_zero h a b 1 z hz)).add
    (jointIntegral_C2 (fun u=>coframeFixedSample u.1 a b (1,u.2)) a (jointCoframeForm_smooth a b)
      (fun h z hz=>coframeFixedSample_zero h a b 1 z hz))).add
    (jointIntegral_C2 (fun u=>fixedSample (diagonalFiber p) u.1 a b (1,u.2)) a (jointFiber_smooth p a b)
      (fun h z hz=>fixedSample_zero (diagonalFiber p) h a b 1 z hz))

theorem sourceSamples_ray (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (p : PhysicalMomentum) (a b : QuantumTest) :
    nativeFixedSample (r • f) a b (1,z.val)=nativeFixedSample f a b (r,z.val) ∧
    coframeFixedSample (r • f) a b (1,z.val)=coframeFixedSample f a b (r,z.val) ∧
    fixedSample (diagonalFiber p) (r • f) a b (1,z.val)=fixedSample (diagonalFiber p) f a b (r,z.val) :=by
  have curve : fieldCoordinateCurve (r • f) 1 z.val=fieldCoordinateCurve f r z.val:=
    (jointCurve_original (r • f,z.val)).trans (jointCurve_ray f r z.val)
  have hx : jointCurve (r • f,z.val)∈physicalChart:=by rw [jointCurve_ray];exact moved
  have ratio (N : ℕ) (v : SourceCoordinateSlice) : spatialRatio (r • f) N 1 z.val v=spatialRatio f N r z.val v:=
    (jointRatio_source N (r • f,z.val) z.property hx v).symm.trans (jointRatio_ray f N r z moved v)
  have correction (v : SourceCoordinateSlice) : spatialCorrection (r • f) (1,z.val) v=spatialCorrection f (r,z.val) v :=by
    apply ContinuousLinearMap.ext;intro x;apply PiLp.ext;intro word
    simp only [spatialCorrection,weight_apply,ratio]
  have mom (test : QuantumTest) (v : Ambient) : correctedMomentum (r • f) test v (1,z.val)=correctedMomentum f test v (r,z.val) :=by
    simp only [correctedMomentum,correctedDerivative,curve,correction]
  have cof (test : QuantumTest) (i : Fin 6) : correctedCoframe (r • f) test i (1,z.val)=correctedCoframe f test i (r,z.val) :=by
    simp only [correctedCoframe,correctedDerivative,correction]
  constructor
  · simp only [nativeFixedSample,basePair,curve,mom]
  constructor
  · simp only [coframeFixedSample,mixedFixedSample,basePair,curve,cof,correctedSpin,correctedNumber]
  · simp only [fixedSample,curve]

theorem jointForm_ray (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (fun r : ℝ=>jointForm p a b (r • f))=ᶠ[𝓝 0] completeForm f p a b :=by
  have small : ∀ᶠr : ℝ in 𝓝 0,|r|<fieldRadius f a:=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  filter_upwards [small] with r hr
  have sample (z : SourceCoordinateSlice) :
      nativeFixedSample (r • f) a b (1,z)=nativeFixedSample f a b (r,z) ∧
      coframeFixedSample (r • f) a b (1,z)=coframeFixedSample f a b (r,z) ∧
      fixedSample (diagonalFiber p) (r • f) a b (1,z)=fixedSample (diagonalFiber p) f a b (r,z) :=by
    by_cases inside : z∈tsupport a
    · exact sourceSamples_ray f r ⟨z,a.tsupport_subset inside⟩ (fieldRadius_chart f a r z hr.le inside) p a b
    · simp only [nativeFixedSample_zero _ a b _ z inside,coframeFixedSample_zero _ a b _ z inside,
        fixedSample_zero _ _ a b _ z inside,and_self]
  unfold jointForm completeForm nativeFixedIntegral coframeFixedIntegral fixedFiber
  have first:=integral_congr_ae (Filter.Eventually.of_forall (fun z=>(sample z).1)) (μ:=GaussHistoryHilbert.configurationMeasure)
  have second:=integral_congr_ae (Filter.Eventually.of_forall (fun z=>(sample z).2.1)) (μ:=GaussHistoryHilbert.configurationMeasure)
  have third:=integral_congr_ae (Filter.Eventually.of_forall (fun z=>(sample z).2.2)) (μ:=GaussHistoryHilbert.configurationMeasure)
  rw [first,second,third]

open GaussYukawaCoefficient
open NativeHistoryGrade (Label)
abbrev Index:=GaussUnitaryHistory.Index
local instance : Fintype Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _

def jointCompression (p : PhysicalMomentum) (F : Index) (h : Field289) : H→L[ℂ] H:=
  sourceAssembly p F (fun i j=>jointForm p (bareTest p F i) (bareTest p F j) h)

theorem jointCompression_C2 (p : PhysicalMomentum) (F : Index) : ContDiffAt ℝ 2 (jointCompression p F) 0 :=by
  apply ContDiffAt.sum;intro g _
  apply ContDiffAt.sum;intro i _
  apply ContDiffAt.sum;intro j _
  exact (jointForm_C2 p (bareTest p F i) (bareTest p F j)).smul contDiffAt_const

theorem jointCompression_ray (f : Field289) (p : PhysicalMomentum) (F : Index) :
    (fun r : ℝ=>jointCompression p F (r • f))=ᶠ[𝓝 0] transportedCompression f p F :=by
  have each (i j : PhysicalBasisIndex p F):=
    (jointForm_ray f p (bareTest p F i) (bareTest p F j)).trans
      (completeForm_source f p (bareTest p F i) (bareTest p F j)).symm
  have all:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (each i))
  filter_upwards [all] with r hr
  exact congrArg (sourceAssembly p F) (funext (fun i=>funext (fun j=>hr i j)))

def slopeLinear (z : SourceCoordinateSlice) : Field289→ₗ[ℝ] FiberMap where
  toFun f:=slopeFiber f z
  map_add' f g:=by
    change sourceMap (((tangentLinear z) (f+g)).2.1 : Scalar)=sourceMap ((fieldVector f z).2.1 : Scalar)+sourceMap ((fieldVector g z).2.1 : Scalar)
    rw [map_add]
    exact sourceMap.map_add _ _
  map_smul' r f:=by
    change sourceMap (((tangentLinear z) (r • f)).2.1 : Scalar)=r • sourceMap ((fieldVector f z).2.1 : Scalar)
    rw [map_smul]
    exact sourceMap.map_smul r _

theorem slopeFiber_coordinates (f : Field289) (z : SourceCoordinateSlice) :
    slopeFiber f z=∑i : Fin 289,f i • slopeFiber (fieldBasis i) z :=by
  change slopeLinear z f=∑i : Fin 289,f i • slopeLinear z (fieldBasis i)
  have source:=congrArg (slopeLinear z) (field_coordinates f)
  simpa only [map_sum,map_smul] using source

def slopeTest (f : Field289) (phi : Localizer) (a : QuantumTest) : QuantumTest:=
  localMultiplier (fun z=>(phi z:ℂ) • slopeFiber f z)
    (fun z=>(Complex.ofRealCLM.contDiff.contDiffAt.comp z.val phi.contDiff.contDiffAt).smul (slopeFiber_smooth f z)) a

theorem uncutSlope_core_source (f : Field289) (phi : Localizer) (a : QuantumTest) :
    uncutSlope f phi (embed a)=embed (slopeTest f phi a) :=by
  rw [uncutSlope,sub_apply,uncutOperator_core,uncutOperator_core,←map_sub]
  apply congrArg embed;apply DFunLike.ext;intro z
  change ((phi z:ℂ) • uncutFiber f 1 z) (a z)-((phi z:ℂ) • uncutFiber f 0 z) (a z)=((phi z:ℂ) • slopeFiber f z) (a z)
  rw [uncutFiber_affine f 1 z]
  simp only [one_smul,smul_add,add_apply,add_sub_cancel_left]

theorem uncutSlope_coordinates (f : Field289) (phi : Localizer) :
    uncutSlope f phi=∑i : Fin 289,f i • uncutSlope (fieldBasis i) phi :=by
  apply GaussYukawaGrade.core_ext;intro a
  simp only [sum_apply,smul_apply,uncutSlope_core_source]
  let E:=embed.restrictScalars ℝ
  have linear : E (∑i : Fin 289,f i • slopeTest (fieldBasis i) phi a)=∑i : Fin 289,f i • E (slopeTest (fieldBasis i) phi a) :=by
    simp only [map_sum,map_smul]
  change E (slopeTest f phi a)=∑i : Fin 289,f i • E (slopeTest (fieldBasis i) phi a)
  rw [←linear]
  apply congrArg E;apply DFunLike.ext;intro z
  change ((phi z:ℂ) • slopeFiber f z) (a z)=(∑i : Fin 289,f i • slopeTest (fieldBasis i) phi a) z
  rw [slopeFiber_coordinates]
  simp only [Finset.smul_sum,sum_apply,smul_apply,slopeTest,localMultiplier]
  apply Finset.sum_congr rfl;intro i _
  exact smul_comm (phi z:ℂ) (f i) (slopeFiber (fieldBasis i) z (a z))

theorem uncutOperator_base (f : Field289) (phi : Localizer) : uncutOperator f phi 0=uncutOperator 0 phi 0 :=by
  apply GaussYukawaGrade.core_ext;intro a
  rw [uncutOperator_core,uncutOperator_core]
  apply congrArg embed;apply DFunLike.ext;intro z
  change ((phi z:ℂ) • uncutFiber f 0 z) (a z)=((phi z:ℂ) • uncutFiber 0 0 z) (a z)
  simp only [uncutFiber,curve_zero]

def jointY (phi : Localizer) (h : Field289) : H→L[ℂ] H:=
  uncutOperator 0 phi 0+∑i : Fin 289,h i • uncutSlope (fieldBasis i) phi

theorem jointY_source (phi : Localizer) (h : Field289) : jointY phi h=uncutOperator h phi 1 :=by
  rw [uncutOperator_affine,uncutOperator_base,one_smul,uncutSlope_coordinates]
  rfl

theorem jointY_C2 (phi : Localizer) : ContDiffAt ℝ 2 (jointY phi) 0 :=by
  apply ContDiffAt.add contDiffAt_const
  apply ContDiffAt.sum;intro i _
  exact ((contDiffAt_pi.mp (contDiffAt_id : ContDiffAt ℝ 2 (id : Field289→Field289) 0)) i).smul contDiffAt_const

theorem jointY_ray (f : Field289) (phi : Localizer) (r : ℝ) : jointY phi (r • f)=uncutOperator f phi r :=by
  rw [uncutOperator_affine,uncutOperator_base,uncutSlope_coordinates]
  simp only [jointY,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

def jointGenerator (p : PhysicalMomentum) (F : Index) (z : ℂ) (h : Field289) : H→L[ℂ] H:=
  jointCompression p F h+jointY (finiteRetainer p F) h-z • 1

theorem jointGenerator_C2 (p : PhysicalMomentum) (F : Index) (z : ℂ) : ContDiffAt ℝ 2 (jointGenerator p F z) 0 :=
  ((jointCompression_C2 p F).add (jointY_C2 (finiteRetainer p F))).sub contDiffAt_const

theorem jointGenerator_ray (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) :
    (fun r : ℝ=>jointGenerator p F z (r • f))=ᶠ[𝓝 0] (sourceGenerator f p F none z) :=by
  filter_upwards [jointCompression_ray f p F] with r hr
  change jointCompression p F (r • f)+jointY (finiteRetainer p F) (r • f)-z • 1=
    transportedCompression f p F r+uncutOperator f (finiteRetainer p F) r-z • 1
  rw [hr,jointY_ray]

end LowEnergy.PreparationVacuumJointFieldResponse
