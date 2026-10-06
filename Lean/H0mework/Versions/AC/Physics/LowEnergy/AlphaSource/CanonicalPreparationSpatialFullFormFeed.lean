import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationSpatialMomentumTransport
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationHalfDensityCompressionFeed

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumSpatialDensityTransport
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

open GaussNativeMatter GaussCoframeForm

open PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open CanonicalPreparationCore.Completed PreparationVacuumSourcePreparedResponse
open GaussNativeEnergy NativeHistoryGrade
abbrev Index:=GaussUnitaryHistory.Index
local instance : Fintype Label:=Fintype.ofFinite _

def basePair (f : Field289) (c : SourceCoordinateSlice→ℝ) (u : Parameter) (a b : FockFiber) : ℂ:=
  pairSample u.2 a ((c (fieldCoordinateCurve f u.1 u.2):ℂ) • b)

theorem pair_transport_scalar (f : Field289) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (a b : FockFiber) (c : ℂ) :
    pairSample (fieldCoordinateCurve f r z.val) (transportFiber f z.val r a) (c • transportFiber f z.val r b)=
      pairSample z.val a (c • b) :=by
  rw [←map_smul]
  exact pair_transport f z r moved a (c • b)

def nativeFixedSample (f : Field289) (a b : QuantumTest) (u : Parameter) : ℂ:=
  (1/2:ℂ)*(∑i : GaussNativeForm.ScalarIndex,basePair f scalarWeight u
    (correctedMomentum f a (GaussNativeForm.scalarDirection i) u) (correctedMomentum f b (GaussNativeForm.scalarDirection i) u))+
  (1/2:ℂ)*(∑j : GaussNativeForm.LieIndex,∑i : Fin 3,∑k : Fin 3,basePair f (fun z=>gaugeWeight z i k) u
    (correctedMomentum f a (GaussNativeForm.gaugeDirection i j) u) (correctedMomentum f b (GaussNativeForm.gaugeDirection k j) u))+
    basePair f potential u (a u.2) (b u.2)

def mixedFixedSample (f : Field289) (a b : QuantumTest) (i : Fin 6) (k : Fin 7)
    (c : SourceCoordinateSlice→ℝ) (u : Parameter) : ℂ:=
  (1/2:ℂ)*(basePair f c u (correctedSpin a k u) (correctedCoframe f b i u)+
    basePair f c u (correctedCoframe f a i u) (correctedSpin b k u))

def coframeFixedSample (f : Field289) (a b : QuantumTest) (u : Parameter) : ℂ:=
  (∑i : Fin 6,∑j : Fin 6,basePair f (GaussCoframeKinetic.coefficient i j) u (correctedCoframe f a i u) (correctedCoframe f b j u))+
  (mixedFixedSample f a b 1 5 (currentCoefficient 0) u+mixedFixedSample f a b 3 3 (currentCoefficient 1) u+
    mixedFixedSample f a b 3 4 (fun z=>-currentCoefficient 0 z) u+mixedFixedSample f a b 4 3 (currentCoefficient 2) u)+
  (∑k : Fin 7,(spinWeight k:ℂ)*basePair f inverseVolume u (correctedSpin a k u) (correctedSpin b k u))+
  (1/2:ℂ)*(basePair f numberCoefficient u (correctedNumber a u) (b u.2)+basePair f numberCoefficient u (a u.2) (correctedNumber b u))+
    basePair f volumePotential u (a u.2) (b u.2)

theorem movingNative_fixed (f : Field289) (a b : QuantumTest) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) :
    movingNative f (transportedSection f a) (transportedSection f b) (r,z.val)=nativeFixedSample f a b (r,z.val) :=by
  have ha (v : Ambient):=movingMomentum_source f a v r z moved
  have hb (v : Ambient):=movingMomentum_source f b v r z moved
  simp only [movingNative,movingPair,ha,hb,transportedSection,nativeFixedSample,basePair]
  simp only [pair_transport_scalar f r z moved]

theorem movingCoframe_fixed (f : Field289) (a b : QuantumTest) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) :
    movingCoframeForm f (transportedSection f a) (transportedSection f b) (r,z.val)=coframeFixedSample f a b (r,z.val) :=by
  have ha (i : Fin 6):=movingCoframe_source f a i r z moved
  have hb (i : Fin 6):=movingCoframe_source f b i r z moved
  simp only [movingCoframeForm,movingMixed,movingPair,ha,hb,movingSpin_source,movingNumber_source,
    transportedSection,coframeFixedSample,mixedFixedSample,basePair,pair_transport_scalar f r z moved]

theorem sourceDomain_near (f : Field289) (u : Parameter) (base : u.2∈physicalChart)
    (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ∀ᶠw in 𝓝 u,w.2∈physicalChart ∧ fieldCoordinateCurve f w.1 w.2∈physicalChart :=by
  have hb : ∀ᶠw in 𝓝 u,w.2∈physicalChart:=continuous_snd.continuousAt.preimage_mem_nhds (physicalChart.isOpen.mem_nhds base)
  have hm : ∀ᶠw in 𝓝 u,fieldCoordinateCurve f w.1 w.2∈physicalChart:=
    (field_curve_smooth f u.1 ⟨u.2,base⟩).continuousAt.preimage_mem_nhds (physicalChart.isOpen.mem_nhds moved)
  exact hb.and hm

theorem nativeFixedSample_smooth (f : Field289) (a b : QuantumTest) (u : Parameter)
    (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (nativeFixedSample f a b) u :=by
  apply (movingNative_smooth f (transportedSection f a) (transportedSection f b) u base moved
    (transportedSection_smooth f a u base moved) (transportedSection_smooth f b u base moved)).congr_of_eventuallyEq
  filter_upwards [sourceDomain_near f u base moved] with w hw
  exact (movingNative_fixed f a b w.1 ⟨w.2,hw.1⟩ hw.2).symm

theorem coframeFixedSample_smooth (f : Field289) (a b : QuantumTest) (u : Parameter)
    (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (coframeFixedSample f a b) u :=by
  apply (movingCoframeForm_smooth f (transportedSection f a) (transportedSection f b) u base moved
    (transportedSection_smooth f a u base moved) (transportedSection_smooth f b u base moved)).congr_of_eventuallyEq
  filter_upwards [sourceDomain_near f u base moved] with w hw
  exact (movingCoframe_fixed f a b w.1 ⟨w.2,hw.1⟩ hw.2).symm

theorem nativeFixedSample_zero (f : Field289) (a b : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : nativeFixedSample f a b (r,z)=0 :=by
  simp only [nativeFixedSample,basePair,correctedMomentum_zero f a _ r z outside,
    image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left,Finset.sum_const_zero,mul_zero,add_zero]

theorem coframeFixedSample_zero (f : Field289) (a b : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : coframeFixedSample f a b (r,z)=0 :=by
  simp only [coframeFixedSample,mixedFixedSample,basePair,correctedCoframe_zero f a _ r z outside,
    correctedSpin,correctedNumber,image_eq_zero_of_notMem_tsupport outside,map_zero,
    pairSample_zero_left,Finset.sum_const_zero,mul_zero,add_zero]

def nativeFixedIntegral (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ:=
  ∫z,nativeFixedSample f a b (r,z) ∂GaussHistoryHilbert.configurationMeasure

def coframeFixedIntegral (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ:=
  ∫z,coframeFixedSample f a b (r,z) ∂GaussHistoryHilbert.configurationMeasure

def nativeFixedJets (f : Field289) (a b : QuantumTest) : TwoJets (nativeFixedIntegral f a b):=
  parameterIntegralJets (nativeFixedSample f a b) f a (nativeFixedSample_smooth f a b) (nativeFixedSample_zero f a b)

def coframeFixedJets (f : Field289) (a b : QuantumTest) : TwoJets (coframeFixedIntegral f a b):=
  parameterIntegralJets (coframeFixedSample f a b) f a (coframeFixedSample_smooth f a b) (coframeFixedSample_zero f a b)

theorem nativeIntegral_fixed (f : Field289) (a b : QuantumTest) (r : ℝ) (small : |r|<fieldRadius f a) :
    nativeIntegral f a b r=nativeFixedIntegral f a b r :=by
  unfold nativeIntegral nativeFixedIntegral
  apply integral_congr_ae;apply Filter.Eventually.of_forall;intro z
  by_cases inside : z∈tsupport a
  · exact movingNative_fixed f a b r ⟨z,a.tsupport_subset inside⟩ (fieldRadius_chart f a r z small.le inside)
  · dsimp only
    rw [nativeFixedSample_zero f a b r z inside]
    simp only [movingNative,movingPair,movingMomentum,transportedSection_zero_outside f a r z inside,
      spatialJet_zero_outside f a r z _ inside,map_zero,zero_add,add_zero,smul_zero,
      pairSample_zero_left,Finset.sum_const_zero,mul_zero]

theorem source_integrable (S : Parameter→ℂ) (f : Field289) (a : QuantumTest)
    (smooth : ∀u,u.2∈physicalChart→fieldCoordinateCurve f u.1 u.2∈physicalChart→ ContDiffAt ℝ ∞ S u)
    (zero : ∀r z,z∉tsupport a→S (r,z)=0) (r : ℝ) (small : |r|<fieldRadius f a) :
    Integrable (fun z=>S (r,z)) GaussHistoryHilbert.configurationMeasure :=by
  have continuous : Continuous (fun z=>S (r,z)) :=by
    apply continuous_iff_continuousAt.mpr;intro z
    by_cases inside : z∈tsupport a
    · exact (smooth (r,z) (a.tsupport_subset inside) (fieldRadius_chart f a r z small.le inside)).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds inside] with y hy
      exact zero r y hy
  apply continuous.integrable_of_hasCompactSupport
  apply a.hasCompactSupport.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_tsupport a)
  intro z hz;by_contra outside;exact hz (zero r z outside)

theorem coframeIntegral_single_integral (f : Field289) (a b : QuantumTest) (r : ℝ) (small : |r|<fieldRadius f a) :
    coframeIntegral f a b r=∫z,movingCoframeForm f (transportedSection f a) (transportedSection f b) (r,z)
      ∂GaussHistoryHilbert.configurationMeasure :=by
  have term (op oq : SectionOp) (c : SourceCoordinateSlice→ℝ) (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
      Integrable (fun z=>movingPair f (sectionValue f a op) (sectionValue f b oq) c (r,z)) GaussHistoryHilbert.configurationMeasure :=
    source_integrable _ f a
      (fun u hz hx=>movingPair_smooth f _ _ c hc u hz hx (sectionValue_smooth f a op u hz hx) (sectionValue_smooth f b oq u hz hx))
      (fun r z hz=>by simp only [movingPair,sectionValue_zero f a op r z hz,pairSample_zero_left]) r small
  have kin (i j : Fin 6):=term (.coframe i) (.coframe j) (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)
  have mix (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice→ℝ) (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val):=
    (term (.spin k) (.coframe i) c hc).add (term (.coframe i) (.spin k) c hc)
  have m0:=mix 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0)
  have m1:=mix 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1)
  have m2:=mix 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg)
  have m3:=mix 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2)
  have spin (k : Fin 7):=term (.spin k) (.spin k) inverseVolume inverseVolume_smooth
  have n0:=term .number .base numberCoefficient numberCoefficient_smooth
  have n1:=term .base .number numberCoefficient numberCoefficient_smooth
  have potential:=term .base .base volumePotential volumePotential_smooth
  have ik:=integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>kin i j))
  have ic:=(((m0.const_mul (1/2:ℂ)).add (m1.const_mul (1/2:ℂ))).add (m2.const_mul (1/2:ℂ))).add (m3.const_mul (1/2:ℂ))
  have isp:=integrable_finsetSum Finset.univ (fun k _=>(spin k).const_mul (spinWeight k:ℂ))
  have inu:=(n0.add n1).const_mul (1/2:ℂ)
  have kr : (∫z,∑i : Fin 6,∑j : Fin 6,movingPair f (sectionValue f a (.coframe i)) (sectionValue f b (.coframe j))
      (GaussCoframeKinetic.coefficient i j) (r,z) ∂GaussHistoryHilbert.configurationMeasure)=
      ∑i : Fin 6,∑j : Fin 6,pairIntegral f a b (.coframe i) (.coframe j) (GaussCoframeKinetic.coefficient i j) r :=by
    rw [integral_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>kin i j))]
    apply Finset.sum_congr rfl;intro i _
    exact integral_finsetSum Finset.univ (fun j _=>kin i j)
  have mr (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice→ℝ) (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
      (∫z,movingMixed f (transportedSection f a) (transportedSection f b) i k c (r,z)
        ∂GaussHistoryHilbert.configurationMeasure)=mixedIntegral f a b i k c r :=by
    change (∫z,(1/2:ℂ)*(movingPair f (sectionValue f a (.spin k)) (sectionValue f b (.coframe i)) c (r,z)+
      movingPair f (sectionValue f a (.coframe i)) (sectionValue f b (.spin k)) c (r,z)) ∂GaussHistoryHilbert.configurationMeasure)=_
    rw [integral_const_mul,integral_add (term (.spin k) (.coframe i) c hc) (term (.coframe i) (.spin k) c hc)]
    rfl
  have sr : (∫z,∑k : Fin 7,(spinWeight k:ℂ)*movingPair f (sectionValue f a (.spin k)) (sectionValue f b (.spin k)) inverseVolume (r,z)
      ∂GaussHistoryHilbert.configurationMeasure)=∑k : Fin 7,(spinWeight k:ℂ)*pairIntegral f a b (.spin k) (.spin k) inverseVolume r :=by
    rw [integral_finsetSum Finset.univ (fun k _=>(spin k).const_mul (spinWeight k:ℂ))]
    apply Finset.sum_congr rfl;intro k _
    exact integral_const_mul _ _
  simp only [sectionValue,Pi.add_apply] at ik ic isp inu potential m0 m1 m2 m3 n0 n1 kr sr
  simp only [movingMixed,sectionValue] at mr
  have r4:=integral_add (((ik.add ic).add isp).add inu) potential
  have r3:=integral_add ((ik.add ic).add isp) inu
  have r2:=integral_add (ik.add ic) isp
  have r1:=integral_add ik ic
  have c3:=integral_add (((m0.const_mul (1/2:ℂ)).add (m1.const_mul (1/2:ℂ))).add (m2.const_mul (1/2:ℂ))) (m3.const_mul (1/2:ℂ))
  have c2:=integral_add ((m0.const_mul (1/2:ℂ)).add (m1.const_mul (1/2:ℂ))) (m2.const_mul (1/2:ℂ))
  have c1:=integral_add (m0.const_mul (1/2:ℂ)) (m1.const_mul (1/2:ℂ))
  simp only [Pi.add_apply] at r4 r3 r2 r1 c3 c2 c1
  unfold movingCoframeForm movingMixed
  rw [r4,r3,r2,r1,c3,c2,c1,
    kr,mr 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0),
    mr 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1),
    mr 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg),
    mr 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2),sr,
    integral_const_mul,integral_add n0 n1]
  rfl

theorem coframeIntegral_fixed (f : Field289) (a b : QuantumTest) (r : ℝ) (small : |r|<fieldRadius f a) :
    coframeIntegral f a b r=coframeFixedIntegral f a b r :=by
  rw [coframeIntegral_single_integral f a b r small];unfold coframeFixedIntegral
  apply integral_congr_ae;apply Filter.Eventually.of_forall;intro z
  by_cases inside : z∈tsupport a
  · exact movingCoframe_fixed f a b r ⟨z,a.tsupport_subset inside⟩ (fieldRadius_chart f a r z small.le inside)
  · dsimp only
    rw [coframeFixedSample_zero f a b r z inside]
    simp only [movingCoframeForm,movingMixed,movingPair,movingCoframe,movingSpin,movingNumber,
      transportedSection_zero_outside f a r z inside,spatialJet_zero_outside f a r z _ inside,
      map_zero,zero_add,add_zero,smul_zero,pairSample_zero_left,Finset.sum_const_zero,mul_zero]

def completeForm (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (r : ℝ) : ℂ:=
  nativeFixedIntegral f a b r+coframeFixedIntegral f a b r+fixedFiber (diagonalFiber p) f a b r

def completeJets (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : TwoJets (completeForm f p a b):=
  ((nativeFixedJets f a b).add (coframeFixedJets f a b)).add (fixedJets (diagonalFiber p) (diagonalFiber_smooth p) f a b)

theorem completeForm_source (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    transportedForm f p a b=ᶠ[𝓝 0] completeForm f p a b :=by
  have small : ∀ᶠr : ℝ in 𝓝 0,|r|<fieldRadius f a:=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  filter_upwards [transportedForm_fixed f p a b,small] with r hr hs
  rw [hr]
  change nativeIntegral f a b r+coframeIntegral f a b r+fixedFiber (diagonalFiber p) f a b r=_
  rw [nativeIntegral_fixed f a b r hs,coframeIntegral_fixed f a b r hs]
  rfl

theorem complete_first_source (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (transportedJets f p a b).first 0=(completeJets f p a b).first 0 :=
  (transportedJets f p a b).actual.1.unique
    ((completeJets f p a b).actual.1.congr_of_eventuallyEq (completeForm_source f p a b))

theorem complete_second_source (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (transportedJets f p a b).second=(completeJets f p a b).second :=
  (transportedJets f p a b).actual.2.unique
    ((completeJets f p a b).actual.2.congr_of_eventuallyEq (completeForm_source f p a b).deriv)

theorem compression_complete_source (f : Field289) (p : PhysicalMomentum) (F : Index) :
    transportedCompression f p F=ᶠ[𝓝 0] fun r=>sourceAssembly p F
      (fun i j=>completeForm f p (bareTest p F i) (bareTest p F j) r) :=by
  have all:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr
    (fun j=>completeForm_source f p (bareTest p F i) (bareTest p F j)))
  filter_upwards [all] with r hr
  exact congrArg (sourceAssembly p F) (funext (fun i=>funext (fun j=>hr i j)))

def completeCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) : H→L[ℂ] H:=
  sourceAssembly p F (fun i j=>(completeJets f p (bareTest p F i) (bareTest p F j)).first 0)+sourceYJet f p F o 1 0

def completeContact (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) : H→L[ℂ] H:=
  sourceAssembly p F (fun i j=>(completeJets f p (bareTest p F i) (bareTest p F j)).second)+sourceYJet f p F o 2 0

theorem sourceCurrent_complete (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) :
    PreparationVacuumUncutYukawa.sourceCurrent f p F o 0=completeCurrent f p F o :=by
  unfold PreparationVacuumUncutYukawa.sourceCurrent completeCurrent transportedCurrent
  congr 1
  apply congrArg (sourceAssembly p F);funext i j
  exact complete_first_source f p _ _

theorem sourceContact_complete (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) :
    PreparationVacuumUncutYukawa.sourceContact f p F o=completeContact f p F o :=by
  unfold PreparationVacuumUncutYukawa.sourceContact completeContact transportedContact
  congr 1
  apply congrArg (sourceAssembly p F);funext i j
  exact complete_second_source f p _ _

def completeInverseContact (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) : H→L[ℂ] H:=
  -(sourceResolvent f p F o z 0*completeContact f p F o*sourceResolvent f p F o z 0-
    sourceResolvent f p F o z 0*completeCurrent f p F o*sourceResolvent f p F o z 0*completeCurrent f p F o*sourceResolvent f p F o z 0-
    sourceResolvent f p F o z 0*completeCurrent f p F o*sourceResolvent f p F o z 0*completeCurrent f p F o*sourceResolvent f p F o z 0)

theorem sourceInverseContact_complete (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) :
    sourceInverseContact f p F o z=completeInverseContact f p F o z :=by
  simp only [sourceInverseContact,sourceContact_complete,sourceCurrent_complete,completeInverseContact]

attribute [local irreducible] completeCurrent completeContact completeInverseContact sourceProfile sourceResolvent observedResponse

def completeSlope (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (o : Option ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) : ℂ:=
  -inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    ((sourceResolvent f p F o z 0*completeCurrent f p F o*sourceResolvent f p F o z 0)
      (completedLeg right b t (sourceProfile epsilon precision)))

theorem observed_complete_first (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (observedResponse epsilon precision f p F o z left right a s b t)
      (completeSlope epsilon precision f p F o z left right a s b t) 0 :=by
  have h:=(observedJets epsilon precision f p F o z hz left right a s b t).actual.1
  simpa only [observedJets,sourceInsertion,sourceCurrent_complete,neg_apply,inner_neg_right,completeSlope] using h

theorem observed_complete_second (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (deriv (observedResponse epsilon precision f p F o z left right a s b t))
      (inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        (completeInverseContact f p F o z (completedLeg right b t (sourceProfile epsilon precision)))) 0 :=by
  rw [←sourceInverseContact_complete]
  have h:=(observedJets epsilon precision f p F o z hz left right a s b t).actual.2
  exact h

theorem curvature_complete_first (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (observedCurvature epsilon precision sourceMomentum row p F o z left right a s b t)
      (completeSlope epsilon precision (readerReal sourceMomentum row) p F o z left right a s b t+
        Complex.I*completeSlope epsilon precision (readerImag sourceMomentum row) p F o z left right a s b t) 0 :=by
  unfold observedCurvature
  have realPart:=observed_complete_first epsilon precision (readerReal sourceMomentum row) p F o z hz left right a s b t
  have imagPart:=observed_complete_first epsilon precision (readerImag sourceMomentum row) p F o z hz left right a s b t
  have h:=realPart.add ((imagPart.sub_const
    (observedResponse epsilon precision (readerImag sourceMomentum row) p F o z left right a s b t 0)).const_mul Complex.I)
  exact h

end LowEnergy.PreparationVacuumSpatialDensityTransport
