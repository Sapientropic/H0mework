import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationActionCurveConsumer

set_option autoImplicit false
set_option maxHeartbeats 600000
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

-- A source coordinate changes the actual coefficient; the quantum test and its jet stay at z.
def sampledMomentum (v : Ambient) (test : QuantumTest) (z x : SourceCoordinateSlice) : FockFiber :=
  (-Complex.I) • (fderiv ℝ test z (direction v x)+connection v x (test z))

theorem sampledMomentum_source (v : Ambient) (test : QuantumTest) (z : SourceCoordinateSlice) :
    sampledMomentum v test z z=covariantMomentum v test z := rfl

def inverseFirst (h x : SourceCoordinateSlice) : Ambient →L[ℝ] Split :=
  -(inverseL x).comp ((variationL h).comp (inverseL x))

theorem inverseFirst_source (h : SourceCoordinateSlice) (x : physicalChart) :
    fderiv ℝ inverseL x.val h=inverseFirst h x.val := by
  apply ContinuousLinearMap.ext
  intro v
  exact inverse_derivative x h v

theorem inverse_curve_first (h : SourceCoordinateSlice) (x : physicalChart) :
    HasDerivAt (fun r : ℝ=>inverseL (x.val+r • h)) (inverseFirst h x.val) 0 := by
  have path : HasDerivAt (fun r : ℝ=>x.val+r • h) h 0 := by
    convert! (hasDerivAt_const (0:ℝ) x.val).add ((hasDerivAt_id (0:ℝ)).smul_const h) using 1
    simp only [zero_add,one_smul]
  have generated:=(inverse_smooth x).differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 path (by simp)
  rw [inverseFirst_source] at generated
  exact generated

def inverseSecond (h k x : SourceCoordinateSlice) : Ambient →L[ℝ] Split :=
  (inverseL x).comp ((variationL h).comp ((inverseL x).comp ((variationL k).comp (inverseL x))))+
  (inverseL x).comp ((variationL k).comp ((inverseL x).comp ((variationL h).comp (inverseL x))))

theorem inverse_curve_second (h : SourceCoordinateSlice) (x : physicalChart) :
    HasDerivAt (fun r : ℝ=>inverseFirst h (x.val+r • h)) (inverseSecond h h x.val) 0 := by
  have first:=inverse_curve_first h x
  have generated:=(first.clm_comp ((hasDerivAt_const (0:ℝ) (variationL h)).clm_comp first)).neg
  simp only [zero_smul,add_zero] at generated
  convert! generated using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [inverseFirst,inverseSecond,ContinuousLinearMap.comp_apply,
      neg_apply,add_apply,map_neg,zero_apply,zero_add]
  abel

def sampledMomentumFirst (h : SourceCoordinateSlice) (v : Ambient) (test : QuantumTest)
    (z x : SourceCoordinateSlice) : FockFiber :=
  (-Complex.I) • (fderiv ℝ test z (0,(inverseFirst h x v).2)+
    GaussNativeMatter.nativeFock (inverseFirst h x v).1 (test z))

def splitRead (test : QuantumTest) (z : SourceCoordinateSlice) : Split →L[ℝ] FockFiber :=
  (-Complex.I) • (((fderiv ℝ test z).comp (ContinuousLinearMap.inr ℝ Coframe Slice)).comp
    (ContinuousLinearMap.snd ℝ NativeLie Slice)+
    (((ContinuousLinearMap.apply ℂ FockFiber (test z)).restrictScalars ℝ).comp
      GaussNativeMatter.nativeFock.toContinuousLinearMap).comp
        (ContinuousLinearMap.fst ℝ NativeLie Slice))

def momentumRead (v : Ambient) (test : QuantumTest) (z : SourceCoordinateSlice) :
    (Ambient →L[ℝ] Split) →L[ℝ] FockFiber :=
  (splitRead test z).comp (ContinuousLinearMap.apply ℝ Split v)

theorem sampledMomentum_smooth (v : Ambient) (test : QuantumTest) (z : SourceCoordinateSlice)
    (x : physicalChart) : ContDiffAt ℝ ∞ (sampledMomentum v test z) x.val := by
  have hm : ContDiff ℝ ∞ (momentumRead v test z) := ContinuousLinearMap.contDiff _
  convert! hm.contDiffAt.comp x.val (inverse_smooth x) using 1

theorem sampledMomentum_curve_first (h : SourceCoordinateSlice) (v : Ambient) (test : QuantumTest)
    (z : SourceCoordinateSlice) (x : physicalChart) :
    HasDerivAt (fun r : ℝ=>sampledMomentum v test z (x.val+r • h))
      (sampledMomentumFirst h v test z x.val) 0 := by
  have hv:=(inverse_curve_first h x).clm_apply (hasDerivAt_const (0:ℝ) v)
  simp only [zero_smul,add_zero,map_zero] at hv
  have hs : HasFDerivAt (splitRead test z) (splitRead test z) (inverseL x.val v) :=
    (splitRead test z).hasFDerivAt
  have generated:=hs.comp_hasDerivAt_of_eq 0 hv (by simp only [zero_smul,add_zero])
  convert! generated using 1

def pairSample (x : SourceCoordinateSlice) (u v : FockFiber) : ℂ :=
  ∑ word : Occupation,complexDensity word.card x*star (u word)*v word

theorem pairSample_source (f g : QuantumTest) (z : SourceCoordinateSlice) :
    pairSample z (f z) (g z)=densityPair f g z := (densityPair_sum f g z).symm

def nativeSample (f g : QuantumTest) (z x : SourceCoordinateSlice) : ℂ :=
  (1/2:ℂ)*(∑ a : GaussNativeForm.ScalarIndex,
    pairSample x (sampledMomentum (GaussNativeForm.scalarDirection a) f z x)
      ((scalarWeight x:ℂ) • sampledMomentum (GaussNativeForm.scalarDirection a) g z x))+
  (1/2:ℂ)*(∑ a : GaussNativeForm.LieIndex,∑ i : Fin 3,∑ j : Fin 3,
    pairSample x (sampledMomentum (GaussNativeForm.gaugeDirection i a) f z x)
      ((gaugeWeight x i j:ℂ) • sampledMomentum (GaussNativeForm.gaugeDirection j a) g z x))+
  pairSample x (f z) ((potential x:ℂ) • g z)

section Param
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sampledMomentum_param (v : Ambient) (test : QuantumTest)
    (X Z : E→SourceCoordinateSlice) (w : E) (hx : X w∈physicalChart)
    (hX : ContDiffAt ℝ ∞ X w) (hZ : ContDiffAt ℝ ∞ Z w) :
    ContDiffAt ℝ ∞ (fun u=>sampledMomentum v test (Z u) (X u)) w := by
  have d:=(test.contDiff.fderiv_right (m:=∞) (by simp)).contDiffAt.comp w hZ
  have a:=(direction_smooth v ⟨X w,hx⟩).comp w hX
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have c:=R.contDiff.contDiffAt.comp w ((connection_smooth v ⟨X w,hx⟩).comp w hX)
  exact ((d.clm_apply a).add (c.clm_apply (test.contDiff.contDiffAt.comp w hZ))).const_smul (-Complex.I)

theorem pairSample_param (X : E→SourceCoordinateSlice) (U V : E→FockFiber) (w : E)
    (hx : X w∈physicalChart) (hX : ContDiffAt ℝ ∞ X w)
    (hU : ContDiffAt ℝ ∞ U w) (hV : ContDiffAt ℝ ∞ V w) :
    ContDiffAt ℝ ∞ (fun u=>pairSample (X u) (U u) (V u)) w := by
  apply ContDiffAt.sum
  intro word _
  let P : FockFiber →L[ℝ] ℂ :=(PiLp.proj (𝕜:=ℂ) 2 (fun _ : Occupation=>ℂ) word).restrictScalars ℝ
  have hu:=P.contDiff.contDiffAt.comp w hU
  have hv:=P.contDiff.contDiffAt.comp w hV
  let C : ℂ →L[ℝ] ℂ := (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
  have hs:=C.contDiff.contDiffAt.comp w hu
  exact (((complexDensity_smooth word.card ⟨X w,hx⟩).comp w hX).mul hs).mul hv

theorem nativeSample_param (f g : QuantumTest) (X Z : E→SourceCoordinateSlice) (w : E)
    (hx : X w∈physicalChart) (hX : ContDiffAt ℝ ∞ X w) (hZ : ContDiffAt ℝ ∞ Z w) :
    ContDiffAt ℝ ∞ (fun u=>nativeSample f g (Z u) (X u)) w := by
  have c (a : SourceCoordinateSlice→ℝ) (ha : ContDiffAt ℝ ∞ a (X w)) :
      ContDiffAt ℝ ∞ (fun u=>(a (X u):ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ha.comp w hX)
  have term (v v' : Ambient) (a : SourceCoordinateSlice→ℝ) (ha : ContDiffAt ℝ ∞ a (X w)) :
      ContDiffAt ℝ ∞ (fun u=>pairSample (X u) (sampledMomentum v f (Z u) (X u))
        ((a (X u):ℂ) • sampledMomentum v' g (Z u) (X u))) w :=
    pairSample_param X _ _ w hx hX (sampledMomentum_param v f X Z w hx hX hZ)
      ((c a ha).smul (sampledMomentum_param v' g X Z w hx hX hZ))
  unfold nativeSample
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · apply ContDiffAt.mul contDiffAt_const
      apply ContDiffAt.sum
      intro a _
      exact term _ _ scalarWeight (scalarWeight_smooth ⟨X w,hx⟩)
    · apply ContDiffAt.mul contDiffAt_const
      apply ContDiffAt.sum
      intro a _
      apply ContDiffAt.sum
      intro i _
      apply ContDiffAt.sum
      intro j _
      exact term _ _ (fun x=>gaugeWeight x i j) (gaugeWeight_smooth i j ⟨X w,hx⟩)
  · exact pairSample_param X _ _ w hx hX (f.contDiff.contDiffAt.comp w hZ)
      ((c potential (potential_smooth ⟨X w,hx⟩)).smul (g.contDiff.contDiffAt.comp w hZ))
end Param

theorem pairSample_zero_left (x : SourceCoordinateSlice) (v : FockFiber) : pairSample x 0 v=0 := by
  simp [pairSample]

theorem sampledMomentum_zero_outside (v : Ambient) (f : QuantumTest) (z x : SourceCoordinateSlice)
    (outside : z∉tsupport f) : sampledMomentum v f z x=0 := by
  rw [sampledMomentum,fderiv_of_notMem_tsupport ℝ outside,image_eq_zero_of_notMem_tsupport outside]
  simp

theorem nativeSample_zero_outside (f g : QuantumTest) (z x : SourceCoordinateSlice)
    (outside : z∉tsupport f) : nativeSample f g z x=0 := by
  simp only [nativeSample,sampledMomentum_zero_outside _ f z x outside,
    image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left,Finset.sum_const_zero,mul_zero,add_zero]

private theorem density_sandwich (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) (z : SourceCoordinateSlice) :
    pairSample z (sampledMomentum v f z z) ((c z:ℂ) • sampledMomentum w g z z)=
      densityPair (covariantMomentum v f) (GaussNativeForm.multiply c hc (covariantMomentum w g)) z := by
  rw [←pairSample_source,sampledMomentum_source,sampledMomentum_source]
  rfl

def nativeScalarTerm (f g : QuantumTest) (a : GaussNativeForm.ScalarIndex) : SourceCoordinateSlice→ℂ :=
  fun z=>densityPair (covariantMomentum (GaussNativeForm.scalarDirection a) f)
    (GaussNativeForm.multiply scalarWeight scalarWeight_smooth
      (covariantMomentum (GaussNativeForm.scalarDirection a) g)) z

def nativeGaugeTerm (f g : QuantumTest) (a : GaussNativeForm.LieIndex) (i j : Fin 3) : SourceCoordinateSlice→ℂ :=
  fun z=>densityPair (covariantMomentum (GaussNativeForm.gaugeDirection i a) f)
    (GaussNativeForm.multiply (fun x=>gaugeWeight x i j) (gaugeWeight_smooth i j)
      (covariantMomentum (GaussNativeForm.gaugeDirection j a) g)) z

theorem nativeSample_diagonal (f g : QuantumTest) (z : SourceCoordinateSlice) :
    nativeSample f g z z=(1/2:ℂ)*(∑ a,nativeScalarTerm f g a z)+
      (1/2:ℂ)*(∑ a,∑ i,∑ j,nativeGaugeTerm f g a i j z)+
      densityPair f (GaussNativeForm.multiply potential potential_smooth g) z := by
  have scalar a:=density_sandwich (GaussNativeForm.scalarDirection a)
    (GaussNativeForm.scalarDirection a) scalarWeight scalarWeight_smooth f g z
  have gauge a i j:=density_sandwich (GaussNativeForm.gaugeDirection i a)
    (GaussNativeForm.gaugeDirection j a) (fun x=>gaugeWeight x i j) (gaugeWeight_smooth i j) f g z
  simp only [nativeSample,nativeScalarTerm,nativeGaugeTerm]
  simp_rw [scalar,gauge]
  congr 1
  rw [←pairSample_source]
  rfl

theorem nativeSample_integrable (f g : QuantumTest) :
    Integrable (fun z=>nativeSample f g z z) GaussHistoryHilbert.configurationMeasure := by
  have scalar : Integrable (fun z=>(1/2:ℂ)*∑ a,nativeScalarTerm f g a z) GaussHistoryHilbert.configurationMeasure :=
    (integrable_finsetSum Finset.univ (fun _ _=>densityPair_integrable _ _)).const_mul _
  have gauge : Integrable (fun z=>(1/2:ℂ)*∑ a,∑ i,∑ j,nativeGaugeTerm f g a i j z) GaussHistoryHilbert.configurationMeasure :=
    (integrable_finsetSum Finset.univ (fun _ _=>integrable_finsetSum Finset.univ (fun _ _=>
      integrable_finsetSum Finset.univ (fun _ _=>densityPair_integrable _ _)))).const_mul _
  exact ((scalar.add gauge).add (densityPair_integrable _ _)).congr
    (Filter.Eventually.of_forall fun z=>(nativeSample_diagonal f g z).symm)

theorem integral_add_three (A B C : SourceCoordinateSlice→ℂ)
    (hA : Integrable A GaussHistoryHilbert.configurationMeasure)
    (hB : Integrable B GaussHistoryHilbert.configurationMeasure)
    (hC : Integrable C GaussHistoryHilbert.configurationMeasure) :
    (∫ z,A z+B z+C z ∂GaussHistoryHilbert.configurationMeasure)=
      (∫ z,A z ∂GaussHistoryHilbert.configurationMeasure)+
      (∫ z,B z ∂GaussHistoryHilbert.configurationMeasure)+
      (∫ z,C z ∂GaussHistoryHilbert.configurationMeasure) :=
  (integral_add (hA.add hB) hC).trans (congrArg (fun v=>v+∫ z,C z ∂GaussHistoryHilbert.configurationMeasure)
    (integral_add hA hB))

private theorem pair_add (f g h : QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul (c : ℂ) (f g : QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sum {ι : Type*} [Fintype ι] (f : QuantumTest) (g : ι→QuantumTest) :
    sourcePair f (∑ i,g i)=∑ i,sourcePair f (g i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem sandwich_pair_read (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourcePair f (GaussNativeForm.sandwich v w c hc g)=
      sourcePair (covariantMomentum v f) (GaussNativeForm.multiply c hc (covariantMomentum w g)) :=
  GaussNativeForm.adjoint_pair v f _

theorem native_form_source (f g : QuantumTest) :
    (∫ z,nativeSample f g z z ∂GaussHistoryHilbert.configurationMeasure)=sourcePair f (GaussNativeForm.nativeAction g) := by
  have scalar a : Integrable (nativeScalarTerm f g a) GaussHistoryHilbert.configurationMeasure:=densityPair_integrable _ _
  have gauge a i j : Integrable (nativeGaugeTerm f g a i j) GaussHistoryHilbert.configurationMeasure:=densityPair_integrable _ _
  have hS : Integrable (fun z=>(1/2:ℂ)*∑ a,nativeScalarTerm f g a z) GaussHistoryHilbert.configurationMeasure :=
    (integrable_finsetSum Finset.univ fun a _=>scalar a).const_mul _
  have hG : Integrable (fun z=>(1/2:ℂ)*∑ a,∑ i,∑ j,nativeGaugeTerm f g a i j z) GaussHistoryHilbert.configurationMeasure :=
    (integrable_finsetSum Finset.univ fun a _=>integrable_finsetSum Finset.univ fun i _=>
      integrable_finsetSum Finset.univ fun j _=>gauge a i j).const_mul _
  simp_rw [nativeSample_diagonal]
  rw [integral_add_three _ _ _ hS hG (densityPair_integrable f (GaussNativeForm.multiply potential potential_smooth g)),
    integral_const_mul,integral_const_mul,
    integral_finsetSum Finset.univ (fun a _=>scalar a),
    integral_finsetSum Finset.univ (fun a _=>integrable_finsetSum Finset.univ fun i _=>
      integrable_finsetSum Finset.univ fun j _=>gauge a i j)]
  simp_rw [integral_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ fun j _=>gauge _ i j),
    integral_finsetSum Finset.univ (fun j _=>gauge _ _ j),nativeScalarTerm,nativeGaugeTerm,←sourcePair_integral]
  simp only [GaussNativeForm.nativeAction,GaussNativeForm.scalarKinetic,GaussNativeForm.gaugeKinetic,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,pair_add,pair_smul,pair_sum,sandwich_pair_read]

end LowEnergy.PreparationVacuumSourceActionJets
