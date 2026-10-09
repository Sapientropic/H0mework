import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGradedSourceForm

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumGradedTransport
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair GaussDensityCore
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn PreparationVacuumSourceActionJets
open CanonicalPreparationCore PreparationVacuumFullFieldRiesz
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators Distributions

def transportedSection (f : Field289) (a : QuantumTest) (u : Parameter) : FockFiber :=
  transportFiber f u.2 u.1 (a u.2)

theorem halfRatio_param_smooth (f : Field289) (N : ℕ) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v : Parameter=>halfRatio f N v.2 v.1) u := by
  have base :=(coreHalfDensity_smooth N ⟨_,hz⟩).comp u contDiffAt_snd
  have moved :=(coreHalfDensity_smooth N ⟨_,hx⟩).comp u (field_curve_smooth f u.1 ⟨_,hz⟩)
  convert! base.mul (moved.inv (coreHalfDensity_ne_zero N ⟨_,hx⟩)) using 1

theorem transportedSection_smooth (f : Field289) (a : QuantumTest) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (transportedSection f a) u := by
  apply (contDiffAt_piLp 2).mpr
  intro word
  let P : FockFiber →L[ℝ] ℂ :=(PiLp.proj (𝕜:=ℂ) 2 (fun _ : Occupation=>ℂ) word).restrictScalars ℝ
  exact (halfRatio_param_smooth f word.card u hz hx).mul
    (P.contDiff.contDiffAt.comp u (a.contDiff.contDiffAt.comp u contDiffAt_snd))

theorem transportedSection_zero_outside (f : Field289) (a : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : transportedSection f a (r,z)=0 := by
  unfold transportedSection
  rw [image_eq_zero_of_notMem_tsupport outside,map_zero]

theorem transportedSection_full_smooth (f : Field289) (a : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice)
    (small : |r|<fieldRadius f a) : ContDiffAt ℝ ∞ (transportedSection f a) (r,z) := by
  by_cases inside : z∈tsupport a
  · exact transportedSection_smooth f a (r,z) (a.tsupport_subset inside)
      (fieldRadius_chart f a r z small.le inside)
  · apply (contDiffAt_const (c:=(0:FockFiber))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isClosed_tsupport a |>.isOpen_compl.mem_nhds inside)] with u hu
    exact transportedSection_zero_outside f a u.1 u.2 hu

def certifiedTransportTest (f : Field289) (a : QuantumTest) (r : ℝ) (small : |r|<fieldRadius f a) : QuantumTest where
  toFun z:=transportedSection f a (r,z)
  contDiff':=by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (transportedSection_full_smooth f a r z small).comp z (contDiff_const.prodMk contDiff_id).contDiffAt
  hasCompactSupport':=by
    apply a.hasCompactSupport.of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_tsupport a)
    intro z hz
    by_contra outside
    exact hz (transportedSection_zero_outside f a r z outside)
  tsupport_subset':=by
    apply Set.Subset.trans _ a.tsupport_subset
    apply closure_minimal _ (isClosed_tsupport a)
    intro z hz
    by_contra outside
    exact hz (transportedSection_zero_outside f a r z outside)

def transportTest (f : Field289) (a : QuantumTest) (r : ℝ) : QuantumTest :=
  if h : |r|<fieldRadius f a then certifiedTransportTest f a r h else a

theorem transportTest_apply (f : Field289) (a : QuantumTest) (r : ℝ)
    (small : |r|<fieldRadius f a) (z : SourceCoordinateSlice) :
    transportTest f a r z=transportedSection f a (r,z) := by
  rw [transportTest,dif_pos small]; rfl

theorem transportedSection_zero (f : Field289) (a : QuantumTest) (z : SourceCoordinateSlice) :
    transportedSection f a (0,z)=a z := by
  by_cases hz : z∈physicalChart
  · apply PiLp.ext; intro word
    change halfRatio f word.card z 0*a z word=a z word
    rw [halfRatio_zero f word.card ⟨z,hz⟩,one_mul]
  · have outside : z∉tsupport a:=fun h=>hz (a.tsupport_subset h)
    rw [transportedSection_zero_outside f a 0 z outside,image_eq_zero_of_notMem_tsupport outside]

theorem transportTest_zero (f : Field289) (a : QuantumTest) : transportTest f a 0=a := by
  apply DFunLike.ext; intro z
  rw [transportTest_apply f a 0 (by simpa using fieldRadius_positive f a),transportedSection_zero]

def spatialJet (U : Parameter → FockFiber) (u : Parameter) (v : SourceCoordinateSlice) : FockFiber :=
  fderiv ℝ U u (0,v)

theorem transportTest_spatial (f : Field289) (a : QuantumTest) (r : ℝ)
    (small : |r|<fieldRadius f a) (z v : SourceCoordinateSlice) :
    fderiv ℝ (transportTest f a r) z v=spatialJet (transportedSection f a) (r,z) v := by
  have equal : (⇑(transportTest f a r):SourceCoordinateSlice→FockFiber)=fun w=>transportedSection f a (r,w) :=
    funext (transportTest_apply f a r small)
  rw [equal]
  have joint :=((transportedSection_full_smooth f a r z small).differentiableAt (by simp)).hasFDerivAt
  have h:=joint.comp z ((hasFDerivAt_const r z).prodMk (hasFDerivAt_id z))
  change (fderiv ℝ (transportedSection f a ∘ Prod.mk r) z) v=_
  rw [h.fderiv]
  rfl

open GaussNativeEnergy GaussNativePotential GaussLiveMomentum GaussCoframeForm
open CanonicalGradedSpatialSource PreparationVacuumActionDecomposition PreparationVacuumSourceFieldFamily

def movingMomentum (f : Field289) (U : Parameter → FockFiber) (v : Ambient) (u : Parameter) : FockFiber :=
  (-Complex.I) • (spatialJet U u (direction v (fieldCoordinateCurve f u.1 u.2))+
    connection v (fieldCoordinateCurve f u.1 u.2) (U u))

def movingCoframe (U : Parameter → FockFiber) (i : Fin 6) (u : Parameter) : FockFiber :=
  (-Complex.I) • spatialJet U u (GaussCoframeCore.coframeDirection i)

def movingSpin (U : Parameter → FockFiber) (k : Fin 7) (u : Parameter) : FockFiber :=
  GaussQuantumMultiplier.quantized (GaussCoframeSpin.full k) (U u)

def movingNumber (U : Parameter → FockFiber) (u : Parameter) : FockFiber :=
  SourceQuantumFockGauge.fiberNumber (U u)

def movingPair (f : Field289) (U V : Parameter → FockFiber) (c : SourceCoordinateSlice → ℝ) (u : Parameter) : ℂ :=
  pairSample (fieldCoordinateCurve f u.1 u.2) (U u) ((c (fieldCoordinateCurve f u.1 u.2):ℂ) • V u)

def movingFiber (f : Field289) (U V : Parameter → FockFiber) (A : SourceCoordinateSlice → FiberMap) (u : Parameter) : ℂ :=
  pairSample (fieldCoordinateCurve f u.1 u.2) (U u) (A (fieldCoordinateCurve f u.1 u.2) (V u))

def movingNative (f : Field289) (U V : Parameter → FockFiber) (u : Parameter) : ℂ :=
  (1/2:ℂ)*(∑i : GaussNativeForm.ScalarIndex,movingPair f
    (movingMomentum f U (GaussNativeForm.scalarDirection i)) (movingMomentum f V (GaussNativeForm.scalarDirection i)) scalarWeight u)+
  (1/2:ℂ)*(∑a : GaussNativeForm.LieIndex,∑i : Fin 3,∑j : Fin 3,movingPair f
    (movingMomentum f U (GaussNativeForm.gaugeDirection i a)) (movingMomentum f V (GaussNativeForm.gaugeDirection j a))
      (fun z=>gaugeWeight z i j) u)+movingPair f U V potential u

def movingMixed (f : Field289) (U V : Parameter → FockFiber) (i : Fin 6) (k : Fin 7)
    (c : SourceCoordinateSlice → ℝ) (u : Parameter) : ℂ :=
  (1/2:ℂ)*(movingPair f (movingSpin U k) (movingCoframe V i) c u+
    movingPair f (movingCoframe U i) (movingSpin V k) c u)

def movingCoframeForm (f : Field289) (U V : Parameter → FockFiber) (u : Parameter) : ℂ :=
  (∑i : Fin 6,∑j : Fin 6,movingPair f (movingCoframe U i) (movingCoframe V j) (GaussCoframeKinetic.coefficient i j) u)+
  (movingMixed f U V 1 5 (currentCoefficient 0) u+movingMixed f U V 3 3 (currentCoefficient 1) u+
    movingMixed f U V 3 4 (fun z=>-currentCoefficient 0 z) u+movingMixed f U V 4 3 (currentCoefficient 2) u)+
  (∑k : Fin 7,(spinWeight k:ℂ)*movingPair f (movingSpin U k) (movingSpin V k) inverseVolume u)+
  (1/2:ℂ)*(movingPair f (movingNumber U) V numberCoefficient u+movingPair f U (movingNumber V) numberCoefficient u)+
  movingPair f U V volumePotential u

def movingPhysical (f : Field289) (p : PhysicalMomentum) (U V : Parameter → FockFiber) (u : Parameter) : ℂ :=
  movingNative f U V u+movingCoframeForm f U V u+movingFiber f U V (actualFiber p) u-
    movingFiber f U V retainedCoefficient u-
    movingFiber f U V (fun z=>GaussYukawaCoefficient.sourceMap (scalarField z)) u

theorem spatialJet_smooth (U : Parameter → FockFiber) (V : Parameter → SourceCoordinateSlice) (u : Parameter)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun v=>spatialJet U v (V v)) u :=
  (hU.fderiv_right (m:=∞) (by simp)).clm_apply (contDiffAt_const.prodMk hV)

theorem movingMomentum_smooth (f : Field289) (U : Parameter → FockFiber) (v : Ambient) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) : ContDiffAt ℝ ∞ (movingMomentum f U v) u := by
  have hX:=field_curve_smooth f u.1 ⟨_,hz⟩
  have d:=spatialJet_smooth U _ u hU ((direction_smooth v ⟨_,hx⟩).comp u hX)
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have c:=R.contDiff.contDiffAt.comp u ((connection_smooth v ⟨_,hx⟩).comp u hX)
  exact (d.add (c.clm_apply hU)).const_smul (-Complex.I)

theorem movingCoframe_smooth (U : Parameter → FockFiber) (i : Fin 6) (u : Parameter)
    (hU : ContDiffAt ℝ ∞ U u) : ContDiffAt ℝ ∞ (movingCoframe U i) u :=
  (spatialJet_smooth U _ u hU contDiffAt_const).const_smul (-Complex.I)

theorem movingSpin_smooth (U : Parameter → FockFiber) (k : Fin 7) (u : Parameter)
    (hU : ContDiffAt ℝ ∞ U u) : ContDiffAt ℝ ∞ (movingSpin U k) u :=
  ((GaussQuantumMultiplier.quantized (GaussCoframeSpin.full k)).restrictScalars ℝ).contDiff.contDiffAt.comp u hU

theorem movingNumber_smooth (U : Parameter → FockFiber) (u : Parameter)
    (hU : ContDiffAt ℝ ∞ U u) : ContDiffAt ℝ ∞ (movingNumber U) u :=
  (SourceQuantumFockGauge.fiberNumber.restrictScalars ℝ).contDiff.contDiffAt.comp u hU

theorem movingPair_smooth (f : Field289) (U V : Parameter → FockFiber) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) : ContDiffAt ℝ ∞ (movingPair f U V c) u := by
  have hX:=field_curve_smooth f u.1 ⟨_,hz⟩
  have coeff:=Complex.ofRealCLM.contDiff.contDiffAt.comp u ((hc ⟨_,hx⟩).comp u hX)
  exact pairSample_param _ U _ u hx hX hU (coeff.smul hV)

theorem movingFiber_smooth (f : Field289) (U V : Parameter → FockFiber) (A : SourceCoordinateSlice → FiberMap)
    (hA : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) : ContDiffAt ℝ ∞ (movingFiber f U V A) u := by
  have hX:=field_curve_smooth f u.1 ⟨_,hz⟩
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have coeff:=R.contDiff.contDiffAt.comp u ((hA ⟨_,hx⟩).comp u hX)
  exact pairSample_param _ U _ u hx hX hU (coeff.clm_apply hV)

theorem movingNative_smooth (f : Field289) (U V : Parameter → FockFiber) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) : ContDiffAt ℝ ∞ (movingNative f U V) u := by
  have first:=ContDiffAt.sum (s:=Finset.univ) (fun (i : GaussNativeForm.ScalarIndex) _=>
    movingPair_smooth f _ _ scalarWeight scalarWeight_smooth u hz hx
      (movingMomentum_smooth f U (GaussNativeForm.scalarDirection i) u hz hx hU)
      (movingMomentum_smooth f V (GaussNativeForm.scalarDirection i) u hz hx hV))
  have second:=ContDiffAt.sum (s:=Finset.univ) (fun (a : GaussNativeForm.LieIndex) _=>ContDiffAt.sum (s:=Finset.univ) (fun (i : Fin 3) _=>
    ContDiffAt.sum (s:=Finset.univ) (fun (j : Fin 3) _=>movingPair_smooth f _ _ (fun z=>gaugeWeight z i j)
      (fun z=>gaugeWeight_smooth i j z) u hz hx
      (movingMomentum_smooth f U (GaussNativeForm.gaugeDirection i a) u hz hx hU)
      (movingMomentum_smooth f V (GaussNativeForm.gaugeDirection j a) u hz hx hV))))
  exact ((contDiffAt_const.mul first).add (contDiffAt_const.mul second)).add
    (movingPair_smooth f U V potential potential_smooth u hz hx hU hV)

theorem movingMixed_smooth (f : Field289) (U V : Parameter → FockFiber) (i : Fin 6) (k : Fin 7)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) : ContDiffAt ℝ ∞ (movingMixed f U V i k c) u :=
  contDiffAt_const.mul ((movingPair_smooth f _ _ c hc u hz hx (movingSpin_smooth U k u hU) (movingCoframe_smooth V i u hV)).add
    (movingPair_smooth f _ _ c hc u hz hx (movingCoframe_smooth U i u hU) (movingSpin_smooth V k u hV)))

theorem movingCoframeForm_smooth (f : Field289) (U V : Parameter → FockFiber) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) : ContDiffAt ℝ ∞ (movingCoframeForm f U V) u := by
  have kin:=ContDiffAt.sum (s:=Finset.univ) (fun (i : Fin 6) _=>ContDiffAt.sum (s:=Finset.univ) (fun (j : Fin 6) _=>
    movingPair_smooth f _ _ _ (GaussCoframeKinetic.coefficient_smooth i j) u hz hx
      (movingCoframe_smooth U i u hU) (movingCoframe_smooth V j u hV)))
  have cur:=(((movingMixed_smooth f U V 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0) u hz hx hU hV).add
    (movingMixed_smooth f U V 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1) u hz hx hU hV)).add
    (movingMixed_smooth f U V 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg) u hz hx hU hV)).add
    (movingMixed_smooth f U V 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2) u hz hx hU hV)
  have spin:=ContDiffAt.sum (s:=Finset.univ) (fun (k : Fin 7) _=>(contDiffAt_const (c:=(spinWeight k:ℂ))).mul
    (movingPair_smooth f _ _ inverseVolume inverseVolume_smooth u hz hx (movingSpin_smooth U k u hU) (movingSpin_smooth V k u hV)))
  have num:=(contDiffAt_const (c:=(1/2:ℂ))).mul ((movingPair_smooth f _ _ numberCoefficient numberCoefficient_smooth u hz hx
    (movingNumber_smooth U u hU) hV).add (movingPair_smooth f _ _ numberCoefficient numberCoefficient_smooth u hz hx
      hU (movingNumber_smooth V u hV)))
  exact (((kin.add cur).add spin).add num).add (movingPair_smooth f U V volumePotential volumePotential_smooth u hz hx hU hV)

theorem movingPhysical_smooth (f : Field289) (p : PhysicalMomentum) (U V : Parameter → FockFiber) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) : ContDiffAt ℝ ∞ (movingPhysical f p U V) u :=
  ((((movingNative_smooth f U V u hz hx hU hV).add (movingCoframeForm_smooth f U V u hz hx hU hV)).add
    (movingFiber_smooth f U V (actualFiber p) (actualFiber_smooth p) u hz hx hU hV)).sub
    (movingFiber_smooth f U V retainedCoefficient retainedCoefficient_smooth u hz hx hU hV)).sub
    (movingFiber_smooth f U V _ (fun _=>(GaussYukawaCoefficient.sourceMap.contDiff.comp scalarField_smooth).contDiffAt) u hz hx hU hV)

theorem transportedSection_zero_near (f : Field289) (a : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : transportedSection f a=ᶠ[𝓝 (r,z)] fun _=>0 := by
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (isClosed_tsupport a |>.isOpen_compl.mem_nhds outside)] with u hu
  exact transportedSection_zero_outside f a u.1 u.2 hu

theorem spatialJet_zero_outside (f : Field289) (a : QuantumTest) (r : ℝ) (z v : SourceCoordinateSlice)
    (outside : z∉tsupport a) : spatialJet (transportedSection f a) (r,z) v=0 := by
  rw [spatialJet,(transportedSection_zero_near f a r z outside).fderiv_eq]
  simp

inductive SectionOp where
  | base
  | coframe (i : Fin 6)
  | spin (k : Fin 7)
  | number

def sectionValue (f : Field289) (a : QuantumTest) : SectionOp → Parameter → FockFiber
  | .base=>transportedSection f a
  | .coframe i=>movingCoframe (transportedSection f a) i
  | .spin k=>movingSpin (transportedSection f a) k
  | .number=>movingNumber (transportedSection f a)

theorem sectionValue_smooth (f : Field289) (a : QuantumTest) (op : SectionOp) (u : Parameter)
    (hz : u.2∈physicalChart) (hx : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (sectionValue f a op) u := by
  have h:=transportedSection_smooth f a u hz hx
  cases op with
  | base=>exact h
  | coframe i=>exact movingCoframe_smooth _ i u h
  | spin k=>exact movingSpin_smooth _ k u h
  | number=>exact movingNumber_smooth _ u h

theorem sectionValue_zero (f : Field289) (a : QuantumTest) (op : SectionOp) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : sectionValue f a op (r,z)=0 := by
  cases op <;> simp only [sectionValue,movingMomentum,movingCoframe,movingSpin,movingNumber,
    transportedSection_zero_outside f a r z outside,spatialJet_zero_outside f a r z _ outside,
    map_zero,zero_add,add_zero,smul_zero]

def parameterIntegralJets (S : Parameter → ℂ) (f : Field289) (a : QuantumTest)
    (smooth : ∀u : Parameter,u.2∈physicalChart → fieldCoordinateCurve f u.1 u.2∈physicalChart → ContDiffAt ℝ ∞ S u)
    (zero : ∀r z,z∉tsupport a → S (r,z)=0) :
    TwoJets (fun r=>∫z,S (r,z) ∂GaussHistoryHilbert.configurationMeasure) := by
  have full (r : ℝ) (z : SourceCoordinateSlice) (small : |r|<fieldRadius f a) : ContDiffAt ℝ ∞ S (r,z) := by
    by_cases inside : z∈tsupport a
    · exact smooth (r,z) (a.tsupport_subset inside) (fieldRadius_chart f a r z small.le inside)
    · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (isClosed_tsupport a |>.isOpen_compl.mem_nhds inside)] with u hu
      exact zero u.1 u.2 hu
  exact integralJets S (tsupport a) a.hasCompactSupport (fieldRadius f a) (fieldRadius_positive f a) full zero

def pairIntegral (f : Field289) (a b : QuantumTest) (op oq : SectionOp) (c : SourceCoordinateSlice → ℝ) (r : ℝ) : ℂ :=
  ∫z,movingPair f (sectionValue f a op) (sectionValue f b oq) c (r,z) ∂GaussHistoryHilbert.configurationMeasure

def pairIntegralJets (f : Field289) (a b : QuantumTest) (op oq : SectionOp) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : TwoJets (pairIntegral f a b op oq c) :=
  parameterIntegralJets _ f a
    (fun u hz hx=>movingPair_smooth f _ _ c hc u hz hx (sectionValue_smooth f a op u hz hx) (sectionValue_smooth f b oq u hz hx))
    (fun r z outside=>by simp only [movingPair,sectionValue_zero f a op r z outside,pairSample_zero_left])

def fiberIntegral (f : Field289) (a b : QuantumTest) (A : SourceCoordinateSlice → FiberMap) (r : ℝ) : ℂ :=
  ∫z,movingFiber f (transportedSection f a) (transportedSection f b) A (r,z) ∂GaussHistoryHilbert.configurationMeasure

def fiberIntegralJets (f : Field289) (a b : QuantumTest) (A : SourceCoordinateSlice → FiberMap)
    (hA : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) : TwoJets (fiberIntegral f a b A) :=
  parameterIntegralJets _ f a
    (fun u hz hx=>movingFiber_smooth f _ _ A hA u hz hx (transportedSection_smooth f a u hz hx) (transportedSection_smooth f b u hz hx))
    (fun r z outside=>by simp only [movingFiber,transportedSection_zero_outside f a r z outside,pairSample_zero_left])

def nativeIntegral (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ :=
  ∫z,movingNative f (transportedSection f a) (transportedSection f b) (r,z) ∂GaussHistoryHilbert.configurationMeasure

def nativeIntegralJets (f : Field289) (a b : QuantumTest) : TwoJets (nativeIntegral f a b) :=
  parameterIntegralJets _ f a
    (fun u hz hx=>movingNative_smooth f _ _ u hz hx (transportedSection_smooth f a u hz hx) (transportedSection_smooth f b u hz hx))
    (fun r z outside=>by
      simp only [movingNative,movingPair,movingMomentum,transportedSection_zero_outside f a r z outside,
        spatialJet_zero_outside f a r z _ outside,map_zero,zero_add,add_zero,smul_zero,pairSample_zero_left,
        Finset.sum_const_zero,mul_zero,zero_add])

def sectionTest : SectionOp → QuantumTest → QuantumTest
  | .base=>id
  | .coframe i=>GaussCoframeCore.momentum i
  | .spin k=>GaussCoframeSpin.current k
  | .number=>GaussCoframeForm.number

theorem sectionValue_readback (f : Field289) (a : QuantumTest) (op : SectionOp) (r : ℝ)
    (small : |r|<fieldRadius f a) (z : SourceCoordinateSlice) :
    sectionValue f a op (r,z)=sectionTest op (transportTest f a r) z := by
  cases op with
  | base=>exact (transportTest_apply f a r small z).symm
  | coframe i=>
    change (-Complex.I) • spatialJet (transportedSection f a) (r,z) (GaussCoframeCore.coframeDirection i)=
      (-Complex.I) • (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (transportTest f a r)) z
    rw [GaussCoframeCore.derivative_apply,transportTest_spatial f a r small]
  | spin k=>
    change GaussQuantumMultiplier.quantized (GaussCoframeSpin.full k) (transportedSection f a (r,z))=
      GaussQuantumMultiplier.quantized (GaussCoframeSpin.full k) (transportTest f a r z)
    rw [transportTest_apply f a r small]
  | number=>
    apply PiLp.ext; intro word
    change fiberNumber (transportedSection f a (r,z)) word=GaussCoframeForm.number (transportTest f a r) z word
    rw [fiberNumber_apply,GaussCoframeForm.number_apply,transportTest_apply f a r small]

theorem movingMomentum_readback (f : Field289) (a : QuantumTest) (v : Ambient) (r : ℝ)
    (small : |r|<fieldRadius f a) (z : SourceCoordinateSlice) :
    movingMomentum f (transportedSection f a) v (r,z)=
      sampledMomentum v (transportTest f a r) z (fieldCoordinateCurve f r z) := by
  unfold movingMomentum sampledMomentum
  rw [transportTest_spatial f a r small,transportTest_apply f a r small]

theorem pairIntegral_readback (f : Field289) (a b : QuantumTest) (op oq : SectionOp) (c : SourceCoordinateSlice → ℝ)
    (r : ℝ) (ha : |r|<fieldRadius f a) (hb : |r|<fieldRadius f b) :
    pairIntegral f a b op oq c r=rowFieldForm f c (sectionTest op (transportTest f a r)) (sectionTest oq (transportTest f b r)) r := by
  unfold pairIntegral rowFieldForm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [movingPair,rowSample,sectionValue_readback f a op r ha z,sectionValue_readback f b oq r hb z]

theorem fiberIntegral_readback (f : Field289) (a b : QuantumTest) (A : SourceCoordinateSlice → FiberMap)
    (r : ℝ) (ha : |r|<fieldRadius f a) (hb : |r|<fieldRadius f b) :
    fiberIntegral f a b A r=fiberFieldForm f A (transportTest f a r) (transportTest f b r) r := by
  unfold fiberIntegral fiberFieldForm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [movingFiber,fiberSample,transportTest_apply f a r ha z,transportTest_apply f b r hb z]

theorem nativeIntegral_readback (f : Field289) (a b : QuantumTest) (r : ℝ)
    (ha : |r|<fieldRadius f a) (hb : |r|<fieldRadius f b) :
    nativeIntegral f a b r=nativeFieldForm f (transportTest f a r) (transportTest f b r) r := by
  unfold nativeIntegral nativeFieldForm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [movingNative,movingPair,nativeSample,movingMomentum_readback f a _ r ha z,
      movingMomentum_readback f b _ r hb z,transportTest_apply f a r ha z,transportTest_apply f b r hb z]

def mixedIntegral (f : Field289) (a b : QuantumTest) (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice → ℝ) (r : ℝ) : ℂ :=
  (1/2:ℂ)*(pairIntegral f a b (.spin k) (.coframe i) c r+pairIntegral f a b (.coframe i) (.spin k) c r)

def mixedIntegralJets (f : Field289) (a b : QuantumTest) (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : TwoJets (mixedIntegral f a b i k c) :=
  TwoJets.scale (1/2) ((pairIntegralJets f a b (.spin k) (.coframe i) c hc).add
    (pairIntegralJets f a b (.coframe i) (.spin k) c hc))

def coframeIntegral (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ :=
  (∑i : Fin 6,∑j : Fin 6,pairIntegral f a b (.coframe i) (.coframe j) (GaussCoframeKinetic.coefficient i j) r)+
  (mixedIntegral f a b 1 5 (currentCoefficient 0) r+mixedIntegral f a b 3 3 (currentCoefficient 1) r+
    mixedIntegral f a b 3 4 (fun z=>-currentCoefficient 0 z) r+mixedIntegral f a b 4 3 (currentCoefficient 2) r)+
  (∑k : Fin 7,(spinWeight k:ℂ)*pairIntegral f a b (.spin k) (.spin k) inverseVolume r)+
  (1/2:ℂ)*(pairIntegral f a b .number .base numberCoefficient r+pairIntegral f a b .base .number numberCoefficient r)+
  pairIntegral f a b .base .base volumePotential r

def coframeIntegralJets (f : Field289) (a b : QuantumTest) : TwoJets (coframeIntegral f a b) := by
  let kin:=sumJets (fun i : Fin 6=>sumJets (fun j : Fin 6=>pairIntegralJets f a b (.coframe i) (.coframe j)
    _ (GaussCoframeKinetic.coefficient_smooth i j)))
  let cur:=(((mixedIntegralJets f a b 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0)).add
    (mixedIntegralJets f a b 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1))).add
    (mixedIntegralJets f a b 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg))).add
    (mixedIntegralJets f a b 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2))
  let spin:=sumJets (fun k : Fin 7=>TwoJets.scale (spinWeight k:ℂ)
    (pairIntegralJets f a b (.spin k) (.spin k) inverseVolume inverseVolume_smooth))
  let num:=TwoJets.scale (1/2) ((pairIntegralJets f a b .number .base numberCoefficient numberCoefficient_smooth).add
    (pairIntegralJets f a b .base .number numberCoefficient numberCoefficient_smooth))
  exact (((kin.add cur).add spin).add num).add (pairIntegralJets f a b .base .base volumePotential volumePotential_smooth)

theorem coframeIntegral_readback (f : Field289) (a b : QuantumTest) (r : ℝ)
    (ha : |r|<fieldRadius f a) (hb : |r|<fieldRadius f b) :
    coframeIntegral f a b r=coframeFieldForm f (transportTest f a r) (transportTest f b r) r := by
  simp only [coframeIntegral,mixedIntegral,coframeFieldForm,mixedFieldForm,pairIntegral_readback f a b _ _ _ r ha hb,
    sectionTest,id_eq]

def transportedForm (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (r : ℝ) : ℂ :=
  nativeIntegral f a b r+coframeIntegral f a b r+fiberIntegral f a b (actualFiber p) r-
    fiberIntegral f a b retainedCoefficient r-fiberIntegral f a b yukawaFiber r

def transportedJets (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : TwoJets (transportedForm f p a b) :=
  ((((nativeIntegralJets f a b).add (coframeIntegralJets f a b)).add
    (fiberIntegralJets f a b (actualFiber p) (actualFiber_smooth p))).sub
    (fiberIntegralJets f a b retainedCoefficient retainedCoefficient_smooth)).sub
    (fiberIntegralJets f a b yukawaFiber yukawaFiber_smooth)

theorem transportedForm_readback (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (r : ℝ)
    (ha : |r|<fieldRadius f a) (hb : |r|<fieldRadius f b) :
    transportedForm f p a b r=physicalForm f p (transportTest f a r) (transportTest f b r) r := by
  simp only [transportedForm,physicalForm,fieldForm,nativeIntegral_readback f a b r ha hb,
    coframeIntegral_readback f a b r ha hb,fiberIntegral_readback f a b _ r ha hb]

theorem transportedForm_zero (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    transportedForm f p a b 0=physicalForm f p a b 0 := by
  rw [transportedForm_readback f p a b 0 (by simpa using fieldRadius_positive f a)
    (by simpa using fieldRadius_positive f b),transportTest_zero,transportTest_zero]

theorem transportedForm_germ (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    transportedForm f p a b=ᶠ[𝓝 0] fun r=>physicalForm f p (transportTest f a r) (transportTest f b r) r := by
  have first : ∀ᶠr in 𝓝 (0:ℝ),|r|<fieldRadius f a :=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  have second : ∀ᶠr in 𝓝 (0:ℝ),|r|<fieldRadius f b :=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f b))
  filter_upwards [first,second] with r hr kr
  exact transportedForm_readback f p a b r hr kr

theorem transportedForm_two_jets (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fun r=>physicalForm f p (transportTest f a r) (transportTest f b r) r) ((transportedJets f p a b).first 0) 0 := by
  exact (transportedJets f p a b).actual.1.congr_of_eventuallyEq (transportedForm_germ f p a b).symm

theorem transportedForm_contact (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (deriv (fun r=>physicalForm f p (transportTest f a r) (transportTest f b r) r))
      (transportedJets f p a b).second 0 :=
  (transportedJets f p a b).actual.2.congr_of_eventuallyEq (transportedForm_germ f p a b).deriv.symm

theorem transportFiber_grade (f : Field289) (z : SourceCoordinateSlice) (r : ℝ) (g : NativeHistoryGrade.Label) (v : FockFiber) :
    transportFiber f z r (GaussCoreLabel.fiberPiece g v)=GaussCoreLabel.fiberPiece g (transportFiber f z r v) := by
  apply PiLp.ext; intro word
  simp only [transportFiber,GaussFockWeights.weight_apply,GaussCoreLabel.fiberPiece_apply]
  split_ifs <;> simp

theorem transportTest_grade (f : Field289) (a : QuantumTest) (r : ℝ) (g : NativeHistoryGrade.Label)
    (ha : |r|<fieldRadius f a) (hg : |r|<fieldRadius f (GaussCoreLabel.project g a)) :
    transportTest f (GaussCoreLabel.project g a) r=GaussCoreLabel.project g (transportTest f a r) := by
  apply DFunLike.ext; intro z
  rw [transportTest_apply f _ r hg,GaussCoreLabel.project_apply,transportTest_apply f a r ha]
  exact transportFiber_grade f z r g (a z)

theorem transportedBasis_gram (f : Field289) (p : PhysicalMomentum) (F : Index) (i j : PhysicalBasisIndex p F) :
    transportedPair f (bareTest p F i) (bareTest p F j)=ᶠ[𝓝 0] fun _=>if i=j then (1:ℂ) else 0 := by
  have base : sourcePair (bareTest p F i) (bareTest p F j)=(if i=j then (1:ℂ) else 0) := by
    rw [sourcePair,bareTest_embed,bareTest_embed]
    exact (physicalBasis p F).inner_eq_ite i j
  simpa only [base] using transportedPair_original f (bareTest p F i) (bareTest p F j)

attribute [local irreducible] transportedForm transportedJets physicalForm physicalJets transportTest bareTest physicalBasis physicalFrame

open NativeHistoryGrade (Label)
local instance : Fintype Label:=Fintype.ofFinite _

def sourceAssembly (p : PhysicalMomentum) (F : Index)
    (entries : PhysicalBasisIndex p F → PhysicalBasisIndex p F → ℂ) : H →L[ℂ] H :=
  ∑g : Label,∑i : PhysicalBasisIndex p F,∑j : PhysicalBasisIndex p F,
    entries i j • InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j))

def transportedCompression (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ) : H →L[ℂ] H :=
  sourceAssembly p F (fun i j=>transportedForm f p (bareTest p F i) (bareTest p F j) r)

def transportedCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ) : H →L[ℂ] H :=
  sourceAssembly p F (fun i j=>(transportedJets f p (bareTest p F i) (bareTest p F j)).first r)

def transportedContact (f : Field289) (p : PhysicalMomentum) (F : Index) : H →L[ℂ] H :=
  sourceAssembly p F (fun i j=>(transportedJets f p (bareTest p F i) (bareTest p F j)).second)

theorem transportedCompression_source (f : Field289) (p : PhysicalMomentum) (F : Index) :
    transportedCompression f p F=ᶠ[𝓝 0] fun r : ℝ=>sourceAssembly p F (fun i j=>
      physicalForm f p (transportTest f (bareTest p F i) r) (transportTest f (bareTest p F j) r) r) := by
  have h:=Filter.eventually_all.mpr (fun i : PhysicalBasisIndex p F=>Filter.eventually_all.mpr
    (fun j : PhysicalBasisIndex p F=>transportedForm_germ f p (bareTest p F i) (bareTest p F j)))
  filter_upwards [h] with r hr
  apply congrArg (sourceAssembly p F)
  funext i j
  exact hr i j

theorem transportedCompression_zero (f : Field289) (p : PhysicalMomentum) (F : Index) :
    transportedCompression f p F 0=CanonicalPhysicalSpatial.compression p F := by
  rw [←gradedForm_zero f p F]
  simp only [transportedCompression,sourceAssembly,gradedForm,transportedForm_zero]

theorem transportedCompression_first (f : Field289) (p : PhysicalMomentum) (F : Index) :
    HasDerivAt (transportedCompression f p F) (transportedCurrent f p F 0) 0 := by
  unfold transportedCompression transportedCurrent sourceAssembly
  apply HasDerivAt.fun_sum; intro g _
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  exact (transportedJets f p (bareTest p F i) (bareTest p F j)).actual.1.smul_const
    (InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j)))

theorem transportedCurrent_second (f : Field289) (p : PhysicalMomentum) (F : Index) :
    HasDerivAt (transportedCurrent f p F) (transportedContact f p F) 0 := by
  unfold transportedCurrent transportedContact sourceAssembly
  apply HasDerivAt.fun_sum; intro g _
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  exact (transportedJets f p (bareTest p F i) (bareTest p F j)).second_derivative.smul_const
    (InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j)))

open CanonicalPhysicalYResolvent FullYSourceCutoffVolterra
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] finiteFull transportedCompression transportedCurrent transportedContact

def transportedResolvent (f : Field289) (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  Ring.inverse (transportedCompression f p F r+cutoff cut-z • 1)

theorem transportedResolvent_zero (f : Field289) (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ)
    (hz : z.im≠0) : transportedResolvent f p F cut z 0=finiteFull p F cut z := by
  rw [transportedResolvent,transportedCompression_zero]
  exact Ring.inverse_unit (originalFullUnit p F cut z hz)

theorem transportedResolvent_first (f : Field289) (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ)
    (hz : z.im≠0) : HasDerivAt (transportedResolvent f p F cut z)
      (-(finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z)) 0 := by
  have source:=((transportedCompression_first f p F).add_const (cutoff cut)).sub_const (z • 1)
  have inverse:=hasFDerivAt_ringInverse (𝕜:=ℝ) (originalFullUnit p F cut z hz)
  have same : (originalFullUnit p F cut z hz : H →L[ℂ] H)=transportedCompression f p F 0+cutoff cut-z • 1 := by
    rw [transportedCompression_zero]; rfl
  have generated:=inverse.comp_hasDerivAt_of_eq 0 source same
  convert! generated using 1

def transportedInsertion (f : Field289) (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  transportedResolvent f p F cut z r*transportedCurrent f p F r*transportedResolvent f p F cut z r

theorem transportedInsertion_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ)
    (hz : z.im≠0) : HasDerivAt (transportedInsertion f p F cut z)
      (finiteFull p F cut z*transportedContact f p F*finiteFull p F cut z-
        finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z-
        finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z) 0 := by
  have R:=transportedResolvent_first f p F cut z hz
  have J : HasDerivAt (transportedCurrent f p F) (transportedContact f p F) 0 := by
    convert! transportedCurrent_second f p F using 1
  have product:=(R.mul J).mul R
  simp only [Pi.mul_apply,transportedResolvent_zero f p F cut z hz] at product
  have algebra:=inverse_insertion_algebra (finiteFull p F cut z) (transportedCurrent f p F 0) (transportedContact f p F)
  convert! product.congr_deriv algebra.symm using 1

theorem transportedCompression_derivative_near (f : Field289) (p : PhysicalMomentum) (F : Index) :
    ∀ᶠr in 𝓝 (0:ℝ),HasDerivAt (transportedCompression f p F) (transportedCurrent f p F r) r := by
  have h:=Filter.eventually_all.mpr (fun i : PhysicalBasisIndex p F=>Filter.eventually_all.mpr
    (fun j : PhysicalBasisIndex p F=>(transportedJets f p (bareTest p F i) (bareTest p F j)).derivative_near))
  filter_upwards [h] with r hr
  unfold transportedCompression transportedCurrent sourceAssembly
  apply HasDerivAt.fun_sum; intro g _
  apply HasDerivAt.fun_sum; intro i _
  apply HasDerivAt.fun_sum; intro j _
  exact (hr i j).smul_const (InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j)))

theorem inverse_curve_derivative {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (Q : ℝ → A) (r : ℝ) (D : A) (hd : HasDerivAt Q D r) (hu : IsUnit (Q r)) :
    HasDerivAt (fun s=>Ring.inverse (Q s)) (-(Ring.inverse (Q r)*D*Ring.inverse (Q r))) r := by
  obtain ⟨u,hu⟩:=hu
  have h:=(hasFDerivAt_ringInverse (𝕜:=ℝ) u).comp_hasDerivAt_of_eq r hd hu
  rw [←hu,Ring.inverse_unit]
  convert! h using 1

theorem transportedResolvent_derivative_near (f : Field289) (p : PhysicalMomentum) (F : Index)
    (cut : ℕ) (z : ℂ) (hz : z.im≠0) :
    ∀ᶠr in 𝓝 (0:ℝ),HasDerivAt (transportedResolvent f p F cut z) (-transportedInsertion f p F cut z r) r := by
  let Q : ℝ → H →L[ℂ] H:=fun r=>transportedCompression f p F r+cutoff cut-z • 1
  have same : Q 0=(originalFullUnit p F cut z hz : H →L[ℂ] H) := by
    dsimp only [Q]; rw [transportedCompression_zero]; rfl
  have continuity : ContinuousAt Q 0 :=
    (((transportedCompression_first f p F).add_const (cutoff cut)).sub_const (z • 1)).continuousAt
  have available : ∀ᶠA : H →L[ℂ] H in 𝓝 (Q 0),IsUnit A := by
    rw [same]
    exact Units.nhds (originalFullUnit p F cut z hz)
  have units : ∀ᶠr in 𝓝 (0:ℝ),IsUnit (Q r) := continuity.eventually available
  filter_upwards [units,transportedCompression_derivative_near f p F] with r hr hd
  exact inverse_curve_derivative Q r (transportedCurrent f p F r)
    ((hd.add_const (cutoff cut)).sub_const (z • 1)) hr

theorem transportedResolvent_second (f : Field289) (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ)
    (hz : z.im≠0) : HasDerivAt (deriv (transportedResolvent f p F cut z))
      (-(finiteFull p F cut z*transportedContact f p F*finiteFull p F cut z-
        finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z-
        finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z)) 0 := by
  apply (transportedInsertion_derivative f p F cut z hz).neg.congr_of_eventuallyEq
  exact (transportedResolvent_derivative_near f p F cut z hz).mono fun r hr=>hr.deriv

def currentMatrixPrice (f : Field289) (p : PhysicalMomentum) (F : Index) : ℝ :=
  ∑g : Label,∑i : PhysicalBasisIndex p F,∑j : PhysicalBasisIndex p F,
    ‖(transportedJets f p (bareTest p F i) (bareTest p F j)).first 0‖*
      ‖physicalFrame p F (g,i)‖*‖physicalFrame p F (g,j)‖

theorem transportedCurrent_price (f : Field289) (p : PhysicalMomentum) (F : Index) :
    ‖transportedCurrent f p F 0‖≤currentMatrixPrice f p F := by
  unfold transportedCurrent sourceAssembly currentMatrixPrice
  apply (norm_sum_le _ _).trans; apply Finset.sum_le_sum; intro g _
  apply (norm_sum_le _ _).trans; apply Finset.sum_le_sum; intro i _
  apply (norm_sum_le _ _).trans; apply Finset.sum_le_sum; intro j _
  rw [norm_smul,InnerProductSpace.norm_rankOne]
  exact le_of_eq (mul_assoc _ _ _).symm

def transportedVertex (f : Field289) (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ) : H →L[ℂ] H :=
  finiteFull (p+k) F cut z*transportedCurrent f p F 0*finiteFull p F cut w

theorem transportedVertex_price (f : Field289) (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    ‖transportedVertex f p k F cut z w‖≤normBound cut z*currentMatrixPrice f p F*normBound cut w :=
  triple_price _ _ _ _ _ _ (finiteFull_bound (p+k) F cut z hz) (transportedCurrent_price f p F) (finiteFull_bound p F cut w hw)

open PreparationVacuumSourcePreparedResponse GaussComposite GaussComposite.SourceGraph

def preparedTransportResponse (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) (r : ℝ) : ℂ :=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (transportedResolvent f p F cut z r (completedLeg right b t (sourceProfile epsilon precision)))

theorem preparedTransportResponse_first (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (preparedTransportResponse epsilon precision f p F cut z left right a s b t)
      (-inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        ((finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z)
          (completedLeg right b t (sourceProfile epsilon precision)))) 0 := by
  convert! paired_derivative (transportedResolvent_first f p F cut z hz)
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision)) using 1
  simp only [neg_apply,inner_neg_right]

theorem preparedTransportResponse_zero (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    preparedTransportResponse epsilon precision f p F cut z left right a s b t 0=
      inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        (finiteFull p F cut z (completedLeg right b t (sourceProfile epsilon precision))) := by
  rw [preparedTransportResponse,transportedResolvent_zero f p F cut z hz]

def resolventContact (f : Field289) (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) : H →L[ℂ] H :=
  -(finiteFull p F cut z*transportedContact f p F*finiteFull p F cut z-
    finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z-
    finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z*transportedCurrent f p F 0*finiteFull p F cut z)

def preparedTransportJets (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    TwoJets (preparedTransportResponse epsilon precision f p F cut z left right a s b t) where
  first r:=inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    ((-transportedInsertion f p F cut z r) (completedLeg right b t (sourceProfile epsilon precision)))
  second:=inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (resolventContact f p F cut z (completedLeg right b t (sourceProfile epsilon precision)))
  derivative_near:=(transportedResolvent_derivative_near f p F cut z hz).mono fun _r hr=>
    paired_derivative hr (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  second_derivative:=paired_derivative (transportedInsertion_derivative f p F cut z hz).neg
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))

def curvatureTransportResponse (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) (r : ℝ) : ℂ :=
  preparedTransportResponse epsilon precision (readerReal sourceMomentum row) p F cut z left right a s b t r+
    Complex.I*(preparedTransportResponse epsilon precision (readerImag sourceMomentum row) p F cut z left right a s b t r-
      preparedTransportResponse epsilon precision (readerImag sourceMomentum row) p F cut z left right a s b t 0)

def curvatureTransportJets (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    TwoJets (curvatureTransportResponse epsilon precision sourceMomentum row p F cut z left right a s b t) :=
  (preparedTransportJets epsilon precision (readerReal sourceMomentum row) p F cut z hz left right a s b t).add
    (TwoJets.scale Complex.I ((preparedTransportJets epsilon precision (readerImag sourceMomentum row) p F cut z hz left right a s b t).sub
      (constantPairJets (preparedTransportResponse epsilon precision (readerImag sourceMomentum row) p F cut z left right a s b t 0))))

theorem curvatureTransportResponse_two_jets (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4 → ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (curvatureTransportResponse epsilon precision sourceMomentum row p F cut z left right a s b t)
      ((curvatureTransportJets epsilon precision sourceMomentum row p F cut z hz left right a s b t).first 0) 0 ∧
    HasDerivAt (deriv (curvatureTransportResponse epsilon precision sourceMomentum row p F cut z left right a s b t))
      (curvatureTransportJets epsilon precision sourceMomentum row p F cut z hz left right a s b t).second 0 :=
  (curvatureTransportJets epsilon precision sourceMomentum row p F cut z hz left right a s b t).actual

end LowEnergy.PreparationVacuumGradedTransport
