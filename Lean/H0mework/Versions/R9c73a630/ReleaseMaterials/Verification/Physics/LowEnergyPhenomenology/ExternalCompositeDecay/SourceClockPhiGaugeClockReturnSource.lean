import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaugeScalarSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseGaugeOuterPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussLiveMomentum SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore SourceClockPhiForwardGeneratorTransport SourceClockPhiCorrectedWeightTransport
open SourceClockPhiOriginalGaussianH0RealPrimitives SourceClockPhiActualCovarianceStep SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale SourceGaugeRadialCurrent
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource ClockPhiMatchedNoiseCore SourceCoframeVolume
open scoped ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev V:End:=volumeAction
attribute [local irreducible] sourcePair embed
private theorem gauge_forward_point (u t : ℝ) (ht:0≤t) (f : QuantumTest)
    (z : SourceCoordinateSlice) (word : Occupation) :
    SourceGaugeScaleTransport.coreFlow u (sourceForwardCore t ht f) z word=
      sourceForwardCore t ht (SourceGaugeScaleTransport.coreFlow u f) z word := by
  rw [SourceGaugeScaleTransport.coreFlow_apply]
  change (Real.exp (18*u) : ℂ)*forwardValue t f (gaugeScale (Real.exp u) z) word=forwardValue t _ z word
  have hv:GaussNativeEnergy.volume (gaugeScale (Real.exp u) z)=GaussNativeEnergy.volume z:=rfl
  have hr:backwardRatio t (gaugeScale (Real.exp u) z)=backwardRatio t z:=rfl
  have hm:backwardPoint t (gaugeScale (Real.exp u) z)=gaugeScale (Real.exp u) (backwardPoint t z):=rfl
  by_cases hz:18*t<GaussNativeEnergy.volume z
  · simp only [forwardValue,hv,if_pos hz]
    change _*(_*f (backwardPoint t (gaugeScale (Real.exp u) z)) word)=
      _*SourceGaugeScaleTransport.coreFlow u f (backwardPoint t z) word
    rw [hm,SourceGaugeScaleTransport.coreFlow_apply,hr]
    ring
  · simp only [forwardValue,hv,if_neg hz,PiLp.zero_apply,mul_zero]

private theorem gauge_forward_generator (t : ℝ) (ht:0≤t) :
    Commute SourceGaugeScaleTransport.generator (sourceForwardCore t ht) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h1:=SourceGaugeScaleTransport.coreFlow_generator (sourceForwardCore t ht f) z word
  have h2:HasDerivAt (fun u : ℝ=>sourceForwardCore t ht (SourceGaugeScaleTransport.coreFlow u f) z word)
      (sourceForwardCore t ht (SourceGaugeScaleTransport.generator f) z word) 0 := by
    change HasDerivAt (fun u : ℝ=>forwardValue t (SourceGaugeScaleTransport.coreFlow u f) z word)
      (forwardValue t (SourceGaugeScaleTransport.generator f) z word) 0
    by_cases hz:18*t<GaussNativeEnergy.volume z
    · simp only [forwardValue,if_pos hz]
      change HasDerivAt (fun u : ℝ=>
        ((((backwardRatio t z)^((word.card+3 : ℝ)/2) : ℝ) : ℂ)*SourceGaugeScaleTransport.coreFlow u f (backwardPoint t z) word))
        (((((backwardRatio t z)^((word.card+3 : ℝ)/2) : ℝ) : ℂ))*SourceGaugeScaleTransport.generator f (backwardPoint t z) word) 0
      exact (SourceGaugeScaleTransport.coreFlow_generator f (backwardPoint t z) word).const_mul
        ((((backwardRatio t z)^((word.card+3 : ℝ)/2) : ℝ) : ℂ))
    · simp only [forwardValue,if_neg hz,PiLp.zero_apply]
      exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
  have he:(fun u : ℝ=>SourceGaugeScaleTransport.coreFlow u (sourceForwardCore t ht f) z word)=
      fun u : ℝ=>sourceForwardCore t ht (SourceGaugeScaleTransport.coreFlow u f) z word :=
    funext (fun u=>gauge_forward_point u t ht f z word)
  rw [he] at h1
  exact h1.unique h2


private theorem combined_gauge_commute(u v:ℝ)(z:SourceCoordinateSlice):
    combinedMap v (gaugeScale (Real.exp u) z)=gaugeScale (Real.exp u) (combinedMap v z):=by
  change (z.1,Real.exp v • (z.2.1+vacuumSlice)-vacuumSlice,Real.exp (-v) • (Real.exp u • z.2.2))=
    (z.1,Real.exp v • (z.2.1+vacuumSlice)-vacuumSlice,Real.exp u • (Real.exp (-v) • z.2.2))
  rw [smul_comm (Real.exp (-v)) (Real.exp u)]
private theorem profile_gauge_flow(u t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    SourceGaugeScaleTransport.coreFlow u (correctedProfileCore t ht ξ η f) z word=
      correctedProfileCore t ht ξ η (SourceGaugeScaleTransport.coreFlow u f) z word:=by
  rw [SourceGaugeScaleTransport.coreFlow_apply]
  change (Real.exp (18*u):ℂ)*((Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η (gaugeScale (Real.exp u) z))):ℂ)*
      f (combinedMap (1*correctedCoefficient t ξ η (gaugeScale (Real.exp u) z)) (gaugeScale (Real.exp u) z)) word)=
    (Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ)*
      SourceGaugeScaleTransport.coreFlow u f (combinedMap (1*correctedCoefficient t ξ η z) z) word
  have hc:correctedCoefficient t ξ η (gaugeScale (Real.exp u) z)=correctedCoefficient t ξ η z:=rfl
  rw [hc,combined_gauge_commute,SourceGaugeScaleTransport.coreFlow_apply]
  ring
private theorem gauge_profile(t:ℝ)(ht:0<t)(ξ η:ℝ):Commute G (correctedProfileCore t ht ξ η):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z;apply PiLp.ext;intro word
  have h1:=SourceGaugeScaleTransport.coreFlow_generator (correctedProfileCore t ht ξ η f) z word
  have h2:HasDerivAt (fun u:ℝ=>correctedProfileCore t ht ξ η (SourceGaugeScaleTransport.coreFlow u f) z word)
      (correctedProfileCore t ht ξ η (G f) z word) 0:=by
    change HasDerivAt (fun u:ℝ=>(Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ)*
      SourceGaugeScaleTransport.coreFlow u f (combinedMap (1*correctedCoefficient t ξ η z) z) word)
      ((Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ)*
        G f (combinedMap (1*correctedCoefficient t ξ η z) z) word) 0
    exact (SourceGaugeScaleTransport.coreFlow_generator f (combinedMap (1*correctedCoefficient t ξ η z) z) word).const_mul _
  have he:(fun u:ℝ=>SourceGaugeScaleTransport.coreFlow u (correctedProfileCore t ht ξ η f) z word)=
      fun u:ℝ=>correctedProfileCore t ht ξ η (SourceGaugeScaleTransport.coreFlow u f) z word:=
    funext (fun u=>profile_gauge_flow u t ht ξ η f z word)
  rw [he] at h1
  exact h1.unique h2
private theorem gauge_gain(t:ℝ):Commute G (sourceGain t):=by
  have h:=SourceGaugeScaleTransport.generator_commutator (sourceGain t)
  have hl:=gauge_invariant_local (sourceGain t)
    (fun z=>(gainProfile t z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) (fun _ _=>rfl) (fun _ _=>rfl)
  rw [hl] at h
  exact sub_eq_zero.mp h

/-- The original complete clock commutes with the actual gauge generator; the profile's rotation and real gain remain intact. -/
theorem actual_complete_gauge_commute(t:ℝ)(ht:0<t)(ξ η:ℝ):Commute G (correctedCompleteCore t ht ξ η):=by
  apply LinearMap.ext
  intro f
  have hj:=LinearMap.congr_fun (gauge_forward_generator t ht.le).eq
  have hp:=LinearMap.congr_fun (gauge_profile t ht ξ η).eq
  have hg:=LinearMap.congr_fun (gauge_gain (Real.sqrt t)).eq
  change G (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) f)))=
    sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) (G f)))
  change ∀f:QuantumTest,G (sourceForwardCore t ht.le f)=sourceForwardCore t ht.le (G f) at hj
  change ∀f:QuantumTest,G (correctedProfileCore t ht ξ η f)=correctedProfileCore t ht ξ η (G f) at hp
  change ∀f:QuantumTest,G (sourceGain (Real.sqrt t) f)=sourceGain (Real.sqrt t) (G f) at hg
  rw [hj,hp,hg]

/-- A source volume square entering the complete clock returns as the literal shifted output volume. -/
theorem actual_complete_volume_input(t:ℝ)(ht:0<t)(ξ η:ℝ):
    correctedCompleteCore t ht ξ η*V=(V-(18*t:ℂ) • (1:End))*correctedCompleteCore t ht ξ η:=by
  have h:=actual_corrected_complete_coframe_multiplier t ht ξ η volume
    (fun _=>volume_smooth.contDiffAt) (fun z w hz=>by change z.1 0*z.1 2*z.1 5=w.1 0*w.1 2*w.1 5;rw [hz])
  have he(hc:∀z:physicalChart,ContDiffAt ℝ ∞ (fun w=>volume (forwardPoint t w)) z.val):
      multiply (fun z=>volume (forwardPoint t z)) hc=V+(18*t:ℂ) • (1:End):=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    by_cases hz:z∈physicalChart
    · change (volume (forwardPoint t z):ℂ) • f z=(volume z:ℂ) • f z+(18*t:ℂ) • f z
      rw [forward_volume t ht.le ⟨z,hz⟩,Complex.ofReal_add,add_smul]
      norm_num only [Complex.ofReal_mul,Complex.ofReal_ofNat]
    · have hz0:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
      change (volume (forwardPoint t z):ℂ) • f z=(volume z:ℂ) • f z+(18*t:ℂ) • f z
      rw [hz0]
      simp only [smul_zero,add_zero]
  rw [he] at h
  change V*correctedCompleteCore t ht ξ η=correctedCompleteCore t ht ξ η*(V+(18*t:ℂ) • (1:End)) at h
  linear_combination (norm:=noncomm_ring) -h
end LowEnergy.ReverseGaugeOuterPayment
