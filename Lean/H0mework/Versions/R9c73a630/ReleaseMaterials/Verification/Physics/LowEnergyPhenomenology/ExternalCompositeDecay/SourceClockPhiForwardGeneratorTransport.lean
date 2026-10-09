import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardCore
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseCore
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiForwardGeneratorTransport
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore SourceClockPhiCombinedScalePressure SourceGaugeRadialCurrent
open scoped Topology ContDiff
private abbrev Op:=QuantumTest →ₗ[ℂ] QuantumTest

private theorem phi_forward_point (u t : ℝ) (ht:0≤t) (f : QuantumTest)
    (z : SourceCoordinateSlice) (word : Occupation) :
    SourceScalarAffineScaleTransport.coreFlow u (sourceForwardCore t ht f) z word=
      sourceForwardCore t ht (SourceScalarAffineScaleTransport.coreFlow u f) z word := by
  rw [SourceScalarAffineScaleTransport.coreFlow_apply]
  change (Real.exp ((61/2 : ℝ)*u) : ℂ)*forwardValue t f
      (SourceScalarAffineScaleTransport.scaleEquiv u z) word=forwardValue t _ z word
  have hv:GaussNativeEnergy.volume (SourceScalarAffineScaleTransport.scaleEquiv u z)=GaussNativeEnergy.volume z:=rfl
  have hr:backwardRatio t (SourceScalarAffineScaleTransport.scaleEquiv u z)=backwardRatio t z:=rfl
  have hm:backwardPoint t (SourceScalarAffineScaleTransport.scaleEquiv u z)=
      SourceScalarAffineScaleTransport.scaleEquiv u (backwardPoint t z):=rfl
  by_cases hz:18*t<GaussNativeEnergy.volume z
  · simp only [forwardValue,hv,if_pos hz]
    change _*(_*f (backwardPoint t (SourceScalarAffineScaleTransport.scaleEquiv u z)) word)=
      _*SourceScalarAffineScaleTransport.coreFlow u f (backwardPoint t z) word
    rw [hm,SourceScalarAffineScaleTransport.coreFlow_apply]
    rw [hr]
    ring
  · simp only [forwardValue,hv,if_neg hz,PiLp.zero_apply,mul_zero]

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

private theorem phi_forward_generator (t : ℝ) (ht:0≤t) :
    Commute SourceScalarAffineScaleTransport.generator (sourceForwardCore t ht) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h1:=SourceScalarAffineScaleTransport.coreFlow_generator (sourceForwardCore t ht f) z word
  have h2:HasDerivAt (fun u : ℝ=>sourceForwardCore t ht (SourceScalarAffineScaleTransport.coreFlow u f) z word)
      (sourceForwardCore t ht (SourceScalarAffineScaleTransport.generator f) z word) 0 := by
    change HasDerivAt (fun u : ℝ=>forwardValue t (SourceScalarAffineScaleTransport.coreFlow u f) z word)
      (forwardValue t (SourceScalarAffineScaleTransport.generator f) z word) 0
    by_cases hz:18*t<GaussNativeEnergy.volume z
    · simp only [forwardValue,if_pos hz]
      change HasDerivAt (fun u : ℝ=>
        ((((backwardRatio t z)^((word.card+3 : ℝ)/2) : ℝ) : ℂ)*SourceScalarAffineScaleTransport.coreFlow u f (backwardPoint t z) word))
        (((((backwardRatio t z)^((word.card+3 : ℝ)/2) : ℝ) : ℂ))*SourceScalarAffineScaleTransport.generator f (backwardPoint t z) word) 0
      exact (SourceScalarAffineScaleTransport.coreFlow_generator f (backwardPoint t z) word).const_mul
        ((((backwardRatio t z)^((word.card+3 : ℝ)/2) : ℝ) : ℂ))
    · simp only [forwardValue,if_neg hz,PiLp.zero_apply]
      exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
  have he:(fun u : ℝ=>SourceScalarAffineScaleTransport.coreFlow u (sourceForwardCore t ht f) z word)=
      fun u : ℝ=>sourceForwardCore t ht (SourceScalarAffineScaleTransport.coreFlow u f) z word :=
    funext (fun u=>phi_forward_point u t ht f z word)
  rw [he] at h1
  exact h1.unique h2

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

theorem actual_forward_generator_commute (t : ℝ) (ht:0≤t) :
    Commute combinedGenerator (sourceForwardCore t ht) := by
  apply LinearMap.ext
  intro f
  have hp:=LinearMap.congr_fun (phi_forward_generator t ht).eq f
  have hg:=LinearMap.congr_fun (gauge_forward_generator t ht).eq f
  change SourceScalarAffineScaleTransport.generator (sourceForwardCore t ht f)-
    SourceGaugeScaleTransport.generator (sourceForwardCore t ht f)=
    sourceForwardCore t ht (SourceScalarAffineScaleTransport.generator f-SourceGaugeScaleTransport.generator f)
  rw [map_sub]
  simp only [Module.End.mul_apply] at hp hg
  rw [hp,hg]

private theorem forwardMultiplier_smooth (t : ℝ) (ht:0≤t) (b : SourceCoordinateSlice→ℝ)
    (hb:∀z : physicalChart,ContDiffAt ℝ ∞ b z.val) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x : SourceCoordinateSlice=>b (forwardPoint t x)) z.val :=
  ContDiffAt.comp (f:=forwardPoint t) z.val (hb ⟨_,forward_chart t ht z⟩) (forward_smooth t ht z)

theorem actual_forward_multiplier_transport (t : ℝ) (ht:0≤t) (b : SourceCoordinateSlice→ℝ)
    (hb:∀z : physicalChart,ContDiffAt ℝ ∞ b z.val) :
    multiply b hb*sourceForwardCore t ht=sourceForwardCore t ht*
      multiply (fun x : SourceCoordinateSlice=>b (forwardPoint t x)) (forwardMultiplier_smooth t ht b hb) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  by_cases hz:18*t<GaussNativeEnergy.volume z
  · change (b z : ℂ)*forwardValue t f z word=forwardValue t _ z word
    simp only [forwardValue,if_pos hz]
    change (b z : ℂ)*(_*f (backwardPoint t z) word)=
      _*((b (forwardPoint t (backwardPoint t z)) : ℂ)*f (backwardPoint t z) word)
    rw [forward_backward t ht z hz]
    ring
  · change (b z : ℂ)*forwardValue t f z word=forwardValue t _ z word
    simp only [forwardValue,if_neg hz,PiLp.zero_apply,mul_zero]
end LowEnergy.SourceClockPhiForwardGeneratorTransport
