import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeSecondOrder
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeSecondActionSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiCoframeForwardCore GaussFockWeights
open ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource ClockPhiHeatCorrectedCovarianceSource
open SourceClockPhiActualCovarianceStep SourceScalarVirialBulk
open scoped ContDiff Topology
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private theorem combined_chart(a:ℝ)(z:physicalChart):combinedMap a z.val∈physicalChart:=by
  have hg:=SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-a)) (Real.exp_pos (-a))
    (SourceScalarAffineScaleTransport.scaleEquiv a z.val)
  have hp:=SourceScalarAffineScaleTransport.scale_chart_iff a z.val
  exact hg.mpr (hp.mpr z.property)
private theorem combined_smooth:ContDiff ℝ ∞ (fun p:ℝ×SourceCoordinateSlice=>combinedMap p.1 p.2):=by
  simp only[combinedMap_apply]
  fun_prop
private theorem coefficient_invariant(t ξ η a:ℝ)(z:SourceCoordinateSlice):
    correctedCoefficient t ξ η (combinedMap a z)=correctedCoefficient t ξ η z:=rfl
private theorem combined_inverse(a:ℝ)(z:SourceCoordinateSlice):combinedMap (-a) (combinedMap a z)=z:=by
  simp only[combinedMap_apply,sub_add_cancel,smul_smul,←Real.exp_add,neg_add_cancel,neg_neg,add_neg_cancel,
    Real.exp_zero,one_smul,add_sub_cancel_right,Prod.eta]

def inverseProfilePoint(t ξ η:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  combinedMap (-correctedCoefficient t ξ η z) z

def localClockPoint(t ξ η:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  forwardPoint t (inverseProfilePoint t ξ η z)
private theorem inverseProfile_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (inverseProfilePoint t ξ η) z.val:=
by
  unfold inverseProfilePoint
  have h:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(-correctedCoefficient t ξ η x,x)) z.val:=
    (coefficient_smooth t ht ξ η z).neg.prodMk contDiffAt_id
  exact ContDiffAt.comp (f:=fun x:SourceCoordinateSlice=>(-correctedCoefficient t ξ η x,x)) z.val
    (combined_smooth.contDiffAt (x:=(-correctedCoefficient t ξ η z.val,z.val))) h
private theorem localClockPoint_chart(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    localClockPoint t ξ η z.val∈physicalChart:=
  forward_chart t ht.le ⟨_,combined_chart _ z⟩
private theorem localClockPoint_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (localClockPoint t ξ η) z.val:=
  (forward_smooth t ht.le ⟨_,combined_chart _ z⟩).comp z.val (inverseProfile_smooth t ht ξ η z)
private theorem point_inverse(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:SourceCoordinateSlice)(hz:18*t<volume z):
    localClockPoint t ξ η (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z))=z:=by
  unfold localClockPoint inverseProfilePoint
  rw [coefficient_invariant,combined_inverse,forward_backward t ht.le z hz]
private def forwardAmplitude(t:ℝ)(z:SourceCoordinateSlice):FockFiber→L[ℂ]FockFiber:=
  weight (fun N=>(Real.rpow (backwardRatio t z) ((N+3:ℝ)/2):ℂ))
private theorem forward_value(t:ℝ)(ht:0≤t)(f:QuantumTest)(z:SourceCoordinateSlice)(hz:18*t<volume z):
    sourceForwardCore t ht f z=forwardAmplitude t z (f (backwardPoint t z)):=by
  apply PiLp.ext
  intro word
  change forwardValue t f z word=_
  rw [forwardValue,if_pos hz]
  rfl
private theorem complete_value(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(hz:18*t<volume z):
    correctedCompleteCore t ht ξ η f z=
      forwardAmplitude t z ((Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η (backwardPoint t z)):ℂ) •
        ((gainProfile (Real.sqrt t) (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)):ℂ) •
          f (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)))):=by
  change sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) f)) z=_
  rw [forward_value t ht.le _ z hz]
  congr 1
  change (Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η (backwardPoint t z))):ℂ) •
    ((gainProfile (Real.sqrt t) (combinedMap (1*correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)):ℂ) •
      f (combinedMap (1*correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)))=_
  simp only[one_mul]
private theorem complete_zero(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(hz:¬18*t<volume z):
    correctedCompleteCore t ht ξ η f z=0:=by
  change forwardValue t (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) f)) z=0
  rw [forwardValue,if_neg hz]
private theorem returnedLocal_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(A:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (hA:∀z:physicalChart,ContDiffAt ℝ ∞ A z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>A (localClockPoint t ξ η x)) z.val:=
  (hA ⟨_,localClockPoint_chart t ht ξ η z⟩).comp z.val (localClockPoint_smooth t ht ξ η z)
def returnedLocalAction(t:ℝ)(ht:0<t)(ξ η:ℝ)(A:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (hA:∀z:physicalChart,ContDiffAt ℝ ∞ A z.val):End:=
  localMultiplier (fun x=>A (localClockPoint t ξ η x)) (returnedLocal_smooth t ht ξ η A hA)

/-- The full one-sided J/profile/gain clock returns every original Number-preserving local
field through its actual coordinate map, retaining the full Fock matrix. -/
theorem actual_corrected_local_action(t:ℝ)(ht:0<t)(ξ η:ℝ)(A:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (hA:∀z:physicalChart,ContDiffAt ℝ ∞ A z.val)
    (hN:∀z:SourceCoordinateSlice,∀c:ℕ→ℂ,Commute (weight c) (A z)):
    localMultiplier A hA*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*returnedLocalAction t ht ξ η A hA:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change A z (correctedCompleteCore t ht ξ η f z)=correctedCompleteCore t ht ξ η (returnedLocalAction t ht ξ η A hA f) z
  by_cases hz:18*t<volume z
  · rw [complete_value t ht ξ η f z hz,complete_value t ht ξ η _ z hz]
    change A z (forwardAmplitude t z ((Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η (backwardPoint t z)):ℂ) •
      ((gainProfile (Real.sqrt t) (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)):ℂ) •
        f (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)))))=
      forwardAmplitude t z ((Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η (backwardPoint t z)):ℂ) •
      ((gainProfile (Real.sqrt t) (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)):ℂ) •
        A (localClockPoint t ξ η (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)))
          (f (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)))))
    rw [point_inverse t ht ξ η z hz]
    have hc:Commute (forwardAmplitude t z) (A z):=hN z _
    have hv:=congrArg (fun T:FockFiber→L[ℂ]FockFiber=>T
      ((Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η (backwardPoint t z)):ℂ) •
      ((gainProfile (Real.sqrt t) (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z)):ℂ) •
        f (combinedMap (correctedCoefficient t ξ η (backwardPoint t z)) (backwardPoint t z))))) hc.eq
    simpa only[mul_apply_eq_comp,map_smul] using hv.symm
  · rw [complete_zero t ht ξ η f z hz,complete_zero t ht ξ η _ z hz,map_zero]
end LowEnergy.FirstCurrentWholeVariance
