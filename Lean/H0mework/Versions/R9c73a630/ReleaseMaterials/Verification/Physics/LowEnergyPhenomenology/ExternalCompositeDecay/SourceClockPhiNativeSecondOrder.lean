import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileNativeAdjoint
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedWeightTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiCoframeForwardCore SourceClockPhiCorrectedWeightTransport ClockPhiHeatCorrectedCovarianceSource
open scoped ContDiff
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private theorem forwardCoefficientSmooth(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>b (forwardPoint t x)) z.val:=
  (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z)
def returnedNativeCoefficient(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):End:=
  multiply (fun x=>b (forwardPoint t x)) (forwardCoefficientSmooth t ht b hb)
def returnedNativeSandwich(t:ℝ)(ht:0<t)(ξ η k:ℝ)(v w:Ambient)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):End:=
  correctedNativeWeight t ht ξ η k*GaussMomentumAdjoint.adjoint v*returnedNativeCoefficient t ht b hb*
    correctedNativeWeight t ht ξ η k*covariantMomentum w
private theorem corrected_sandwich(t:ℝ)(ht:0<t)(ξ η k:ℝ)(v w:Ambient)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(hi:∀x y:SourceCoordinateSlice,x.1=y.1→b x=b y)
    (hP:covariantMomentum w*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*correctedNativeWeight t ht ξ η k*covariantMomentum w)
    (hA:GaussMomentumAdjoint.adjoint v*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*correctedNativeWeight t ht ξ η k*GaussMomentumAdjoint.adjoint v):
    sandwich v w b hb*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*returnedNativeSandwich t ht ξ η k v w b hb:=by
  have hB:multiply b hb*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*returnedNativeCoefficient t ht b hb:=
    actual_corrected_complete_coframe_multiplier t ht ξ η b hb hi
  change (GaussMomentumAdjoint.adjoint v*multiply b hb*covariantMomentum w)*correctedCompleteCore t ht ξ η=_
  unfold returnedNativeSandwich
  calc
    _=GaussMomentumAdjoint.adjoint v*multiply b hb*(covariantMomentum w*correctedCompleteCore t ht ξ η):=by noncomm_ring
    _=GaussMomentumAdjoint.adjoint v*(multiply b hb*correctedCompleteCore t ht ξ η)*
        correctedNativeWeight t ht ξ η k*covariantMomentum w:=by rw [hP];noncomm_ring
    _=(GaussMomentumAdjoint.adjoint v*correctedCompleteCore t ht ξ η)*returnedNativeCoefficient t ht b hb*
        correctedNativeWeight t ht ξ η k*covariantMomentum w:=by rw [hB];noncomm_ring
    _=_:=by rw [hA];noncomm_ring

def returnedScalarKinetic(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  (1/2:ℂ) • ∑a:ScalarIndex,returnedNativeSandwich t ht ξ η 1 (scalarDirection a) (scalarDirection a)
    scalarWeight scalarWeight_smooth

def returnedGaugeKinetic(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  (1/2:ℂ) • ∑a:LieIndex,∑i:Fin 3,∑j:Fin 3,
    returnedNativeSandwich t ht ξ η (-1) (gaugeDirection i a) (gaugeDirection j a)
      (fun x=>gaugeWeight x i j) (gaugeWeight_smooth i j)

/-- All original native scalar and gauge P†cP rows return as actual second-order actions
of the same corrected clock. Every coefficient and both independent adjoint legs are retained. -/
theorem actual_corrected_native_second_order(t:ℝ)(ht:0<t)(ξ η:ℝ):
    scalarKinetic*correctedCompleteCore t ht ξ η=correctedCompleteCore t ht ξ η*returnedScalarKinetic t ht ξ η ∧
    gaugeKinetic*correctedCompleteCore t ht ξ η=correctedCompleteCore t ht ξ η*returnedGaugeKinetic t ht ξ η:=by
  constructor
  · unfold scalarKinetic returnedScalarKinetic
    simp only[smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    have h:=actual_corrected_scalar_momentum_pair t ht ξ η (scalarDirection a) rfl
    exact corrected_sandwich t ht ξ η 1 _ _ _ _ (by rintro ⟨a,b⟩ ⟨d,e⟩ h; cases h; rfl) h.1 h.2
  · unfold gaugeKinetic returnedGaugeKinetic
    simp only[smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hP:=actual_corrected_gauge_momentum_pair t ht ξ η (gaugeDirection j a) rfl
    have hA:=actual_corrected_gauge_momentum_pair t ht ξ η (gaugeDirection i a) rfl
    exact corrected_sandwich t ht ξ η (-1) _ _ _ _ (by rintro ⟨a,b⟩ ⟨d,e⟩ h; cases h; rfl) hP.1 hA.2
end LowEnergy.FirstCurrentWholeVariance
