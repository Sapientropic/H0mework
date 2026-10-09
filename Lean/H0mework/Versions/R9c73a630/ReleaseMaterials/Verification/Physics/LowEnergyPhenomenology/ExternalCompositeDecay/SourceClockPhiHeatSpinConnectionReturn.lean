import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeSpinConnection
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardCore
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiHeatSpinConnectionReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceCoframeSpinConnection SourceClockPhiCoframeForwardCore
open scoped ContDiff Matrix
private theorem diagonal_ne (z:physicalChart):
    z.val.1 0≠0∧z.val.1 2≠0∧z.val.1 5≠0:=by
  have h:=(volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at h
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2,(mul_ne_zero_iff.mp h).2⟩

theorem actual_spin_connection_scale (r:ℝ) (hr:0<r) (z:physicalChart)
    (i:Fin 6) (a:Fin 3):
    spinConnection (r • z.val.1) i a=r⁻¹*spinConnection z.val.1 i a:=by
  obtain ⟨h0,h2,h5⟩:=diagonal_ne z
  fin_cases i <;> fin_cases a <;>
    simp [spinConnection,PiLp.smul_apply,smul_eq_mul]
  all_goals field_simp [hr.ne',h0,h2,h5]

theorem actual_spin_connection_euler (z:physicalChart) (a:Fin 3):
    (∑i:Fin 6,z.val.1 i*spinConnection z.val.1 i a)=0:=by
  obtain ⟨h0,h2,h5⟩:=diagonal_ne z
  fin_cases a <;> simp [spinConnection,Fin.sum_univ_succ]
  all_goals field_simp [h0,h2,h5]
  all_goals ring

theorem actual_forward_current_commute (t:ℝ) (ht:0≤t) (a:Fin 7):
    Commute (sourceForwardCore t ht) (GaussCoframeSpin.current a):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change forwardValue t (GaussCoframeSpin.current a f) z=
    GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (forwardValue t f z)
  by_cases hz:18*t<GaussNativeEnergy.volume z
  · simp only [forwardValue,if_pos hz]
    let c:ℕ→ℂ:=fun N=>(Real.rpow (backwardRatio t z) ((N+3:ℝ)/2):ℂ)
    change GaussFockWeights.weight c
      (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (f (backwardPoint t z)))=
      GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
        (GaussFockWeights.weight c (f (backwardPoint t z)))
    exact congrArg (fun T:FockFiber→L[ℂ]FockFiber=>T (f (backwardPoint t z)))
      (GaussQuantumMultiplier.weight_commute c (GaussCoframeSpin.full a)).eq
  · simp only [forwardValue,if_neg hz,map_zero]
end LowEnergy.SourceClockPhiHeatSpinConnectionReturn
