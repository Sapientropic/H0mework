import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForwardGeneratorTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiForwardNativeReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore SourceClockPhiCombinedScalePressure
open SourceClockPhiForwardGeneratorTransport
open scoped Topology ContDiff
private abbrev Op:=QuantumTest →ₗ[ℂ] QuantumTest

def forwardU (t : ℝ) (z : SourceCoordinateSlice) : ℝ := (GaussNativeEnergy.volume z+18*t)⁻¹
def forwardA (t : ℝ) (z : SourceCoordinateSlice) : ℝ := (Real.sqrt (GaussNativeEnergy.volume z+18*t))⁻¹
theorem forwardU_smooth (t : ℝ) (ht:0≤t) (z : physicalChart) :
    ContDiffAt ℝ ∞ (forwardU t) z.val := by
  have hv:0<GaussNativeEnergy.volume z.val+18*t := by linarith [volume_pos z]
  exact (volume_smooth.contDiffAt.add contDiffAt_const).inv hv.ne'
theorem forwardA_smooth (t : ℝ) (ht:0≤t) (z : physicalChart) :
    ContDiffAt ℝ ∞ (forwardA t) z.val := by
  have hv:0<GaussNativeEnergy.volume z.val+18*t := by linarith [volume_pos z]
  exact ((volume_smooth.contDiffAt.add contDiffAt_const).sqrt hv.ne').inv (Real.sqrt_pos.mpr hv).ne'

def forwardUAction (t : ℝ) (ht:0≤t) : Op := multiply (forwardU t) (forwardU_smooth t ht)
def forwardAAction (t : ℝ) (ht:0≤t) : Op := multiply (forwardA t) (forwardA_smooth t ht)

private theorem inverseForwardU (t : ℝ) (ht:0≤t) :
    multiply (fun z : SourceCoordinateSlice=>reciprocalVolume (forwardPoint t z))
      (fun z=>ContDiffAt.comp (f:=forwardPoint t) z.val
        (reciprocal_volume_smooth ⟨_,forward_chart t ht z⟩) (forward_smooth t ht z))=forwardUAction t ht := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume (forwardPoint t z) : ℂ) • f z=(forwardU t z : ℂ) • f z
    have hv:=forward_volume t ht ⟨z,hz⟩
    unfold reciprocalVolume forwardU
    rw [hv]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (reciprocalVolume (forwardPoint t z) : ℂ) • f z=(forwardU t z : ℂ) • f z
    rw [hf,smul_zero,smul_zero]

private theorem inverseForwardA (t : ℝ) (ht:0≤t) :
    multiply (fun z : SourceCoordinateSlice=>inverseRootVolume (forwardPoint t z))
      (fun z=>ContDiffAt.comp (f:=forwardPoint t) z.val
        (inverse_root_volume_smooth ⟨_,forward_chart t ht z⟩) (forward_smooth t ht z))=forwardAAction t ht := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (inverseRootVolume (forwardPoint t z) : ℂ) • f z=(forwardA t z : ℂ) • f z
    have hv:=forward_volume t ht ⟨z,hz⟩
    unfold inverseRootVolume forwardA
    rw [hv]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (inverseRootVolume (forwardPoint t z) : ℂ) • f z=(forwardA t z : ℂ) • f z
    rw [hf,smul_zero,smul_zero]

theorem actual_forward_U_return (t : ℝ) (ht:0≤t) :
    inverseVolumeAction*sourceForwardCore t ht=sourceForwardCore t ht*forwardUAction t ht := by
  have h:=actual_forward_multiplier_transport t ht reciprocalVolume reciprocal_volume_smooth
  change inverseVolumeAction*sourceForwardCore t ht=_ at h
  rw [inverseForwardU] at h
  exact h

theorem actual_forward_a_return (t : ℝ) (ht:0≤t) :
    inverseRootAction*sourceForwardCore t ht=sourceForwardCore t ht*forwardAAction t ht := by
  have h:=actual_forward_multiplier_transport t ht inverseRootVolume inverse_root_volume_smooth
  change inverseRootAction*sourceForwardCore t ht=_ at h
  rw [inverseForwardA] at h
  exact h

theorem actual_forward_A_return (t : ℝ) (ht:0≤t) :
    combinedConjugate*sourceForwardCore t ht=
      sourceForwardCore t ht*forwardAAction t ht*combinedGenerator := by
  have hd:combinedGenerator*sourceForwardCore t ht=sourceForwardCore t ht*combinedGenerator :=
    (actual_forward_generator_commute t ht).eq
  have hA:inverseRootAction*sourceForwardCore t ht=sourceForwardCore t ht*forwardAAction t ht :=
    actual_forward_a_return t ht
  apply LinearMap.ext
  intro f
  have hdf:=LinearMap.congr_fun hd f
  have haf:=LinearMap.congr_fun hA (combinedGenerator f)
  simp only [Module.End.mul_apply] at hdf haf
  change inverseRootAction (combinedGenerator (sourceForwardCore t ht f))=
    sourceForwardCore t ht (forwardAAction t ht (combinedGenerator f))
  rw [hdf]
  exact haf
end LowEnergy.SourceClockPhiForwardNativeReturn
