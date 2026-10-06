import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceOriginalKineticSquare

/-! Return the generated square to every original core input and its actual electric form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourcePhysicalKineticSquare
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert GaussLiveMomentum GaussCoframeForm
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceKineticTranspose SourceOriginalKineticSquare
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace

def reciprocalVolume (z : SourceCoordinateSlice) : ℝ := (volume z)⁻¹
def inverseRootVolume (z : SourceCoordinateSlice) : ℝ := (Real.sqrt (volume z))⁻¹

theorem reciprocal_volume_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ reciprocalVolume z.val := volume_smooth.contDiffAt.inv (volume_pos z).ne'

theorem inverse_root_volume_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ inverseRootVolume z.val :=
  (volume_smooth.contDiffAt.sqrt (volume_pos z).ne').inv (Real.sqrt_pos.mpr (volume_pos z)).ne'

def inverseVolumeAction : CoreEnd := multiply reciprocalVolume reciprocal_volume_smooth
def inverseRootAction : CoreEnd := multiply inverseRootVolume inverse_root_volume_smooth

theorem volume_inverse (f : QuantumTest) : volumeAction (inverseVolumeAction f)=f := by
  apply DFunLike.ext
  intro z
  change (volume z : ℂ) • ((reciprocalVolume z : ℂ) • f z)=f z
  by_cases hz : z ∈ physicalChart
  · rw [smul_smul]
    have hn : (volume z : ℂ)≠0 := by exact_mod_cast (volume_pos ⟨z,hz⟩).ne'
    simp only [reciprocalVolume,Complex.ofReal_inv,mul_inv_cancel₀ hn,one_smul]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h)),smul_zero,smul_zero]

theorem inverse_root_square (f : QuantumTest) :
    inverseRootAction (inverseRootAction f)=inverseVolumeAction f := by
  apply DFunLike.ext
  intro z
  change (inverseRootVolume z : ℂ) • ((inverseRootVolume z : ℂ) • f z)=
    (reciprocalVolume z : ℂ) • f z
  by_cases hz : z ∈ physicalChart
  · have hs : inverseRootVolume z*inverseRootVolume z=reciprocalVolume z := by
      unfold inverseRootVolume reciprocalVolume
      rw [←mul_inv,Real.mul_self_sqrt (volume_pos ⟨z,hz⟩).le]
    rw [smul_smul,←Complex.ofReal_mul,hs]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h)),smul_zero,smul_zero,smul_zero]

private theorem volume_native_derivative (z : SourceCoordinateSlice) (v : Ambient) :
    fderiv ℝ volume z (direction v z)=0 := by
  rw [volume_derivative]
  simp [direction]

theorem inverse_root_native_derivative (z : physicalChart) (v : Ambient) :
    fderiv ℝ inverseRootVolume z.val (direction v z.val)=0 := by
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hs := hv.sqrt (volume_pos z).ne'
  have hd := (hasDerivAt_inv (Real.sqrt_pos.mpr (volume_pos z)).ne').comp_hasFDerivAt z.val hs
  change fderiv ℝ ((fun r : ℝ => r⁻¹) ∘ (fun w => Real.sqrt (volume w))) z.val _=0
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul,volume_native_derivative,mul_zero]

private theorem real_multiply (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) (f : QuantumTest) :
    (multiply a smooth f : SourceCoordinateSlice → FockFiber)=(fun z => a z • f z) := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem native_multiplier (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (zeroDerivative : ∀ z : physicalChart, ∀ v : Ambient, fderiv ℝ a z.val (direction v z.val)=0)
    (v : Ambient) : Commute (covariantMomentum v) (multiply a smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hd : directional v (multiply a smooth f) z=a z • directional v f z := by
      rw [directional_apply,real_multiply,
        fderiv_fun_smul ((smooth ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change a z • fderiv ℝ f z (direction v z)+fderiv ℝ a z (direction v z) • f z=_
      rw [zeroDerivative ⟨z,hz⟩ v,zero_smul,add_zero]
      rfl
    change (-Complex.I) • (directional v (multiply a smooth f) z+
      connection v z ((a z : ℂ) • f z))=
      (a z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))
    rw [hd,map_smul]
    have hr (p : FockFiber) : a z • p=(a z : ℂ) • p := by
      apply PiLp.ext;intro word;exact Complex.real_smul
    rw [hr,←smul_add,smul_comm]
  · have hl : covariantMomentum v (multiply a smooth f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((covariantMomentum v (multiply a smooth f)).tsupport_subset h))
    have hr : multiply a smooth (covariantMomentum v f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((multiply a smooth (covariantMomentum v f)).tsupport_subset h))
    exact hl.trans hr.symm

private theorem adjoint_multiplier (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) (v : Ambient)
    (commutes : Commute (covariantMomentum v) (multiply a smooth)) :
    Commute (GaussMomentumAdjoint.adjoint v) (multiply a smooth) := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have hc := LinearMap.congr_fun commutes.eq f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (multiply a smooth g))=
    sourcePair f (multiply a smooth (GaussMomentumAdjoint.adjoint v g))
  calc
    _ = sourcePair (covariantMomentum v f) (multiply a smooth g) := adjoint_pair _ _ _
    _ = sourcePair (multiply a smooth (covariantMomentum v f)) g := multiply_pair _ _ _ _
    _ = sourcePair (covariantMomentum v (multiply a smooth f)) g := congrArg (fun x => sourcePair x g) hc.symm
    _ = sourcePair (multiply a smooth f) (GaussMomentumAdjoint.adjoint v g) := (adjoint_pair _ _ _).symm
    _ = _ := (multiply_pair _ _ _ _).symm

theorem inverse_root_electric : Commute inverseRootAction gaugeKinetic := by
  have hP (v : Ambient) : inverseRootAction*covariantMomentum v-covariantMomentum v*inverseRootAction=
      (0 : ℂ) • covariantMomentum v := by
    have hp : Commute (covariantMomentum v) inverseRootAction :=
      native_multiplier inverseRootVolume inverse_root_volume_smooth inverse_root_native_derivative v
    rw [hp.eq]
    simp only [sub_self,zero_smul]
  have hA (v : Ambient) : inverseRootAction*GaussMomentumAdjoint.adjoint v-
      GaussMomentumAdjoint.adjoint v*inverseRootAction=(0 : ℂ) • GaussMomentumAdjoint.adjoint v := by
    have ha : Commute (GaussMomentumAdjoint.adjoint v) inverseRootAction :=
      adjoint_multiplier inverseRootVolume inverse_root_volume_smooth v
        (native_multiplier _ _ inverse_root_native_derivative v)
    rw [ha.eq]
    simp only [sub_self,zero_smul]
  have hM (i j : Fin 3) : inverseRootAction*multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)-
      multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*inverseRootAction=
        (0 : ℂ) • multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) := by
    have hc : Commute inverseRootAction (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
      apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
      exact smul_comm (inverseRootVolume z : ℂ) (gaugeWeight z i j : ℂ) (f z)
    rw [hc.eq,sub_self,zero_smul]
  have hterm (a : LieIndex) (i j : Fin 3) :
      inverseRootAction*sandwich (gaugeDirection i a) (gaugeDirection j a)
        (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)-
      sandwich (gaugeDirection i a) (gaugeDirection j a)
        (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*inverseRootAction=
      (0 : ℂ) • sandwich (gaugeDirection i a) (gaugeDirection j a)
        (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) := by
    have h := SourceDilationAlgebra.homogeneous_mul _ _ _ _ _ (hA (gaugeDirection i a))
      (SourceDilationAlgebra.homogeneous_mul _ _ _ _ _ (hM i j) (hP (gaugeDirection j a)))
    simpa only [zero_add] using! h
  have h := SourceDilationAlgebra.homogeneous_smul inverseRootAction _ (0 : ℂ) (1/2)
    (SourceDilationAlgebra.homogeneous_sum _ _ _ (fun a =>
      SourceDilationAlgebra.homogeneous_sum _ _ _ (fun i =>
        SourceDilationAlgebra.homogeneous_sum _ _ _ (hterm a i))))
  simpa only [zero_smul,sub_eq_zero] using! h

theorem electric_physical_return (f : QuantumTest) :
    sourcePair (inverseVolumeAction f) (volumeAction (gaugeKinetic (inverseVolumeAction f)))=
      sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f)) := by
  have hU (a b : QuantumTest) : sourcePair a (volumeAction b)=sourcePair (volumeAction a) b :=
    multiply_pair _ _ _ _
  have hS (a b : QuantumTest) : sourcePair a (inverseRootAction b)=sourcePair (inverseRootAction a) b :=
    multiply_pair _ _ _ _
  rw [hU,volume_inverse,←inverse_root_square]
  have hcomm (g : QuantumTest) : gaugeKinetic (inverseRootAction g)=inverseRootAction (gaugeKinetic g) :=
    (LinearMap.congr_fun inverse_root_electric.eq g).symm
  rw [hcomm,hS]

theorem physical_kinetic_square (f : QuantumTest) :
    ‖embed (kineticAction f)‖^2=
      ‖embed (symmetricScale (inverseVolumeAction f))‖^2+
      4*radialCoefficient^2*‖embed (dilation (inverseVolumeAction f))‖^2+
        sourceTime 0*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re := by
  have h := original_kinetic_square (inverseVolumeAction f)
  rw [volume_inverse,electric_physical_return] at h
  exact h

end LowEnergy.SourcePhysicalKineticSquare
