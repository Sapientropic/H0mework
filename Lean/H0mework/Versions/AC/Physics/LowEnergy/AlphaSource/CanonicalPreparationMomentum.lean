import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCore
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussCoframeKinetic

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.CanonicalPreparationMomentum
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussDensityCore GaussHistoryHilbert GaussNativeEnergy
open CanonicalPreparationCore
open MeasureTheory Set Filter
open scoped ContDiff Distributions Topology

def volumeDerivative (D z : SourceCoordinateSlice) : ℝ :=
  D.1 0*z.1 2*z.1 5+z.1 0*D.1 2*z.1 5+z.1 0*z.1 2*D.1 5

theorem volume_derivative (D z : SourceCoordinateSlice) :
    fderiv ℝ volume z D=volumeDerivative D z := by
  let read (i : Fin 6) : SourceCoordinateSlice →L[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 6 => ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _)
  have h0 : HasFDerivAt (read 0) (read 0) z := (read 0).hasFDerivAt
  have h2 : HasFDerivAt (read 2) (read 2) z := (read 2).hasFDerivAt
  have h5 : HasFDerivAt (read 5) (read 5) z := (read 5).hasFDerivAt
  have h := (h0.mul h2).mul h5
  change HasFDerivAt volume _ z at h
  rw [h.fderiv]
  change (z.1 0*z.1 2)*D.1 5+z.1 5*(z.1 0*D.1 2+z.1 2*D.1 0)=volumeDerivative D z
  unfold volumeDerivative
  ring

def halfLogVolume (D z : SourceCoordinateSlice) : ℝ := volumeDerivative D z/(2*volume z)

theorem halfLogVolume_smooth (D : SourceCoordinateSlice) (z : physicalChart) :
    ContDiffAt ℝ ∞ (halfLogVolume D) z.val := by
  have hd : ContDiff ℝ ∞ (volumeDerivative D) := by unfold volumeDerivative; fun_prop
  exact hd.contDiffAt.div (contDiffAt_const.mul volume_smooth.contDiffAt)
    (mul_ne_zero (by norm_num) (volume_pos z).ne')

def drift (D : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ScalarTest :=
  GaussDensityCore.multiply (fun z => (halfLogVolume D z : ℂ))
    (fun z => Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (halfLogVolume_smooth D z))

theorem numberRaise_square (z : physicalChart) :
    numberRaise z.val*numberRaise z.val*(volume z.val : ℂ)=1 := by
  rw [numberRaise_volume]
  change (Real.sqrt (volume z.val) : ℂ)⁻¹*(Real.sqrt (volume z.val) : ℂ)⁻¹*
    (volume z.val : ℂ)=1
  have sq : (Real.sqrt (volume z.val) : ℂ)^2=(volume z.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt (volume_pos z).le
  have nz : (Real.sqrt (volume z.val) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (volume_pos z)).ne'
  rw [←sq]
  field_simp

theorem numberRaise_derivative (D : SourceCoordinateSlice) (z : physicalChart) :
    fderiv ℝ numberRaise z.val D=
      -numberRaise z.val*(halfLogVolume D z.val : ℂ) := by
  have hr := ((numberRaise_smooth z).differentiableAt (by simp)).hasFDerivAt
  have hv := (Complex.ofRealCLM.hasFDerivAt.comp z.val
    (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have equal : (fun w => numberRaise w*numberRaise w*(volume w : ℂ)) =ᶠ[𝓝 z.val]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact numberRaise_square ⟨w,hw⟩
  have derived := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L D)
    equal.fderiv_eq
  have product : fderiv ℝ (fun w => numberRaise w*numberRaise w*(volume w : ℂ)) z.val =
      (numberRaise z.val*numberRaise z.val) •
        (Complex.ofRealCLM.comp (fderiv ℝ volume z.val))+
      (volume z.val : ℂ) • (numberRaise z.val • fderiv ℝ numberRaise z.val+
        numberRaise z.val • fderiv ℝ numberRaise z.val) := by
    simpa using! (hr.mul hr |>.mul hv).fderiv
  rw [product] at derived
  have constant : fderiv ℝ (fun _ : SourceCoordinateSlice => (1 : ℂ)) z.val=0 :=
    (hasFDerivAt_const (1 : ℂ) z.val).fderiv
  rw [constant] at derived
  simp only [zero_apply,add_apply,smul_apply,
    smul_eq_mul,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,
    volume_derivative] at derived
  have nz : (volume z.val : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (volume_pos z).ne'
  have nr : numberRaise z.val≠0 := by
    intro h
    have square := numberRaise_square z
    simp [h] at square
  simp only [halfLogVolume,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp
  apply mul_left_cancel₀ nr
  linear_combination derived

theorem weightedTranspose_expand (N : ℕ) (D : SourceCoordinateSlice)
    (f : ScalarTest) (z : physicalChart) :
    weightedTranspose N D f z.val = -GaussDensityCore.derivative D f z.val-
      (complexDensity N z.val)⁻¹*fderiv ℝ (complexDensity N) z.val D*f z.val := by
  rw [weightedTranspose_apply,GaussDensityCore.derivative_apply]
  have hd := ((complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have product : fderiv ℝ (fun w => complexDensity N w*f w) z.val=
      complexDensity N z.val • fderiv ℝ f z.val+
        f z.val • fderiv ℝ (complexDensity N) z.val := by simpa using! (hd.mul hf).fderiv
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul]
  have nz : complexDensity N z.val≠0 := by
    change (density N z.val : ℂ)≠0
    exact_mod_cast (density_pos N z).ne'
  field_simp
  ring

theorem density_succ : complexDensity 1 = fun z => complexDensity 0 z*(volume z : ℂ) := by
  funext z
  simp only [complexDensity,density,GaussNativeEnergy.volume]
  push_cast
  ring

theorem density_log_change (D : SourceCoordinateSlice) (z : physicalChart) :
    (complexDensity 1 z.val)⁻¹*fderiv ℝ (complexDensity 1) z.val D=
      (complexDensity 0 z.val)⁻¹*fderiv ℝ (complexDensity 0) z.val D+
        2*(halfLogVolume D z.val : ℂ) := by
  have hd := ((complexDensity_smooth 0 z).differentiableAt (by simp)).hasFDerivAt
  have hv := Complex.ofRealCLM.hasFDerivAt.comp z.val
    (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have product : fderiv ℝ (fun w => complexDensity 0 w*(volume w : ℂ)) z.val=
      complexDensity 0 z.val • (Complex.ofRealCLM.comp (fderiv ℝ volume z.val))+
        (volume z.val : ℂ) • fderiv ℝ (complexDensity 0) z.val := by
    simpa using! (hd.mul hv).fderiv
  rw [density_succ,product]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,volume_derivative,halfLogVolume,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_ofNat]
  have h0 : complexDensity 0 z.val≠0 := by
    change (density 0 z.val : ℂ)≠0
    exact_mod_cast (density_pos 0 z).ne'
  have hv0 : (volume z.val : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (volume_pos z).ne'
  field_simp
  ring

theorem derivative_numberRaise_apply (D : SourceCoordinateSlice) (f : ScalarTest)
    (z : physicalChart) :
    GaussDensityCore.derivative D (numberRaiseCore f) z.val =
      numberRaise z.val*(GaussDensityCore.derivative D f z.val-drift D f z.val) := by
  rw [GaussDensityCore.derivative_apply,GaussDensityCore.derivative_apply]
  have hr := ((numberRaise_smooth z).differentiableAt (by simp)).hasFDerivAt
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  change fderiv ℝ (fun w => numberRaise w*f w) z.val D=_
  have product : fderiv ℝ (fun w => numberRaise w*f w) z.val=
      numberRaise z.val • fderiv ℝ f z.val+f z.val • fderiv ℝ numberRaise z.val := by
    simpa using! (hr.mul hf).fderiv
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul,numberRaise_derivative]
  change _ = numberRaise z.val*(fderiv ℝ f z.val D-(halfLogVolume D z.val : ℂ)*f z.val)
  ring

private theorem scalarTest_ext {f g : ScalarTest} (h : ∀ z : physicalChart, f z.val=g z.val) : f=g := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · exact h ⟨z,hz⟩
  · rw [image_eq_zero_of_notMem_tsupport (fun t => hz (f.tsupport_subset t)),
      image_eq_zero_of_notMem_tsupport (fun t => hz (g.tsupport_subset t))]

theorem derivative_numberRaise (D : SourceCoordinateSlice) (f : ScalarTest) :
    GaussDensityCore.derivative D (numberRaiseCore f)=
      numberRaiseCore (GaussDensityCore.derivative D f-drift D f) := by
  apply scalarTest_ext
  intro z
  exact derivative_numberRaise_apply D f z

theorem transpose_numberRaise (D : SourceCoordinateSlice) (f : ScalarTest) :
    weightedTranspose 1 D (numberRaiseCore f)=
      numberRaiseCore (weightedTranspose 0 D f-drift D f) := by
  apply scalarTest_ext
  intro z
  rw [weightedTranspose_expand,derivative_numberRaise_apply,numberRaiseCore_apply,
    numberRaiseCore_apply]
  change - (numberRaise z.val*(GaussDensityCore.derivative D f z.val-drift D f z.val))-
    (complexDensity 1 z.val)⁻¹*fderiv ℝ (complexDensity 1) z.val D*(numberRaise z.val*f z.val)=
      numberRaise z.val*(weightedTranspose 0 D f z.val-drift D f z.val)
  rw [weightedTranspose_expand,density_log_change]
  change _=numberRaise z.val*(-GaussDensityCore.derivative D f z.val-
    (complexDensity 0 z.val)⁻¹*fderiv ℝ (complexDensity 0) z.val D*f z.val-
      (halfLogVolume D z.val : ℂ)*f z.val)
  change - (numberRaise z.val * (GaussDensityCore.derivative D f z.val-
    (halfLogVolume D z.val : ℂ)*f z.val))-
    ((complexDensity 0 z.val)⁻¹*fderiv ℝ (complexDensity 0) z.val D+
      2*(halfLogVolume D z.val : ℂ))*(numberRaise z.val*f z.val)=_
  ring

theorem weighted_symmetric_momentum (D : SourceCoordinateSlice) (f : ScalarTest) :
    (1/2 : ℂ) • ((-Complex.I) • GaussDensityCore.derivative D (numberRaiseCore f)+
      Complex.I • weightedTranspose 1 D (numberRaiseCore f))=
    numberRaiseCore ((1/2 : ℂ) • ((-Complex.I) • GaussDensityCore.derivative D f+
      Complex.I • weightedTranspose 0 D f)) := by
  rw [derivative_numberRaise,transpose_numberRaise]
  simp only [map_smul,map_add,map_sub,smul_sub]
  module

theorem gauge_drift_zero (D : SourceCoordinateSlice) (noCoframe : D.1=0)
    (z : SourceCoordinateSlice) : halfLogVolume D z=0 := by
  simp [halfLogVolume,volumeDerivative,noCoframe]

theorem live_direction_drift_zero (v : GaussLiveMomentum.Ambient)
    (atPoint z : SourceCoordinateSlice) :
    halfLogVolume (GaussCoreDifferential.direction v atPoint) z=0 :=
  gauge_drift_zero _ rfl z

theorem coframe_source_drift :
    halfLogVolume (GaussCoframeCore.coframeDirection 0) sourcePoint.val=1/2 := by
  have h2 : (2 : Fin 6)≠0 := by decide
  have h5 : (5 : Fin 6)≠0 := by decide
  have q2 : (![1,0,1,0,0,1] : Fin 6 → ℝ) 2=1 := rfl
  have q5 : (![1,0,1,0,0,1] : Fin 6 → ℝ) 5=1 := rfl
  norm_num [halfLogVolume,volumeDerivative,GaussCoframeCore.coframeDirection,GaussNativeEnergy.volume,
    GaussHistoryHilbert.sourcePoint,SourceQuantumConfigurationHilbert.sourceCoframe_eq,
    EuclideanSpace.single,h2,h5,q2,q5]

theorem coframe_source_raise_derivative :
    fderiv ℝ numberRaise GaussHistoryHilbert.sourcePoint.val
      (GaussCoframeCore.coframeDirection 0)=-(1/2 : ℂ) := by
  rw [numberRaise_derivative,coframe_source_drift,numberRaise_source]
  norm_num

end LowEnergy.CanonicalPreparationMomentum
