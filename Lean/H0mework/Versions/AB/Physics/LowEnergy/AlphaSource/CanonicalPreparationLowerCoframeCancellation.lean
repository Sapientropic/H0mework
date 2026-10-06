import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerCoframeDifferential

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerTensorBudget
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy PreparationScalarCoordinates
open PreparationVacuumLowerLeaves CanonicalPreparationMomentum
open scoped BigOperators ContDiff Topology Matrix

local notation "D" => GaussCoframeCore.coframeDirection

theorem K_derivative (i j : Fin 6) (z : physicalChart) (d : Configuration) :
    fderiv ℝ (K i j) z.val d=
      polynomialSlope z.val.1 d.1 i j/(4*volume z.val)-
        GaussCoframeKinetic.polynomial z.val.1 i j*volumeDerivative d z.val/(4*(volume z.val)^2) := by
  have hp : DifferentiableAt ℝ (fun w : Configuration => GaussCoframeKinetic.polynomial w.1 i j) z.val := by
    have hs : ContDiffAt ℝ ∞ (fun w => (4*volume w)*K i j w) z.val :=
      (contDiffAt_const.mul volume_smooth.contDiffAt).mul (K_smooth i j z)
    apply (hs.differentiableAt (by simp)).congr_of_eventuallyEq
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    unfold K
    field_simp [(volume_pos ⟨w,hw⟩).ne']
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hi := (hasDerivAt_inv (volume_pos z).ne').comp_hasFDerivAt z.val hv
  have hd := (hi.const_mul (1/4 : ℝ)).mul hp.hasFDerivAt
  have same : K i j=(fun w => (1/4 : ℝ)*(volume w)⁻¹*GaussCoframeKinetic.polynomial w.1 i j) := by
    funext w; unfold K; ring
  have read : fderiv ℝ (fun w => (1/4 : ℝ)*(volume w)⁻¹*GaussCoframeKinetic.polynomial w.1 i j) z.val=_ := hd.fderiv
  rw [same,read]
  simp only [add_apply,smul_apply,smul_eq_mul,Function.comp_apply]
  rw [polynomial_derivative,volume_derivative]
  field_simp [(volume_pos z).ne']
  ring

def divergenceWeight : Fin 6 → ℝ := ![1,0,0,-1,-1,-1]
def divergenceRead (i : Fin 6) (z : Configuration) : ℝ := divergenceWeight i*z.1 i/(2*volume z)

theorem K_divergence (i : Fin 6) (z : physicalChart) :
    (∑ j : Fin 6,fderiv ℝ (K i j) z.val (D j))=divergenceRead i z.val := by
  simp only [K_derivative,Fin.sum_univ_six]
  have h0 := z.property.1.ne'
  have h2 := z.property.2.1.ne'
  have h5 := z.property.2.2.1.ne'
  fin_cases i <;>
    norm_num [polynomialSlope,GaussCoframeKinetic.polynomial,divergenceRead,divergenceWeight,
      volume,volumeDerivative,GaussCoframeCore.coframeDirection,EuclideanSpace.single,PiLp.single_apply,Fin.ext_iff] <;>
    field_simp [h0,h2,h5] <;> ring_nf <;> rfl

theorem divergenceRead_derivative (i : Fin 6) (z : physicalChart) :
    fderiv ℝ (divergenceRead i) z.val (D i)=divergenceWeight i/(2*volume z.val)-
      divergenceWeight i*z.val.1 i*volumeDerivative (D i) z.val/(2*(volume z.val)^2) := by
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hi := (hasDerivAt_inv (volume_pos z).ne').comp_hasFDerivAt z.val hv
  have hd := (hi.const_mul (divergenceWeight i/2)).mul (qRead i).hasFDerivAt
  have same : divergenceRead i=(fun w => (divergenceWeight i/2)*(volume w)⁻¹*qRead i w) := by
    funext w; unfold divergenceRead; rw [qRead_apply]; ring
  have read : fderiv ℝ (fun w => (divergenceWeight i/2)*(volume w)⁻¹*qRead i w) z.val=_ := hd.fderiv
  rw [same,read]
  simp only [add_apply,smul_apply,smul_eq_mul,qRead_apply,volume_derivative,Function.comp_apply]
  have diagonal : (D i).1 i=1 := by simp [GaussCoframeCore.coframeDirection,EuclideanSpace.single]
  rw [diagonal]
  field_simp [(volume_pos z).ne']
  ring

theorem divergenceRead_sum (z : physicalChart) :
    (∑ i : Fin 6,fderiv ℝ (divergenceRead i) z.val (D i))=-(volume z.val)⁻¹ := by
  simp only [divergenceRead_derivative,Fin.sum_univ_six]
  have h0 := z.property.1.ne'
  have h2 := z.property.2.1.ne'
  have h5 := z.property.2.2.1.ne'
  norm_num [divergenceWeight,volume,volumeDerivative,GaussCoframeCore.coframeDirection,
    EuclideanSpace.single,PiLp.single_apply,Fin.ext_iff]
  field_simp [h0,h2,h5]
  ring_nf


theorem K_second_sum (z : physicalChart) :
    (∑ i : Fin 6,∑ j : Fin 6,
      fderiv ℝ (fun w => fderiv ℝ (K i j) w (D j)) z.val (D i))=-(volume z.val)⁻¹ := by
  calc
    _ = ∑ i : Fin 6,fderiv ℝ (divergenceRead i) z.val (D i) := by
      apply Finset.sum_congr rfl
      intro i _
      have same : (fun w => ∑ j : Fin 6,fderiv ℝ (K i j) w (D j))=ᶠ[𝓝 z.val]divergenceRead i := by
        filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
        exact K_divergence i ⟨w,hw⟩
      rw [←same.fderiv_eq,fderiv_fun_sum]
      · simp only [sum_apply]
      · intro j _
        exact (((K_smooth i j z).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    _ = _ := divergenceRead_sum z

def L (i : Fin 6) (z : Configuration) : ℝ := 2*halfLogVolume (D i) z

def halfFlux (i : Fin 6) (z : Configuration) : ℝ := z.1 i/(4*volume z)

theorem L_smooth (i : Fin 6) (z : physicalChart) : ContDiffAt ℝ ∞ (L i) z.val := by
  exact contDiffAt_const.mul (halfLogVolume_smooth (D i) z)

theorem K_halfFlux (i : Fin 6) (z : physicalChart) :
    (∑ j : Fin 6,K i j z.val*L j z.val)=halfFlux i z.val := by
  have hf := CanonicalPreparationCorrection.original_row_flux i z
  have scaled := congrArg (fun t : ℝ => (2/sourceTime 0)*t) hf
  rw [Finset.mul_sum] at scaled
  calc
    _ = ∑ j : Fin 6,(2/sourceTime 0)*(GaussCoframeKinetic.coefficient i j z.val*halfLogVolume (D j) z.val) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [K_original]
      unfold L
      ring
    _ = (2/sourceTime 0)*CanonicalPreparationCorrection.fluxCoefficient i z.val := scaled
    _ = _ := by
      unfold CanonicalPreparationCorrection.fluxCoefficient halfFlux
      field_simp [source_time_nonzero]
      ring

theorem halfFlux_derivative (i : Fin 6) (z : physicalChart) :
    fderiv ℝ (halfFlux i) z.val (D i)=1/(4*volume z.val)-
      z.val.1 i*volumeDerivative (D i) z.val/(4*(volume z.val)^2) := by
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hi := (hasDerivAt_inv (volume_pos z).ne').comp_hasFDerivAt z.val hv
  have hd := (hi.const_mul (1/4 : ℝ)).mul (qRead i).hasFDerivAt
  have same : halfFlux i=(fun w => (1/4 : ℝ)*(volume w)⁻¹*qRead i w) := by
    funext w; unfold halfFlux; rw [qRead_apply]; ring
  have read : fderiv ℝ (fun w => (1/4 : ℝ)*(volume w)⁻¹*qRead i w) z.val=_ := hd.fderiv
  rw [same,read]
  simp only [add_apply,smul_apply,smul_eq_mul,qRead_apply,volume_derivative,Function.comp_apply]
  have diagonal : (D i).1 i=1 := by simp [GaussCoframeCore.coframeDirection,EuclideanSpace.single]
  rw [diagonal]
  field_simp [(volume_pos z).ne']
  ring

theorem halfFlux_sum (z : physicalChart) :
    (∑ i : Fin 6,fderiv ℝ (halfFlux i) z.val (D i))=3/(4*volume z.val) := by
  simp only [halfFlux_derivative,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have group : (∑ i : Fin 6,z.val.1 i*volumeDerivative (D i) z.val/(4*(volume z.val)^2))=
      (3*volume z.val)/(4*(volume z.val)^2) := by
    rw [←Finset.sum_div,CanonicalPreparationCorrection.volume_euler_sum]
  rw [group]
  field_simp [(volume_pos z).ne']
  ring

theorem halfFlux_drift (z : physicalChart) :
    (∑ i : Fin 6,L i z.val*halfFlux i z.val)=3/(4*volume z.val) := by
  have hf := CanonicalPreparationCorrection.flux_drift z
  have scaled := congrArg (fun t : ℝ => (4/sourceTime 0)*t) hf
  rw [Finset.mul_sum] at scaled
  calc
    _ = ∑ i : Fin 6,(4/sourceTime 0)*(halfLogVolume (D i) z.val*
        CanonicalPreparationCorrection.fluxCoefficient i z.val) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold L halfFlux CanonicalPreparationCorrection.fluxCoefficient
      field_simp [source_time_nonzero]
      ring
    _ = _ := scaled.trans (by field_simp [source_time_nonzero]; ring)

def coframeHalf (z : Configuration) : ℝ :=
  ∑ i : Fin 6,∑ j : Fin 6,
    (K i j z*(L i z*L j z+fderiv ℝ (L j) z (D i))+
      fderiv ℝ (K i j) z (D i)*L j z)

def coframeQuarter (z : Configuration) : ℝ :=
  (1/4 : ℝ)*∑ i : Fin 6,∑ j : Fin 6,
    fderiv ℝ (fun w => fderiv ℝ (K i j) w (D j)) z (D i)

theorem coframeHalf_cancel (z : physicalChart) : coframeHalf z.val=3/(2*volume z.val) := by
  have product (i j : Fin 6) : fderiv ℝ (fun w => K i j w*L j w) z.val (D i)=
      K i j z.val*fderiv ℝ (L j) z.val (D i)+L j z.val*fderiv ℝ (K i j) z.val (D i) := by
    have hd := ((K_smooth i j z).differentiableAt (by simp)).hasFDerivAt.mul
      ((L_smooth j z).differentiableAt (by simp)).hasFDerivAt
    exact congrArg (fun F : Configuration →L[ℝ] ℝ => F (D i)) hd.fderiv
  have row (i : Fin 6) : (∑ j : Fin 6,
      (K i j z.val*(L i z.val*L j z.val+fderiv ℝ (L j) z.val (D i))+
        fderiv ℝ (K i j) z.val (D i)*L j z.val))=
      fderiv ℝ (halfFlux i) z.val (D i)+L i z.val*halfFlux i z.val := by
    have same : (fun w => ∑ j : Fin 6,K i j w*L j w)=ᶠ[𝓝 z.val]halfFlux i := by
      filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
      exact K_halfFlux i ⟨w,hw⟩
    rw [←same.fderiv_eq,fderiv_fun_sum (fun j _ =>
      ((K_smooth i j z).mul (L_smooth j z)).differentiableAt (by simp))]
    simp only [sum_apply,product]
    rw [←K_halfFlux i z,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold coframeHalf
  simp only [row,Finset.sum_add_distrib,halfFlux_sum,halfFlux_drift]
  ring

theorem coframeQuarter_cancel (z : physicalChart) : coframeQuarter z.val=-(1/(4*volume z.val)) := by
  rw [coframeQuarter,K_second_sum]
  ring

theorem coframe_cancellation (z : physicalChart) :
    coframeHalf z.val+coframeQuarter z.val=5/(4*volume z.val) := by
  rw [coframeHalf_cancel,coframeQuarter_cancel]
  ring

end LowEnergy.PreparationVacuumLowerTensorBudget
