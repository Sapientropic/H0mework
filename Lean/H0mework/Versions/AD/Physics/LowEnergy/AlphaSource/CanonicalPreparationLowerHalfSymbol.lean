import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerWeightedAction

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerTensor
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussDensityCore
open PreparationScalarCoordinates CanonicalPreparationCore
open PreparationVacuumLowerLeaves PreparationActualFactor PreparationVacuumDensityTrace PreparationVacuumFactor
open scoped BigOperators ContDiff Topology

def ell (i : Fin 100) (z : SourceCoordinateSlice) : ℂ := sourceHalfLog (rawDirection i) z
def P (i k : Fin 100) (z : SourceCoordinateSlice) : ℂ := sourceTensor i k z

theorem P_smooth (i k : Fin 100) (z : physicalChart) : ContDiffAt ℝ ∞ (P i k) z.val := by
  have smooth : ContDiffAt ℝ ∞ (sourceTensor i k) z.val := by
    unfold sourceTensor
    apply ContDiffAt.sum
    intro a _
    exact ((sourceCoefficient_smooth a z).mul
      ((rawCovector i).contDiff.contDiffAt.comp z.val (sourceLeft_smooth a z))).mul
        ((rawCovector k).contDiff.contDiffAt.comp z.val (sourceRight_smooth a z))
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z.val smooth

theorem ell_smooth (i : Fin 100) (z : physicalChart) : ContDiffAt ℝ ∞ (ell i) z.val := by
  have half : ContDiffAt ℝ ∞ sourceHalf z.val := coreHalfDensity_smooth 0 z
  exact (half.inv (coreHalfDensity_ne_zero 0 z)).mul
    ((half.fderiv_right (by simp)).clm_apply contDiffAt_const)

theorem tensorFlux_smooth (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => tensorFlux f w i) z.val := by
  unfold tensorFlux
  apply ContDiffAt.sum
  intro k _
  have derivative : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  exact (P_smooth i k z).mul (derivative.contDiffAt.clm_apply contDiffAt_const)

def halfFlux (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  ∑ k : Fin 100,P i k z*(fderiv ℝ f z (rawDirection k)-ell k z*f z)

theorem originalHalfFlux (f : ScalarTest) (z : physicalChart) (i : Fin 100) :
    sourceHalf z.val*tensorFlux (inverseHalfCore f) z.val i=halfFlux f z.val i := by
  unfold tensorFlux halfFlux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have derivative:=sourceHalf_derivative_readback (rawDirection k) f z
  change sourceHalf z.val*(P i k z.val*fderiv ℝ (inverseHalfCore f) z.val (rawDirection k))=
    P i k z.val*(fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)
  rw [mul_left_comm,derivative]
  rfl

theorem halfFlux_smooth (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => halfFlux f w i) z.val := by
  unfold halfFlux
  apply ContDiffAt.sum
  intro k _
  have derivative : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  exact (P_smooth i k z).mul ((derivative.contDiffAt.clm_apply contDiffAt_const).sub
    ((ell_smooth k z).mul f.contDiff.contDiffAt))

private theorem halfFlux_derivative (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    fderiv ℝ (fun w => halfFlux f w i) z.val (rawDirection i)=
      sourceHalf z.val*fderiv ℝ (fun w => tensorFlux (inverseHalfCore f) w i) z.val (rawDirection i)+
      tensorFlux (inverseHalfCore f) z.val i*fderiv ℝ sourceHalf z.val (rawDirection i) := by
  have equal : (fun w => sourceHalf w*tensorFlux (inverseHalfCore f) w i)=ᶠ[𝓝 z.val]
      (fun w => halfFlux f w i) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact originalHalfFlux f ⟨w,hw⟩ i
  have hu:=((coreHalfDensity_smooth 0 z).differentiableAt (by simp)).hasFDerivAt
  have hg:=((tensorFlux_smooth (inverseHalfCore f) i z).differentiableAt (by simp)).hasFDerivAt
  have product : fderiv ℝ (fun w => sourceHalf w*tensorFlux (inverseHalfCore f) w i) z.val=
      sourceHalf z.val • fderiv ℝ (fun w => tensorFlux (inverseHalfCore f) w i) z.val+
      tensorFlux (inverseHalfCore f) z.val i • fderiv ℝ sourceHalf z.val := by
    simpa only [sourceHalf] using! (hu.mul hg).fderiv
  rw [←equal.fderiv_eq,product]
  rfl

theorem originalHalfDivergence (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*rawWeightedDivergence (tensorFlux (inverseHalfCore f)) z.val=
      -∑ i : Fin 100,(fderiv ℝ (fun w => halfFlux f w i) z.val (rawDirection i)+ell i z.val*halfFlux f z.val i) := by
  unfold rawWeightedDivergence
  rw [mul_neg,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [densityDrift_halfLog,halfFlux_derivative,←originalHalfFlux f z i]
  have nonzero:=coreHalfDensity_ne_zero 0 z
  change sourceHalf z.val*(fderiv ℝ (fun w => tensorFlux (inverseHalfCore f) w i) z.val (rawDirection i)+
      2*((sourceHalf z.val)⁻¹*fderiv ℝ sourceHalf z.val (rawDirection i))*tensorFlux (inverseHalfCore f) z.val i)=
    sourceHalf z.val*fderiv ℝ (fun w => tensorFlux (inverseHalfCore f) w i) z.val (rawDirection i)+
      tensorFlux (inverseHalfCore f) z.val i*fderiv ℝ sourceHalf z.val (rawDirection i)+
      ((sourceHalf z.val)⁻¹*fderiv ℝ sourceHalf z.val (rawDirection i))*
        (sourceHalf z.val*tensorFlux (inverseHalfCore f) z.val i)
  change sourceHalf z.val≠0 at nonzero
  field_simp
  ring

theorem originalHalfVacuum_fluxAction (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      (-∑ i : Fin 100,(fderiv ℝ (fun w => halfFlux f w i) z.val (rawDirection i)+ell i z.val*halfFlux f z.val i))+
      ((potential z.val+GaussCoframeForm.volumePotential z.val : ℝ) : ℂ)*f z.val := by
  rw [originalVacuum_tensorAction,mul_add,originalHalfDivergence]
  have cancel:=sourceHalf_inverseCore f z
  rw [show sourceHalf z.val*
      (((potential z.val+GaussCoframeForm.volumePotential z.val : ℝ) : ℂ)*inverseHalfCore f z.val)=
    ((potential z.val+GaussCoframeForm.volumePotential z.val : ℝ) : ℂ)*
      (sourceHalf z.val*inverseHalfCore f z.val) by ring,cancel]

def tensorHalfPotential (z : SourceCoordinateSlice) : ℂ :=
  ∑ i : Fin 100,∑ k : Fin 100,
    (fderiv ℝ (P i k) z (rawDirection i)*ell k z+
      P i k z*(fderiv ℝ (ell k) z (rawDirection i)+ell i z*ell k z))

def tensorPrincipalAction (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  -∑ i : Fin 100,∑ k : Fin 100,
    (P i k z*fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z (rawDirection i)+
      fderiv ℝ (P i k) z (rawDirection i)*fderiv ℝ f z (rawDirection k))

private theorem halfFlux_expand (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    fderiv ℝ (fun w => halfFlux f w i) z.val (rawDirection i)=
      ∑ k : Fin 100,
        (fderiv ℝ (P i k) z.val (rawDirection i)*
          (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)+
        P i k z.val*(fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)-
          fderiv ℝ (ell k) z.val (rawDirection i)*f z.val-ell k z.val*fderiv ℝ f z.val (rawDirection i))) := by
  have derivative : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  have terms (k : Fin 100) : DifferentiableAt ℝ
      (fun w => P i k w*(fderiv ℝ f w (rawDirection k)-ell k w*f w)) z.val :=
    ((P_smooth i k z).mul ((derivative.contDiffAt.clm_apply contDiffAt_const).sub
      ((ell_smooth k z).mul f.contDiff.contDiffAt))).differentiableAt (by simp)
  unfold halfFlux
  rw [fderiv_fun_sum (fun k _ => terms k)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hp:=((P_smooth i k z).differentiableAt (by simp)).hasFDerivAt
  have hd:=((derivative.contDiffAt (x:=z.val) |>.clm_apply (contDiffAt_const (c:=rawDirection k))).differentiableAt
    (by simp)).hasFDerivAt
  have he:=((ell_smooth k z).differentiableAt (by simp)).hasFDerivAt
  have hf:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have product : fderiv ℝ (fun w => P i k w*(fderiv ℝ f w (rawDirection k)-ell k w*f w)) z.val=
      P i k z.val • (fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val-
        (ell k z.val • fderiv ℝ f z.val+f z.val • fderiv ℝ (ell k) z.val))+
      (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val) • fderiv ℝ (P i k) z.val := by
    simpa only using! (hp.mul (hd.sub (he.mul hf))).fderiv
  rw [product]
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul]
  ring

theorem originalHalfVacuum_normalForm (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      tensorPrincipalAction f z.val+
        (tensorHalfPotential z.val+((potential z.val+GaussCoframeForm.volumePotential z.val : ℝ) : ℂ))*f z.val := by
  have cross : (∑ i : Fin 100,∑ k : Fin 100,P i k z.val*ell k z.val*fderiv ℝ f z.val (rawDirection i))=
      ∑ i : Fin 100,∑ k : Fin 100,P i k z.val*ell i z.val*fderiv ℝ f z.val (rawDirection k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    unfold P
    rw [sourceTensor_symmetric k i]
  have term (i k : Fin 100) :
      -(fderiv ℝ (P i k) z.val (rawDirection i)*
          (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)+
        P i k z.val*(fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)-
          fderiv ℝ (ell k) z.val (rawDirection i)*f z.val-ell k z.val*fderiv ℝ f z.val (rawDirection i))+
        ell i z.val*(P i k z.val*(fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)))=
      -(P i k z.val*fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)+
        fderiv ℝ (P i k) z.val (rawDirection i)*fderiv ℝ f z.val (rawDirection k))+
      (fderiv ℝ (P i k) z.val (rawDirection i)*ell k z.val+
        P i k z.val*(fderiv ℝ (ell k) z.val (rawDirection i)+ell i z.val*ell k z.val))*f z.val+
      P i k z.val*ell k z.val*fderiv ℝ f z.val (rawDirection i)-
        P i k z.val*ell i z.val*fderiv ℝ f z.val (rawDirection k) := by ring
  have fluxterm (i : Fin 100) :
      fderiv ℝ (fun w => halfFlux f w i) z.val (rawDirection i)+ell i z.val*halfFlux f z.val i=
      ∑ k : Fin 100,(fderiv ℝ (P i k) z.val (rawDirection i)*
          (fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val)+
        P i k z.val*(fderiv ℝ (fun w => fderiv ℝ f w (rawDirection k)) z.val (rawDirection i)-
          fderiv ℝ (ell k) z.val (rawDirection i)*f z.val-ell k z.val*fderiv ℝ f z.val (rawDirection i))+
        ell i z.val*(P i k z.val*(fderiv ℝ f z.val (rawDirection k)-ell k z.val*f z.val))) := by
    rw [halfFlux_expand]
    simp only [halfFlux,Finset.mul_sum,←Finset.sum_add_distrib]
  rw [originalHalfVacuum_fluxAction]
  simp only [fluxterm]
  rw [←Finset.sum_neg_distrib]
  simp only [←Finset.sum_neg_distrib]
  simp only [term]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,←Finset.sum_mul]
  have crossFactored : (∑ i : Fin 100,(∑ k : Fin 100,P i k z.val*ell k z.val)*
      fderiv ℝ f z.val (rawDirection i))=
      ∑ i : Fin 100,∑ k : Fin 100,P i k z.val*ell i z.val*fderiv ℝ f z.val (rawDirection k) := by
    simpa only [Finset.sum_mul] using cross
  rw [crossFactored]
  unfold tensorPrincipalAction tensorHalfPotential
  simp only [Finset.sum_add_distrib]
  ring

def tensorWeylCorrection (z : SourceCoordinateSlice) : ℂ :=
  (1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,
    fderiv ℝ (fun w => fderiv ℝ (P i k) w (rawDirection k)) z (rawDirection i)

def sourceWeylZero (z : SourceCoordinateSlice) : ℂ :=
  tensorHalfPotential z+((potential z+GaussCoframeForm.volumePotential z : ℝ) : ℂ)+tensorWeylCorrection z

def sourceWeylPrincipalAction (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  tensorPrincipalAction f z-tensorWeylCorrection z*f z

theorem originalHalfVacuum_WeylZero (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      sourceWeylPrincipalAction f z.val+sourceWeylZero z.val*f z.val := by
  rw [originalHalfVacuum_normalForm]
  unfold sourceWeylPrincipalAction sourceWeylZero
  ring

end LowEnergy.PreparationVacuumLowerTensor
