import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockAcceleration
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeClockGram
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeCovariantSquare
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCovariantGramRadial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockReflectedForm
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussCoframeForm SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceQuantumScalarChart SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceCoframeDilation SourcePhysicalKineticSquare SourceKineticTranspose SourceDilationRemainder
open SourceClockAcceleration SourceCoframeCovariantAction SourceCoframeCovariantSquare
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] GaussDiagonalHistory.diagonalAction dilation

private theorem pair_add_right (f g h : QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_right (f g : QuantumTest) (c : ℂ) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_smul_left (f g : QuantumTest) (c : ℂ) : sourcePair (c • f) g=(starRingEnd ℂ c)*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_sum_right {ι : Type*} [Fintype ι] (f : QuantumTest) (g : ι → QuantumTest) :
    sourcePair f (∑i,g i)=∑i,sourcePair f (g i) := by simp only [sourcePair,map_sum,inner_sum]
private theorem pair_sum_left {ι : Type*} [Fintype ι] (f : ι → QuantumTest) (g : QuantumTest) :
    sourcePair (∑i,f i) g=∑i,sourcePair (f i) g := by simp only [sourcePair,map_sum,sum_inner]
private theorem pair_norm (f : QuantumTest) : (sourcePair f f).re=‖embed f‖^2 := by
  simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜 := ℂ) (embed f)
private theorem pair_self_im (f : QuantumTest) : (sourcePair f f).im=0 := by
  have h := inner_self_im (𝕜 := ℂ) (embed f)
  exact h

/-- The same covariant coframe columns that already contain all four mixed terms. -/
def eulerMomentum : End := ∑ i : Fin 6,coordinateAction i*SourceCoframeCovariantAction.covariantMomentum i
def densityShift : End := number+(4:ℂ) • (1:End)

private theorem connection_euler : (∑ i : Fin 6,coordinateAction i*connectionAction i)=(0:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have h := congrArg (fun A : SourceCoframeSpinConnection.FiberEnd => A (f z))
      (SourceCovariantGramRadial.original_connection_radial ⟨z,hz⟩)
    simp only [sum_apply,smul_apply] at h
    change (∑ i : Fin 6,(z.1 i : ℂ) • (SourceCoframeSpinConnection.connectionFiber i z (f z)))=0
    have he (i : Fin 6) : (z.1 i : ℂ) • (SourceCoframeSpinConnection.connectionFiber i z (f z))=
        z.1 i • (SourceCoframeSpinConnection.connectionFiber i z (f z)) := by
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    simpa only [he,zero_apply] using h
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem euler_source : eulerMomentum=(-Complex.I) • eulerAction := by
  unfold eulerMomentum SourceCoframeCovariantAction.covariantMomentum
  simp only [mul_add,Finset.sum_add_distrib,connection_euler,add_zero]
  unfold eulerAction GaussCoframeCore.momentum
  simp only [mul_smul_comm,←Finset.smul_sum]

private theorem density_pair (f g : QuantumTest) : sourcePair f (densityShift g)=sourcePair (densityShift f) g := by
  change sourcePair f (number g+(4:ℂ) • g)=sourcePair (number f+(4:ℂ) • f) g
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,map_ofNat]
  exact congrArg (·+(4:ℂ)*sourcePair f g) (number_pair f g)
private theorem density_current : Commute dilation densityShift := by
  have hn : Commute dilation number := sub_eq_zero.mp SourceDilationKinetic.number_current
  exact hn.add_right ((Commute.one_right dilation).smul_right (4:ℂ))
private theorem density_real (f : QuantumTest) : (sourcePair f (densityShift f)).im=0 := by
  have h := congrArg Complex.im (pair_conjugate f (densityShift f))
  rw [←density_pair] at h
  simp only [Complex.conj_im] at h
  linarith
private theorem dilation_real (f : QuantumTest) : (sourcePair f (dilation f)).im=0 := by
  have h := congrArg Complex.im (pair_conjugate f (dilation f))
  rw [←dilation_pair] at h
  simp only [Complex.conj_im] at h
  linarith
private theorem mixed_real (f : QuantumTest) : (sourcePair (dilation f) (densityShift f)).im=0 := by
  have hc := LinearMap.congr_fun density_current.eq f
  have he : sourcePair (dilation f) (densityShift f)=sourcePair (densityShift f) (dilation f) := by
    rw [←dilation_pair,←density_pair]
    exact congrArg (sourcePair f) hc
  have h := congrArg Complex.im (pair_conjugate (dilation f) (densityShift f))
  rw [←he] at h
  simp only [Complex.conj_im] at h
  linarith

private theorem euler_dilation : eulerMomentum=(3/2:ℂ) • dilation+(3*Complex.I/2) • densityShift := by
  rw [euler_source,dilation_operator]
  unfold densityShift
  simp only [smul_add,smul_smul]
  module

/-- The complete Number density correction is fixed by the original formal transpose. -/
theorem original_dilation_density_square (f : QuantumTest) :
    ‖embed (dilation f)‖^2=(4/9:ℝ)*‖embed (eulerMomentum f)‖^2-‖embed (densityShift f)‖^2 := by
  have hx : embed (eulerMomentum f)=(3/2:ℂ) • embed (dilation f)+
      (3*Complex.I/2) • embed (densityShift f) := by
    rw [euler_dilation]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
  have hn : ‖embed (eulerMomentum f)‖^2=
      (9/4:ℝ)*(‖embed (dilation f)‖^2+‖embed (densityShift f)‖^2) := by
    rw [hx,norm_add_sq (𝕜 := ℂ),norm_smul,norm_smul,inner_smul_left,inner_smul_right]
    have h1 : ‖(3/2:ℂ)‖=(3/2:ℝ) := by norm_num
    have h2 : ‖(3*Complex.I/2:ℂ)‖=(3/2:ℝ) := by rw [norm_div,norm_mul];norm_num
    rw [h1,h2]
    have hi := mixed_real f
    change (sourcePair (dilation f) (densityShift f)).im=0 at hi
    change _+2*((starRingEnd ℂ (3/2:ℂ))*((3*Complex.I/2)*sourcePair (dilation f) (densityShift f))).re+_=_
    simp only [map_div₀,map_ofNat,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,
      Complex.I_re,Complex.I_im]
    norm_num
    rw [hi]
    ring
  nlinarith only [hn]

private theorem euler_imaginary (f : QuantumTest) :
    (sourcePair f (eulerMomentum f)).im=(3/2:ℝ)*(sourcePair f (densityShift f)).re := by
  rw [euler_dilation,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,
    pair_add_right,pair_smul_right,pair_smul_right]
  simp only [Complex.add_im,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.I_re,Complex.I_im]
  norm_num
  rw [dilation_real]

private theorem covariant_adjoint_pair (i : Fin 6) (f g : QuantumTest) :
    sourcePair f (covariantAdjoint i g)=sourcePair (SourceCoframeCovariantAction.covariantMomentum i f) g := by
  have h := congrArg (starRingEnd ℂ) (original_covariant_pair i g f)
  simpa only [pair_conjugate] using h.symm

private theorem covariant_volume (i : Fin 6) (f : QuantumTest) :
    SourceCoframeCovariantAction.covariantMomentum i (volumeAction f)=
      volumeAction (SourceCoframeCovariantAction.covariantMomentum i f)+
        (-Complex.I) • SourceCoframeVolume.gradientAction i f := by
  change GaussCoframeCore.momentum i (volumeAction f)+connectionAction i (volumeAction f)=_
  rw [SourceCoframeVolume.momentum_volume]
  have hc : connectionAction i (volumeAction f)=volumeAction (connectionAction i f) := by
    apply DFunLike.ext
    intro z
    exact map_smul (SourceCoframeSpinConnection.connectionFiber i z) (volume z:ℂ) (f z)
  rw [hc]
  change _=volumeAction (GaussCoframeCore.momentum i f+connectionAction i f)+_
  rw [map_add]
  abel

private theorem polynomial_smooth (i j : Fin 6) : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice =>
    GaussCoframeKinetic.polynomial z.1 i j) := by
  fin_cases i <;> fin_cases j <;> simp [GaussCoframeKinetic.polynomial] <;> fun_prop

private def polynomialAction (i j : Fin 6) : End := multiply
  (fun z => GaussCoframeKinetic.polynomial z.1 i j) (fun _ => (polynomial_smooth i j).contDiffAt)
private def polynomialForm (f : QuantumTest) : ℝ :=
  (∑ i : Fin 6,∑ j : Fin 6,sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
    (polynomialAction i j (SourceCoframeCovariantAction.covariantMomentum j f))).re

private theorem metric_volume (i j : Fin 6) : volumeAction*metricAction i j=
    ((sourceTime 0:ℂ)/4) • polynomialAction i j := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change (volume z:ℂ) • ((GaussCoframeKinetic.coefficient i j z:ℂ) • f z)=
      ((sourceTime 0:ℂ)/4) • ((GaussCoframeKinetic.polynomial z.1 i j:ℂ) • f z)
    rw [smul_smul,smul_smul]
    congr 1
    unfold GaussCoframeKinetic.coefficient
    push_cast
    field_simp [show (volume z:ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem pair_add_left (f g h : QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_right (f g h : QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem gradient_metric_left (j : Fin 6) :
    (∑ i : Fin 6,SourceCoframeVolume.gradientAction i*metricAction i j)=
      ((sourceTime 0:ℂ)/4) • coordinateAction j := by
  have he (i : Fin 6) : SourceCoframeVolume.gradientAction i*metricAction i j=
      coefficientAction j i*SourceCoframeVolume.gradientAction i := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (volumeGradient z i:ℂ) • ((GaussCoframeKinetic.coefficient i j z:ℂ) • f z)=
      (GaussCoframeKinetic.coefficient j i z:ℂ) • ((volumeGradient z i:ℂ) • f z)
    rw [GaussCoframeKinetic.coefficient_symmetric]
    exact smul_comm _ _ _
  simp_rw [he]
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using source_gradient_contraction j

private theorem covariant_volume_pair (f : QuantumTest) :
    sourcePair (volumeAction f) (covariantKinetic f)=
      ((sourceTime 0:ℂ)/4)*(∑ i : Fin 6,∑ j : Fin 6,
        sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
          (polynomialAction i j (SourceCoframeCovariantAction.covariantMomentum j f)))+
      (Complex.I*(sourceTime 0:ℂ)/4)*sourcePair f (eulerMomentum f) := by
  have h1 (i j : Fin 6) : sourcePair (volumeAction (SourceCoframeCovariantAction.covariantMomentum i f))
      (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j f))=
      ((sourceTime 0:ℂ)/4)*sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
        (polynomialAction i j (SourceCoframeCovariantAction.covariantMomentum j f)) := by
    have hU (a b : QuantumTest) : sourcePair (volumeAction a) b=sourcePair a (volumeAction b) :=
      (multiply_pair volume (fun _ => volume_smooth.contDiffAt) a b).symm
    rw [hU]
    change sourcePair _ ((volumeAction*metricAction i j) (SourceCoframeCovariantAction.covariantMomentum j f))=_
    rw [metric_volume,LinearMap.smul_apply,pair_smul_right]
  have h2 : (∑ i : Fin 6,∑ j : Fin 6,sourcePair (SourceCoframeVolume.gradientAction i f)
      (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j f)))=
      ((sourceTime 0:ℂ)/4)*sourcePair f (eulerMomentum f) := by
    rw [Finset.sum_comm]
    have hr (j : Fin 6) : (∑ i : Fin 6,sourcePair (SourceCoframeVolume.gradientAction i f)
        (metricAction i j (SourceCoframeCovariantAction.covariantMomentum j f)))=
        ((sourceTime 0:ℂ)/4)*sourcePair f (coordinateAction j (SourceCoframeCovariantAction.covariantMomentum j f)) := by
      have h := congrArg (fun A : End => sourcePair f (A (SourceCoframeCovariantAction.covariantMomentum j f)))
        (gradient_metric_left j)
      simp only [LinearMap.sum_apply,Module.End.mul_apply,LinearMap.smul_apply,pair_sum_right,pair_smul_right] at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro i _
      exact (multiply_pair _ _ f _).symm
    simp_rw [hr]
    rw [←Finset.mul_sum]
    congr 1
    simp only [eulerMomentum,LinearMap.sum_apply,Module.End.mul_apply,pair_sum_right]
  simp only [covariantKinetic,LinearMap.sum_apply,Module.End.mul_apply,pair_sum_right,
    covariant_adjoint_pair,covariant_volume,pair_add_left,pair_smul_left,map_neg,Complex.conj_I,neg_neg,
    Finset.sum_add_distrib,h1,←Finset.mul_sum]
  rw [h2]
  ring

/-- The actual weighted formal transpose contributes this explicit Number-density term. -/
theorem original_covariant_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (covariantKinetic f))).re=
      sourceTime 0/4*polynomialForm f-3*sourceTime 0/8*(sourcePair f (densityShift f)).re := by
  have hU : sourcePair f (volumeAction (covariantKinetic f))=
      sourcePair (volumeAction f) (covariantKinetic f) := multiply_pair _ _ _ _
  rw [hU,covariant_volume_pair]
  simp only [Complex.add_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  norm_num
  rw [euler_imaginary]
  simp only [polynomialForm,Complex.re_sum]
  ring

/-- The literal factor-one trace-reversed six-by-six coframe Gram. -/
def reflectedForm (f : QuantumTest) : ℝ :=
  (∑ i : Fin 6,∑ j : Fin 6,sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
    (((coordinateAction i*coordinateAction j)-polynomialAction i j)
      (SourceCoframeCovariantAction.covariantMomentum j f))).re

private theorem reflected_trace (f : QuantumTest) :
    reflectedForm f=‖embed (eulerMomentum f)‖^2-polynomialForm f := by
  unfold reflectedForm polynomialForm
  simp only [LinearMap.sub_apply,pair_sub_right,Finset.sum_sub_distrib,Complex.sub_re]
  congr 1
  have he : (∑ i : Fin 6,∑ j : Fin 6,
      sourcePair (SourceCoframeCovariantAction.covariantMomentum i f)
        ((coordinateAction i*coordinateAction j) (SourceCoframeCovariantAction.covariantMomentum j f)))=
      sourcePair (eulerMomentum f) (eulerMomentum f) := by
    simp only [eulerMomentum,LinearMap.sum_apply,Module.End.mul_apply,pair_sum_left,pair_sum_right]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact multiply_pair _ _ _ _
  rw [he,pair_norm]

/-- The full covariant differential part is reflected, with the exact lower-order density correction exposed. -/
theorem original_reflected_covariant_form (f : QuantumTest) :
    (9*(sourceTime 0)^2/16)*‖embed (dilation f)‖^2-
      sourceTime 0*(sourcePair f (volumeAction (covariantKinetic f))).re=
    (sourceTime 0)^2/4*reflectedForm f-
      (9*(sourceTime 0)^2/16)*‖embed (densityShift f)‖^2+
      (3*(sourceTime 0)^2/8)*(sourcePair f (densityShift f)).re := by
  rw [original_dilation_density_square,original_covariant_volume_form,reflected_trace]
  ring

def scalarForm (f : QuantumTest) : ℝ := ∑ a : ScalarIndex,
  ‖embed (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)‖^2
private theorem gauge_volume_smooth (i j : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => volume w*gaugeWeight w i j) z.val :=
  volume_smooth.contDiffAt.mul (gaugeWeight_smooth i j z)
def gaugeForm (f : QuantumTest) : ℝ := (1/2:ℝ)*(∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
  sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
    (multiply (fun z => volume z*gaugeWeight z i j) (gauge_volume_smooth i j)
      (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f))).re
def spinForm (f : QuantumTest) : ℝ := ∑ a : Fin 7,residualWeight a*‖embed (GaussCoframeSpin.current a f)‖^2
def numberForm (f : QuantumTest) : ℝ := (sourcePair f (number f)).re
def densityForm (f : QuantumTest) : ℝ := (9/16:ℝ)*‖embed (number f)‖^2+3*numberForm f+(15/2:ℝ)*‖embed f‖^2

private theorem scalar_weight_volume : volumeAction*multiply scalarWeight scalarWeight_smooth=
    (-(sourceTime 0:ℂ)) • (1:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change (volume z:ℂ) • ((scalarWeight z:ℂ) • f z)=(-(sourceTime 0:ℂ)) • f z
    rw [smul_smul]
    congr 1
    unfold scalarWeight
    push_cast
    field_simp [show (volume z:ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem volume_pair (f g : QuantumTest) : sourcePair f (volumeAction g)=sourcePair (volumeAction f) g :=
  multiply_pair _ _ _ _

private theorem scalar_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (scalarKinetic f))).re= -(sourceTime 0/2)*scalarForm f := by
  have ht (a : ScalarIndex) : sourcePair (volumeAction f)
      (sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth f)=
      (-(sourceTime 0:ℂ))*sourcePair (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)
        (GaussCoreDifferential.covariantMomentum (scalarDirection a) f) := by
    change sourcePair (volumeAction f) (GaussMomentumAdjoint.adjoint (scalarDirection a)
      (multiply scalarWeight scalarWeight_smooth (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)))=_
    rw [GaussNativeForm.adjoint_pair]
    have hc := LinearMap.congr_fun (SourceHamiltonianVolume.native_momentum_volume (scalarDirection a)).eq f
    change GaussCoreDifferential.covariantMomentum (scalarDirection a) (volumeAction f)=
      volumeAction (GaussCoreDifferential.covariantMomentum (scalarDirection a) f) at hc
    rw [hc,←volume_pair]
    change sourcePair _ ((volumeAction*multiply scalarWeight scalarWeight_smooth) _)=_
    rw [scalar_weight_volume,LinearMap.smul_apply,Module.End.one_apply,pair_smul_right]
  rw [volume_pair]
  simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,pair_smul_right,pair_sum_right,ht,←Finset.mul_sum]
  have hc : (1/2:ℂ)*(-(sourceTime 0:ℂ))=((-sourceTime 0/2:ℝ):ℂ) := by push_cast;ring
  rw [←mul_assoc,hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum,pair_norm,scalarForm]
  ring

private theorem gauge_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (gaugeKinetic f))).re=gaugeForm f := by
  have ht (a : LieIndex) (i j : Fin 3) : sourcePair (volumeAction f)
      (sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) f)=
      sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
        (multiply (fun z => volume z*gaugeWeight z i j) (gauge_volume_smooth i j)
          (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)) := by
    change sourcePair (volumeAction f) (GaussMomentumAdjoint.adjoint (gaugeDirection i a)
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
        (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)))=_
    rw [GaussNativeForm.adjoint_pair]
    have hc := LinearMap.congr_fun (SourceHamiltonianVolume.native_momentum_volume (gaugeDirection i a)).eq f
    change GaussCoreDifferential.covariantMomentum (gaugeDirection i a) (volumeAction f)=
      volumeAction (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f) at hc
    rw [hc,←volume_pair]
    congr 1
    apply DFunLike.ext
    intro z
    change (volume z:ℂ) • ((gaugeWeight z i j:ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z))=
      ((volume z*gaugeWeight z i j:ℝ):ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z)
    simp only [smul_smul,Complex.ofReal_mul]
  rw [volume_pair]
  simp only [gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,pair_smul_right,pair_sum_right,ht]
  unfold gaugeForm
  simp only [Complex.mul_re,Complex.div_re,Complex.div_im]
  norm_num

private theorem spin_volume_action (a : Fin 7) :
    volumeAction*(GaussCoframeSpin.current a*multiply inverseVolume inverseVolume_smooth*GaussCoframeSpin.current a)=
      (sourceTime 0:ℂ) • (GaussCoframeSpin.current a*GaussCoframeSpin.current a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change (volume z:ℂ) • (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
      ((inverseVolume z:ℂ) • (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (f z))))=
      (sourceTime 0:ℂ) • (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
        (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (f z)))
    rw [map_smul,smul_smul]
    congr 1
    unfold inverseVolume
    push_cast
    field_simp [show (volume z:ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem spin_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (spinRemainder f))).re=sourceTime 0*spinForm f := by
  have he : volumeAction*spinRemainder=
      ∑ a : Fin 7,((residualWeight a:ℂ)*(sourceTime 0:ℂ)) • (GaussCoframeSpin.current a*GaussCoframeSpin.current a) := by
    unfold spinRemainder
    simp only [Finset.mul_sum,mul_smul_comm,spin_volume_action,smul_smul]
  have hs (a : Fin 7) : sourcePair f (GaussCoframeSpin.current a (GaussCoframeSpin.current a f))=
      sourcePair (GaussCoframeSpin.current a f) (GaussCoframeSpin.current a f) := GaussCoframeSpin.current_pair a f _
  change (sourcePair f ((volumeAction*spinRemainder) f)).re=_
  rw [he]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_sum_right,pair_smul_right,
    hs,Complex.re_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,pair_norm,spinForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem number_volume_action : volumeAction*numberShift=
    ((-9*(sourceTime 0:ℂ)/8):ℂ) • number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · apply PiLp.ext
    intro word
    change (volume z:ℂ)*((1/2:ℂ)*
      ((number (multiply numberCoefficient numberCoefficient_smooth f) z word)+
      (numberCoefficient z:ℂ)*(number f z word)))=(-9*(sourceTime 0:ℂ)/8)*(number f z word)
    rw [number_apply,number_apply]
    change (volume z:ℂ)*((1/2:ℂ)*((word.card:ℂ)*((numberCoefficient z:ℂ)*f z word)+
      (numberCoefficient z:ℂ)*((word.card:ℂ)*f z word)))=_
    unfold numberCoefficient inverseVolume
    push_cast
    field_simp [show (volume z:ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem number_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (numberShift f))).re= -(9*sourceTime 0/8)*numberForm f := by
  change (sourcePair f ((volumeAction*numberShift) f)).re=_
  rw [number_volume_action,LinearMap.smul_apply,pair_smul_right]
  have hc : (-9*(sourceTime 0:ℂ)/8)=((-9*sourceTime 0/8:ℝ):ℂ) := by push_cast;rfl
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,numberForm]
  ring

private theorem density_shift_form (f : QuantumTest) :
    (sourcePair f (densityShift f)).re=numberForm f+4*‖embed f‖^2 := by
  change (sourcePair f (number f+(4:ℂ) • f)).re=_
  rw [pair_add_right,pair_smul_right]
  simp only [Complex.add_re,Complex.mul_re,numberForm]
  norm_num
  rw [pair_norm]
private theorem density_shift_norm (f : QuantumTest) :
    ‖embed (densityShift f)‖^2=‖embed (number f)‖^2+8*numberForm f+16*‖embed f‖^2 := by
  change ‖embed (number f+(4:ℂ) • f)‖^2=_
  rw [map_add,map_smul,norm_add_sq (𝕜 := ℂ),norm_smul,inner_smul_right]
  have hc : ‖(4:ℂ)‖=4 := by norm_num
  rw [hc]
  change _+2*((4:ℂ)*sourcePair (number f) f).re+_=_
  rw [←number_pair]
  simp only [Complex.mul_re,numberForm]
  norm_num
  ring

private theorem kinetic_pair_core (f g : QuantumTest) :
    sourcePair f (kineticAction g)=sourcePair (kineticAction f) g := by
  have h := SourceKineticTranspose.kinetic_pair (coreEquiv f) (coreEquiv g)
  change sourcePair (kineticAction (coreEquiv.symm (coreEquiv f))) g=
    sourcePair f (kineticAction (coreEquiv.symm (coreEquiv g))) at h
  simpa only [coreEquiv.symm_apply_apply] using h.symm

private theorem symmetric_scale_form (f : QuantumTest) :
    (sourcePair f (SourceOriginalKineticSquare.symmetricScale f)).re=
      (sourcePair f (volumeAction (kineticAction f))).re := by
  have hp : sourcePair f (kineticAction (volumeAction f))=
      (starRingEnd ℂ) (sourcePair f (volumeAction (kineticAction f))) := by
    rw [kinetic_pair_core,GaussNativeForm.pair_conjugate]
    exact volume_pair (kineticAction f) f
  rw [SourceOriginalKineticSquare.symmetric_scale_source]
  change (sourcePair f ((1/2:ℂ) • (kineticAction (volumeAction f)+volumeAction (kineticAction f)))).re=_
  rw [pair_smul_right,pair_add_right,hp]
  simp only [Complex.mul_re,Complex.add_re,Complex.conj_re]
  norm_num
  ring

private theorem kinetic_covariant_split : kineticAction=
    scalarKinetic+gaugeKinetic+covariantKinetic+spinRemainder+numberShift := by
  unfold kineticAction
  rw [original_coframe_covariant]
  abel
private theorem kinetic_form_split (f : QuantumTest) :
    (sourcePair f (volumeAction (kineticAction f))).re=
      (sourcePair f (volumeAction (scalarKinetic f))).re+gaugeForm f+
      (sourcePair f (volumeAction (covariantKinetic f))).re+
      (sourcePair f (volumeAction (spinRemainder f))).re+
      (sourcePair f (volumeAction (numberShift f))).re := by
  rw [kinetic_covariant_split]
  simp only [LinearMap.add_apply,map_add,pair_add_right,Complex.add_re]
  rw [gauge_volume_form]

def localForm (f : QuantumTest) : ℝ := (sourcePair f (volumeAction (localAction f))).re
def spatialForm (f : QuantumTest) : ℝ := (sourcePair f (volumeAction (spatialAction f))).re

/-- All native columns, reflected covariant coframe columns, spin and Number terms return in the same original clock form. -/
theorem original_clock_bulk_form (f : QuantumTest) :
    (sourcePair f (clockBulk f)).re=
      (sourceTime 0)^2/4*reflectedForm f+(sourceTime 0)^2/2*scalarForm f+
      sourceTime 0*gaugeForm f-(sourceTime 0)^2*spinForm f-(sourceTime 0)^2*densityForm f+
      2*sourceTime 0*localForm f+sourceTime 0*spatialForm f := by
  have hd : sourcePair f (dilation (dilation f))=sourcePair (dilation f) (dilation f) := dilation_pair _ _
  have he : (sourcePair f (clockBulk f)).re=
      9*(sourceTime 0)^2/16*‖embed (dilation f)‖^2-
      sourceTime 0*(sourcePair f (SourceOriginalKineticSquare.symmetricScale f)).re+
      2*sourceTime 0*gaugeForm f+2*sourceTime 0*localForm f+sourceTime 0*spatialForm f := by
    have hc : (9*(sourceTime 0:ℂ)^2/16)=((9*(sourceTime 0)^2/16:ℝ):ℂ) := by push_cast;rfl
    have hc2 : 2*(sourceTime 0:ℂ)=((2*sourceTime 0:ℝ):ℂ) := by push_cast;rfl
    simp only [clockBulk,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      pair_add_right,pair_sub_right,pair_smul_right,hd,hc,hc2,Complex.add_re,Complex.sub_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,pair_norm,localForm,spatialForm]
    rw [gauge_volume_form]
  rw [he,symmetric_scale_form,kinetic_form_split,scalar_volume_form,spin_volume_form,number_volume_form]
  have hr := original_reflected_covariant_form f
  rw [density_shift_norm,density_shift_form] at hr
  unfold densityForm
  nlinarith only [hr]

private theorem radius_smooth : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice => 4*(GaussYukawaCoefficient.radius z)^2-1) := by
  exact (contDiff_const.mul (GaussYukawaCoefficient.radius_smooth.pow 2)).sub contDiff_const
private def radiusAction : End := multiply (fun z => 4*(GaussYukawaCoefficient.radius z)^2-1)
  (fun _ => radius_smooth.contDiffAt)
def radiusForm (f : QuantumTest) : ℝ := (sourcePair f (radiusAction f)).re

private theorem local_inverse_return :
    inverseVolumeAction*(volumeAction*localAction)*inverseVolumeAction=(sourceTime 0:ℂ) • radiusAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • ((localPotential z:ℂ) • ((reciprocalVolume z:ℂ) • f z)))=
      (sourceTime 0:ℂ) • ((4*(GaussYukawaCoefficient.radius z)^2-1:ℝ):ℂ) • f z
    rw [SourceHamiltonianScaleJet.local_radius_source]
    simp only [reciprocalVolume,smul_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sub,
      Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_one]
    congr 1
    field_simp [show (volume z:ℂ)≠0 from by exact_mod_cast (volume_pos ⟨z,hz⟩).ne']
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem local_inverse_form (f : QuantumTest) :
    localForm (inverseVolumeAction f)=sourceTime 0*radiusForm f := by
  have hv (a b : QuantumTest) : sourcePair (inverseVolumeAction a) b=sourcePair a (inverseVolumeAction b) :=
    (multiply_pair reciprocalVolume reciprocal_volume_smooth a b).symm
  unfold localForm
  rw [hv]
  change (sourcePair f ((inverseVolumeAction*(volumeAction*localAction)*inverseVolumeAction) f)).re=_
  rw [local_inverse_return,LinearMap.smul_apply,pair_smul_right]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,radiusForm]

/-- Direct consumption of the completed current: the radius-squared slot is on the original f, with every signed lower-order source retained. -/
theorem original_completed_reflected_form (f : QuantumTest) :
    (sourcePair f (completedAcceleration f)).re=
      (sourceTime 0)^2/4*reflectedForm (inverseVolumeAction f)+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f)+
      sourceTime 0*gaugeForm (inverseVolumeAction f)-
      (sourceTime 0)^2*spinForm (inverseVolumeAction f)-
      (sourceTime 0)^2*densityForm (inverseVolumeAction f)+
      2*(sourceTime 0)^2*radiusForm f+sourceTime 0*spatialForm (inverseVolumeAction f) := by
  rw [original_completed_volume_source]
  change (sourcePair f (inverseVolumeAction (clockBulk (inverseVolumeAction f)))).re=_
  have hv (a b : QuantumTest) : sourcePair a (inverseVolumeAction b)=sourcePair (inverseVolumeAction a) b :=
    multiply_pair reciprocalVolume reciprocal_volume_smooth a b
  rw [hv,original_clock_bulk_form,local_inverse_form]
  ring

open MeasureTheory SourceCoframeClockGram
local instance : InnerProductSpace ℝ FockFiber := InnerProductSpace.rclikeToReal ℂ FockFiber

/-- This pointwise square root is the actual Number density of sourcePair. -/
private def densityRoot (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  GaussFockWeights.weight (fun N => (Real.sqrt (GaussDensityCore.density N z):ℂ))

private theorem density_root_pair (z : physicalChart) (f g : QuantumTest) :
    inner ℂ (densityRoot z.val (f z.val)) (densityRoot z.val (g z.val))=densityPair f g z.val := by
  rw [PiLp.inner_apply,densityPair_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [RCLike.inner_apply]
  change ((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*g z.val word)*
      star ((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*f z.val word)=_
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  have hs : ((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*
      (Real.sqrt (GaussDensityCore.density word.card z.val):ℂ))=
      (GaussDensityCore.density word.card z.val:ℂ) := by
    rw [←Complex.ofReal_mul,Real.mul_self_sqrt (GaussDensityCore.density_pos word.card z).le]
  change _=(GaussDensityCore.density word.card z.val:ℂ)*(starRingEnd ℂ (f z.val word))*g z.val word
  calc
    _=(((Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)*
      (Real.sqrt (GaussDensityCore.density word.card z.val):ℂ)))*
        (starRingEnd ℂ (f z.val word))*g z.val word := by ring
    _=_ := by rw [hs]

private def reflectedKernel (f : QuantumTest) (z : SourceCoordinateSlice) : ℝ :=
  ∑ i : Fin 6,∑ j : Fin 6,(densityPair (SourceCoframeCovariantAction.covariantMomentum i f)
    (((coordinateAction i*coordinateAction j)-polynomialAction i j)
      (SourceCoframeCovariantAction.covariantMomentum j f)) z).re

/-- Six positive original coframe rows, integrated with the true Number-weighted source density. -/
def coframeGram (f : QuantumTest) : ℝ :=
  ∫ z : SourceCoordinateSlice,clockGram z.1
    (fun i => densityRoot z ((SourceCoframeCovariantAction.covariantMomentum i f) z))
    ∂GaussHistoryHilbert.configurationMeasure

private theorem reflected_kernel_square (f : QuantumTest) (z : SourceCoordinateSlice) :
    reflectedKernel f z=clockGram z.1
      (fun i => densityRoot z ((SourceCoframeCovariantAction.covariantMomentum i f) z)) := by
  by_cases hz : z∈physicalChart
  · rw [←original_clock_fiber_square]
    unfold reflectedKernel clockQuadratic
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_eq_re_inner ℂ,RCLike.re_to_complex,density_root_pair ⟨z,hz⟩]
    have he : densityPair (SourceCoframeCovariantAction.covariantMomentum i f)
        (((coordinateAction i*coordinateAction j)-polynomialAction i j)
          (SourceCoframeCovariantAction.covariantMomentum j f)) z=
        (clockPolynomial z.1 i j:ℂ)*densityPair (SourceCoframeCovariantAction.covariantMomentum i f)
          (SourceCoframeCovariantAction.covariantMomentum j f) z := by
      unfold densityPair
      change inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
        ((SourceCoframeCovariantAction.covariantMomentum i f) z))
        ((z.1 i:ℂ) • ((z.1 j:ℂ) • ((SourceCoframeCovariantAction.covariantMomentum j f) z))-
        (GaussCoframeKinetic.polynomial z.1 i j:ℂ) • ((SourceCoframeCovariantAction.covariantMomentum j f) z))=_
      simp only [inner_sub_right,inner_smul_right,clockPolynomial,Complex.ofReal_sub,Complex.ofReal_mul]
      ring
    rw [he]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    simp only [reflectedKernel,densityPair,h0,map_zero,inner_zero_right,Complex.zero_re,Finset.sum_const_zero]
    simp [clockGram]

private theorem pair_real_integral (f g : QuantumTest) :
    (sourcePair f g).re=∫ z : SourceCoordinateSlice,(densityPair f g z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
  rw [sourcePair_integral]
  exact (integral_re (densityPair_integrable f g)).symm

/-- The literal complex differential Gram is exactly the six positive source squares, without replacing sourcePair by an unweighted fiber norm. -/
theorem original_reflected_coframe_gram (f : QuantumTest) : reflectedForm f=coframeGram f := by
  have hi (i j : Fin 6) : Integrable (fun z : SourceCoordinateSlice =>
      (densityPair (SourceCoframeCovariantAction.covariantMomentum i f)
        (((coordinateAction i*coordinateAction j)-polynomialAction i j)
          (SourceCoframeCovariantAction.covariantMomentum j f)) z).re)
        GaussHistoryHilbert.configurationMeasure := (densityPair_integrable _ _).re
  have hsum : reflectedForm f=∫ z : SourceCoordinateSlice,reflectedKernel f z
      ∂GaussHistoryHilbert.configurationMeasure := by
    unfold reflectedForm reflectedKernel
    simp only [Complex.re_sum]
    simp_rw [pair_real_integral]
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_finsetSum Finset.univ (fun j _ => hi i j)).symm
  rw [hsum]
  unfold coframeGram
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (reflected_kernel_square f)

theorem original_coframe_gram_nonnegative (f : QuantumTest) : 0≤coframeGram f := by
  apply integral_nonneg
  intro z
  unfold clockGram
  positivity

/-- The completed source force now consumes the genuine positive coframe Gram, retaining the entire signed spin/density/spatial remainder. -/
theorem original_completed_square_form (f : QuantumTest) :
    (sourcePair f (completedAcceleration f)).re=
      (sourceTime 0)^2/4*coframeGram (inverseVolumeAction f)+
      (sourceTime 0)^2/2*scalarForm (inverseVolumeAction f)+
      sourceTime 0*gaugeForm (inverseVolumeAction f)-
      (sourceTime 0)^2*spinForm (inverseVolumeAction f)-
      (sourceTime 0)^2*densityForm (inverseVolumeAction f)+
      2*(sourceTime 0)^2*radiusForm f+sourceTime 0*spatialForm (inverseVolumeAction f) := by
  rw [original_completed_reflected_form,original_reflected_coframe_gram]

end LowEnergy.SourceClockReflectedForm
