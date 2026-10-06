import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationAction

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPreparationCorrection
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussDensityCore GaussHistoryHilbert GaussNativeEnergy
open CanonicalPreparationCore CanonicalPreparationMomentum
open MeasureTheory Set Filter
open scoped ContDiff Distributions Topology

local notation "D" => GaussCoframeCore.coframeDirection

@[simp] private theorem vec6_two (a b c d e f : ℝ) : (![a,b,c,d,e,f] : Fin 6 → ℝ) 2=c := rfl
@[simp] private theorem vec6_three (a b c d e f : ℝ) : (![a,b,c,d,e,f] : Fin 6 → ℝ) 3=d := rfl
@[simp] private theorem vec6_four (a b c d e f : ℝ) : (![a,b,c,d,e,f] : Fin 6 → ℝ) 4=e := rfl
@[simp] private theorem vec6_five (a b c d e f : ℝ) : (![a,b,c,d,e,f] : Fin 6 → ℝ) 5=f := rfl

def fluxCoefficient (i : Fin 6) (z : SourceCoordinateSlice) : ℝ :=
  (sourceTime 0/8)*(volume z)⁻¹*z.1 i

theorem flux_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fluxCoefficient i) z.val :=
  (contDiffAt_const.mul (volume_smooth.contDiffAt.inv (volume_pos z).ne')).mul (by fun_prop)

theorem original_row_flux (i : Fin 6) (z : physicalChart) :
    (∑ j : Fin 6, GaussCoframeKinetic.coefficient i j z.val*halfLogVolume (D j) z.val)=
      fluxCoefficient i z.val := by
  have h0 := z.property.1.ne'
  have h2 := z.property.2.1.ne'
  have h5 := z.property.2.2.1.ne'
  fin_cases i <;>
    simp only [Fin.sum_univ_six,GaussCoframeKinetic.coefficient,GaussCoframeKinetic.polynomial,
      halfLogVolume,volumeDerivative,GaussCoframeCore.coframeDirection,EuclideanSpace.single,
      GaussNativeEnergy.volume,fluxCoefficient,PiLp.single_apply] <;>
    norm_num [Fin.ext_iff] <;>
    field_simp [h0,h2,h5] <;> ring_nf <;> rfl

def flux (i : Fin 6) : ScalarTest →ₗ[ℂ] ScalarTest :=
  GaussDensityCore.multiply (fun z => (fluxCoefficient i z : ℂ))
    (fun z => Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (flux_smooth i z))

private theorem test_ext {f g : ScalarTest} (h : ∀ z : physicalChart, f z.val=g z.val) : f=g := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · exact h ⟨z,hz⟩
  · rw [image_eq_zero_of_notMem_tsupport (fun t => hz (f.tsupport_subset t)),
      image_eq_zero_of_notMem_tsupport (fun t => hz (g.tsupport_subset t))]

private def evaluation (z : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ℂ where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sum_apply (g : Fin 6 → ScalarTest) (z : SourceCoordinateSlice) :
    (∑ i, g i) z=∑ i, g i z := by
  change evaluation z (∑ i, g i)=∑ i, evaluation z (g i)
  exact map_sum (evaluation z) g Finset.univ

theorem original_row_flux_core (i : Fin 6) (f : ScalarTest) :
    (∑ j : Fin 6, coframeCoefficient i j (drift (D j) f))=flux i f := by
  apply test_ext
  intro z
  have h := congrArg (fun r : ℝ => (r : ℂ)*f z.val) (original_row_flux i z)
  push_cast at h
  rw [Finset.sum_mul] at h
  rw [sum_apply]
  convert! h using 1
  apply Finset.sum_congr rfl
  intro j _
  change (GaussCoframeKinetic.coefficient i j z.val : ℂ)*
    ((halfLogVolume (D j) z.val : ℂ)*f z.val)=_
  ring

theorem drift_coefficient (i j : Fin 6) (f : ScalarTest) :
    drift (D i) (coframeCoefficient i j f)=coframeCoefficient j i (drift (D i) f) := by
  apply DFunLike.ext
  intro z
  change (halfLogVolume (D i) z : ℂ)*((GaussCoframeKinetic.coefficient i j z : ℂ)*f z)=
    (GaussCoframeKinetic.coefficient j i z : ℂ)*((halfLogVolume (D i) z : ℂ)*f z)
  rw [GaussCoframeKinetic.coefficient_symmetric i j]
  ring

theorem correction_flux (f : ScalarTest) :
    coframeCorrection f=
      -(∑ i : Fin 6, weightedTranspose 0 (D i) (flux i f))-
       (∑ i : Fin 6, flux i (GaussDensityCore.derivative (D i) f))+
       ∑ i : Fin 6, drift (D i) (flux i f) := by
  have first : (∑ i : Fin 6, ∑ j : Fin 6,
      weightedTranspose 0 (D i) (coframeCoefficient i j (drift (D j) f)))=
      ∑ i : Fin 6, weightedTranspose 0 (D i) (flux i f) := by
    simp only [←map_sum,original_row_flux_core]
  have middle : (∑ i : Fin 6, ∑ j : Fin 6,
      drift (D i) (coframeCoefficient i j (GaussDensityCore.derivative (D j) f)))=
      ∑ j : Fin 6, flux j (GaussDensityCore.derivative (D j) f) := by
    simp only [drift_coefficient]
    rw [Finset.sum_comm]
    simp only [original_row_flux_core]
  have last : (∑ i : Fin 6, ∑ j : Fin 6,
      drift (D i) (coframeCoefficient i j (drift (D j) f)))=
      ∑ i : Fin 6, drift (D i) (flux i f) := by
    simp only [←map_sum,original_row_flux_core]
  unfold coframeCorrection coframeCorrectionTerm
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  rw [first,middle,last]

def euler (z : SourceCoordinateSlice) : SourceCoordinateSlice := (z.1,0)

theorem euler_sum (z : SourceCoordinateSlice) : (∑ i : Fin 6, z.1 i • D i)=euler z := by
  apply Prod.ext
  · change (LinearMap.fst ℝ _ _) (∑ i : Fin 6, z.1 i • D i)=z.1
    rw [map_sum]
    change (∑ i : Fin 6, z.1 i • EuclideanSpace.single i 1)=z.1
    apply PiLp.ext
    intro k
    simp [EuclideanSpace.single,WithLp.ofLp_sum,Finset.sum_apply,Pi.single_apply]
  · change (LinearMap.snd ℝ _ _) (∑ i : Fin 6, z.1 i • D i)=0
    rw [map_sum]
    simp only [map_smul]
    change (∑ i : Fin 6, z.1 i • (0 : GaussLiveMomentum.Slice))=0
    simp

theorem volume_euler (z : SourceCoordinateSlice) :
    fderiv ℝ volume z (euler z)=3*volume z := by
  rw [volume_derivative]
  simp only [volumeDerivative,euler,GaussNativeEnergy.volume]
  ring

theorem complexDensity_euler (z : physicalChart) :
    fderiv ℝ (complexDensity 0) z.val (euler z.val)=6*complexDensity 0 z.val := by
  let scale (r : ℝ) : SourceCoordinateSlice := (r • z.val.1,z.val.2)
  have hs : HasDerivAt scale (euler z.val) 1 := by
    simpa only [scale,euler,one_smul,id_eq] using!
      ((hasDerivAt_id (1 : ℝ)).smul_const z.val.1).prodMk (hasDerivAt_const 1 z.val.2)
  have one : scale 1=z.val := by simp [scale]
  have scaling : (fun r : ℝ => complexDensity 0 (scale r))=
      (fun r : ℝ => (r : ℂ)^6*complexDensity 0 z.val) := by
    funext r
    simp only [complexDensity,density,scale,PiLp.smul_apply,smul_eq_mul]
    push_cast
    ring
  have chain := ((complexDensity_smooth 0 z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 hs one.symm
  have actual := ((hasDerivAt_id (1 : ℝ)).ofReal_comp.pow 6).mul_const (complexDensity 0 z.val)
  change HasDerivAt (fun r => complexDensity 0 (scale r)) _ 1 at chain
  rw [scaling] at chain
  have equal := chain.unique actual
  norm_num at equal
  exact equal

theorem flux_derivative (i : Fin 6) (z : physicalChart) :
    fderiv ℝ (fluxCoefficient i) z.val (D i)=
      sourceTime 0/8*(volume z.val)⁻¹-
        (sourceTime 0/8)*z.val.1 i*(volume z.val^2)⁻¹*volumeDerivative (D i) z.val := by
  let read : SourceCoordinateSlice →L[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 6 => ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _)
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have hi := (hasDerivAt_inv (volume_pos z).ne').comp_hasFDerivAt z.val hv
  have hx : HasFDerivAt read read z.val := read.hasFDerivAt
  have product : fderiv ℝ (fluxCoefficient i) z.val=
      (sourceTime 0/8*(volume z.val)⁻¹) • read+
      z.val.1 i • ((sourceTime 0/8) • (-((volume z.val)^2)⁻¹ • fderiv ℝ volume z.val)) := by
    simpa only [fluxCoefficient,read] using! ((hi.const_mul (sourceTime 0/8)).mul hx).fderiv
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul,volume_derivative]
  have read_direction : read (D i)=1 := by
    simp [read,GaussCoframeCore.coframeDirection,EuclideanSpace.single]
  rw [read_direction]
  ring

theorem volume_euler_sum (z : SourceCoordinateSlice) :
    (∑ i : Fin 6, z.1 i*volumeDerivative (D i) z)=3*volume z := by
  calc
    _ = ∑ i : Fin 6, fderiv ℝ volume z (z.1 i • D i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,volume_derivative]
      rfl
    _ = _ := by rw [←map_sum,euler_sum,volume_euler]

theorem flux_divergence (z : physicalChart) :
    (∑ i : Fin 6, fderiv ℝ (fluxCoefficient i) z.val (D i))=
      3*sourceTime 0/(8*volume z.val) := by
  simp only [flux_derivative,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  have h : (∑ i : Fin 6, (sourceTime 0/8)*z.val.1 i*(volume z.val^2)⁻¹*
      volumeDerivative (D i) z.val)=
      (sourceTime 0/8)*(volume z.val^2)⁻¹*(3*volume z.val) := by
    rw [←volume_euler_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  field_simp [(volume_pos z).ne']
  ring

theorem flux_density (z : physicalChart) :
    (∑ i : Fin 6, (complexDensity 0 z.val)⁻¹*
      fderiv ℝ (complexDensity 0) z.val (D i)*(fluxCoefficient i z.val : ℂ))=
      (6*sourceTime 0/(8*volume z.val) : ℝ) := by
  have eulerRead : (∑ i : Fin 6, (z.val.1 i : ℂ)*fderiv ℝ (complexDensity 0) z.val (D i))=
      6*complexDensity 0 z.val := by
    calc
      _ = ∑ i : Fin 6, fderiv ℝ (complexDensity 0) z.val (z.val.1 i • D i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        rfl
      _ = _ := by rw [←map_sum,euler_sum,complexDensity_euler]
  have group : (∑ i : Fin 6, (complexDensity 0 z.val)⁻¹*
      fderiv ℝ (complexDensity 0) z.val (D i)*(fluxCoefficient i z.val : ℂ))=
      (complexDensity 0 z.val)⁻¹*((sourceTime 0/8*(volume z.val)⁻¹ : ℝ) : ℂ)*
        (∑ i : Fin 6, (z.val.1 i : ℂ)*fderiv ℝ (complexDensity 0) z.val (D i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [fluxCoefficient,Complex.ofReal_mul]
    ring
  rw [group,eulerRead]
  have nz : complexDensity 0 z.val≠0 := by
    change (density 0 z.val : ℂ)≠0
    exact_mod_cast (density_pos 0 z).ne'
  push_cast
  field_simp

theorem flux_drift (z : physicalChart) :
    (∑ i : Fin 6, halfLogVolume (D i) z.val*fluxCoefficient i z.val)=
      3*sourceTime 0/(16*volume z.val) := by
  have group : (∑ i : Fin 6, halfLogVolume (D i) z.val*fluxCoefficient i z.val)=
      sourceTime 0/(16*volume z.val^2)*
        (∑ i : Fin 6, z.val.1 i*volumeDerivative (D i) z.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold halfLogVolume fluxCoefficient
    field_simp
    ring
  rw [group,volume_euler_sum]
  field_simp [(volume_pos z).ne']

theorem derivative_flux (i : Fin 6) (f : ScalarTest) (z : physicalChart) :
    GaussDensityCore.derivative (D i) (flux i f) z.val=
      (fluxCoefficient i z.val : ℂ)*GaussDensityCore.derivative (D i) f z.val+
        (fderiv ℝ (fluxCoefficient i) z.val (D i) : ℂ)*f z.val := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z.val
    ((flux_smooth i z).differentiableAt (by simp)).hasFDerivAt
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z.val)
  have product : fderiv ℝ (fun w => (fluxCoefficient i w : ℂ)*f w) z.val=
      (fluxCoefficient i z.val : ℂ) • fderiv ℝ f z.val+
      f z.val • (Complex.ofRealCLM.comp (fderiv ℝ (fluxCoefficient i) z.val)) := by
    simpa using! (hc.mul hf).fderiv
  rw [GaussDensityCore.derivative_apply,GaussDensityCore.derivative_apply]
  change fderiv ℝ (fun w => (fluxCoefficient i w : ℂ)*f w) z.val (D i)=_
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply]
  ring

theorem correction_apply (f : ScalarTest) (z : physicalChart) :
    coframeCorrection f z.val=(21*sourceTime 0/(16*volume z.val) : ℝ)*f z.val := by
  have grouped : coframeCorrection f z.val=
      ∑ i : Fin 6, (-weightedTranspose 0 (D i) (flux i f) z.val-
        flux i (GaussDensityCore.derivative (D i) f) z.val+drift (D i) (flux i f) z.val) := by
    rw [correction_flux]
    change -(∑ i : Fin 6, weightedTranspose 0 (D i) (flux i f)) z.val-
      (∑ i : Fin 6, flux i (GaussDensityCore.derivative (D i) f)) z.val+
      (∑ i : Fin 6, drift (D i) (flux i f)) z.val=_
    simp only [sum_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  rw [grouped]
  calc
    _ = ∑ i : Fin 6,
        ((fderiv ℝ (fluxCoefficient i) z.val (D i) : ℂ)+
          (complexDensity 0 z.val)⁻¹*fderiv ℝ (complexDensity 0) z.val (D i)*
            (fluxCoefficient i z.val : ℂ)+
          (halfLogVolume (D i) z.val*fluxCoefficient i z.val : ℝ))*f z.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedTranspose_expand,derivative_flux]
      change -((-( (fluxCoefficient i z.val : ℂ)*GaussDensityCore.derivative (D i) f z.val+
          (fderiv ℝ (fluxCoefficient i) z.val (D i) : ℂ)*f z.val))-
          (complexDensity 0 z.val)⁻¹*fderiv ℝ (complexDensity 0) z.val (D i)*
          ((fluxCoefficient i z.val : ℂ)*f z.val))-
        (fluxCoefficient i z.val : ℂ)*GaussDensityCore.derivative (D i) f z.val+
        (halfLogVolume (D i) z.val : ℂ)*((fluxCoefficient i z.val : ℂ)*f z.val)=_
      push_cast
      ring
    _ = _ := by
      rw [←Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_add_distrib,
        ←Complex.ofReal_sum,flux_divergence,flux_density,←Complex.ofReal_sum,flux_drift]
      push_cast
      field_simp
      ring

def correctionPotential : ScalarTest →ₗ[ℂ] ScalarTest :=
  GaussDensityCore.multiply (fun z => ((21/16 : ℝ)*GaussCoframeForm.inverseVolume z : ℝ))
    (fun z => Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
      (contDiffAt_const.mul (GaussCoframeForm.inverseVolume_smooth z)))

theorem correction_potential (f : ScalarTest) : coframeCorrection f=correctionPotential f := by
  apply test_ext
  intro z
  rw [correction_apply]
  change (21*sourceTime 0/(16*volume z.val) : ℝ)*f z.val=
    ((21/16 : ℝ)*(sourceTime 0/volume z.val) : ℝ)*f z.val
  push_cast
  ring

theorem kinetic_creation_potential (f : ScalarTest) :
    GaussCoframeKinetic.kinetic (createdCore f)=
      createdCore (coframeKinetic 0 f+correctionPotential f) := by
  rw [original_kinetic_creation,correction_potential]

end LowEnergy.CanonicalPreparationCorrection
