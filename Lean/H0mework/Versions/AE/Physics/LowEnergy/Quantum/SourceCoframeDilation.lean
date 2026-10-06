import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCoframeVolumeCurrent

/-! The original six coframe columns generate the full Number-weighted dilation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceCoframeDilation
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussNativeForm GaussCoframeCore
open SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Topology InnerProductSpace

private theorem transpose_component (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word =
      GaussDensityCore.weightedTranspose word.card v (component word f) z.val := by
  let h := GaussDensityCore.weightedTranspose word.card v (component word f)
  have row : embed (GaussCoframeCore.transpose v f) word=scalarLp word.card h := by
    rw [GaussCoframeCore.transpose_embed]
    rfl
  have ae : (fun w : physicalChart => GaussCoframeCore.transpose v f w.val word) =ᵐ[
      GaussHistoryHilbert.numberMeasure word.card] (fun w : physicalChart => h w.val) :=
    (embed_ae (GaussCoframeCore.transpose v f) word).symm.trans (row ▸ scalarLp_ae word.card h)
  have eq := MeasureTheory.Measure.eq_of_ae_eq ae
    ((component word (GaussCoframeCore.transpose v f)).continuous.comp continuous_subtype_val)
    (h.continuous.comp continuous_subtype_val)
  exact congrFun eq z

private theorem euler_sum (z : SourceCoordinateSlice) :
    (∑ i : Fin 6, z.1 i • coframeDirection i) = euler z := by
  apply Prod.ext
  · apply PiLp.ext
    intro j
    fin_cases j <;> simp [euler, coframeDirection, Fin.sum_univ_succ]
  · simp [euler, coframeDirection, Fin.sum_univ_succ]

private theorem coframe_sum (z : SourceCoordinateSlice) (L : SourceCoordinateSlice →L[ℝ] ℂ) :
    (∑ i : Fin 6, (z.1 i : ℂ)*L (coframeDirection i)) = L (euler z) := by
  rw [←euler_sum, map_sum]
  simp only [map_smul, Complex.real_smul]

private theorem complex_density_euler (N : ℕ) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.complexDensity N) z.val (euler z.val) =
      (3*(N+2) : ℕ)*GaussDensityCore.complexDensity N z.val := by
  have h := (Complex.ofRealCLM.hasFDerivAt (x := GaussDensityCore.density N z.val)).comp z.val
    (((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt)
  change HasFDerivAt (GaussDensityCore.complexDensity N) _ z.val at h
  rw [h.fderiv]
  change (fderiv ℝ (GaussDensityCore.density N) z.val (euler z.val) : ℂ) = _
  rw [density_euler]
  push_cast
  rfl

private theorem transpose_formula (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word =
      -fderiv ℝ (component word f) z.val v -
        (GaussDensityCore.complexDensity word.card z.val)⁻¹ *
          fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v * f z.val word := by
  rw [transpose_component, GaussDensityCore.weightedTranspose_apply,
    fderiv_fun_mul
      ((GaussDensityCore.complexDensity_smooth word.card z).differentiableAt (by simp))
      ((component word f).contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hn : GaussDensityCore.complexDensity word.card z.val ≠ 0 := by
    change (GaussDensityCore.density word.card z.val : ℂ) ≠ 0
    exact_mod_cast (GaussDensityCore.density_pos word.card z).ne'
  change -(GaussDensityCore.complexDensity word.card z.val)⁻¹ *
      (GaussDensityCore.complexDensity word.card z.val *
        fderiv ℝ (component word f) z.val v +
        f z.val word * fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v) = _
  field_simp [hn]
  ring

private theorem coordinate_component (i : Fin 6) (f : QuantumTest) (word : Occupation) :
    (component word (coordinateAction i f) : SourceCoordinateSlice → ℂ) =
      fun z => (z.1 i : ℂ)*component word f z := rfl

private theorem coordinate_component_derivative (i : Fin 6) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    fderiv ℝ (component word (coordinateAction i f)) z (coframeDirection i) =
      (z.1 i : ℂ)*fderiv ℝ (component word f) z (coframeDirection i)+f z word := by
  rw [coordinate_component]
  have hc := (Complex.ofRealCLM.comp (SourceCoframeVolume.coordinate i)).hasFDerivAt (x := z)
  change HasFDerivAt (fun w : SourceCoordinateSlice => (w.1 i : ℂ)) _ z at hc
  rw [fderiv_fun_mul hc.differentiableAt
    ((component word f).contDiff.differentiable (by simp)).differentiableAt, hc.fderiv]
  simp [SourceCoframeVolume.coordinate, coframeDirection, component]

private theorem momentum_component (i : Fin 6) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    momentum i f z word = -Complex.I * fderiv ℝ (component word f) z (coframeDirection i) := by
  have h := congrArg (fun g : GaussDensityCore.ScalarTest => g z)
    (GaussCoframeCore.component_derivative (coframeDirection i) f word)
  change GaussCoframeCore.derivative (coframeDirection i) f z word =
    GaussDensityCore.derivative (coframeDirection i) (component word f) z at h
  rw [GaussDensityCore.derivative_apply] at h
  change -Complex.I * GaussCoframeCore.derivative (coframeDirection i) f z word = _
  rw [h]

theorem dilation_apply (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    dilation f z.val word = -Complex.I *
      ((2/3 : ℂ)*fderiv ℝ (component word f) z.val (euler z.val)+
        (word.card+4 : ℂ)*f z.val word) := by
  have hterm (i : Fin 6) :
      (GaussCoframeCore.adjoint i (coordinateAction i f)+coordinateAction i (momentum i f))
          z.val word =
        -Complex.I*((2 : ℂ)*((z.val.1 i : ℂ)*
          fderiv ℝ (component word f) z.val (coframeDirection i))+f z.val word+
          (GaussDensityCore.complexDensity word.card z.val)⁻¹ *
            ((z.val.1 i : ℂ)*fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val
              (coframeDirection i))*f z.val word) := by
    change Complex.I*GaussCoframeCore.transpose (coframeDirection i) (coordinateAction i f)
      z.val word + (z.val.1 i : ℂ)*momentum i f z.val word = _
    rw [transpose_formula, coordinate_component_derivative, momentum_component]
    change Complex.I*(-((z.val.1 i : ℂ)*
      fderiv ℝ (component word f) z.val (coframeDirection i)+f z.val word)-
      (GaussDensityCore.complexDensity word.card z.val)⁻¹ *
        fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val (coframeDirection i)*
          ((z.val.1 i : ℂ)*f z.val word))+
      (z.val.1 i : ℂ)*(-Complex.I*fderiv ℝ (component word f) z.val (coframeDirection i)) = _
    ring
  change (1/3 : ℂ) * (∑ i : Fin 6,
    (GaussCoframeCore.adjoint i (coordinateAction i f)+coordinateAction i (momentum i f))
      z.val word) = _
  simp_rw [hterm]
  rw [←Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.mul_sum]
  rw [coframe_sum, coframe_sum, complex_density_euler]
  have hn : GaussDensityCore.complexDensity word.card z.val ≠ 0 := by
    change (GaussDensityCore.density word.card z.val : ℂ) ≠ 0
    exact_mod_cast (GaussDensityCore.density_pos word.card z).ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp [hn]
  ring

theorem dilation_pair (f g : QuantumTest) :
    sourcePair f (dilation g) = sourcePair (dilation f) g := by
  have hterm (i : Fin 6) :
      sourcePair f (GaussCoframeCore.adjoint i (coordinateAction i g)+coordinateAction i (momentum i g)) =
      sourcePair (GaussCoframeCore.adjoint i (coordinateAction i f)+coordinateAction i (momentum i f)) g := by
    have ha : sourcePair f (GaussCoframeCore.adjoint i (coordinateAction i g)) =
        sourcePair (coordinateAction i (momentum i f)) g :=
      (GaussCoframeKinetic.adjoint_pair i f (coordinateAction i g)).trans
        (multiply_pair _ _ (momentum i f) g)
    have hb : sourcePair f (coordinateAction i (momentum i g)) =
        sourcePair (GaussCoframeCore.adjoint i (coordinateAction i f)) g :=
      (multiply_pair _ _ f (momentum i g)).trans (momentum_pair i (coordinateAction i f) g)
    simp only [sourcePair, map_add, inner_add_left, inner_add_right] at ha hb ⊢
    rw [ha, hb, add_comm]
  simp only [dilation, LinearMap.smul_apply, LinearMap.sum_apply, sourcePair, map_smul,
    map_sum, inner_smul_left, inner_smul_right, inner_sum, sum_inner,
    map_div₀, map_one, map_ofNat]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hterm i)

def eulerAction : CoreEnd := ∑ i : Fin 6,
  coordinateAction i * GaussCoframeCore.derivative (coframeDirection i)

theorem eulerAction_component (f : QuantumTest) (word : Occupation) (z : SourceCoordinateSlice) :
    eulerAction f z word = fderiv ℝ (component word f) z (euler z) := by
  have hd (i : Fin 6) : GaussCoframeCore.derivative (coframeDirection i) f z word =
      fderiv ℝ (component word f) z (coframeDirection i) := by
    have h := congrArg (fun g : GaussDensityCore.ScalarTest => g z)
      (GaussCoframeCore.component_derivative (coframeDirection i) f word)
    change GaussCoframeCore.derivative (coframeDirection i) f z word =
      GaussDensityCore.derivative (coframeDirection i) (component word f) z at h
    simpa only [GaussDensityCore.derivative_apply] using h
  change (∑ i : Fin 6, (z.1 i : ℂ)*GaussCoframeCore.derivative (coframeDirection i) f z word) = _
  simp_rw [hd]
  exact coframe_sum z _

theorem eulerAction_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    eulerAction f z = fderiv ℝ f z (euler z) := by
  apply PiLp.ext
  intro word
  rw [eulerAction_component]
  have h := congrArg (fun g : GaussDensityCore.ScalarTest => g z)
    (GaussCoframeCore.component_derivative (euler z) f word)
  change GaussCoframeCore.derivative (euler z) f z word =
    GaussDensityCore.derivative (euler z) (component word f) z at h
  rw [GaussCoframeCore.derivative_apply, GaussDensityCore.derivative_apply] at h
  exact h.symm

theorem dilation_operator :
    dilation = (-Complex.I) • ((2/3 : ℂ) • eulerAction +
      GaussCoframeForm.number + (4 : ℂ) • (LinearMap.id : CoreEnd)) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · apply PiLp.ext
    intro word
    rw [dilation_apply f word ⟨z,hz⟩]
    change -Complex.I*((2/3 : ℂ)*fderiv ℝ (component word f) z (euler z)+
      (word.card+4 : ℂ)*f z word) =
      -Complex.I*((2/3 : ℂ)*eulerAction f z word+GaussCoframeForm.number f z word+
        4*f z word)
    rw [eulerAction_component, GaussCoframeForm.number_apply]
    ring
  · have hl : dilation f z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((dilation f).tsupport_subset h))
    have hr : (((-Complex.I) • ((2/3 : ℂ) • eulerAction+GaussCoframeForm.number+
        (4 : ℂ) • (LinearMap.id : CoreEnd))) f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz
        ((((-Complex.I) • ((2/3 : ℂ) • eulerAction+GaussCoframeForm.number+
          (4 : ℂ) • (LinearMap.id : CoreEnd))) f).tsupport_subset h))
    exact hl.trans hr.symm

end LowEnergy.SourceCoframeDilation
