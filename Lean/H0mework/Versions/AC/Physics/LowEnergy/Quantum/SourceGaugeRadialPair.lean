import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceGaugeRadialCurrent
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussCoframeCore

/-! Full-Fock weighted gauge Euler and radial integration by parts on the original core. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceGaugeRadialPair
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge GaussHistoryHilbert GaussLiveMomentum
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussNativeForm GaussCoframeCore
open SourceGaugeRadialCurrent
open scoped ContDiff Topology InnerProductSpace
abbrev CoreEnd := QuantumTest →ₗ[ℂ] QuantumTest
abbrev GaugeIndex := Fin (Module.finrank ℝ coordinateSlice)
def gaugeBasis : Module.Basis GaugeIndex ℝ coordinateSlice := Module.finBasis ℝ coordinateSlice

def gaugeCoordinate (i : GaugeIndex) : SourceCoordinateSlice →L[ℝ] ℝ :=
  (gaugeBasis.coord i).toContinuousLinearMap.comp
    ((ContinuousLinearMap.snd ℝ scalarSlice coordinateSlice).comp
      (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice)))

def gaugeAxis (i : GaugeIndex) : SourceCoordinateSlice := (0,0,gaugeBasis i)

def coordinateAction (i : GaugeIndex) : CoreEnd :=
  multiply (gaugeCoordinate i) (fun _ => (gaugeCoordinate i).contDiff.contDiffAt)

def gaugeEulerAction : CoreEnd := ∑ i : GaugeIndex,
  coordinateAction i*GaussCoframeCore.derivative (gaugeAxis i)

def gaugeEulerTranspose : CoreEnd := ∑ i : GaugeIndex,
  GaussCoframeCore.transpose (gaugeAxis i)*coordinateAction i

private def evaluate (z : SourceCoordinateSlice) (word : Occupation) : QuantumTest →ₗ[ℂ] ℂ where
  toFun f := f z word
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem euler_sum (z : SourceCoordinateSlice) :
    (∑ i : GaugeIndex, gaugeCoordinate i z • gaugeAxis i)=gaugeEuler z := by
  apply Prod.ext
  · simp [gaugeAxis, gaugeEuler, Prod.fst_sum]
  · apply Prod.ext
    · simp [gaugeAxis, gaugeEuler, Prod.fst_sum, Prod.snd_sum]
    · simp only [Prod.snd_sum, gaugeAxis, Prod.smul_mk]
      change (∑ i : GaugeIndex, gaugeBasis.coord i z.2.2 • gaugeBasis i)=z.2.2
      exact gaugeBasis.sum_repr z.2.2

private theorem derivative_component (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    GaussCoframeCore.derivative v f z word=fderiv ℝ (component word f) z v := by
  have h := congrArg (fun g : GaussDensityCore.ScalarTest => g z)
    (GaussCoframeCore.component_derivative v f word)
  change GaussCoframeCore.derivative v f z word=
    GaussDensityCore.derivative v (component word f) z at h
  simpa only [GaussDensityCore.derivative_apply] using h

private theorem gauge_sum (z : SourceCoordinateSlice) (L : SourceCoordinateSlice →L[ℝ] ℂ) :
    (∑ i : GaugeIndex, (gaugeCoordinate i z : ℂ)*L (gaugeAxis i))=L (gaugeEuler z) := by
  rw [←euler_sum, map_sum]
  simp only [map_smul, Complex.real_smul]

theorem gauge_euler_component (f : QuantumTest) (word : Occupation) (z : SourceCoordinateSlice) :
    gaugeEulerAction f z word=fderiv ℝ (component word f) z (gaugeEuler z) := by
  change evaluate z word ((∑ i : GaugeIndex,
    coordinateAction i*GaussCoframeCore.derivative (gaugeAxis i)) f)=_
  rw [LinearMap.sum_apply, map_sum]
  change (∑ i : GaugeIndex, (gaugeCoordinate i z : ℂ)*
    GaussCoframeCore.derivative (gaugeAxis i) f z word)=_
  simp_rw [derivative_component]
  exact gauge_sum z _

theorem gauge_euler_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    gaugeEulerAction f z=fderiv ℝ f z (gaugeEuler z) := by
  apply PiLp.ext
  intro word
  rw [gauge_euler_component]
  have h := derivative_component (gaugeEuler z) f word z
  rw [GaussCoframeCore.derivative_apply] at h
  exact h.symm

private theorem transpose_component (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word=
      GaussDensityCore.weightedTranspose word.card v (component word f) z.val := by
  let h := GaussDensityCore.weightedTranspose word.card v (component word f)
  have row : embed (GaussCoframeCore.transpose v f) word=scalarLp word.card h := by
    rw [GaussCoframeCore.transpose_embed]
    rfl
  have ae : (fun w : physicalChart => GaussCoframeCore.transpose v f w.val word) =ᵐ[
      GaussHistoryHilbert.numberMeasure word.card] (fun w : physicalChart => h w.val) :=
    (embed_ae (GaussCoframeCore.transpose v f) word).symm.trans (row ▸ scalarLp_ae word.card h)
  have he := MeasureTheory.Measure.eq_of_ae_eq ae
    ((component word (GaussCoframeCore.transpose v f)).continuous.comp continuous_subtype_val)
    (h.continuous.comp continuous_subtype_val)
  exact congrFun he z

private theorem transpose_formula (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : physicalChart) :
    GaussCoframeCore.transpose v f z.val word=
      -fderiv ℝ (component word f) z.val v-
        (GaussDensityCore.complexDensity word.card z.val)⁻¹*
          fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v*f z.val word := by
  rw [transpose_component, GaussDensityCore.weightedTranspose_apply,
    fderiv_fun_mul ((GaussDensityCore.complexDensity_smooth word.card z).differentiableAt (by simp))
      ((component word f).contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hn : GaussDensityCore.complexDensity word.card z.val≠0 := by
    change (GaussDensityCore.density word.card z.val : ℂ)≠0
    exact_mod_cast (GaussDensityCore.density_pos word.card z).ne'
  change -(GaussDensityCore.complexDensity word.card z.val)⁻¹ *
      (GaussDensityCore.complexDensity word.card z.val*fderiv ℝ (component word f) z.val v+
        f z.val word*fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val v)=_
  field_simp [hn]
  ring

private theorem coordinate_component (i : GaugeIndex) (f : QuantumTest) (word : Occupation) :
    (component word (coordinateAction i f) : SourceCoordinateSlice → ℂ)=
      fun z => (gaugeCoordinate i z : ℂ)*component word f z := rfl

private theorem coordinate_axis (i : GaugeIndex) : gaugeCoordinate i (gaugeAxis i)=1 := by
  change gaugeBasis.coord i (gaugeBasis i)=1
  simp

private theorem coordinate_component_derivative (i : GaugeIndex) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    fderiv ℝ (component word (coordinateAction i f)) z (gaugeAxis i)=
      (gaugeCoordinate i z : ℂ)*fderiv ℝ (component word f) z (gaugeAxis i)+f z word := by
  rw [coordinate_component]
  have hc := (Complex.ofRealCLM.comp (gaugeCoordinate i)).hasFDerivAt (x := z)
  change HasFDerivAt (fun w => (gaugeCoordinate i w : ℂ)) _ z at hc
  rw [fderiv_fun_mul hc.differentiableAt
    ((component word f).contDiff.differentiable (by simp)).differentiableAt, hc.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, coordinate_axis, Complex.ofReal_one, mul_one]
  rfl

theorem gauge_euler_transpose_component (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    gaugeEulerTranspose f z.val word=
      -fderiv ℝ (component word f) z.val (gaugeEuler z.val)-36*f z.val word := by
  have hterm (i : GaugeIndex) :
      GaussCoframeCore.transpose (gaugeAxis i) (coordinateAction i f) z.val word =
        -((gaugeCoordinate i z.val : ℂ)*fderiv ℝ (component word f) z.val (gaugeAxis i)+
          f z.val word+(GaussDensityCore.complexDensity word.card z.val)⁻¹*
            ((gaugeCoordinate i z.val : ℂ)*
              fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val (gaugeAxis i))*f z.val word) := by
    rw [transpose_formula, coordinate_component_derivative]
    change -((gaugeCoordinate i z.val : ℂ)*fderiv ℝ (component word f) z.val (gaugeAxis i)+
      f z.val word)-(GaussDensityCore.complexDensity word.card z.val)⁻¹*
        fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val (gaugeAxis i)*
          ((gaugeCoordinate i z.val : ℂ)*f z.val word)=_
    ring
  change evaluate z.val word ((∑ i : GaugeIndex,
    GaussCoframeCore.transpose (gaugeAxis i)*coordinateAction i) f)=_
  rw [LinearMap.sum_apply, map_sum]
  change (∑ i : GaugeIndex, GaussCoframeCore.transpose (gaugeAxis i) (coordinateAction i f) z.val word)=_
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  simp only [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.mul_sum]
  rw [gauge_sum, gauge_sum, complex_density_euler]
  have hn : GaussDensityCore.complexDensity word.card z.val≠0 := by
    change (GaussDensityCore.density word.card z.val : ℂ)≠0
    exact_mod_cast (GaussDensityCore.density_pos word.card z).ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    coordinateSlice_finrank, nsmul_eq_mul]
  field_simp [hn]
  ring

theorem gauge_euler_transpose (f : QuantumTest) :
    gaugeEulerTranspose f= -gaugeEulerAction f-(36 : ℂ) • f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · apply PiLp.ext
    intro word
    change gaugeEulerTranspose f z word= -gaugeEulerAction f z word-36*f z word
    rw [gauge_euler_transpose_component f word ⟨z,hz⟩, gauge_euler_component]
  · have hl : gaugeEulerTranspose f z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz ((gaugeEulerTranspose f).tsupport_subset h))
    have hr : (-gaugeEulerAction f-(36 : ℂ) • f) z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz ((-gaugeEulerAction f-(36 : ℂ) • f).tsupport_subset h))
    exact hl.trans hr.symm

theorem gauge_euler_pair (f g : QuantumTest) :
    sourcePair f (gaugeEulerAction g)=sourcePair (gaugeEulerTranspose f) g := by
  simp only [gaugeEulerAction, gaugeEulerTranspose, LinearMap.sum_apply, sourcePair,
    map_sum, inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (coordinateAction i (GaussCoframeCore.derivative (gaugeAxis i) g))=
    sourcePair (GaussCoframeCore.transpose (gaugeAxis i) (coordinateAction i f)) g
  exact (multiply_pair _ _ f (GaussCoframeCore.derivative (gaugeAxis i) g)).trans
    (GaussCoframeCore.derivative_pair (gaugeAxis i) (coordinateAction i f) g)

def radialWeightAction : CoreEnd := multiply radialWeight radial_weight_smooth
def radialAction : CoreEnd := radialWeightAction*gaugeEulerAction
def radialTranspose : CoreEnd := gaugeEulerTranspose*radialWeightAction

private theorem radial_weight_action_real (f : QuantumTest) :
    (radialWeightAction f : SourceCoordinateSlice → FockFiber)=fun z => radialWeight z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

theorem gauge_euler_radial_weight (f : QuantumTest) :
    gaugeEulerAction (radialWeightAction f)=radialWeightAction (gaugeEulerAction f)-
      (2 : ℂ) • radialWeightAction f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · rw [gauge_euler_apply, radial_weight_action_real,
      fderiv_fun_smul ((radial_weight_smooth ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
    change radialWeight z • fderiv ℝ f z (gaugeEuler z)+
      fderiv ℝ radialWeight z (gaugeEuler z) • f z = _
    rw [radial_weight_euler ⟨z,hz⟩]
    change radialWeight z • fderiv ℝ f z (gaugeEuler z)+
      (-2*radialWeight z) • f z = radialWeightAction (gaugeEulerAction f) z-
        (2 : ℂ) • radialWeightAction f z
    simp only [radial_weight_action_real, gauge_euler_apply]
    apply PiLp.ext
    intro word
    change (radialWeight z : ℂ)*(fderiv ℝ f z (gaugeEuler z)) word+
      ((-2*radialWeight z : ℝ) : ℂ)*f z word=
      (radialWeight z : ℂ)*(fderiv ℝ f z (gaugeEuler z)) word-
        2*((radialWeight z : ℂ)*f z word)
    push_cast
    ring
  · have hl : gaugeEulerAction (radialWeightAction f) z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz ((gaugeEulerAction (radialWeightAction f)).tsupport_subset h))
    have hr : (radialWeightAction (gaugeEulerAction f)-(2 : ℂ) • radialWeightAction f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz
        ((radialWeightAction (gaugeEulerAction f)-(2 : ℂ) • radialWeightAction f).tsupport_subset h))
    exact hl.trans hr.symm

theorem radial_transpose (f : QuantumTest) :
    radialTranspose f= -radialAction f-(34 : ℂ) • radialWeightAction f := by
  change gaugeEulerTranspose (radialWeightAction f)=_
  rw [gauge_euler_transpose, gauge_euler_radial_weight]
  change -(radialWeightAction (gaugeEulerAction f)-(2 : ℂ) • radialWeightAction f)-
    (36 : ℂ) • radialWeightAction f=
      -radialWeightAction (gaugeEulerAction f)-(34 : ℂ) • radialWeightAction f
  module

theorem radial_pair (f g : QuantumTest) :
    sourcePair f (radialAction g)=sourcePair (radialTranspose f) g :=
  (multiply_pair _ _ f (gaugeEulerAction g)).trans (gauge_euler_pair (radialWeightAction f) g)

theorem original_radial_current (f g : QuantumTest) :
    sourcePair f (radialAction g)+sourcePair (radialAction f) g=
      -(34 : ℂ)*sourcePair f (radialWeightAction g) := by
  rw [radial_pair, radial_transpose]
  have hw : sourcePair (radialWeightAction f) g=sourcePair f (radialWeightAction g) :=
    (multiply_pair _ _ f g).symm
  simp only [sourcePair, map_sub, map_neg, map_smul, inner_sub_left, inner_neg_left,
    inner_smul_left, map_ofNat] at hw ⊢
  rw [hw]
  ring

theorem original_radial_cross (f : QuantumTest) :
    (sourcePair f (radialAction f)).re= -17*(sourcePair f (radialWeightAction f)).re := by
  have h := congrArg Complex.re (original_radial_current f f)
  have hs := congrArg Complex.re (pair_conjugate f (radialAction f))
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re,
    Complex.conj_re] at h hs
  norm_num at h
  linarith

theorem radial_action_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    radialAction f z=radialWeight z • fderiv ℝ f z (gaugeEuler z) := by
  change radialWeightAction (gaugeEulerAction f) z=_
  simp only [radial_weight_action_real, gauge_euler_apply]

theorem original_native_radial_current (f : QuantumTest) (z : physicalChart) :
    (-Complex.I) • (fderiv ℝ f z.val (direction (radialAmbient z.val) z.val)+
      connection (radialAmbient z.val) z.val (f z.val)) = (-Complex.I) • radialAction f z.val := by
  rw [radial_native_direction, radial_connection_zero, zero_apply,
    add_zero, map_smul, radial_action_apply]

end LowEnergy.SourceGaugeRadialPair
