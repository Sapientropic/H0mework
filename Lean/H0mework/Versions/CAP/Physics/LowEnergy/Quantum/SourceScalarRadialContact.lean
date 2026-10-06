import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceGammaNativeBudget
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceElectricColumns
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussCoframeCore

/-! Original scalar61 Euler and the complete native radial contact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceScalarRadialContact
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge GaussHistoryHilbert GaussLiveMomentum
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussNativeForm GaussCoframeCore
open SourceQuantumScalarOrbitDimensions
open GaussNativeEnergy GaussMomentumAdjoint GaussRadialMomentum GaussYukawaCoefficient
open SourceGammaNativeBudget SourceClosedCostNativeProbe
open scoped ContDiff Topology InnerProductSpace
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

def scalarEuler (z : SourceCoordinateSlice) : SourceCoordinateSlice := (0,z.2.1,0)

abbrev CoreEnd := QuantumTest →ₗ[ℂ] QuantumTest
abbrev SliceIndex := Fin (Module.finrank ℝ scalarSlice)
def sliceBasis : Module.Basis SliceIndex ℝ scalarSlice := Module.finBasis ℝ scalarSlice

def sliceCoordinate (i : SliceIndex) : SourceCoordinateSlice →L[ℝ] ℝ :=
  (sliceBasis.coord i).toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ scalarSlice coordinateSlice).comp
      (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice)))

def sliceAxis (i : SliceIndex) : SourceCoordinateSlice := (0,sliceBasis i,0)

def coordinateAction (i : SliceIndex) : CoreEnd :=
  multiply (sliceCoordinate i) (fun _ => (sliceCoordinate i).contDiff.contDiffAt)

def scalarEulerAction : CoreEnd := ∑ i : SliceIndex,
  coordinateAction i*GaussCoframeCore.derivative (sliceAxis i)

def scalarEulerTranspose : CoreEnd := ∑ i : SliceIndex,
  GaussCoframeCore.transpose (sliceAxis i)*coordinateAction i

private def evaluate (z : SourceCoordinateSlice) (word : Occupation) : QuantumTest →ₗ[ℂ] ℂ where
  toFun f := f z word
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem euler_sum (z : SourceCoordinateSlice) :
    (∑ i : SliceIndex, sliceCoordinate i z • sliceAxis i)=scalarEuler z := by
  apply Prod.ext
  · simp [sliceAxis,scalarEuler,Prod.fst_sum]
  · apply Prod.ext
    · simp only [Prod.fst_sum,Prod.snd_sum,sliceAxis,Prod.smul_mk]
      change (∑ i : SliceIndex, sliceBasis.coord i z.2.1 • sliceBasis i)=z.2.1
      exact sliceBasis.sum_repr z.2.1
    · simp [sliceAxis,scalarEuler,Prod.snd_sum]

private theorem derivative_component (v : SourceCoordinateSlice) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    GaussCoframeCore.derivative v f z word=fderiv ℝ (component word f) z v := by
  have h := congrArg (fun g : GaussDensityCore.ScalarTest => g z)
    (GaussCoframeCore.component_derivative v f word)
  change GaussCoframeCore.derivative v f z word=
    GaussDensityCore.derivative v (component word f) z at h
  simpa only [GaussDensityCore.derivative_apply] using h

private theorem scalar_sum (z : SourceCoordinateSlice) (L : SourceCoordinateSlice →L[ℝ] ℂ) :
    (∑ i : SliceIndex, (sliceCoordinate i z : ℂ)*L (sliceAxis i))=L (scalarEuler z) := by
  rw [←euler_sum, map_sum]
  simp only [map_smul, Complex.real_smul]

theorem scalar_euler_component (f : QuantumTest) (word : Occupation) (z : SourceCoordinateSlice) :
    scalarEulerAction f z word=fderiv ℝ (component word f) z (scalarEuler z) := by
  change evaluate z word ((∑ i : SliceIndex,
    coordinateAction i*GaussCoframeCore.derivative (sliceAxis i)) f)=_
  rw [LinearMap.sum_apply, map_sum]
  change (∑ i : SliceIndex, (sliceCoordinate i z : ℂ)*
    GaussCoframeCore.derivative (sliceAxis i) f z word)=_
  simp_rw [derivative_component]
  exact scalar_sum z _

theorem scalar_euler_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    scalarEulerAction f z=fderiv ℝ f z (scalarEuler z) := by
  apply PiLp.ext
  intro word
  rw [scalar_euler_component]
  have h := derivative_component (scalarEuler z) f word z
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

private theorem complex_density_euler (N : ℕ) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.complexDensity N) z.val (scalarEuler z.val)=0 := by
  have hd := ((GaussDensityCore.complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => z.val+r • scalarEuler z.val) (scalarEuler z.val) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (scalarEuler z.val) |>.const_add z.val
  have hh := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  have he : (fun r : ℝ => GaussDensityCore.complexDensity N (z.val+r • scalarEuler z.val))=
      (fun _ : ℝ => GaussDensityCore.complexDensity N z.val) := by
    funext r
    simp only [GaussDensityCore.complexDensity,GaussDensityCore.density,scalarEuler,
      Prod.smul_mk,Prod.fst_add,Prod.snd_add,smul_zero,add_zero]
  change HasDerivAt (fun r : ℝ => GaussDensityCore.complexDensity N (z.val+r • scalarEuler z.val))
    (fderiv ℝ (GaussDensityCore.complexDensity N) z.val (scalarEuler z.val)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

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

private theorem coordinate_component (i : SliceIndex) (f : QuantumTest) (word : Occupation) :
    (component word (coordinateAction i f) : SourceCoordinateSlice → ℂ)=
      fun z => (sliceCoordinate i z : ℂ)*component word f z := rfl

private theorem coordinate_axis (i : SliceIndex) : sliceCoordinate i (sliceAxis i)=1 := by
  change sliceBasis.coord i (sliceBasis i)=1
  simp

private theorem coordinate_component_derivative (i : SliceIndex) (f : QuantumTest)
    (word : Occupation) (z : SourceCoordinateSlice) :
    fderiv ℝ (component word (coordinateAction i f)) z (sliceAxis i)=
      (sliceCoordinate i z : ℂ)*fderiv ℝ (component word f) z (sliceAxis i)+f z word := by
  rw [coordinate_component]
  have hc := (Complex.ofRealCLM.comp (sliceCoordinate i)).hasFDerivAt (x := z)
  change HasFDerivAt (fun w => (sliceCoordinate i w : ℂ)) _ z at hc
  rw [fderiv_fun_mul hc.differentiableAt
    ((component word f).contDiff.differentiable (by simp)).differentiableAt, hc.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, coordinate_axis, Complex.ofReal_one, mul_one]
  rfl

theorem scalar_euler_transpose_component (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    scalarEulerTranspose f z.val word=
      -fderiv ℝ (component word f) z.val (scalarEuler z.val)-61*f z.val word := by
  have hterm (i : SliceIndex) :
      GaussCoframeCore.transpose (sliceAxis i) (coordinateAction i f) z.val word =
        -((sliceCoordinate i z.val : ℂ)*fderiv ℝ (component word f) z.val (sliceAxis i)+
          f z.val word+(GaussDensityCore.complexDensity word.card z.val)⁻¹*
            ((sliceCoordinate i z.val : ℂ)*
              fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val (sliceAxis i))*f z.val word) := by
    rw [transpose_formula, coordinate_component_derivative]
    change -((sliceCoordinate i z.val : ℂ)*fderiv ℝ (component word f) z.val (sliceAxis i)+
      f z.val word)-(GaussDensityCore.complexDensity word.card z.val)⁻¹*
        fderiv ℝ (GaussDensityCore.complexDensity word.card) z.val (sliceAxis i)*
          ((sliceCoordinate i z.val : ℂ)*f z.val word)=_
    ring
  change evaluate z.val word ((∑ i : SliceIndex,
    GaussCoframeCore.transpose (sliceAxis i)*coordinateAction i) f)=_
  rw [LinearMap.sum_apply, map_sum]
  change (∑ i : SliceIndex, GaussCoframeCore.transpose (sliceAxis i) (coordinateAction i f) z.val word)=_
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  simp only [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.mul_sum]
  rw [scalar_sum, scalar_sum, complex_density_euler]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    scalarSlice_finrank,nsmul_eq_mul,mul_zero]
  ring

theorem scalar_euler_transpose (f : QuantumTest) :
    scalarEulerTranspose f= -scalarEulerAction f-(61 : ℂ) • f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · apply PiLp.ext
    intro word
    change scalarEulerTranspose f z word= -scalarEulerAction f z word-61*f z word
    rw [scalar_euler_transpose_component f word ⟨z,hz⟩, scalar_euler_component]
  · have hl : scalarEulerTranspose f z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz ((scalarEulerTranspose f).tsupport_subset h))
    have hr : (-scalarEulerAction f-(61 : ℂ) • f) z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz ((-scalarEulerAction f-(61 : ℂ) • f).tsupport_subset h))
    exact hl.trans hr.symm

theorem scalar_euler_pair (f g : QuantumTest) :
    sourcePair f (scalarEulerAction g)=sourcePair (scalarEulerTranspose f) g := by
  simp only [scalarEulerAction, scalarEulerTranspose, LinearMap.sum_apply, sourcePair,
    map_sum, inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (coordinateAction i (GaussCoframeCore.derivative (sliceAxis i) g))=
    sourcePair (GaussCoframeCore.transpose (sliceAxis i) (coordinateAction i f)) g
  exact (multiply_pair _ _ f (GaussCoframeCore.derivative (sliceAxis i) g)).trans
    (GaussCoframeCore.derivative_pair (sliceAxis i) (coordinateAction i f) g)


/-- The number 61 comes from the original scalar slice and its original weighted measure. -/
theorem scalar_euler_current (f g : QuantumTest) :
    sourcePair f (scalarEulerAction g)+sourcePair (scalarEulerAction f) g=
      -(61 : ℂ)*sourcePair f g := by
  rw [scalar_euler_pair,scalar_euler_transpose]
  simp only [sourcePair,map_sub,map_neg,map_smul,inner_sub_left,inner_neg_left,
    inner_smul_left,map_ofNat]
  ring

private theorem scalar_slice_inverse (z : physicalChart) (q : scalarSlice) :
    inverseL z.val ((q : Scalar),0)=(0,(q,0)) := by
  have hs : splitMap z.val (0,(q,0))=((q : Scalar),0) := by
    simp [splitMap,sliceMap,orbitMap]
  rw [←hs,inverse_left]

private theorem scalar_native_expansion (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex, SourceClosedCostNativeProbe.coordinate (scalarDirection a) z •
      scalarDirection a)=((z.2.1 : Scalar),0) := by
  apply Prod.ext
  · simp only [Prod.fst_sum,Prod.smul_fst]
    change (∑ a : ScalarIndex, inner ℝ (z.2.1 : Scalar) (scalarBasis a) • scalarBasis a)=_
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using
      scalarBasis.sum_repr (z.2.1 : Scalar)
  · simp [scalarDirection,Prod.snd_sum]

def radialMomentum : CoreEnd := ∑ a : ScalarIndex,
  SourceGammaNativeBudget.scalarColumn a*covariantMomentum (scalarDirection a)

def radialAdjoint : CoreEnd := ∑ a : ScalarIndex,
  GaussMomentumAdjoint.adjoint (scalarDirection a)*SourceGammaNativeBudget.scalarColumn a

/-- The full native scalar sum returns the true scalar Euler; its inverse-L connection cancels. -/
theorem scalar_native_contraction : radialMomentum=(-Complex.I) • scalarEulerAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have he := congrArg (SourceElectricColumns.pointMomentum f z) (scalar_native_expansion z)
    simp only [map_sum,map_smul] at he
    have hs : radialMomentum f z=∑ a : ScalarIndex,
        SourceClosedCostNativeProbe.coordinate (scalarDirection a) z •
          SourceElectricColumns.pointMomentum f z (scalarDirection a) := by
      simp only [radialMomentum,LinearMap.sum_apply,sum_apply,Module.End.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    rw [hs,he]
    have hi := scalar_slice_inverse ⟨z,hz⟩ z.2.1
    have hd : direction ((z.2.1 : Scalar),0) z=scalarEuler z := by
      simp only [direction,hi,scalarEuler]
    have hc : connection ((z.2.1 : Scalar),0) z=0 := by
      simp only [connection,hi,map_zero]
    change (-Complex.I) • (fderiv ℝ f z (direction ((z.2.1 : Scalar),0) z)+
      connection ((z.2.1 : Scalar),0) z (f z))=(-Complex.I) • scalarEulerAction f z
    rw [hd,hc,zero_apply,add_zero,scalar_euler_apply]
  · exact (image_eq_zero_of_notMem_tsupport (fun h => hz ((radialMomentum f).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h => hz (((-Complex.I) • scalarEulerAction f).tsupport_subset h))).symm

private theorem radial_adjoint_pair (f g : QuantumTest) :
    sourcePair f (radialAdjoint g)=sourcePair (radialMomentum f) g := by
  simp only [radialAdjoint,radialMomentum,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro a _
  change sourcePair f (GaussMomentumAdjoint.adjoint (scalarDirection a)
      (SourceGammaNativeBudget.scalarColumn a g))=
    sourcePair (SourceGammaNativeBudget.scalarColumn a (covariantMomentum (scalarDirection a) f)) g
  exact (adjoint_pair _ _ _).trans
    (multiply_pair (SourceClosedCostNativeProbe.coordinate (scalarDirection a))
      (fun _ => (GaussRadialMomentum.scalarCoordinate.contDiff.inner ℝ contDiff_const).contDiffAt) _ _)

/-- Independent P-sharp is returned by the same original sourcePair, including the exact divergence. -/
theorem scalar_adjoint_contraction :
    radialAdjoint=(-Complex.I) • (scalarEulerAction+(61 : ℂ) • (1 : CoreEnd)) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have h := scalar_euler_current f g
  rw [radial_adjoint_pair,scalar_native_contraction]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,sourcePair,
    map_smul,map_add,inner_smul_right,inner_smul_left,inner_add_right,map_neg,Complex.conj_I,neg_neg]
  change Complex.I*sourcePair (scalarEulerAction f) g=
    (-Complex.I)*(sourcePair f (scalarEulerAction g)+(61 : ℂ)*sourcePair f g)
  linear_combination Complex.I*h

open GaussRadialDomain SourceNativeCutoffContact

def radialProfile (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (((m+1 : ℕ) : ℝ)*(1-reciprocal z)^m-
    ((ell+1 : ℕ) : ℝ)*(1-reciprocal z)^ell)/(4*radius z^3)

theorem radial_profile_smooth (m ell : ℕ) : ContDiff ℝ ∞ (radialProfile m ell) :=
  ((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow _)).sub
    (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow _))).div
      (contDiff_const.mul (radius_smooth.pow 3))
      (fun z => mul_ne_zero (by norm_num) (pow_ne_zero _ (radius_pos z).ne'))

def weightedProfileAction (m ell : ℕ) : CoreEnd :=
  multiply (fun z => GaussCoframeForm.inverseVolume z*radialProfile m ell z)
    (fun z => (GaussCoframeForm.inverseVolume_smooth z).mul (radial_profile_smooth m ell).contDiffAt)

private theorem contact_radial_coefficient (a : ScalarIndex) (m ell : ℕ) (z : SourceCoordinateSlice) :
    thetaDerivative (scalarDirection a) m ell z=
      SourceClosedCostNativeProbe.coordinate (scalarDirection a) z*radialProfile m ell z := by
  unfold thetaDerivative GaussRadialMomentum.radialDerivative radialProfile
  change (_-_)*(-inner ℝ (z.2.1 : Scalar) (scalarBasis a)/(4*radius z^3))=
    inner ℝ (z.2.1 : Scalar) (scalarBasis a)*((_ - _)/(4*radius z^3))
  ring

private theorem weight_contact (a : ScalarIndex) (m ell : ℕ) :
    multiply scalarWeight scalarWeight_smooth*contactAction (scalarDirection a) m ell=
      Complex.I • (SourceGammaNativeBudget.scalarColumn a*weightedProfileAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (scalarWeight z : ℂ)*((-Complex.I)*(thetaDerivative (scalarDirection a) m ell z : ℂ)*f z word)=
    Complex.I*((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ)*
      (((GaussCoframeForm.inverseVolume z*radialProfile m ell z : ℝ) : ℂ)*f z word))
  rw [contact_radial_coefficient]
  unfold scalarWeight GaussCoframeForm.inverseVolume
  push_cast
  ring

private theorem contact_weight (a : ScalarIndex) (m ell : ℕ) :
    contactAction (scalarDirection a) m ell*multiply scalarWeight scalarWeight_smooth=
      Complex.I • (weightedProfileAction m ell*SourceGammaNativeBudget.scalarColumn a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((-Complex.I)*(thetaDerivative (scalarDirection a) m ell z : ℂ))*((scalarWeight z : ℂ)*f z word)=
    Complex.I*(((GaussCoframeForm.inverseVolume z*radialProfile m ell z : ℝ) : ℂ)*
      ((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ)*f z word))
  rw [contact_radial_coefficient]
  unfold scalarWeight GaussCoframeForm.inverseVolume
  push_cast
  ring

private theorem contact_term {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (a w c q h p : R)
    (hw : w*c=Complex.I • (q*h)) (hc : c*w=Complex.I • (h*q)) :
    a*w*c+c*w*p=Complex.I • (a*q*h+h*(q*p)) := by
  calc
    _=a*(w*c)+(c*w)*p := by noncomm_ring
    _=a*(Complex.I • (q*h))+(Complex.I • (h*q))*p := by rw [hw,hc]
    _=_ := by simp only [mul_smul_comm,smul_mul_assoc,←smul_add,mul_assoc]

/-- The whole contact is one weighted scalar61 Euler current; no native/chart term is separately discarded. -/
theorem full_radial_contact (m ell : ℕ) :
    SourceGammaNativeBudget.scalarContact m ell=(1/2 : ℂ) •
      (scalarEulerAction*weightedProfileAction m ell+
        weightedProfileAction m ell*scalarEulerAction+(61 : ℂ) • weightedProfileAction m ell) := by
  have ht (a : ScalarIndex) :
      GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
          contactAction (scalarDirection a) m ell+
        contactAction (scalarDirection a) m ell*multiply scalarWeight scalarWeight_smooth*
          covariantMomentum (scalarDirection a)=
      Complex.I • (GaussMomentumAdjoint.adjoint (scalarDirection a)*
          SourceGammaNativeBudget.scalarColumn a*weightedProfileAction m ell+
        weightedProfileAction m ell*(SourceGammaNativeBudget.scalarColumn a*covariantMomentum (scalarDirection a))) := by
    simpa only using! contact_term (R := CoreEnd) _ _ _ _ _ _
      (weight_contact a m ell) (contact_weight a m ell)
  have hr : SourceGammaNativeBudget.scalarContact m ell=(Complex.I/2) •
      (radialAdjoint*weightedProfileAction m ell+weightedProfileAction m ell*radialMomentum) := by
    simp only [SourceGammaNativeBudget.scalarContact,ht,←Finset.smul_sum,smul_smul,
      Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,radialAdjoint,radialMomentum]
    congr 1
    ring
  have hI : (Complex.I/2)*(-Complex.I)=(1/2 : ℂ) := by
    calc _=(-Complex.I*Complex.I)/2 := by ring
         _=1/2 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  rw [hr,scalar_native_contraction,scalar_adjoint_contraction]
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add]
  rw [smul_smul,hI]
  simp only [add_mul,smul_mul_assoc,one_mul]
  module

/-- The full signed original H0 returns its actual cutoff commutator to this source current. -/
theorem original_hamiltonian_radial_contact (m ell : ℕ) :
    GaussDiagonalHistory.diagonalAction*SourceMixedNativeReturn.thetaAction m ell-
        SourceMixedNativeReturn.thetaAction m ell*GaussDiagonalHistory.diagonalAction=
      (1/2 : ℂ) • (scalarEulerAction*weightedProfileAction m ell+
        weightedProfileAction m ell*scalarEulerAction+(61 : ℂ) • weightedProfileAction m ell) := by
  rw [SourceGammaNativeBudget.full_cutoff_contact,add_sub_cancel_left,full_radial_contact]

end LowEnergy.SourceScalarRadialContact
