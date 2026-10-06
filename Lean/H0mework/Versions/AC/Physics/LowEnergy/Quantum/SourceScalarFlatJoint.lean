import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourcePairedMomentumFlux
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussCoframeCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarFlatJoint
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory SourceCoframeVolumeCurrent
open GaussYukawaCoefficient SourceMixedNativeReturn SourceScalarPairedTransport
open SourcePairedRadialFlux SourcePairedMomentumFlux SourceEscapeCurrent
open FullYSourceResolventGraphSplice SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace BigOperators

private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
private abbrev OriginalCore : Type := diagonal.domain

abbrev SliceIndex := Fin (Module.finrank ℝ scalarSlice)
def scalarFrame : OrthonormalBasis SliceIndex ℝ scalarSlice := stdOrthonormalBasis ℝ scalarSlice

def scalarAxis (v : scalarSlice) : SourceCoordinateSlice := (0,v,0)
def flatMomentum (v : scalarSlice) : CoreEnd := (-Complex.I) • GaussCoframeCore.derivative (scalarAxis v)

/-- Every scalar-slice direction is returned by the full original twelve-Gauss inverse. -/
theorem native_scalar_slice_inverse (z : physicalChart) (v : scalarSlice) :
    inverseL z.val ((v : Scalar),0)=(0,(v,0)) := by
  have h : splitMap z.val (0,(v,0))=((v : Scalar),0) := by simp [splitMap,sliceMap,orbitMap]
  rw [←h,inverse_left]

/-- The original momentum restricted to the scalar61 slice is the actual flat derivative. -/
theorem actual_flat_momentum (v : scalarSlice) : covariantMomentum ((v : Scalar),0)=flatMomentum v := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · rw [covariantMomentum_apply,native_scalar_slice_inverse ⟨z,hz⟩]
    change (-Complex.I) • (fderiv ℝ f z (scalarAxis v)+GaussNativeMatter.nativeFock 0 (f z))=_
    rw [map_zero,zero_apply,add_zero]
    exact congrArg (fun x : FockFiber => (-Complex.I) • x) (GaussCoframeCore.derivative_apply _ _ _).symm
  · have hl : covariantMomentum ((v : Scalar),0) f z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((covariantMomentum ((v : Scalar),0) f).tsupport_subset h))
    have hr : flatMomentum v f z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((flatMomentum v f).tsupport_subset h))
    exact hl.trans hr.symm

theorem actual_scalar_density_derivative (N : ℕ) (v : scalarSlice) (z : physicalChart) :
    fderiv ℝ (GaussDensityCore.complexDensity N) z.val (scalarAxis v)=0 := by
  have hd := ((GaussDensityCore.complexDensity_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => z.val+r • scalarAxis v) (scalarAxis v) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (scalarAxis v) |>.const_add z.val
  have hh := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  have he : (fun r : ℝ => GaussDensityCore.complexDensity N (z.val+r • scalarAxis v))=
      (fun _ : ℝ => GaussDensityCore.complexDensity N z.val) := by
    funext r
    simp only [GaussDensityCore.complexDensity,GaussDensityCore.density,scalarAxis,
      Prod.smul_mk,Prod.fst_add,Prod.snd_add,smul_zero,add_zero]
  change HasDerivAt (fun r : ℝ => GaussDensityCore.complexDensity N (z.val+r • scalarAxis v))
    (fderiv ℝ (GaussDensityCore.complexDensity N) z.val (scalarAxis v)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

private theorem scalar_transpose (N : ℕ) (v : scalarSlice) (f : GaussDensityCore.ScalarTest) :
    GaussDensityCore.weightedTranspose N (scalarAxis v) f= -GaussDensityCore.derivative (scalarAxis v) f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · rw [GaussDensityCore.weightedTranspose_apply N _ _ ⟨z,hz⟩,
      fderiv_fun_mul ((GaussDensityCore.complexDensity_smooth N ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [actual_scalar_density_derivative N v ⟨z,hz⟩]
    have hn : GaussDensityCore.complexDensity N z≠0 := by
      change (GaussDensityCore.density N z : ℂ)≠0
      exact_mod_cast (GaussDensityCore.density_pos N ⟨z,hz⟩).ne'
    change -(GaussDensityCore.complexDensity N z)⁻¹*
      (GaussDensityCore.complexDensity N z*fderiv ℝ f z (scalarAxis v)+f z*0)=
      -GaussDensityCore.derivative (scalarAxis v) f z
    rw [GaussDensityCore.derivative_apply]
    simp only [mul_zero,add_zero]
    field_simp [hn]
  · have hl : GaussDensityCore.weightedTranspose N (scalarAxis v) f z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((GaussDensityCore.weightedTranspose N (scalarAxis v) f).tsupport_subset h))
    have hr : (-GaussDensityCore.derivative (scalarAxis v) f) z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz ((-GaussDensityCore.derivative (scalarAxis v) f).tsupport_subset h))
    exact hl.trans hr.symm

private theorem flat_transpose (v : scalarSlice) (f : QuantumTest) :
    GaussCoframeCore.transpose (scalarAxis v) f= -GaussCoframeCore.derivative (scalarAxis v) f := by
  apply embed_injective
  rw [GaussCoframeCore.transpose_embed,map_neg]
  apply PiLp.ext
  intro word
  change GaussScalarTransport.scalarEmbed word.card
    (GaussDensityCore.weightedTranspose word.card (scalarAxis v) (component word f))=
    -(embed (GaussCoframeCore.derivative (scalarAxis v) f) word)
  rw [scalar_transpose,map_neg]
  change -(GaussScalarTransport.scalarEmbed word.card (GaussDensityCore.derivative (scalarAxis v) (component word f)))=
    -(GaussScalarTransport.scalarEmbed word.card (component word (GaussCoframeCore.derivative (scalarAxis v) f)))
  rw [GaussCoframeCore.component_derivative]

theorem flat_momentum_pair (v : scalarSlice) (f g : QuantumTest) :
    sourcePair f (flatMomentum v g)=sourcePair (flatMomentum v f) g := by
  have h := GaussCoframeCore.derivative_pair (scalarAxis v) f g
  rw [flat_transpose] at h
  change inner ℂ (embed f) (embed ((-Complex.I) • GaussCoframeCore.derivative (scalarAxis v) g))=
    inner ℂ (embed ((-Complex.I) • GaussCoframeCore.derivative (scalarAxis v) f)) (embed g)
  rw [map_smul,map_smul,inner_smul_right,inner_smul_left]
  have hh : sourcePair f (GaussCoframeCore.derivative (scalarAxis v) g)=
      -sourcePair (GaussCoframeCore.derivative (scalarAxis v) f) g := by
    simpa only [sourcePair,map_neg,inner_neg_left] using h
  change (-Complex.I)*sourcePair f (GaussCoframeCore.derivative (scalarAxis v) g)=_
  rw [hh]
  simp only [sourcePair,map_neg,Complex.conj_I,neg_neg]
  ring

private theorem flat_constant (sharp : Bool) (a : Scalar) (v : scalarSlice) :
    Commute (flatMomentum v) (constantAction sharp a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let T := (branchMap sharp a).restrictScalars ℝ
  have h := T.hasFDerivAt.comp z ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change (-Complex.I) • GaussCoframeCore.derivative (scalarAxis v) (constantAction sharp a f) z=
    branchMap sharp a ((-Complex.I) • GaussCoframeCore.derivative (scalarAxis v) f z)
  rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,map_smul]
  apply congrArg (fun x : FockFiber => (-Complex.I) • x)
  change fderiv ℝ (T ∘ f) z (scalarAxis v)=T (fderiv ℝ f z (scalarAxis v))
  rw [h.fderiv]
  rfl

def flatScalarCurrent (sharp : Bool) : CoreEnd :=
  ∑ i : SliceIndex, constantAction sharp (scalarFrame i : Scalar)*flatMomentum (scalarFrame i)

/-- True transpose of the scalar61 current, including every original Number density and both CAR branches. -/
theorem flat_scalar_current_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (flatScalarCurrent sharp g)=sourcePair (flatScalarCurrent (!sharp) f) g := by
  simp only [flatScalarCurrent,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  change sourcePair f (constantAction sharp (scalarFrame i : Scalar) (flatMomentum (scalarFrame i) g))=
    sourcePair (constantAction (!sharp) (scalarFrame i : Scalar) (flatMomentum (scalarFrame i) f)) g
  exact ((constant_pair sharp (scalarFrame i : Scalar) f _).trans (flat_momentum_pair _ _ g)).trans
    (congrArg (fun x : QuantumTest => sourcePair x g)
      (LinearMap.congr_fun (flat_constant (!sharp) (scalarFrame i : Scalar) (scalarFrame i)).eq f))

private theorem basis_readout {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] V) (x : E) : (∑ i,(inner ℝ x (b i)) • T (b i))=T x := by
  have h := congrArg T (b.sum_repr' x)
  simp only [map_sum,map_smul] at h
  have he : (∑ i,(inner ℝ x (b i)) • T (b i))=(∑ i,(inner ℝ (b i) x) • T (b i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm x (b i)]
  exact he.trans h

private theorem flat_scalar_sum (sharp : Bool) :
    (∑ i : SliceIndex,constantAction sharp (scalarFrame i : Scalar)*
      SourceClosedCostNativeProbe.coordinateAction ((scalarFrame i : Scalar),0))=scalarAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.sum_apply,sum_apply]
  change (∑ i : SliceIndex,branchMap sharp (scalarFrame i : Scalar)
    ((inner ℝ (z.2.1 : Scalar) (scalarFrame i : Scalar) : ℂ) • f z))=branchMap sharp (z.2.1 : Scalar) (f z)
  let T : scalarSlice →ₗ[ℝ] FockFiber :=
    { toFun := fun v => branchMap sharp (v : Scalar) (f z)
      map_add' := by intro x y; simp only [Submodule.coe_add,map_add,add_apply]
      map_smul' := by intro c x; simp only [Submodule.coe_smul,map_smul,smul_apply]; rfl }
  have he := basis_readout scalarFrame T z.2.1
  calc
    _ = ∑ i : SliceIndex,(inner ℝ z.2.1 (scalarFrame i)) • T (scalarFrame i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    _ = _ := he

private theorem flat_potential (m ell : ℕ) (v : scalarSlice) :
    flatMomentum v*potentialAction m ell=potentialAction m ell*flatMomentum v+
      (-Complex.I) • (SourceClosedCostNativeProbe.coordinateAction ((v : Scalar),0)*SourceMixedNativeReturn.thetaAction m ell) := by
  rw [←actual_flat_momentum]
  exact LinearMap.ext (momentum_potential m ell ((v : Scalar),0))

private theorem end_sum_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] (C P Q : ι → Module.End ℂ V) (b T : Module.End ℂ V)
    (hC : ∀ a, Commute (C a) b)
    (hP : ∀ a, P a*b=b*P a+(-Complex.I) • (Q a*T)) :
    (∑ a,C a*P a)*b-b*(∑ a,C a*P a)=(-Complex.I) • ((∑ a,C a*Q a)*T) := by
  simp only [Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc,hP,mul_add,←mul_assoc,(hC a).eq]
  simp only [mul_smul_comm,←mul_assoc]
  abel

private theorem constant_potential (sharp : Bool) (a : Scalar) (m ell : ℕ) :
    Commute (constantAction sharp a) (potentialAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (branchMap sharp a) (radialPotential m ell z : ℂ) (f z)

theorem actual_flat_scalar_commutator (sharp : Bool) (m ell : ℕ) :
    flatScalarCurrent sharp*potentialAction m ell-potentialAction m ell*flatScalarCurrent sharp=
      (-Complex.I) • (scalarAction sharp*SourceMixedNativeReturn.thetaAction m ell) := by
  have h := end_sum_commutator (fun i => constantAction sharp (scalarFrame i : Scalar))
    (fun i => flatMomentum (scalarFrame i))
    (fun i => SourceClosedCostNativeProbe.coordinateAction ((scalarFrame i : Scalar),0))
    (potentialAction m ell) (SourceMixedNativeReturn.thetaAction m ell)
    (fun i => constant_potential sharp (scalarFrame i : Scalar) m ell) (fun i => flat_potential m ell (scalarFrame i))
  exact h.trans (congrArg (fun A : CoreEnd => (-Complex.I) • (A*SourceMixedNativeReturn.thetaAction m ell)) (flat_scalar_sum sharp))

private theorem subtract_commutes {R : Type*} [Ring R] (a c b : R)
    (h : a*b-b*a=c*b-b*c) : Commute (a-c) b := by
  change (a-c)*b=b*(a-c)
  rw [sub_mul,mul_sub]
  apply sub_eq_zero.mp
  calc
    _ = (a*b-b*a)-(c*b-b*c) := by abel
    _ = 0 := sub_eq_zero.mpr h

/-- The native angular and connection remainder cancels in the complete radial commutator. -/
theorem actual_angular_radial_cancellation (sharp : Bool) (m ell : ℕ) :
    Commute (scalarMomentum sharp-flatScalarCurrent sharp) (potentialAction m ell) := by
  have hn := actual_scalar_commutator sharp m ell
  have hf := actual_flat_scalar_commutator sharp m ell
  have hi : Complex.I • (flatScalarCurrent sharp*potentialAction m ell-potentialAction m ell*flatScalarCurrent sharp)=
      scalarAction sharp*SourceMixedNativeReturn.thetaAction m ell := by
    rw [hf,smul_smul]
    norm_num
  have h := smul_right_injective CoreEnd Complex.I_ne_zero (hn.symm.trans hi.symm)
  exact subtract_commutes (scalarMomentum sharp) (flatScalarCurrent sharp) (potentialAction m ell) h

theorem actual_flat_scalar_pair (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q))=
      Complex.I*(sourcePair (flatScalarCurrent (!sharp) p) (potentialAction m ell q)-
        sourcePair (potentialAction m ell p) (flatScalarCurrent sharp q)) := by
  have h := LinearMap.congr_fun (actual_flat_scalar_commutator sharp m ell) q
  have hh := congrArg (fun f : QuantumTest => Complex.I • f) h
  have hc : scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q)=
      Complex.I • (flatScalarCurrent sharp (potentialAction m ell q)-potentialAction m ell (flatScalarCurrent sharp q)) := by
    simpa only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.smul_apply,smul_smul,
      show Complex.I*(-Complex.I)=1 by simp,one_smul] using hh.symm
  change inner ℂ (embed p) (embed (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q)))=_
  rw [hc,map_smul,map_sub,inner_smul_right,inner_sub_right]
  exact congrArg (fun a : ℂ => Complex.I*a) (congrArg₂ (fun a b : ℂ => a-b)
    (flat_scalar_current_pair sharp p (potentialAction m ell q))
    (potential_pair m ell p (flatScalarCurrent sharp q)))

private theorem star_im_ne (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- The original entire signed response descends to scalar61; no angular response is estimated separately. -/
theorem actual_joint_flat_return (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    radialResponse sharp m ell F z hz g k+externalMomentum sharp m ell F z hz g k=
      sourcePair (flatScalarCurrent (!sharp) (coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)))
        (potentialAction m ell (coreEquiv.symm (sourceCore F z hz g)))-
      sourcePair (potentialAction m ell (coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)))
        (flatScalarCurrent sharp (coreEquiv.symm (sourceCore F z hz g))) := by
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  have hs := actual_scalar_relative_ward sharp m ell F z hz g k
  have h6 := actual_six_radial_return sharp m ell F z hz g k
  have he := actual_momentum_external_return sharp m ell F z hz g k
  have hj : sourcePair p (scalarAction sharp (SourceMixedNativeReturn.thetaAction m ell q))=
      Complex.I*(radialResponse sharp m ell F z hz g k+externalMomentum sharp m ell F z hz g k) := by
    exact hs.trans (by rw [h6,←he]; ring)
  apply mul_left_cancel₀ Complex.I_ne_zero
  exact hj.symm.trans (actual_flat_scalar_pair sharp m ell p q)

/-- Positive scalar61 comparison generated from the original source measure, not positivity of H0. -/
def flatKinetic : CoreEnd := ∑ i : SliceIndex,flatMomentum (scalarFrame i)*flatMomentum (scalarFrame i)

theorem actual_flat_kinetic_square (f : QuantumTest) :
    (sourcePair f (flatKinetic f)).re=∑ i : SliceIndex,‖embed (flatMomentum (scalarFrame i) f)‖^2 := by
  simp only [flatKinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := flat_momentum_pair (scalarFrame i) f (flatMomentum (scalarFrame i) f)
  have hs : (sourcePair (flatMomentum (scalarFrame i) f) (flatMomentum (scalarFrame i) f)).re=
      ‖embed (flatMomentum (scalarFrame i) f)‖^2 := by
    simpa only [sourcePair] using! (inner_self_eq_norm_sq (𝕜 := ℂ) (embed (flatMomentum (scalarFrame i) f)))
  exact (congrArg Complex.re h).trans hs

def rowCost (sharp : Bool) : ℝ := ∑ i : SliceIndex,‖constantBounded sharp (scalarFrame i : Scalar)‖^2

theorem actual_flat_current_bound (sharp : Bool) (f : QuantumTest) :
    ‖embed (flatScalarCurrent sharp f)‖^2 ≤ rowCost sharp*(sourcePair f (flatKinetic f)).re := by
  have hb : ‖embed (flatScalarCurrent sharp f)‖ ≤
      ∑ i : SliceIndex,‖constantBounded sharp (scalarFrame i : Scalar)‖*
        ‖embed (flatMomentum (scalarFrame i) f)‖ := by
    change ‖embed ((∑ i : SliceIndex,constantAction sharp (scalarFrame i : Scalar)*flatMomentum (scalarFrame i)) f)‖ ≤ _
    rw [LinearMap.sum_apply,map_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have he := congrArg norm (constant_bounded_core sharp (scalarFrame i : Scalar) (flatMomentum (scalarFrame i) f))
    exact he.symm.le.trans ((constantBounded sharp (scalarFrame i : Scalar)).le_opNorm _)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : SliceIndex => ‖constantBounded sharp (scalarFrame i : Scalar)‖)
    (fun i : SliceIndex => ‖embed (flatMomentum (scalarFrame i) f)‖)
  rw [actual_flat_kinetic_square]
  exact hs.trans hc

theorem actual_scalar_frame_dimension : Fintype.card SliceIndex=61 := by
  simpa only [SliceIndex,Fintype.card_fin] using SourceQuantumScalarOrbitDimensions.scalarSlice_finrank

/-- Original Gamma consumes the flat signed current without changing its resolvent or source filter. -/
theorem actual_gamma_flat_cofinal (sharp : Bool) (m ell : ℕ) (g k : OriginalCore) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0,
      SourceGammaNativeBudget.sourceGamma sharp m ell F g k z=
        SourcePairedMomentumFlux.coefficient*Complex.I*(
          sourcePair (flatScalarCurrent (!sharp) (coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)))
            (potentialAction m ell (coreEquiv.symm (sourceCore F z hz g)))-
          sourcePair (potentialAction m ell (coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)))
            (flatScalarCurrent sharp (coreEquiv.symm (sourceCore F z hz g))))-
        Complex.I*SourceMovingJetFlux.fixedEndpointProfile sharp m ell F g k z := by
  filter_upwards [actual_gamma_external_cofinal sharp m ell g k] with F hF
  intro z hz
  exact (hF z hz).trans (congrArg (fun a : ℂ =>
    SourcePairedMomentumFlux.coefficient*Complex.I*a-
      Complex.I*SourceMovingJetFlux.fixedEndpointProfile sharp m ell F g k z)
    (actual_joint_flat_return sharp m ell F z hz g k))

end LowEnergy.SourceScalarFlatJoint
