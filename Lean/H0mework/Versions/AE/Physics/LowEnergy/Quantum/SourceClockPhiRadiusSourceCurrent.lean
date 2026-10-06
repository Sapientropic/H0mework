import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockRadiusResponseAffine
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockRadiusSourceGeometry
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarVirialBulk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusSourceCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaCoefficient GaussYukawaOperator GaussRadialMomentum
open GaussLiveMomentum GaussNativePotential GaussNativeMatter GaussQuantumMultiplier GaussFockWeights
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockReflectedForm SourceScalarDoubleCurrent SourceScalarRadialContact SourceScalarVirialBulk
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineP286GaugeConnectionVariationDensity
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
abbrev phiRadius := SourceClockRadiusResponseAffine.affineRadius
abbrev phiRadiusAction := SourceClockRadiusResponseAffine.affineRadiusAction
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)

private theorem phi_pos (z : SourceCoordinateSlice) : 0 < phiRadius z := by
  unfold phiRadius SourceClockRadiusResponseAffine.affineRadius
  positivity
private theorem phi_smooth : ContDiff ℝ ∞ phiRadius :=
  SourceClockRadiusResponseAffine.affine_radius_smooth
private theorem phi_square (z : SourceCoordinateSlice) :
    phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
private theorem one_le_phi (z : SourceCoordinateSlice) : 1 ≤ phiRadius z := by
  have h:=phi_square z
  have hp:=(phi_pos z).le
  nlinarith only [h,hp,sq_nonneg ‖scalarField z‖]

def phiReciprocal (z : SourceCoordinateSlice) : ℝ := (phiRadius z)⁻¹
private theorem phi_reciprocal_smooth : ContDiff ℝ ∞ phiReciprocal :=
  phi_smooth.inv (fun z=>(phi_pos z).ne')
def phiInverseAction : End := multiply phiReciprocal (fun _=>phi_reciprocal_smooth.contDiffAt)

def phiDirectionWeight (v : Scalar) (z : SourceCoordinateSlice) : ℝ :=
  -inner ℝ (scalarField z) v/(4*phiRadius z)
private theorem phi_direction_smooth (v : Scalar) : ContDiff ℝ ∞ (phiDirectionWeight v) :=
  (scalarField_smooth.inner ℝ contDiff_const|>.neg).div (contDiff_const.mul phi_smooth)
    (fun z=>mul_ne_zero (by norm_num) (phi_pos z).ne')
def phiDirectionAction (v : Scalar) : End := multiply (phiDirectionWeight v) (fun _=>(phi_direction_smooth v).contDiffAt)

private theorem real_multiply (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ a z.val) (f : QuantumTest) :
    (multiply a smooth f:SourceCoordinateSlice → FockFiber)=(fun z=>a z • f z) := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem phi_action_real (f : QuantumTest) :
    (phiRadiusAction f:SourceCoordinateSlice → FockFiber)=(fun z=>phiRadius z • f z) := by
  unfold phiRadiusAction SourceClockRadiusResponseAffine.affineRadiusAction
  exact real_multiply _ _ f

private theorem phi_derivative (z h : SourceCoordinateSlice) :
    fderiv ℝ phiRadius z h=inner ℝ (scalarField z) (h.2.1:Scalar)/(4*phiRadius z) := by
  have hf:HasFDerivAt scalarField scalarCoordinate z := (scalarCoordinate.hasFDerivAt (x:=z)).const_add vacuum
  have hs:=((hf.norm_sq).mul_const (4⁻¹:ℝ)).const_add 1
  simp only [←div_eq_mul_inv] at hs
  have hd:=hs.sqrt (show 1+‖scalarField z‖^2/4≠0 by positivity)
  change HasFDerivAt phiRadius _ z at hd
  rw [hd.fderiv]
  simp only [smul_apply,two_smul,smul_eq_mul]
  change (1/(2*phiRadius z))*(4⁻¹*(inner ℝ (scalarField z) (h.2.1:Scalar)+
    inner ℝ (scalarField z) (h.2.1:Scalar)))=_
  field_simp
  ring

private theorem mother_self_skew (a : NativeLie) (phi : Scalar) :
    inner ℝ phi (scalarP286ActionBilinear a phi)=0 := by
  have h:=StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) phi phi
  rw [original_scalar_pairing,original_scalar_pairing] at h
  change inner ℝ (scalarP286ActionBilinear a phi) phi+
    inner ℝ phi (scalarP286ActionBilinear a phi)=0 at h
  rw [real_inner_comm (scalarP286ActionBilinear a phi) phi] at h
  have hi:=real_inner_comm phi (scalarP286ActionBilinear a phi)
  linarith only [h,hi]
private theorem inverse_phi_radial (z : physicalChart) (v : Ambient) :
    inner ℝ (scalarField z.val) ((inverseL z.val v).2.1:Scalar)=inner ℝ (scalarField z.val) v.1 := by
  have h:=congrArg Prod.fst (inverse_right z v)
  change scalarP286ActionBilinear (inverseL z.val v).1 (scalarField z.val)+((inverseL z.val v).2.1:Scalar)=v.1 at h
  have hi:=congrArg (fun y:Scalar=>inner ℝ (scalarField z.val) y) h
  rw [inner_add_right,mother_self_skew,zero_add] at hi
  exact hi
private theorem native_phi_derivative (z : physicalChart) (v : Ambient) :
    fderiv ℝ phiRadius z.val (direction v z.val)= -phiDirectionWeight v.1 z.val := by
  rw [phi_derivative]
  change inner ℝ (scalarField z.val) ((inverseL z.val v).2.1:Scalar)/_= _
  rw [inverse_phi_radial]
  unfold phiDirectionWeight
  ring

private theorem native_phi (v : Ambient) :
    bracket (covariantMomentum v) phiRadiusAction=Complex.I • phiDirectionAction v.1 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hd:directional v (phiRadiusAction f) z=phiRadius z • directional v f z-
        phiDirectionWeight v.1 z • f z := by
      rw [directional_apply,phi_action_real,
        fderiv_fun_smul (phi_smooth.differentiable (by simp)).differentiableAt
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change phiRadius z • fderiv ℝ f z (direction v z)+fderiv ℝ phiRadius z (direction v z) • f z=_
      rw [native_phi_derivative ⟨z,hz⟩ v,neg_smul]
      rfl
    change (-Complex.I) • (directional v (phiRadiusAction f) z+
      connection v z ((phiRadius z:ℂ) • f z))-
      (phiRadius z:ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))=
        Complex.I • ((phiDirectionWeight v.1 z:ℂ) • f z)
    rw [hd,map_smul]
    apply PiLp.ext
    intro word
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
    ring
  · have hl:bracket (covariantMomentum v) phiRadiusAction f z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h=>hz ((bracket (covariantMomentum v) phiRadiusAction f).tsupport_subset h))
    have hr:(Complex.I • phiDirectionAction v.1) f z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h=>hz (((Complex.I • phiDirectionAction v.1) f).tsupport_subset h))
    exact hl.trans hr.symm

private theorem test_pair_ext (f g : QuantumTest) (h:∀a,sourcePair a f=sourcePair a g) : f=g := by
  have hz:inner ℂ (embed (f-g)) (embed (f-g))=0 := by
    calc _=sourcePair (f-g) f-sourcePair (f-g) g := by rw [map_sub];exact inner_sub_right _ _ _
         _=0 := sub_eq_zero.mpr (h (f-g))
  apply sub_eq_zero.mp
  exact embed_injective (((inner_self_eq_zero (𝕜:=ℂ)).mp hz).trans (map_zero embed).symm)

private theorem adjoint_phi (v : Ambient) :
    bracket (GaussMomentumAdjoint.adjoint v) phiRadiusAction=Complex.I • phiDirectionAction v.1 := by
  apply LinearMap.ext
  intro g
  apply test_pair_ext
  intro f
  have hn:=LinearMap.congr_fun (native_phi v) f
  change covariantMomentum v (phiRadiusAction f)-phiRadiusAction (covariantMomentum v f)=
    Complex.I • phiDirectionAction v.1 f at hn
  have hp:=congrArg (fun q=>sourcePair q g) hn
  have h1:=GaussNativeForm.adjoint_pair v f (phiRadiusAction g)
  have h2:=GaussNativeForm.adjoint_pair v (phiRadiusAction f) g
  have hr1:=multiply_pair phiRadius (fun _=>phi_smooth.contDiffAt) (covariantMomentum v f) g
  have hr2:=multiply_pair phiRadius (fun _=>phi_smooth.contDiffAt) f (GaussMomentumAdjoint.adjoint v g)
  have hd:=multiply_pair (phiDirectionWeight v.1) (fun _=>(phi_direction_smooth v.1).contDiffAt) f g
  change sourcePair (covariantMomentum v f) (phiRadiusAction g)=
    sourcePair (phiRadiusAction (covariantMomentum v f)) g at hr1
  change sourcePair f (phiRadiusAction (GaussMomentumAdjoint.adjoint v g))=
    sourcePair (phiRadiusAction f) (GaussMomentumAdjoint.adjoint v g) at hr2
  change sourcePair f (phiDirectionAction v.1 g)=sourcePair (phiDirectionAction v.1 f) g at hd
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_smul_left,Complex.conj_I] at hp
  change sourcePair f (GaussMomentumAdjoint.adjoint v (phiRadiusAction g)-
    phiRadiusAction (GaussMomentumAdjoint.adjoint v g))=sourcePair f (Complex.I • phiDirectionAction v.1 g)
  simp only [sourcePair,map_smul,inner_smul_right]
  change inner ℂ (embed f) (embed (GaussMomentumAdjoint.adjoint v (phiRadiusAction g)-
    phiRadiusAction (GaussMomentumAdjoint.adjoint v g)))=_
  rw [map_sub,inner_sub_right]
  simp only [sourcePair] at h1 h2 hr1 hr2 hd
  linear_combination h1+hr1-h2-hr2-hp-Complex.I*hd

/-- Every actual native row and its original weighted transpose return the same full-phi derivative. -/
theorem original_phi_radius_native_jet (v : Ambient) :
    bracket (covariantMomentum v) phiRadiusAction=Complex.I • phiDirectionAction v.1 ∧
      bracket (GaussMomentumAdjoint.adjoint v) phiRadiusAction=Complex.I • phiDirectionAction v.1 :=
  ⟨native_phi v,adjoint_phi v⟩

private theorem phi_direction_bound (v : Scalar) (z : SourceCoordinateSlice) :
    |phiDirectionWeight v z| ≤ ‖v‖/2 := by
  have hr:=phi_square z
  have hp:=phi_pos z
  have hq:‖scalarField z‖ ≤ 2*phiRadius z := by nlinarith [norm_nonneg (scalarField z)]
  have hi:=norm_inner_le_norm (𝕜:=ℝ) (scalarField z) v
  rw [Real.norm_eq_abs] at hi
  rw [phiDirectionWeight,abs_div,abs_neg,abs_of_pos (mul_pos (by norm_num) hp)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  have h:=mul_le_mul_of_nonneg_right hq (norm_nonneg v)
  nlinarith only [hi,h]
private def phiDirectionFiber (v : Scalar) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (phiDirectionWeight v z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem phi_direction_fiber_smooth (v : Scalar) : ContDiff ℝ ∞ (phiDirectionFiber v) :=
  (Complex.ofRealCLM.contDiff.comp (phi_direction_smooth v)).smul contDiff_const
private theorem phi_direction_commutes (v : Scalar) (z : physicalChart) (w : ℕ → ℂ) :
    Commute (weight w) (phiDirectionFiber v z) := (Commute.one_right _).smul_right _
private theorem phi_direction_fiber_bound (v : Scalar) (z : physicalChart) (f : FockFiber) :
    ‖phiDirectionFiber v z f‖ ≤ (‖v‖/2)*‖f‖ := by
  change ‖(phiDirectionWeight v z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (phi_direction_bound v z) (norm_nonneg f)
def phiDirectionOperator (v : Scalar) : Op := GaussBoundedMultiplier.extension (phiDirectionFiber v)
  (fun _=>(phi_direction_fiber_smooth v).contDiffAt) (phi_direction_commutes v) (‖v‖/2) (by positivity) (phi_direction_fiber_bound v)
theorem original_phi_direction_core (v : Scalar) (f : QuantumTest) :
    phiDirectionOperator v (embed f)=embed (phiDirectionAction v f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
theorem original_phi_direction_norm (v : Scalar) : ‖phiDirectionOperator v‖ ≤ ‖v‖/2 :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private def phiInverseFiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (phiReciprocal z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem phi_inverse_fiber_smooth : ContDiff ℝ ∞ phiInverseFiber :=
  (Complex.ofRealCLM.contDiff.comp phi_reciprocal_smooth).smul contDiff_const
private theorem phi_inverse_commutes (z : physicalChart) (w : ℕ → ℂ) :
    Commute (weight w) (phiInverseFiber z) := (Commute.one_right _).smul_right _
private theorem phi_inverse_bound (z : physicalChart) (f : FockFiber) : ‖phiInverseFiber z f‖ ≤ 1*‖f‖ := by
  change ‖(phiReciprocal z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,phiReciprocal,abs_inv,abs_of_pos (phi_pos z)]
  exact mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (one_le_phi z)) (norm_nonneg f)
def phiInverseBounded : Op := GaussBoundedMultiplier.extension phiInverseFiber
  (fun _=>phi_inverse_fiber_smooth.contDiffAt) phi_inverse_commutes 1 (by norm_num) phi_inverse_bound
private theorem phi_inverse_core (f : QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f

private theorem phi_direction_square (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,(phiDirectionWeight (scalarBasis a) z)^2)=(1-phiReciprocal z^2)/4 := by
  simp only [phiDirectionWeight,div_pow,neg_sq]
  rw [←Finset.sum_div,scalarBasis.sum_sq_inner_left]
  have h:=phi_square z
  unfold phiReciprocal
  field_simp [(phi_pos z).ne']
  nlinarith only [h]
private theorem phi_action_square (f : QuantumTest) :
    (∑ a : ScalarIndex,phiDirectionAction (scalarBasis a) (phiDirectionAction (scalarBasis a) f))=
      (1/4:ℂ) • (f-phiInverseAction (phiInverseAction f)) := by
  apply DFunLike.ext
  intro z
  simp only [sum_apply]
  change (∑ a : ScalarIndex,(phiDirectionWeight (scalarBasis a) z:ℂ) • ((phiDirectionWeight (scalarBasis a) z:ℂ) • f z))=
    (1/4:ℂ) • (f z-(phiReciprocal z:ℂ) • ((phiReciprocal z:ℂ) • f z))
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [phi_direction_square]
  have he:(((1-phiReciprocal z^2)/4:ℝ):ℂ)=(1/4:ℂ)-(1/4:ℂ)*(phiReciprocal z:ℂ)^2 := by push_cast;ring
  rw [he]
  module
private theorem phi_core_energy (f : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (phiDirectionAction (scalarBasis a) f)‖^2)=
      (‖embed f‖^2-‖embed (phiInverseAction f)‖^2)/4 := by
  have he:=congrArg (sourcePair f) (phi_action_square f)
  have hp (a : ScalarIndex) : sourcePair f (phiDirectionAction (scalarBasis a) (phiDirectionAction (scalarBasis a) f))=
      sourcePair (phiDirectionAction (scalarBasis a) f) (phiDirectionAction (scalarBasis a) f) := multiply_pair _ _ _ _
  have hi:sourcePair f (phiInverseAction (phiInverseAction f))=sourcePair (phiInverseAction f) (phiInverseAction f) := multiply_pair _ _ _ _
  simp only [sourcePair,map_sum,map_smul,map_sub,inner_sum,inner_smul_right,inner_sub_right] at he
  change (∑ a : ScalarIndex,sourcePair f (phiDirectionAction (scalarBasis a) (phiDirectionAction (scalarBasis a) f)))=
    (1/4:ℂ)*(sourcePair f f-sourcePair f (phiInverseAction (phiInverseAction f))) at he
  simp_rw [hp,hi] at he
  have hr:=congrArg Complex.re he
  have hquarter (z:ℂ):((1/4:ℂ)*z).re=(1/4:ℝ)*z.re := by norm_num [Complex.mul_re]
  rw [Complex.re_sum,hquarter,Complex.sub_re] at hr
  have hself (q:QuantumTest):(sourcePair q q).re=‖embed q‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (embed q)
  simp only [hself] at hr
  exact hr.trans (by ring)

/-- Full ambient70 Parseval reads the original affine field; the slice61 and broken9 are not exchanged. -/
theorem original_phi_gradient_energy (x : H) :
    (∑ a : ScalarIndex,‖phiDirectionOperator (scalarBasis a) x‖^2)=
      (‖x‖^2-‖phiInverseBounded x‖^2)/4 := by
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro v
  obtain ⟨f,rfl⟩:=coreEquiv.surjective v
  change (∑ a : ScalarIndex,‖phiDirectionOperator (scalarBasis a) (embed f)‖^2)=
    (‖embed f‖^2-‖phiInverseBounded (embed f)‖^2)/4
  simp only [original_phi_direction_core,phi_inverse_core]
  exact phi_core_energy f

private theorem multiplier_commutes (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) : Commute (localMultiplier A smooth) phiRadiusAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (phiRadius z:ℂ) (f z)
private theorem real_commutes (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c smooth) phiRadiusAction :=
  multiplier_commutes _ _
private theorem quantum_commutes (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ (fun w=>quantized (A w)) z.val) :
    Commute (GaussQuantumMultiplier.action A smooth) phiRadiusAction := multiplier_commutes _ _
private theorem paired_commutes (A B : End) (pair : GaussCoframeForm.Paired B A)
    (commutes : Commute A phiRadiusAction) : Commute B phiRadiusAction := by
  apply LinearMap.ext
  intro g
  apply test_pair_ext
  intro f
  have hc:=LinearMap.congr_fun commutes.eq f
  change A (phiRadiusAction f)=phiRadiusAction (A f) at hc
  change sourcePair f (B (phiRadiusAction g))=sourcePair f (phiRadiusAction (B g))
  calc _=sourcePair (A f) (phiRadiusAction g) := pair f (phiRadiusAction g)
       _=sourcePair (phiRadiusAction (A f)) g := multiply_pair _ _ _ _
       _=sourcePair (A (phiRadiusAction f)) g := by rw [hc]
       _=sourcePair (phiRadiusAction f) (B g) := (pair (phiRadiusAction f) g).symm
       _=_ := (multiply_pair _ _ _ _).symm
private theorem coframe_derivative (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) phiRadiusAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (phiRadiusAction f) z=
    phiRadiusAction (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f) z
  rw [GaussCoframeCore.derivative_apply,phi_action_real,
    fderiv_fun_smul (phi_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  have hd:fderiv ℝ phiRadius z (GaussCoframeCore.coframeDirection i)=0 := by
    rw [phi_derivative]
    change inner ℝ (scalarField z) 0/_=0
    simp
  change phiRadius z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    fderiv ℝ phiRadius z (GaussCoframeCore.coframeDirection i) • f z=_
  rw [hd,zero_smul,add_zero]
  change phiRadius z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)=
    (phiRadius z:ℂ) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z
  rw [GaussCoframeCore.derivative_apply]
  apply PiLp.ext
  intro word
  exact Complex.real_smul
private theorem coframe_momentum (i : Fin 6) : Commute (GaussCoframeCore.momentum i) phiRadiusAction :=
  (coframe_derivative i).smul_left (-Complex.I)
private theorem coframe_adjoint (i : Fin 6) : Commute (GaussCoframeCore.adjoint i) phiRadiusAction :=
  paired_commutes _ _ (GaussCoframeKinetic.adjoint_pair i) (coframe_momentum i)
private theorem coframe_current (a : Fin 7) : Commute (GaussCoframeSpin.current a) phiRadiusAction := quantum_commutes _ _
private theorem coframe_kinetic : Commute GaussCoframeKinetic.kinetic phiRadiusAction := by
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  exact (coframe_adjoint i).mul_left ((real_commutes _ _).mul_left (coframe_momentum j))
private theorem coframe_mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeForm.mixed i a c smooth) phiRadiusAction :=
  (((coframe_current a).mul_left ((real_commutes c smooth).mul_left (coframe_momentum i))).add_left
    ((coframe_adjoint i).mul_left ((real_commutes c smooth).mul_left (coframe_current a)))).smul_left _
private theorem coframe_commutes : Commute GaussCoframeForm.coframeAction phiRadiusAction := by
  apply Commute.add_left
  · apply Commute.add_left
    · apply Commute.add_left
      · exact coframe_kinetic.add_left (((coframe_mixed _ _ _ _).add_left
          (coframe_mixed _ _ _ _)).add_left (coframe_mixed _ _ _ _)|>.add_left (coframe_mixed _ _ _ _))
      · apply Commute.sum_left
        intro a _
        exact ((coframe_current a).mul_left ((real_commutes _ _).mul_left (coframe_current a))).smul_left _
    · exact (((quantum_commutes _ _).mul_left (real_commutes _ _)).add_left
        ((real_commutes _ _).mul_left (quantum_commutes _ _))).smul_left _
  · exact real_commutes _ _
private theorem matter_commutes : Commute GaussMatterCore.matterAction phiRadiusAction := by
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  exact quantum_commutes _ _
private theorem gauge_momentum (v : Ambient) (hv:v.1=0) : Commute (covariantMomentum v) phiRadiusAction := by
  have h:=native_phi v
  have hz:phiDirectionAction v.1=0 := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (phiDirectionWeight v.1 z:ℂ) • f z=0
    rw [phiDirectionWeight,hv,inner_zero_right]
    simp
  rw [hz,smul_zero] at h
  exact sub_eq_zero.mp h
private theorem gauge_adjoint (v : Ambient) (hv:v.1=0) : Commute (GaussMomentumAdjoint.adjoint v) phiRadiusAction :=
  paired_commutes _ _ (GaussNativeForm.adjoint_pair v) (gauge_momentum v hv)
private theorem gauge_commutes : Commute gaugeKinetic phiRadiusAction := by
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  exact (gauge_adjoint (gaugeDirection i a) rfl).mul_left
    ((real_commutes _ _).mul_left (gauge_momentum (gaugeDirection j a) rfl))

/-- Every actual non-scalar Hamiltonian department preserves the same auxiliary real field radius. -/
theorem original_phi_radius_non_scalar_commute :
    Commute gaugeKinetic phiRadiusAction ∧ Commute GaussCoframeForm.coframeAction phiRadiusAction ∧
      Commute GaussMatterCore.matterAction phiRadiusAction ∧ Commute (diagonalAction-scalarKinetic) phiRadiusAction := by
  refine ⟨gauge_commutes,coframe_commutes,matter_commutes,?_⟩
  change Commute ((scalarKinetic+gaugeKinetic+multiply potential potential_smooth)+
    GaussCoframeForm.coframeAction+GaussMatterCore.matterAction-scalarKinetic) phiRadiusAction
  have he:((scalarKinetic+gaugeKinetic+multiply potential potential_smooth)+
    GaussCoframeForm.coframeAction+GaussMatterCore.matterAction-scalarKinetic)=
      gaugeKinetic+multiply potential potential_smooth+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction := by abel
  rw [he]
  exact ((gauge_commutes.add_left (real_commutes _ _)).add_left coframe_commutes).add_left matter_commutes

def phiRadiusCurrent : End := (Complex.I/2:ℂ) • ∑ a : ScalarIndex,
  (Pa a*W*phiDirectionAction (scalarBasis a)+phiDirectionAction (scalarBasis a)*W*P a)

theorem original_phi_radius_scalar_current : bracket scalarKinetic phiRadiusAction=phiRadiusCurrent := by
  have hs (a : ScalarIndex) : bracket (Pa a*(W*P a)) phiRadiusAction=
      Complex.I • (Pa a*W*phiDirectionAction (scalarBasis a)+phiDirectionAction (scalarBasis a)*W*P a) := by
    have hw:=(real_commutes scalarWeight scalarWeight_smooth).eq
    have he:bracket (Pa a*(W*P a)) phiRadiusAction=
        Pa a*W*bracket (P a) phiRadiusAction+bracket (Pa a) phiRadiusAction*W*P a := by
      unfold bracket
      linear_combination (norm:=noncomm_ring) Pa a*hw*P a
    rw [he,native_phi,adjoint_phi]
    simp only [scalarDirection,mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]
  unfold scalarKinetic sandwich phiRadiusCurrent
  simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,
    Finset.mul_sum,←Finset.sum_sub_distrib,←smul_sub]
  have h:=Finset.sum_congr (s₁:=Finset.univ) rfl (fun a _=>hs a)
  simp only [bracket] at h
  rw [h,←Finset.smul_sum,smul_smul]
  congr 1
  ring

theorem original_phi_radius_hamiltonian_current : bracket diagonalAction phiRadiusAction=phiRadiusCurrent := by
  have h:=original_phi_radius_non_scalar_commute.2.2.2.eq
  have hs:=original_phi_radius_scalar_current
  unfold bracket at h hs ⊢
  linear_combination (norm:=noncomm_ring) h+hs

private theorem phi_euler_derivative (z : SourceCoordinateSlice) :
    fderiv ℝ phiRadius z (phiEuler z)=phiRadius z-phiReciprocal z := by
  rw [phi_derivative]
  change inner ℝ (scalarField z) (scalarField z)/(4*phiRadius z)=_
  rw [real_inner_self_eq_norm_sq]
  have hs:=phi_square z
  unfold phiReciprocal
  field_simp [(phi_pos z).ne']
  nlinarith only [hs]

/-- The original phi-Euler differentiates rho; it does not replace the old centered cutoff. -/
theorem original_phi_euler_radius : bracket phiEulerAction phiRadiusAction=phiRadiusAction-phiInverseAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change phiEulerAction (phiRadiusAction f) z-phiRadiusAction (phiEulerAction f) z=
    phiRadiusAction f z-phiInverseAction f z
  rw [phi_euler_apply,phi_action_real,
    fderiv_fun_smul (phi_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change phiRadius z • fderiv ℝ f z (phiEuler z)+fderiv ℝ phiRadius z (phiEuler z) • f z-
    (phiRadius z:ℂ) • phiEulerAction f z=_
  rw [phi_euler_derivative,phi_euler_apply]
  apply PiLp.ext
  intro word
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
  change _=(phiRadius z:ℂ)*f z word-(phiReciprocal z:ℂ)*f z word
  push_cast
  ring

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

private theorem root_native (v : Ambient) : Commute (covariantMomentum v) inverseRootAction :=
  native_multiplier inverseRootVolume inverse_root_volume_smooth inverse_root_native_derivative v

private theorem weight_pair (p q : QuantumTest) :
    sourcePair p (multiply scalarWeight scalarWeight_smooth q)=
      (-(sourceTime 0 : ℂ))*sourcePair (inverseRootAction p) (inverseRootAction q) := by
  have he : multiply scalarWeight scalarWeight_smooth q=(-(sourceTime 0 : ℂ)) • inverseVolumeAction q := by
    apply DFunLike.ext
    intro z
    change (scalarWeight z : ℂ) • q z=(-(sourceTime 0 : ℂ)) • ((reciprocalVolume z : ℂ) • q z)
    rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
    congr 1
  rw [he,←inverse_root_square]
  have hp : sourcePair p (inverseRootAction (inverseRootAction q))=
    sourcePair (inverseRootAction p) (inverseRootAction q) := multiply_pair _ _ _ _
  simpa only [sourcePair,map_smul,inner_smul_right] using congrArg (fun c : ℂ => -(sourceTime 0 : ℂ)*c) hp


private theorem direction_root (a : ScalarIndex) : Commute (phiDirectionAction (scalarBasis a)) inverseRootAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (phiDirectionWeight (scalarBasis a) z:ℂ) (inverseRootVolume z:ℂ) (f z)

theorem original_phi_radius_current_pair (p q : QuantumTest) : sourcePair p (phiRadiusCurrent q)=
    (-Complex.I*(sourceTime 0:ℂ)/2)*∑ a : ScalarIndex,
      (sourcePair (P a (inverseRootAction p)) (phiDirectionAction (scalarBasis a) (inverseRootAction q))+
        sourcePair (phiDirectionAction (scalarBasis a) (inverseRootAction p)) (P a (inverseRootAction q))) := by
  have hP (a : ScalarIndex) (f : QuantumTest) :
      inverseRootAction (P a f)=P a (inverseRootAction f) :=
    (LinearMap.congr_fun (root_native (scalarDirection a)).eq f).symm
  have hd (a : ScalarIndex) (f : QuantumTest) :
      inverseRootAction (phiDirectionAction (scalarBasis a) f)=phiDirectionAction (scalarBasis a) (inverseRootAction f) :=
    (LinearMap.congr_fun (direction_root a).eq f).symm
  have hs (a : ScalarIndex) : sourcePair p ((Pa a*W*phiDirectionAction (scalarBasis a)+phiDirectionAction (scalarBasis a)*W*P a) q)=
      (-(sourceTime 0:ℂ))*(sourcePair (P a (inverseRootAction p)) (phiDirectionAction (scalarBasis a) (inverseRootAction q))+
        sourcePair (phiDirectionAction (scalarBasis a) (inverseRootAction p)) (P a (inverseRootAction q))) := by
    change sourcePair p (Pa a (W (phiDirectionAction (scalarBasis a) q))+phiDirectionAction (scalarBasis a) (W (P a q)))=_
    simp only [sourcePair,map_add,inner_add_right]
    change sourcePair p (Pa a (W (phiDirectionAction (scalarBasis a) q)))+sourcePair p (phiDirectionAction (scalarBasis a) (W (P a q)))=_
    have hdp : sourcePair p (phiDirectionAction (scalarBasis a) (W (P a q)))=sourcePair (phiDirectionAction (scalarBasis a) p) (W (P a q)) :=
      GaussNativeForm.multiply_pair _ _ p _
    rw [GaussNativeForm.adjoint_pair,hdp,weight_pair,weight_pair,hP,hd,hd,hP]
    simp only [sourcePair]
    ring
  simp only [phiRadiusCurrent,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  change (Complex.I/2:ℂ)*(∑ a : ScalarIndex,sourcePair p ((Pa a*W*phiDirectionAction (scalarBasis a)+phiDirectionAction (scalarBasis a)*W*P a) q))=_
  simp_rw [hs]
  rw [←Finset.mul_sum]
  simp only [sourcePair]
  ring

private theorem gradient_energy (f : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (phiDirectionAction (scalarBasis a) f)‖^2) ≤ (1/4:ℝ)*‖embed f‖^2 := by
  have h := original_phi_gradient_energy (embed f)
  simp only [original_phi_direction_core] at h
  nlinarith only [h,sq_nonneg ‖phiInverseBounded (embed f)‖]

private theorem young (x y δ : ℝ) (hδ : 0 < δ) : x*y ≤ δ*x^2+y^2/(4*δ) := by
  have h := sq_nonneg (2*δ*x-y)
  have he : δ*x^2+y^2/(4*δ)=(4*δ^2*x^2+y^2)/(4*δ) := by
    field_simp
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 4*δ)).mpr
  nlinarith only [h]

private theorem column_pair_price (p q : QuantumTest) (δ : ℝ) (hδ : 0 < δ) :
    (∑ a : ScalarIndex,‖sourcePair (P a p) (phiDirectionAction (scalarBasis a) q)‖) ≤ δ*scalarForm p+‖embed q‖^2/(16*δ) := by
  have h (a : ScalarIndex) := (norm_inner_le_norm (𝕜 := ℂ) (embed (P a p))
    (embed (phiDirectionAction (scalarBasis a) q))).trans (young _ _ δ hδ)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => h a)
  change (∑ a : ScalarIndex,‖sourcePair (P a p) (phiDirectionAction (scalarBasis a) q)‖) ≤ _ at hs
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div] at hs
  have hg := div_le_div_of_nonneg_right (gradient_energy q) (by positivity : 0 ≤ 4*δ)
  apply hs.trans
  change δ*scalarForm p+(∑ a : ScalarIndex,‖embed (phiDirectionAction (scalarBasis a) q)‖^2)/(4*δ) ≤ _
  exact add_le_add le_rfl (hg.trans_eq (by ring))

/-- One finite source gradient Gram pays both native legs; there is no factor seventy or assumed moving native bound. -/
theorem original_phi_radius_current_price (p q : QuantumTest) (δ : ℝ) (hδ : 0 < δ) :
    ‖sourcePair p (phiRadiusCurrent q)‖ ≤ (|sourceTime 0|/2)*
      (δ*(scalarForm (inverseRootAction p)+scalarForm (inverseRootAction q))+
        (‖embed (inverseRootAction p)‖^2+‖embed (inverseRootAction q)‖^2)/(16*δ)) := by
  have h1 := column_pair_price (inverseRootAction p) (inverseRootAction q) δ hδ
  have h2 := column_pair_price (inverseRootAction q) (inverseRootAction p) δ hδ
  have he (a : ScalarIndex) : ‖sourcePair (phiDirectionAction (scalarBasis a) (inverseRootAction p)) (P a (inverseRootAction q))‖=
      ‖sourcePair (P a (inverseRootAction q)) (phiDirectionAction (scalarBasis a) (inverseRootAction p))‖ := by
    exact norm_inner_symm _ _
  have hn : ‖-Complex.I*(sourceTime 0:ℂ)/2‖=|sourceTime 0|/2 := by
    simp only [norm_div,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
      one_mul]
    norm_num
  rw [original_phi_radius_current_pair,norm_mul,hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ a : ScalarIndex,‖sourcePair (P a (inverseRootAction p)) (phiDirectionAction (scalarBasis a) (inverseRootAction q))+
      sourcePair (phiDirectionAction (scalarBasis a) (inverseRootAction p)) (P a (inverseRootAction q))‖ := norm_sum_le _ _
    _ ≤ (∑ a : ScalarIndex,‖sourcePair (P a (inverseRootAction p)) (phiDirectionAction (scalarBasis a) (inverseRootAction q))‖)+
      ∑ a : ScalarIndex,‖sourcePair (P a (inverseRootAction q)) (phiDirectionAction (scalarBasis a) (inverseRootAction p))‖ := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      exact (norm_add_le _ _).trans_eq (by rw [he])
    _ ≤ _ := (add_le_add h1 h2).trans_eq (by ring)


end LowEnergy.SourceClockPhiRadiusSourceCurrent
