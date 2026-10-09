import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaQ8RadiusBudget
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceRetardedForcingTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRadiusResponseAffine
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaCoefficient GaussYukawaOperator
open GaussNativePotential GaussNativeMatter GaussQuantumMultiplier
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceClockYukawaQ8RadiusBudget SourceRetardedForcingTail SourceRelativePowerTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] resolventCore diagonalAction finiteResolvent

/-- A restriction of the unchanged affine scalar field, used only to calculate its radial current. -/
def affineRadius (x : SourceCoordinateSlice) : ℝ := Real.sqrt (1+‖scalarField x‖^2/4)
private theorem affine_pos (x : SourceCoordinateSlice) : 0<affineRadius x := by unfold affineRadius;positivity
theorem affine_radius_smooth : ContDiff ℝ ∞ affineRadius := by
  apply ContDiff.sqrt
  · exact contDiff_const.add ((scalarField_smooth.norm_sq ℝ).div_const 4)
  · intro x;positivity

def affineRadiusAction : End := multiply affineRadius (fun _ => affine_radius_smooth.contDiffAt)
def centerDifference (x : SourceCoordinateSlice) : ℝ := radius x-affineRadius x
private theorem difference_smooth : ContDiff ℝ ∞ centerDifference := radius_smooth.sub affine_radius_smooth

def centerPrice : ℝ := ‖vacuum‖/2

/-- The original centered radius and the affine-source radius differ by the actual fixed vacuum price. -/
theorem original_radius_center_bound (x : SourceCoordinateSlice) : |centerDifference x| ≤ centerPrice := by
  let a := ‖(x.2.1:Scalar)‖
  let b := ‖scalarField x‖
  let c := ‖vacuum‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hs : radius x^2=1+a^2/4 := Real.sq_sqrt (by positivity)
  have ht : affineRadius x^2=1+b^2/4 := Real.sq_sqrt (by positivity)
  have hp := (radius_pos x).le
  have hq := (affine_pos x).le
  have h1 : b ≤ a+c := by
    exact (norm_add_le vacuum (x.2.1:Scalar)).trans_eq (add_comm c a)
  have h2 : a ≤ b+c := by
    have he : (x.2.1:Scalar)=scalarField x-vacuum := by unfold scalarField;abel
    change ‖(x.2.1:Scalar)‖  ≤  ‖scalarField x‖+‖vacuum‖
    rw [he]
    exact norm_sub_le _ _
  have h3 : a ≤ 2*radius x := by nlinarith only [hs,ha,hp]
  have h4 : b ≤ 2*affineRadius x := by nlinarith only [ht,hb,hq]
  have h1sq := pow_le_pow_left₀ hb h1 2
  have h2sq := pow_le_pow_left₀ ha h2 2
  have hc1 := mul_le_mul_of_nonneg_left h3 hc
  have hc2 := mul_le_mul_of_nonneg_left h4 hc
  have hr : radius x ≤ affineRadius x+c/2 := by
    nlinarith only [hs,ht,h2sq,hc2,ha,hb,hc,hp,hq]
  have ht' : affineRadius x ≤ radius x+c/2 := by
    nlinarith only [hs,ht,h1sq,hc1,ha,hb,hc,hp,hq]
  unfold centerDifference centerPrice
  change |radius x-affineRadius x| ≤ c/2
  exact abs_le.mpr ⟨by linarith only [ht'],by linarith only [hr]⟩

private def centerFiber (x : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (centerDifference x:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem center_smooth : ContDiff ℝ ∞ centerFiber :=
  (Complex.ofRealCLM.contDiff.comp difference_smooth).smul contDiff_const
private theorem center_commutes (x : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (centerFiber x) :=
  (Commute.one_right _).smul_right _
private theorem center_bound (x : SourceCoordinateSlice) (v : FockFiber) :
    ‖centerFiber x v‖ ≤ centerPrice*‖v‖ := by
  change ‖(centerDifference x:ℂ) • v‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (original_radius_center_bound x) (norm_nonneg v)

def centerAction : End := localMultiplier centerFiber (fun _ => center_smooth.contDiffAt)
def centerBounded : Op := GaussBoundedMultiplier.extension centerFiber (fun _ => center_smooth.contDiffAt)
  (fun x => center_commutes x) centerPrice (by unfold centerPrice;positivity) (fun x => center_bound x)

def centerSource (g : diagonal.domain) : diagonal.domain := coreEquiv (centerAction (coreEquiv.symm g))
private theorem center_core (f : QuantumTest) : centerBounded (embed f)=embed (centerAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem center_norm : ‖centerBounded‖ ≤ centerPrice := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem center_source (g : diagonal.domain) : (centerSource g:H)=centerBounded (g:H) := by
  change embed (centerAction (coreEquiv.symm g))=_
  rw [←center_core]
  exact congrArg centerBounded (congrArg Subtype.val (coreEquiv.apply_symm_apply g))

private theorem radius_difference : radiusAction-affineRadiusAction=centerAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change radius x • f x-(affineRadius x:ℂ) • f x=(centerDifference x:ℂ) • f x
  apply PiLp.ext
  intro word
  simp only [PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul,centerDifference,Complex.ofReal_sub]
  ring
private theorem center_theta (m ell : ℕ) : Commute (thetaAction m ell) centerAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  rw [thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact smul_comm (SourceNativeCutoffContact.theta m ell x:ℂ) (centerDifference x:ℂ) (f x)
private theorem core_embed (f : QuantumTest) : (coreEquiv f:H)=embed f := rfl
private theorem source_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact source_embed _

def affineResponseCore (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  thetaAction m ell (bracket affineRadiusAction (resolventCore F z hz) (coreEquiv.symm g))

def affineResponseBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (μ*‖embed (affineResponseCore m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)‖^2)

attribute [local irreducible] affineResponseCore radiusResponseCore centerBounded centerSource centerAction affineRadiusAction

/-- The bounded center difference returns through two original fixed input legs, on the same compression. -/
theorem actual_radius_affine_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radiusResponseCore m ell F z hz g)=embed (affineResponseCore m ell F z hz g)+
      (centerBounded (relativeTail m ell (finiteResolvent F z (g:H)))-
        relativeTail m ell (finiteResolvent F z (centerSource g:H))) := by
  have h : radiusResponseCore m ell F z hz g=affineResponseCore m ell F z hz g+
      centerAction (thetaAction m ell (resolventCore F z hz (coreEquiv.symm g)))-
      thetaAction m ell (resolventCore F z hz (centerAction (coreEquiv.symm g))) := by
    have hr : radiusAction=affineRadiusAction+centerAction := by
      rw [←radius_difference]
      abel
    unfold radiusResponseCore affineResponseCore bracket
    rw [hr]
    simp only [add_mul,mul_add,LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,map_add,map_sub]
    have hc := LinearMap.congr_fun (center_theta m ell).eq (resolventCore F z hz (coreEquiv.symm g))
    simp only [Module.End.mul_apply] at hc
    rw [hc]
    abel
  have he := congrArg embed h
  simp only [map_sub,map_add,←center_core,←theta_core,resolvent_embed,source_embed] at he
  rw [←center_source g] at he
  change embed (radiusResponseCore m ell F z hz g)=embed (affineResponseCore m ell F z hz g)+
    centerBounded (relativeTail m ell (finiteResolvent F z (g:H)))-
    relativeTail m ell (finiteResolvent F z (centerSource g:H)) at he
  exact he.trans (by abel)

private theorem square_add (p q : H) : ‖p+q‖^2 ≤ 2*‖p‖^2+2*‖q‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le p q) 2
  nlinarith only [h,sq_nonneg (‖p‖-‖q‖)]
private theorem square_sub (p q : H) : ‖p-q‖^2 ≤ 2*‖p‖^2+2*‖q‖^2 := by
  simpa only [sub_eq_add_neg,norm_neg] using square_add p (-q)
private theorem radius_point_bound (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ‖embed (radiusResponseCore m ell F z hz g)‖^2 ≤ 2*‖embed (affineResponseCore m ell F z hz g)‖^2+
      4*centerPrice^2*‖relativeTail m ell (finiteResolvent F z (g:H))‖^2+
      4*‖relativeTail m ell (finiteResolvent F z (centerSource g:H))‖^2 := by
  rw [actual_radius_affine_source]
  let x := relativeTail m ell (finiteResolvent F z (g:H))
  let y := relativeTail m ell (finiteResolvent F z (centerSource g:H))
  have ha := square_add (embed (affineResponseCore m ell F z hz g)) (centerBounded x-y)
  have hb := square_sub (centerBounded x) y
  have hc := (centerBounded.le_opNorm x).trans (mul_le_mul_of_nonneg_right center_norm (norm_nonneg x))
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  change ‖embed (affineResponseCore m ell F z hz g)+(centerBounded x-y)‖^2 ≤ _
  nlinarith only [ha,hb,hc2]

/-- The original radius response pays its entire change of radial center internally, before the source filter. -/
theorem actual_original_radius_affine_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        radiusResponseBudget m ell F μ hμ g ≤ ENNReal.ofReal ε+2*affineResponseBudget m ell F μ hμ g := by
  intro ε hε
  let C := 4*μ*(centerPrice^2+1)
  have hC : 0<C := by dsimp [C];positivity
  obtain ⟨N1,h1⟩ := actual_theta_full_frequency_tail μ hμ g (ε/C) (by positivity)
  obtain ⟨N2,h2⟩ := actual_theta_full_frequency_tail μ hμ (centerSource g) (ε/C) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hg hb
  let X := fun w : ℝ => ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2)
  let Y := fun w : ℝ => ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (centerSource g:H))‖^2)
  have hc := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have mx : Measurable X := (((relativeTail m ell).continuous.comp (hc.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have my : Measurable Y := (((relativeTail m ell).continuous.comp (hc.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have hA : 0 ≤ 4*μ*centerPrice^2 := by positivity
  have hB : 0 ≤ 4*μ := by positivity
  have hi : radiusResponseBudget m ell F μ hμ g ≤ 2*affineResponseBudget m ell F μ hμ g+
      ENNReal.ofReal (4*μ*centerPrice^2)*(∫⁻ w : ℝ,X w)+ENNReal.ofReal (4*μ)*(∫⁻ w : ℝ,Y w) := by
    unfold radiusResponseBudget affineResponseBudget
    calc
      _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2*(μ*‖embed (affineResponseCore m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g)‖^2))+
          ENNReal.ofReal (4*μ*centerPrice^2)*X w+ENNReal.ofReal (4*μ)*Y w := by
        apply lintegral_mono
        intro w
        have hp := mul_le_mul_of_nonneg_left (radius_point_bound m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g) hμ.le
        have hp' : μ*‖embed (radiusResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2 ≤
            2*(μ*‖embed (affineResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2)+
            (4*μ*centerPrice^2)*‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2+
            (4*μ)*‖relativeTail m ell (finiteResolvent F (line μ w) (centerSource g:H))‖^2 := by nlinarith only [hp]
        apply (ENNReal.ofReal_le_ofReal hp').trans
        dsimp only [X,Y]
        rw [←ENNReal.ofReal_mul hA,←ENNReal.ofReal_mul hB]
        exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
      _=_ := by
        rw [lintegral_add_right _ (my.const_mul _),lintegral_add_right _ (mx.const_mul _)]
        simp_rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        norm_num
  have he : ENNReal.ofReal (4*μ*centerPrice^2)*ENNReal.ofReal (ε/C)+
      ENNReal.ofReal (4*μ)*ENNReal.ofReal (ε/C)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hA,←ENNReal.ofReal_mul hB,
      ←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp [C]
    field_simp
  calc
    _ ≤ (2*affineResponseBudget m ell F μ hμ g+ENNReal.ofReal (4*μ*centerPrice^2)*ENNReal.ofReal (ε/C))+
      ENNReal.ofReal (4*μ)*ENNReal.ofReal (ε/C) := hi.trans
        (add_le_add (add_le_add le_rfl (mul_le_mul le_rfl hg zero_le zero_le))
          (mul_le_mul le_rfl hb zero_le zero_le))
    _=_ := by rw [add_assoc,he,add_comm]

end LowEnergy.SourceClockRadiusResponseAffine
