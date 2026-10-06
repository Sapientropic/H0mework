import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiEndpointNativePressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiEndpointNativePrice
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open GaussNativePotential GaussYukawaCoefficient GaussRadialMomentum GaussNativeMatter GaussQuantumMultiplier
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourcePhysicalKineticSquare SourceClockAcceleration SourceClockReflectedForm
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarInverseBulk
open SourceScalarDoubleCurrent SourceScalarPairedTransport
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiRadiusResponseNativeBudget
open SourceClockYukawaCubicCurrent SourceClockPhiZeroSeedEndpointTail
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev Q : End := 1-S
private abbrev D (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell
private abbrev d (a : ScalarIndex) : End := D a*S^2
attribute [local irreducible] resolventCore compressionCore defectAction diagonalAction

private theorem real_commute (c b : SourceCoordinateSlice → ℝ)
    (hc : ∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hb : ∀z:physicalChart,ContDiffAt ℝ ∞ b z.val) : Commute (multiply c hc) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (b z:ℂ) (f z)
private theorem phi_pos (z : SourceCoordinateSlice) : 0 < phiRadius z := by
  unfold phiRadius SourceClockRadiusResponseAffine.affineRadius
  positivity
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul]
  have h : (phiReciprocal z:ℂ)*(phiRadius z:ℂ)=1 := by
    unfold phiReciprocal
    push_cast
    field_simp [(phi_pos z).ne']
  rw [h,one_smul]
private theorem radius_inverse : r*S=(1:End) :=
  (real_commute _ _ _ _).eq.symm.trans inverse_radius
private theorem inverse_D (a : ScalarIndex) : Commute S (D a) := real_commute _ _ _ _
private theorem inverse_d (a : ScalarIndex) : Commute S (d a) :=
  (inverse_D a).mul_right ((Commute.refl S).pow_right 2)
private theorem inverse_P (a : ScalarIndex) :
    bracket (P a) S=(-Complex.I) • d a := by
  have h : bracket (P a) r=Complex.I • D a :=
    (original_phi_radius_native_jet (scalarDirection a)).1
  have hm : bracket (P a) S= -(S*bracket (P a) r*S) := by
    have h1 : S*P a*r*S=S*P a := by
      calc _=S*P a*(r*S) := by noncomm_ring
           _=_ := by rw [radius_inverse,mul_one]
    have h2 : S*r*P a*S=P a*S := by rw [inverse_radius,one_mul]
    calc _= -(S*P a*r*S-S*r*P a*S) := by rw [h1,h2];unfold bracket;abel
         _=_ := by unfold bracket;noncomm_ring
  rw [hm,h]
  have hd : S*D a*S=d a := by
    rw [(inverse_D a).eq]
    change D a*S*S=D a*S^2
    rw [pow_two,mul_assoc]
  simp only [mul_smul_comm,smul_mul_assoc,neg_smul,hd]

private theorem Q_commute {A : End} (h : Commute S A) : Commute Q A :=
  (Commute.one_left A).sub_left h
private theorem first_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (B m ell) A :=
  (((Q_commute h).pow_left ell).smul_left _).sub_left (((Q_commute h).pow_left m).smul_left _)
private theorem theta_commute {A : End} (h : Commute S A) (m ell : ℕ) : Commute (T m ell) A :=
  ((Q_commute h).pow_left (m+1)).sub_left ((Q_commute h).pow_left (ell+1))
private theorem bracket_product (A X Y : End) : bracket A (X*Y)=bracket A X*Y+X*bracket A Y := by
  unfold bracket;noncomm_ring
private theorem bracket_sub (A X Y : End) : bracket A (X-Y)=bracket A X-bracket A Y := by
  unfold bracket;noncomm_ring
private theorem inverse_Q (a : ScalarIndex) : bracket (P a) Q=Complex.I • d a := by
  rw [bracket_sub]
  have hz : bracket (P a) (1:End)=0 := by simp [bracket]
  rw [hz,inverse_P,zero_sub,neg_smul,neg_neg]
private theorem geometric_successor (a : ScalarIndex) (k : ℕ) :
    bracket (P a) (Q^(k+1))=((k+1:ℂ)*Complex.I) • (Q^k*d a) := by
  induction k with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul] using inverse_Q a
  | succ k ih =>
    rw [show k+1+1=(k+1)+1 from rfl,pow_succ,bracket_product,ih,inverse_Q]
    have hm : (Q^k*d a)*Q=Q^(k+1)*d a := by
      rw [mul_assoc,(Q_commute (inverse_d a)).symm.eq,←mul_assoc,←pow_succ]
    simp only [smul_mul_assoc,mul_smul_comm]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module
private theorem theta_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) (T m ell)=(-Complex.I) • (B m ell*d a) := by
  rw [T,phiThetaAction,bracket_sub,geometric_successor,geometric_successor]
  simp only [B,SourceClockPhiRadiusResponseHessian.phiFirstPeak,sub_mul,smul_mul_assoc,smul_sub,smul_smul]
  module

private abbrev U : End := inverseVolumeAction
private abbrev n : ℝ := sourceTime 0
private abbrev A (m ell : ℕ) : End := S*T m ell
private abbrev Z (m ell : ℕ) : End := S^2*T m ell+S^3*B m ell

private theorem endpoint_native (a : ScalarIndex) (m ell : ℕ) :
    bracket (P a) (A m ell)=(-Complex.I) • (D a*Z m ell) := by
  rw [A,bracket_product,inverse_P,theta_native]
  have hm : S*(B m ell*d a)=D a*(S^3*B m ell) := by
    change S*(B m ell*(D a*S^2))=_
    have hBD := first_commute (inverse_D a) m ell
    have hBS := (first_commute (Commute.refl S) m ell).pow_right 2
    calc
      _=S*(B m ell*D a)*S^2 := by noncomm_ring
      _=S*(D a*B m ell)*S^2 := by rw [hBD.eq]
      _=(S*D a)*(B m ell*S^2) := by noncomm_ring
      _=(D a*S)*(S^2*B m ell) := by rw [(inverse_D a).eq,hBS.eq]
      _=_ := by noncomm_ring
  simp only [smul_mul_assoc,mul_smul_comm,hm]
  change (-Complex.I) • (D a*S^2*T m ell)+
    (-Complex.I) • (D a*(S^3*B m ell))=(-Complex.I) • (D a*(S^2*T m ell+S^3*B m ell))
  rw [mul_add,smul_add]
  simp only [mul_assoc]

private theorem endpoint_native_apply (a : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    P a (A m ell f)=A m ell (P a f)+(-Complex.I) • (D a (Z m ell f)) := by
  have he := LinearMap.congr_fun (endpoint_native a m ell) f
  change P a (A m ell f)-A m ell (P a f)=(-Complex.I) • (D a (Z m ell f)) at he
  exact sub_eq_iff_eq_add'.mp he

private theorem one_le_phi (z:SourceCoordinateSlice) : 1 ≤ phiRadius z := by
  have hp := (phi_pos z).le
  have hs : phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
  nlinarith only [hp,hs,sq_nonneg ‖scalarField z‖]
private theorem reciprocal_smooth : ContDiff ℝ ∞ phiReciprocal :=
  SourceClockRadiusResponseAffine.affine_radius_smooth.inv (fun z=>(phi_pos z).ne')
private def aCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  phiReciprocal z*((1-phiReciprocal z)^(m+1)-(1-phiReciprocal z)^(ell+1))
private def zCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  phiReciprocal z^2*((1-phiReciprocal z)^(m+1)-(1-phiReciprocal z)^(ell+1))+
    phiReciprocal z^3*((ell+1:ℝ)*(1-phiReciprocal z)^ell-(m+1:ℝ)*(1-phiReciprocal z)^m)
private theorem a_smooth (m ell : ℕ) : ContDiff ℝ ∞ (aCoefficient m ell) :=
  reciprocal_smooth.mul (((contDiff_const.sub reciprocal_smooth).pow _).sub
    ((contDiff_const.sub reciprocal_smooth).pow _))
private theorem z_smooth (m ell : ℕ) : ContDiff ℝ ∞ (zCoefficient m ell) :=
  ((reciprocal_smooth.pow 2).mul (((contDiff_const.sub reciprocal_smooth).pow _).sub
    ((contDiff_const.sub reciprocal_smooth).pow _))).add
    ((reciprocal_smooth.pow 3).mul
      ((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow _)).sub
        (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow _))))
private theorem linear_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) :
    (k+1:ℝ)*s*(1-s)^k ≤ 1 := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have ht := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(k+1-j)*((k+1).choose j:ℝ))
    (fun j _ => by positivity) (show 1∈Finset.range (k+1+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at ht
  simp only [pow_one,Nat.add_sub_cancel,Nat.choose_one_right,Nat.cast_add,Nat.cast_one] at ht
  nlinarith only [ht]
private theorem a_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |aCoefficient m ell z| ≤ 1/(m+2:ℝ) := by
  let s := phiReciprocal z
  have hs : 0 ≤ s := (inv_pos.mpr (phi_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hq1 : 1-s ≤ 1 := by linarith
  have he := pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hml 1)
  have ht : 0 ≤ (1-s)^(m+1)-(1-s)^(ell+1) := sub_nonneg.mpr he
  have hup : (1-s)^(m+1)-(1-s)^(ell+1) ≤ (1-s)^(m+1) :=
    sub_le_self _ (pow_nonneg hq _)
  have hp := linear_peak s hs hs1 (m+1)
  have hpeak : s*(1-s)^(m+1) ≤ 1/(m+2:ℝ) := by
    apply (le_div_iff₀ (show 0<(m+2:ℝ) by positivity)).mpr
    push_cast at hp
    nlinarith only [hp]
  change |s*((1-s)^(m+1)-(1-s)^(ell+1))| ≤ _
  rw [abs_of_nonneg (mul_nonneg hs ht)]
  exact (mul_le_mul_of_nonneg_left hup hs).trans hpeak
private theorem z_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |zCoefficient m ell z| ≤ 5/(m+2:ℝ) := by
  let s := phiReciprocal z
  let x : ℝ := (ell+1:ℝ)*s^2*(1-s)^ell
  let y : ℝ := (m+1:ℝ)*s^2*(1-s)^m
  have hs : 0 ≤ s := (inv_pos.mpr (phi_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_phi z)
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hx0 : 0 ≤ x := by dsimp [x];positivity
  have hy0 : 0 ≤ y := by dsimp [y];positivity
  have hx : x ≤ 2/(m+2:ℝ) := by
    have he := SourceNativeCutoffContact.squared_geometric_peak s hs hs1 ell
    exact he.trans (by gcongr)
  have hy : y ≤ 2/(m+2:ℝ) :=
    SourceNativeCutoffContact.squared_geometric_peak s hs hs1 m
  have ha := a_bound m ell hml z
  have he : zCoefficient m ell z=s*aCoefficient m ell z+s*(x-y) := by
    dsimp [zCoefficient,aCoefficient,s,x,y]
    ring
  rw [he]
  calc
    _ ≤ |s*aCoefficient m ell z|+|s*(x-y)| := abs_add_le _ _
    _ = s*|aCoefficient m ell z|+s*|x-y| := by rw [abs_mul,abs_mul,abs_of_nonneg hs]
    _ ≤ |aCoefficient m ell z|+|x-y| := add_le_add
      (mul_le_of_le_one_left (abs_nonneg _) hs1) (mul_le_of_le_one_left (abs_nonneg _) hs1)
    _ ≤ 1/(m+2:ℝ)+(x+y) := add_le_add ha
      ((abs_sub x y).trans_eq (by rw [abs_of_nonneg hx0,abs_of_nonneg hy0]))
    _ ≤ 1/(m+2:ℝ)+(2/(m+2:ℝ)+2/(m+2:ℝ)) :=
      add_le_add le_rfl (add_le_add hx hy)
    _ = _ := by ring

private theorem real_multiplier_bound (c : SourceCoordinateSlice → ℝ)
    (hc : ContDiff ℝ ∞ c) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z, |c z| ≤ M) (f : QuantumTest) :
    ‖embed ((multiply c (fun _ => hc.contDiffAt)) f)‖ ≤ M*‖embed f‖ := by
  let fiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
    (c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
  have hfs : ContDiff ℝ ∞ fiber :=
    (Complex.ofRealCLM.contDiff.comp hc).smul contDiff_const
  have hcomm (z : physicalChart) (w : ℕ → ℂ) :
      Commute (GaussFockWeights.weight w) (fiber z) :=
    (Commute.one_right _).smul_right _
  have hfbound (z : physicalChart) (x : FockFiber) :
      ‖fiber z x‖ ≤ M*‖x‖ := by
    change ‖(c z:ℂ) • x‖ ≤ _
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg x)
  let op := GaussBoundedMultiplier.extension fiber (fun _ => hfs.contDiffAt)
    hcomm M hM hfbound
  have hcore : op (embed f)=embed ((multiply c (fun _ => hc.contDiffAt)) f) := by
    dsimp [op]
    rw [GaussBoundedMultiplier.extension_core]
    congr 1
  have hnorm : ‖op‖ ≤ M :=
    GaussBoundedMultiplier.extension_norm fiber (fun _ => hfs.contDiffAt)
      hcomm M hM hfbound
  calc
    _ = ‖op (embed f)‖ := by rw [hcore]
    _ ≤ ‖op‖*‖embed f‖ := op.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

private theorem geometric_point (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((Q^k) f) z=(((1-phiReciprocal z:ℝ):ℂ)^k) • f z := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (((Q^k) f) z-(phiReciprocal z:ℂ) • (((Q^k) f) z))=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module
private theorem inverse_power_point (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((S^k) f) z=(phiReciprocal z:ℂ)^k • f z := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (S ((S^k) f)) z=_
    change (phiReciprocal z:ℂ) • (((S^k) f) z)=_
    rw [ih,pow_succ']
    module
private theorem theta_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (T m ell f) z=((((1-phiReciprocal z)^(m+1)-(1-phiReciprocal z)^(ell+1)):ℝ):ℂ) • f z := by
  change ((Q^(m+1)) f) z-((Q^(ell+1)) f) z=_
  rw [geometric_point,geometric_point]
  push_cast
  module
private theorem first_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (B m ell f) z=((((ell+1:ℝ)*(1-phiReciprocal z)^ell-
      (m+1:ℝ)*(1-phiReciprocal z)^m):ℝ):ℂ) • f z := by
  change ((ell+1:ℂ) • ((Q^ell) f) z-(m+1:ℂ) • ((Q^m) f) z)=_
  rw [geometric_point,geometric_point]
  push_cast
  module
private theorem a_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (A m ell f) z=(aCoefficient m ell z:ℂ) • f z := by
  change (phiReciprocal z:ℂ) • (T m ell f) z=_
  rw [theta_point]
  unfold aCoefficient
  push_cast
  module
private theorem z_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (Z m ell f) z=(zCoefficient m ell z:ℂ) • f z := by
  change ((S^2) (T m ell f)) z+((S^3) (B m ell f)) z=_
  rw [inverse_power_point,inverse_power_point,theta_point,first_point]
  unfold zCoefficient
  push_cast
  module
private theorem a_norm (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    ‖embed (A m ell f)‖ ≤ 1/(m+2:ℝ)*‖embed f‖ := by
  have he : A m ell f=multiply (aCoefficient m ell) (fun _ => (a_smooth m ell).contDiffAt) f := by
    apply DFunLike.ext;intro z;exact a_point m ell f z
  rw [he]
  exact real_multiplier_bound _ (a_smooth m ell) _ (by positivity) (a_bound m ell hml) f
private theorem z_norm (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    ‖embed (Z m ell f)‖ ≤ 5/(m+2:ℝ)*‖embed f‖ := by
  have he : Z m ell f=multiply (zCoefficient m ell) (fun _ => (z_smooth m ell).contDiffAt) f := by
    apply DFunLike.ext;intro z;exact z_point m ell f z
  rw [he]
  exact real_multiplier_bound _ (z_smooth m ell) _ (by positivity) (z_bound m ell hml) f

private theorem two_square {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private theorem native_endpoint_energy (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    (∑ a : ScalarIndex,‖embed (U (P a (A m ell f)))‖^2) ≤
      2/(m+2:ℝ)^2*scalarForm (U f)+25/(2*(m+2:ℝ)^2)*‖embed (U f)‖^2 := by
  have hUS : Commute U S := real_commute _ _ _ _
  have hUT : Commute U (T m ell) := (theta_commute hUS.symm m ell).symm
  have hUB : Commute U (B m ell) := (first_commute hUS.symm m ell).symm
  have hUA : Commute U (A m ell) := hUS.mul_right hUT
  have hUZ : Commute U (Z m ell) :=
    ((hUS.pow_right 2).mul_right hUT).add_right ((hUS.pow_right 3).mul_right hUB)
  have hUD (a : ScalarIndex) : Commute U (D a) := real_commute _ _ _ _
  have hUP (a : ScalarIndex) : Commute (P a) U :=
    SourceScalarInverseNativeEnergy.original_native_inverse_commute (scalarDirection a)
  have hrow (a : ScalarIndex) : U (P a (A m ell f))=
      A m ell (P a (U f))+(-Complex.I) • D a (Z m ell (U f)) := by
    have ha := LinearMap.congr_fun hUA.eq (P a f)
    have hd := LinearMap.congr_fun (hUD a).eq (Z m ell f)
    have hz := LinearMap.congr_fun hUZ.eq f
    have hp := LinearMap.congr_fun (hUP a).eq f
    change U (A m ell (P a f))=A m ell (U (P a f)) at ha
    change U (D a (Z m ell f))=D a (U (Z m ell f)) at hd
    change U (Z m ell f)=Z m ell (U f) at hz
    change P a (U f)=U (P a f) at hp
    rw [endpoint_native_apply,map_add,map_smul,ha,hd,hz,←hp]
  have hsquare (a : ScalarIndex) : ‖embed (U (P a (A m ell f)))‖^2 ≤
      2*(1/(m+2:ℝ))^2*‖embed (P a (U f))‖^2+
        2*‖embed (D a (Z m ell (U f)))‖^2 := by
    rw [hrow,map_add,map_smul]
    have ht := two_square (embed (A m ell (P a (U f))))
      ((-Complex.I) • embed (D a (Z m ell (U f))))
    have ha := pow_le_pow_left₀ (norm_nonneg _) (a_norm m ell hml (P a (U f))) 2
    simp only [norm_smul,norm_neg,Complex.norm_I,one_mul,mul_pow] at ht ha
    nlinarith only [ht,ha]
  have hsum := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset ScalarIndex)) => hsquare a)
  have hg := original_phi_gradient_energy (embed (Z m ell (U f)))
  simp_rw [original_phi_direction_core] at hg
  have hn := sq_nonneg ‖phiInverseBounded (embed (Z m ell (U f)))‖
  have hz := pow_le_pow_left₀ (norm_nonneg _) (z_norm m ell hml (U f)) 2
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,mul_pow] at hsum hz
  have hcoef : 2*(1/(m+2:ℝ))^2=2/(m+2:ℝ)^2 := by
    field_simp [show (m+2:ℝ)≠0 by positivity]
  have hcoef' : (1/2:ℝ)*(5/(m+2:ℝ))^2=25/(2*(m+2:ℝ)^2) := by
    field_simp [show (m+2:ℝ)≠0 by positivity]
    norm_num
  rw [←hcoef,←hcoef']
  change _ ≤ 2*(1/(m+2:ℝ))^2*(∑ a : ScalarIndex,‖embed (P a (U f))‖^2)+_
  nlinarith only [hsum,hg,hn,hz]

/-- The entire endpoint native column is paid by the original joint positive slots.
Its fixed rho-source and moving columns are never estimated separately. -/
theorem actual_endpoint_native_price (m ell : ℕ) (hml : m ≤ ell)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ a : ScalarIndex,‖embed (U (P a (endpointState m ell F z hz g)))‖^2) ≤
      4/(n^2*(m+2:ℝ)^2)*phiPositivePrice m ell F z hz g := by
  let v : QuantumTest := phiResponseCore m ell F z hz g
  have hp : endpointState m ell F z hz g=A m ell v := rfl
  rw [hp]
  have he := native_endpoint_energy m ell hml v
  have hc := SourceClockSourceTail.original_inverse_coframe_floor (U v)
  have hs := actual_phi_positive_slots m ell F z hz g
  change n^2/4*coframeGram (U v)+n^2/2*scalarForm (U v)+6*n^2*‖embed v‖^2 ≤
    phiPositivePrice m ell F z hz g at hs
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ n^2/4 by positivity)
  have hf : 0 ≤ 6*n^2*‖embed v‖^2 := by positivity
  have hj : n^2/2*scalarForm (U v)+25*n^2/4*‖embed (U v)‖^2 ≤
      phiPositivePrice m ell F z hz g := by nlinarith only [hs,hc',hf]
  have hn : 0<n := by
    change 0<sourceTime 0
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hm : (m+2:ℝ)≠0 := by positivity
  have hb := mul_le_mul_of_nonneg_left hj (show 0 ≤ 4/(n^2*(m+2:ℝ)^2) by positivity)
  have hk : 4/(n^2*(m+2:ℝ)^2)*(n^2/2*scalarForm (U v)+25*n^2/4*‖embed (U v)‖^2)=
      2/(m+2:ℝ)^2*scalarForm (U v)+25/(m+2:ℝ)^2*‖embed (U v)‖^2 := by
    field_simp [hn.ne',hm]
    ring
  rw [hk] at hb
  have hnon : 0 ≤ 25/(2*(m+2:ℝ)^2)*‖embed (U v)‖^2 := by positivity
  have htwo : 25/(m+2:ℝ)^2=2*(25/(2*(m+2:ℝ)^2)) := by
    field_simp [hm]
  rw [htwo] at hb
  nlinarith only [he,hb,hnon]

end LowEnergy.SourceClockPhiEndpointNativePrice
