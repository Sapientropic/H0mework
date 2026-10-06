import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusClockSturm
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiEndpointNativePressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiNativeWeightedHardy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussFockWeights GaussDensityCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponseHessian
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceClockYukawaCubicCurrent SourceClockPhiEndpointNativePressure SourceClockPhiRadiusResponsePositiveSource
open SourceScalarPairedTransport FullYSourceResolventGraphSplice SourceLocalizedInverseFormPayment
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev S : End := phiInverseAction
private abbrev R : End := phiRadiusAction
private abbrev E : End := phiEulerAction
private abbrev U : End := inverseVolumeAction
private abbrev Q : End := 1-S
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B (m ell : ℕ) : End := phiFirstPeak m ell
private abbrev delta : End := S^3-S
private abbrev w (m ell : ℕ) : End := S*T m ell
private abbrev dw (m ell : ℕ) : End := delta*T m ell+S*(B m ell*delta)
private abbrev W (m ell : ℕ) : End := U*w m ell
attribute [local irreducible] resolventCore diagonalAction compressionCore defectAction

private theorem bracket_product (X Y Z : End) : bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_sub (X Y Z : End) : bracket X (Y-Z)=bracket X Y-bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_add (X Y Z : End) : bracket X (Y+Z)=bracket X Y+bracket X Z := by
  unfold bracket;noncomm_ring
private theorem bracket_smul (X Y : End) (c : ℂ) : bracket X (c • Y)=c • bracket X Y := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem inverse_radius : S*R=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : R*S=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem euler_inverse : bracket E S=delta := by
  have hr : bracket E R=R-S := original_phi_euler_radius
  have h1 : S*E*R*S=S*E := by
    calc _=S*E*(R*S) := by noncomm_ring
         _=_ := by rw [radius_inverse,mul_one]
  have h2 : S*R*E*S=E*S := by rw [inverse_radius,one_mul]
  have hi : bracket E S= -(S*bracket E R*S) := by
    unfold bracket
    calc _= -(S*E*R*S-S*R*E*S) := by rw [h1,h2];abel
         _=_ := by noncomm_ring
  rw [hi,hr]
  change -(S*(R-S)*S)=S^3-S
  calc _= -((S*R)*S)+S^3 := by noncomm_ring
       _=_ := by rw [inverse_radius,one_mul];abel
private theorem q_delta : Commute Q delta :=
  (((Commute.one_left S).sub_left (Commute.refl S)).pow_right 3).sub_right
    ((Commute.one_left S).sub_left (Commute.refl S))
private theorem euler_q : bracket E Q= -delta := by
  rw [Q,bracket_sub,euler_inverse]
  simp only [bracket,mul_one,one_mul,sub_self,zero_sub]
private theorem euler_geometric_succ (n : ℕ) :
    bracket E (Q^(n+1))=(-(n+1:ℂ)) • (Q^n*delta) := by
  induction n with
  | zero => simpa only [zero_add,Nat.cast_zero,pow_one,pow_zero,one_mul,one_smul,neg_smul] using euler_q
  | succ n ih =>
    have hm : (Q^n*delta)*Q=Q^(n+1)*delta := by rw [mul_assoc,←q_delta.eq,←mul_assoc,←pow_succ]
    rw [show n+1+1=(n+1)+1 from rfl,pow_succ,bracket_product,ih,euler_q]
    simp only [smul_mul_assoc,mul_neg]
    rw [hm]
    push_cast
    simp only [pow_succ]
    module
private theorem euler_geometric (n : ℕ) : bracket E (Q^n)=(-(n:ℂ)) • (Q^(n-1)*delta) := by
  cases n with
  | zero => simp [bracket]
  | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using euler_geometric_succ n
private theorem euler_theta (m ell : ℕ) : bracket E (T m ell)=B m ell*delta := by
  change bracket E (Q^(m+1)-Q^(ell+1))=B m ell*delta
  rw [bracket_sub,euler_geometric_succ,euler_geometric_succ]
  change _=((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m)*delta
  simp only [sub_mul,smul_mul_assoc]
  module

private theorem euler_window (m ell : ℕ) : bracket E (w m ell)=dw m ell := by
  change bracket E (S*T m ell)=_
  rw [bracket_product,euler_inverse,euler_theta]

private theorem euler_U : Commute E U := by
  exact sub_eq_zero.mp SourceScalarInverseBulk.inverse_phi
private theorem euler_weight (m ell : ℕ) (f : QuantumTest) :
    E (W m ell f)=W m ell (E f)+U (dw m ell f) := by
  have h := LinearMap.congr_fun (euler_window m ell) f
  change E (w m ell f)-w m ell (E f)=dw m ell f at h
  have hu := LinearMap.congr_fun euler_U.eq (w m ell f)
  change E (U (w m ell f))=U (E (w m ell f)) at hu
  change E (U (w m ell f))=U (w m ell (E f))+U (dw m ell f)
  rw [hu,sub_eq_iff_eq_add'.mp h,map_add]

private def theta (s : ℝ) (m ell : ℕ) : ℝ := (1-s)^(m+1)-(1-s)^(ell+1)
private def beta (s : ℝ) (m ell : ℕ) : ℝ := (ell+1:ℝ)*(1-s)^ell-(m+1:ℝ)*(1-s)^m
private theorem source_s_bounds (z : SourceCoordinateSlice) : 0 ≤ phiReciprocal z ∧ phiReciprocal z ≤ 1 := by
  have hp : 0<phiRadius z := by unfold phiRadius SourceClockRadiusResponseAffine.affineRadius;positivity
  have hs : phiRadius z^2=1+‖scalarField z‖^2/4 := Real.sq_sqrt (by positivity)
  have h1 : 1 ≤ phiRadius z := by nlinarith [sq_nonneg ‖scalarField z‖]
  exact ⟨inv_nonneg.mpr hp.le,(inv_le_one₀ hp).mpr h1⟩
private theorem peak_order (s : ℝ) (_hs : 0  ≤  s) (h1 : s  ≤  1) :
    Antitone (fun k : ℕ => (1+(k:ℝ)*s)*(1-s)^k) := by
  apply antitone_nat_of_succ_le
  intro k
  have hp : 0 ≤ (1-s)^k := pow_nonneg (sub_nonneg.mpr h1) _
  have hpos : 0 ≤ (k+1:ℝ)*s^2*(1-s)^k := by positivity
  rw [pow_succ]
  push_cast
  nlinarith only [hpos]
private theorem scalar_window_sign (s : ℝ) (hs : 0  ≤  s) (h1 : s  ≤  1)
    (m ell : ℕ) (hml : m ≤ ell) :
    0 ≤ theta s m ell ∧ s*beta s m ell ≤ theta s m ell := by
  have ht : (1-s)^(ell+1) ≤ (1-s)^(m+1) :=
    pow_le_pow_of_le_one (sub_nonneg.mpr h1) (by linarith) (by omega)
  have hb := peak_order s hs h1 hml
  constructor
  · exact sub_nonneg.mpr ht
  · dsimp only [theta,beta]
    rw [pow_succ,pow_succ]
    push_cast at hb ⊢
    nlinarith only [hb]
private theorem scalar_positive_derivative (s : ℝ) (hs : 0  ≤  s) (h1 : s  ≤  1)
    (m ell : ℕ) (hml : m ≤ ell) :
    0  ≤  s*theta s m ell*((s^3-s)*theta s m ell+s*beta s m ell*(s^3-s)+2*s*theta s m ell) := by
  obtain ⟨ht,hb⟩ := scalar_window_sign s hs h1 m ell hml
  have hsq : s^2 ≤ 1 := by nlinarith [mul_nonneg hs (sub_nonneg.mpr h1)]
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1-s^2 by linarith)
  have hinner : 0 ≤ (1+s^2)*theta s m ell-(1-s^2)*s*beta s m ell := by
    nlinarith only [hm,mul_nonneg (sq_nonneg s) ht]
  have h := mul_nonneg (mul_nonneg (sq_nonneg s) ht) hinner
  have he : s*theta s m ell*((s^3-s)*theta s m ell+s*beta s m ell*(s^3-s)+2*s*theta s m ell)=
      s^2*theta s m ell*((1+s^2)*theta s m ell-(1-s^2)*s*beta s m ell) := by ring
  rw [he]
  exact h

private theorem inverse_point (f : QuantumTest) (z : SourceCoordinateSlice) : S f z=(phiReciprocal z:ℂ) • f z := rfl
private theorem Q_power_point (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (Q^k) f z=((1-phiReciprocal z:ℝ)^k:ℂ) • f z := by
  induction k generalizing f with
  | zero => simp only [pow_zero,Module.End.one_apply,one_smul]
  | succ k ih =>
    rw [pow_succ']
    change (Q^k) f z-S ((Q^k) f) z=_
    rw [inverse_point,ih,smul_smul]
    push_cast
    rw [pow_succ']
    module
private theorem theta_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    T m ell f z=(theta (phiReciprocal z) m ell:ℂ) • f z := by
  change (Q^(m+1)) f z-(Q^(ell+1)) f z=_
  rw [Q_power_point,Q_power_point]
  unfold theta
  push_cast
  rw [sub_smul]
private theorem beta_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    B m ell f z=(beta (phiReciprocal z) m ell:ℂ) • f z := by
  change (ell+1:ℂ) • ((Q^ell) f z)-(m+1:ℂ) • ((Q^m) f z)=_
  rw [Q_power_point,Q_power_point,smul_smul,smul_smul]
  unfold beta
  push_cast
  rw [sub_smul]
private theorem inverse_power_point (k : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (S^k) f z=(phiReciprocal z:ℂ)^k • f z := by
  induction k generalizing f with
  | zero => simp only [pow_zero,Module.End.one_apply,one_smul]
  | succ k ih =>
    rw [pow_succ']
    change S ((S^k) f) z=_
    rw [inverse_point,ih,smul_smul,←pow_succ']
private theorem w_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    w m ell f z=((phiReciprocal z*theta (phiReciprocal z) m ell:ℝ):ℂ) • f z := by
  change S (T m ell f) z=_
  rw [inverse_point,theta_point,smul_smul,Complex.ofReal_mul]
private theorem dw_point (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    dw m ell f z=(((phiReciprocal z^3-phiReciprocal z)*theta (phiReciprocal z) m ell+
      phiReciprocal z*beta (phiReciprocal z) m ell*(phiReciprocal z^3-phiReciprocal z):ℝ):ℂ) • f z := by
  change (S^3) (T m ell f) z-S (T m ell f) z+
    S (B m ell ((S^3-S) f)) z=_
  rw [inverse_power_point,inverse_point,inverse_point,beta_point,theta_point]
  change _+(phiReciprocal z:ℂ) • ((beta (phiReciprocal z) m ell:ℂ) •
    ((S^3) f z-S f z))=_
  rw [inverse_power_point,inverse_point]
  push_cast
  simp only [smul_sub,smul_smul,add_smul]
  module

private theorem weighted_derivative_nonnegative (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    0 ≤ (sourcePair (W m ell f) (U (dw m ell f)+(2:ℂ) • W m ell f)).re := by
  rw [sourcePair_integral]
  have hi : (∫z,densityPair (W m ell f) (U (dw m ell f)+(2:ℂ) • W m ell f) z
      ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫z,(densityPair (W m ell f) (U (dw m ell f)+(2:ℂ) • W m ell f) z).re
        ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re (densityPair_integrable (W m ell f)
      (U (dw m ell f)+(2:ℂ) • W m ell f))).symm
  rw [hi]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair (W m ell f) (U (dw m ell f)+(2:ℂ) • W m ell f) z).re
  by_cases hz:z∈physicalChart
  · have hd : 0 ≤ (densityPair f f z).re := by
      change 0 ≤ RCLike.re (inner ℂ (weight (fun N=>(density N z:ℂ)) (f z)) (f z))
      rw [GaussBoundedMultiplier.weighted_square _ (fun N=>(density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    let s:=phiReciprocal z
    let t:=theta s m ell
    let b:=beta s m ell
    let u:=reciprocalVolume z
    have hpos := scalar_positive_derivative s (source_s_bounds z).1 (source_s_bounds z).2 m ell hml
    have hl : W m ell f z=((u*s*t:ℝ):ℂ) • f z := by
      change (u:ℂ) • w m ell f z=_
      rw [w_point,smul_smul]
      change ((u:ℂ)*((s*t:ℝ):ℂ)) • f z=((u*s*t:ℝ):ℂ) • f z
      push_cast
      rw [mul_assoc]
    have hr : (U (dw m ell f)+(2:ℂ) • W m ell f) z=
        ((u*((s^3-s)*t+s*b*(s^3-s)+2*s*t):ℝ):ℂ) • f z := by
      change (u:ℂ) • dw m ell f z+(2:ℂ) • W m ell f z=_
      rw [dw_point,hl,smul_smul,smul_smul]
      push_cast
      simp only [add_smul,mul_smul]
      module
    have he : densityPair (W m ell f) (U (dw m ell f)+(2:ℂ) • W m ell f) z=
        ((u^2*(s*t*((s^3-s)*t+s*b*(s^3-s)+2*s*t)):ℝ):ℂ)*densityPair f f z := by
      unfold densityPair
      rw [hl,hr,map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
      push_cast
      ring
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg u) hpos) hd
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    have hw : W m ell f z=0 := by change (reciprocalVolume z:ℂ) • w m ell f z=0;rw [w_point,hf,smul_zero,smul_zero]
    simp only [densityPair,hw,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem inner_re_self (f : QuantumTest) :
    (inner ℂ (embed f) (embed f)).re=‖embed f‖^2 := by
  simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜:=ℂ) (embed f))
private theorem euler_real_pair (f : QuantumTest) :
    (sourcePair f (E f)).re=-(61/2:ℝ)*‖embed f‖^2 := by
  have h := SourceClockPhiRadiusClockSturm.phi_profile_paired_derivative (1:End) f f
  have he : bracket E (1:End)=0 := by simp [bracket]
  rw [he] at h
  simp only [Module.End.one_apply,zero_add,LinearMap.smul_apply,sourcePair,map_smul,
    inner_smul_right] at h
  change inner ℂ (embed f) (embed (E f))= -inner ℂ (embed (E f)) (embed f)-
    (61:ℂ)*inner ℂ (embed f) (embed f) at h
  have hr := congrArg Complex.re h
  have hr2 := congrArg Complex.re (GaussNativeForm.pair_conjugate f (E f))
  simp only [Complex.neg_re,Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,sub_zero,inner_re_self] at hr
  simp only [sourcePair,Complex.conj_re] at hr2
  change (inner ℂ (embed f) (embed (E f))).re=_
  linarith only [hr,hr2]

/-- The actual affine61 transpose pays the entire weighted U mass from the same first radial jet. -/
theorem original_phi_weighted_hardy (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    (57/2:ℝ)*‖embed (U (S (phiThetaAction m ell f)))‖  ≤
      ‖embed (U (S (phiThetaAction m ell (E f))))‖ := by
  have hp:=weighted_derivative_nonnegative m ell hml f
  have he:=euler_real_pair (W m ell f)
  rw [euler_weight] at he
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,
    Complex.add_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,
    inner_re_self] at hp he
  have hb := (Complex.abs_re_le_norm (inner ℂ (embed (W m ell f)) (embed (W m ell (E f))))).trans
    (norm_inner_le_norm _ _)
  have hh := neg_le_abs ((inner ℂ (embed (W m ell f)) (embed (W m ell (E f)))).re)
  change (57/2:ℝ)*‖embed (W m ell f)‖ ≤ ‖embed (W m ell (E f))‖
  by_cases hz : ‖embed (W m ell f)‖=0
  · simp only [hz,mul_zero,norm_nonneg]
  · have hpos : 0<‖embed (W m ell f)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith only [hp,he,hb,hh,hpos]

private abbrev Phi : End := SourceScalarAffineScaleTransport.generator
private abbrev n : ℝ := sourceTime 0
private theorem lapse_pos : 0<n := by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem weighted_Phi (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    ‖embed (W m ell (Phi f))‖ ≤ (118/57:ℝ)*‖embed (W m ell (E f))‖ := by
  have he : W m ell (Phi f)=W m ell (E f)+(61/2:ℂ) • W m ell f := by
    simp only [Phi,SourceScalarAffineScaleTransport.generator,LinearMap.add_apply,
      LinearMap.smul_apply,Module.End.one_apply,map_add,map_smul]
  have hh:=original_phi_weighted_hardy m ell hml f
  change (57/2:ℝ)*‖embed (W m ell f)‖ ≤ ‖embed (W m ell (E f))‖ at hh
  rw [he,map_add]
  have hb:‖embed (W m ell (E f))+embed ((61/2:ℂ) • W m ell f)‖ ≤
      ‖embed (W m ell (E f))‖+(61/2:ℝ)*‖embed (W m ell f)‖ := by
    simpa only [map_smul,norm_smul,norm_div,Complex.norm_ofNat,show (61:ℝ)/2=61/2 from rfl] using
      norm_add_le (embed (W m ell (E f))) (embed ((61/2:ℂ) • W m ell f))
  linarith only [hb,hh]
private theorem weight_U (m ell : ℕ) : Commute (w m ell) U := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change w m ell (U f) z=(reciprocalVolume z:ℂ) • w m ell f z
  rw [w_point,w_point]
  change (↑(phiReciprocal z*theta (phiReciprocal z) m ell):ℂ) • ((reciprocalVolume z:ℂ) • f z)=_
  exact smul_comm _ _ _
private theorem theta_R (m ell : ℕ) : Commute (T m ell) R := by
  have h : Commute S R := inverse_radius.trans radius_inverse.symm
  exact (((Commute.one_left R).sub_left h).pow_left (m+1)).sub_left
    (((Commute.one_left R).sub_left h).pow_left (ell+1))
private theorem weight_square (m ell : ℕ) : w m ell*R^2=T m ell*R := by
  change S*T m ell*R^2=T m ell*R
  calc _=S*(T m ell*R)*R := by simp only [pow_two,mul_assoc]
       _=S*(R*T m ell)*R := by rw [(theta_R m ell).eq]
       _=_ := by rw [←mul_assoc,inverse_radius,one_mul]
private theorem radius_window (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    w m ell (SourceClockPhiRadiusAcceleration.phiSquare (resolventCore F z hz (coreEquiv.symm g)))=
      phiResponseCore m ell F z hz g+T m ell (resolventCore F z hz (R (coreEquiv.symm g))) := by
  have hw:=LinearMap.congr_fun (weight_square m ell) (resolventCore F z hz (coreEquiv.symm g))
  change w m ell ((R^2) (resolventCore F z hz (coreEquiv.symm g)))=
    T m ell (R (resolventCore F z hz (coreEquiv.symm g))) at hw
  change w m ell ((R^2) (resolventCore F z hz (coreEquiv.symm g)))=_
  rw [hw]
  simp only [phiResponseCore,bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  change T m ell (R (resolventCore F z hz (coreEquiv.symm g)))=
    T m ell (R (resolventCore F z hz (coreEquiv.symm g)))-
    T m ell (resolventCore F z hz (R (coreEquiv.symm g)))+
    T m ell (resolventCore F z hz (R (coreEquiv.symm g)))
  abel
private theorem actual_K_point (m ell : ℕ) (hml:m ≤ ell) (F : Index) (z : ℂ)
    (hz:z.im≠0) (g:diagonal.domain) :
    ‖embed (w m ell (pressureTester z (resolventCore F z hz (coreEquiv.symm g))))‖ ≤
      (59*n/57)*‖embed (W m ell (E (resolventCore F z hz (coreEquiv.symm g))))‖+
      2*|z.im| *(‖embed (phiResponseCore m ell F z hz g)‖+
        ‖embed (T m ell (resolventCore F z hz (R (coreEquiv.symm g))))‖) := by
  let q:=resolventCore F z hz (coreEquiv.symm g)
  let v:=phiResponseCore m ell F z hz g
  let h:=T m ell (resolventCore F z hz (R (coreEquiv.symm g)))
  have he:w m ell (pressureTester z q)=(n/2:ℂ) • W m ell (Phi q)-
      (2*Complex.I*(z.im:ℂ)) • (v+h) := by
    have hw:=LinearMap.congr_fun (weight_U m ell).eq (Phi q)
    change w m ell (U (Phi q))=U (w m ell (Phi q)) at hw
    simp only [pressureTester,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      map_sub,map_smul,hw]
    change (n/2:ℂ) • W m ell (Phi q)-(2*Complex.I*(z.im:ℂ)) •
      w m ell (SourceClockPhiRadiusAcceleration.phiSquare q)=_
    rw [show w m ell (SourceClockPhiRadiusAcceleration.phiSquare q)=v+h from
      radius_window m ell F z hz g]
    rfl
  have hn:‖(n/2:ℂ)‖=n/2 := by
    rw [show (n/2:ℂ)=((n/2:ℝ):ℂ) by push_cast;rfl,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by have:=lapse_pos;positivity)]
  have hi:‖(2*Complex.I*(z.im:ℂ))‖=2*|z.im| := by
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have ht := weighted_Phi m ell hml q
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ n/2 by have:=lapse_pos;positivity)
  have hv := mul_le_mul_of_nonneg_left (norm_add_le (embed v) (embed h)) (show 0 ≤ 2*|z.im| by positivity)
  rw [he,map_sub]
  simp only [map_smul,map_add]
  have hb:=norm_sub_le (embed ((n/2:ℂ) • W m ell (Phi q)))
    (embed ((2*Complex.I*(z.im:ℂ)) • (v+h)))
  simp only [map_smul,map_add,norm_smul,hn,hi] at hb
  change _ ≤ (59*n/57)*‖embed (W m ell (E q))‖+2*|z.im| *(‖embed v‖+‖embed h‖)
  linarith only [hb,ht',hv]
private theorem square_three (x a b r s t:ℝ) (hx:0 ≤ x) (_ha:0 ≤ a) (_hb:0 ≤ b)
    (_hr:0 ≤ r) (_hs:0  ≤  s) (_ht:0 ≤ t) (h:x ≤ a*r+b*(s+t)) :
    x^2 ≤ 2*a^2*r^2+4*b^2*s^2+4*b^2*t^2 := by
  have hh: x^2 ≤ (a*r+b*(s+t))^2 := pow_le_pow_left₀ hx h 2
  nlinarith only [hh,sq_nonneg (a*r-b*(s+t)),mul_nonneg (sq_nonneg b) (sq_nonneg (s-t))]

/-- The actual K_z readout retains its native first-jet and response price; its only remaining error is the paid fixed rho-seed window. -/
def weightedPressureError (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g:diagonal.domain) : ℝ :=
  ‖embed (w m ell (pressureTester z (resolventCore F z hz (coreEquiv.symm g))))‖^2-
    2*(59*n/57)^2*‖embed (W m ell (E (resolventCore F z hz (coreEquiv.symm g))))‖^2-
    16*z.im^2*‖embed (phiResponseCore m ell F z hz g)‖^2
private theorem error_point (m ell : ℕ) (hml:m ≤ ell) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    weightedPressureError m ell F z hz g ≤ 16*z.im^2*
      ‖embed (T m ell (resolventCore F z hz (R (coreEquiv.symm g))))‖^2 := by
  have h:=square_three _ (59*n/57) (2*|z.im|) _ _ _ (norm_nonneg _) (by have:=lapse_pos;positivity)
    (by positivity) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (actual_K_point m ell hml F z hz g)
  unfold weightedPressureError
  nlinarith only [h,sq_abs z.im]
private theorem frequency_nonreal (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (t:ℝ) :
    (actualFrequency advanced μ t).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'
private theorem radius_state (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    resolventCore F z hz (R (coreEquiv.symm g))=
      SourceScalarPositiveBulkWard.state F z hz (phiRadiusSource g) := by
  have h:R (coreEquiv.symm g)=coreEquiv.symm (phiRadiusSource g) := by
    unfold phiRadiusSource
    rw [coreEquiv.symm_apply_apply]
  rw [h]
  simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]

/-- The original pressure tester has a source-generated common error tail after the actual radial first-jet and response slots are retained. -/
theorem actual_weighted_pressure_common_payment (μ:ℝ) (hμ:0 < μ) (g:diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻t:ℝ,ENNReal.ofReal (weightedPressureError m ell F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hC:0<16*μ^2 := by positivity
  obtain ⟨N,hN⟩:=SourceClockPhiRadiusResponseNativeBudget.actual_phi_theta_common_tail μ hμ
    (phiRadiusSource g) (ε/(16*μ^2)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have hp (t:ℝ):ENNReal.ofReal (weightedPressureError m ell F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ hμ t) g) ≤ ENNReal.ofReal (16*μ^2)*
      ENNReal.ofReal (‖embed (T m ell (SourceScalarPositiveBulkWard.state F (actualFrequency advanced μ t)
        (frequency_nonreal advanced μ hμ t) (phiRadiusSource g)))‖^2) := by
    rw [←ENNReal.ofReal_mul hC.le]
    apply ENNReal.ofReal_le_ofReal
    have hf:(actualFrequency advanced μ t).im^2=μ^2 := by
      cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
        Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_sq]
    simpa only [hf,radius_state] using error_point m ell hml F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ hμ t) g
  let e : ℝ → ENNReal := fun t=>ENNReal.ofReal (‖embed (T m ell
    (SourceScalarPositiveBulkWard.state F (actualFrequency advanced μ t)
      (frequency_nonreal advanced μ hμ t) (phiRadiusSource g)))‖^2)
  have hf : (∫⁻t:ℝ,e t) ≤ ENNReal.ofReal (ε/(16*μ^2)) := hF advanced
  calc
    _ ≤ (∫⁻t:ℝ,ENNReal.ofReal (16*μ^2)*e t) := lintegral_mono hp
    _ = ENNReal.ofReal (16*μ^2)*(∫⁻t:ℝ,e t) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (16*μ^2)*ENNReal.ofReal (ε/(16*μ^2)) := mul_le_mul_of_nonneg_left hf (by exact bot_le)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC.le]
      congr 1
      field_simp [hC.ne']

end LowEnergy.SourceClockPhiNativeWeightedHardy
