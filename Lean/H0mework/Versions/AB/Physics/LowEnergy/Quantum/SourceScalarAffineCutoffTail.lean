import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarAffineScaleTransport
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceRetardedForcingTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarAffineCutoffTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussRadialDomain GaussYukawaCoefficient GaussUnitaryHistory SourceNativeCutoffContact
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarAffineScaleTransport SourceMixedNativeReturn SourceRelativePowerTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open GaussNativeForm GaussNativeMatter
open GaussFockWeights
open scoped InnerProductSpace ContDiff Topology
abbrev End := SourceScalarGaugeScale.End

private theorem half_geometric (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    (m+1 : ℝ)*(1-q)*q^m  ≤  3*(q^(m/2+1)-q^(m+1)) := by
  let h := m/2+1
  let n := m-m/2
  have ht (h n : ℕ) : (∑ j ∈ Finset.range n,(q^(h+j)-q^(h+j+1)))=q^h-q^(h+n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      have he : h+(n+1)=h+n+1 := by omega
      rw [he]
      ring
  have hs : (n : ℝ)*((1-q)*q^m)  ≤  q^h-q^(h+n) := by
    calc
      _ = ∑ j ∈ Finset.range n,(1-q)*q^m := by simp
      _  ≤  ∑ j ∈ Finset.range n,(q^(h+j)-q^(h+j+1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have he : h+j ≤ m := by dsimp [h,n] at *;have := Finset.mem_range.mp hj;omega
        have hp := pow_le_pow_of_le_one hq hq1 he
        have hc := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hq1)
        simpa only [pow_succ] using! (show (1-q)*q^m ≤ q^(h+j)-q^(h+j)*q from by nlinarith [hc])
      _ = _ := ht h n
  have hn : (m+1 : ℝ)  ≤  3*(n : ℝ) := by
    exact_mod_cast (show m+1 ≤ 3*n from by dsimp [n];omega)
  have hp : 0 ≤ (1-q)*q^m := mul_nonneg (sub_nonneg.mpr hq1) (pow_nonneg hq m)
  have hc := mul_le_mul_of_nonneg_right hn hp
  have he : h+n=m+1 := by dsimp [h,n];omega
  rw [he] at hs
  dsimp [h] at hs
  nlinarith

def eulerCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((m+1 : ℝ)*(1-reciprocal z)^m-(ell+1 : ℝ)*(1-reciprocal z)^ell)*
    reciprocal z*(1-(reciprocal z)^2)

private theorem euler_smooth (m ell : ℕ) : ContDiff ℝ ∞ (eulerCoefficient m ell) :=
  ((((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow m)).sub
      (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow ell))).mul reciprocal_smooth).mul
    (contDiff_const.sub (reciprocal_smooth.pow 2)))

def eulerAction (m ell : ℕ) : End := multiply (eulerCoefficient m ell)
  (fun _ => (euler_smooth m ell).contDiffAt)

private theorem euler_domination (m ell : ℕ) (hm : 1 ≤ m) (hell : m ≤ ell) (z : SourceCoordinateSlice) :
    (eulerCoefficient m ell z)^2  ≤  18*((theta (m/2) m z)^2+(theta (ell/2) ell z)^2) := by
  let s := reciprocal z
  let q := 1-s
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ q := sub_nonneg.mpr hs1
  have hq1 : q ≤ 1 := by dsimp [q];linarith
  have hfactor : 0 ≤ 1-s^2 := by nlinarith
  have hfactor1 : 1-s^2 ≤ 1 := by nlinarith
  have hA := half_geometric q hq hq1 m hm
  have hB := half_geometric q hq hq1 ell (hm.trans hell)
  have hpa : 0 ≤ (m+1 : ℝ)*s*q^m := by positivity
  have hpb : 0 ≤ (ell+1 : ℝ)*s*q^ell := by positivity
  have hab := abs_sub ((m+1 : ℝ)*s*q^m) ((ell+1 : ℝ)*s*q^ell)
  rw [abs_of_nonneg hpa,abs_of_nonneg hpb] at hab
  have he : eulerCoefficient m ell z=
      (((m+1 : ℝ)*s*q^m)-((ell+1 : ℝ)*s*q^ell))*(1-s^2) := by
    dsimp [eulerCoefficient,s,q]
    ring
  have hb : |eulerCoefficient m ell z|  ≤
      3*((theta (m/2) m z)+(theta (ell/2) ell z)) := by
    rw [he,abs_mul,abs_of_nonneg hfactor]
    calc
      _  ≤  ((m+1 : ℝ)*s*q^m+(ell+1 : ℝ)*s*q^ell)*(1-s^2) :=
        mul_le_mul_of_nonneg_right hab hfactor
      _  ≤  ((m+1 : ℝ)*s*q^m+(ell+1 : ℝ)*s*q^ell) :=
        mul_le_of_le_one_right (add_nonneg hpa hpb) hfactor1
      _  ≤  _ := by
        dsimp [theta,q] at *
        nlinarith
  have hn := sq_nonneg (theta (m/2) m z-theta (ell/2) ell z)
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hp
  nlinarith

private theorem theta_euler_derivative (m ell : ℕ) (z : SourceCoordinateSlice) :
    fderiv ℝ (theta m ell) z (SourceScalarRadialContact.scalarEuler z)=eulerCoefficient m ell z := by
  have hd := (hasFDerivAt_const (1 : ℝ) z).sub
    ((reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have h := (hd.pow (m+1)).sub (hd.pow (ell+1))
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ =>
    D (SourceScalarRadialContact.scalarEuler z)) h.fderiv
  change fderiv ℝ (theta m ell) z (SourceScalarRadialContact.scalarEuler z)=_ at he
  rw [he]
  simp only [sub_apply,smul_apply,smul_eq_mul,zero_sub,neg_apply,nsmul_eq_mul,
    Pi.sub_apply,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  rw [GaussRadialMomentum.reciprocal_derivative]
  simp only [SourceScalarRadialContact.scalarEuler,neg_div,neg_neg,real_inner_self_eq_norm_sq]
  have hr : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 :=
    Real.sq_sqrt (by positivity)
  have hn : ‖(z.2.1 : Scalar)‖^2=4*(radius z^2-1) := by nlinarith
  rw [hn]
  unfold eulerCoefficient reciprocal
  simp only [←one_div]
  field_simp [(radius_pos z).ne']

private theorem field_multiplier (E : End) (v : SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (v z))
    (a : SourceCoordinateSlice → ℝ) (ha : ContDiff ℝ ∞ a)
    (f : QuantumTest) (z : SourceCoordinateSlice) :
    (E* multiply a (fun _ => ha.contDiffAt)-multiply a (fun _ => ha.contDiffAt)*E) f z=
      (fderiv ℝ a z (v z) : ℂ) • f z := by
  have hf : (multiply a (fun _ => ha.contDiffAt) f : SourceCoordinateSlice → FockFiber)=
      fun x => a x • f x := by
    funext x
    apply PiLp.ext
    intro word
    exact Complex.real_smul.symm
  change E (multiply a (fun _ => ha.contDiffAt) f) z-(a z : ℂ) • E f z=_
  rw [hE,hE,hf,fderiv_fun_smul (ha.differentiable (by simp)).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt]
  change a z • fderiv ℝ f z (v z)+fderiv ℝ a z (v z) • f z-
    (a z : ℂ) • fderiv ℝ f z (v z)=(fderiv ℝ a z (v z) : ℂ) • f z
  apply PiLp.ext
  intro word
  simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,Complex.real_smul]
  ring

def affineCutoff (m ell : ℕ) : End :=
  SourceScalarVirialBulk.deltaPhi (SourceNativeCutoffContact.thetaAction m ell)

/-- The real affine-source cutoff derivative is the radial Euler cutoff plus the literal vacuum contact. -/
theorem actual_affine_cutoff_return (m ell : ℕ) :
    affineCutoff m ell=eulerAction m ell+
      Complex.I • SourceNativeCutoffContact.contactAction ((vacuum : Scalar),0) m ell := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have he := field_multiplier phiEulerAction phiEuler SourceScalarVirialBulk.phi_euler_apply
    (theta m ell) (theta_smooth m ell) f z
  change (phiEulerAction*SourceNativeCutoffContact.thetaAction m ell-
    SourceNativeCutoffContact.thetaAction m ell*phiEulerAction) f z=_
  have ht : (phiEulerAction*SourceNativeCutoffContact.thetaAction m ell-
      SourceNativeCutoffContact.thetaAction m ell*phiEulerAction) f z=
      (fderiv ℝ (theta m ell) z (phiEuler z) : ℂ) • f z := he
  refine ht.trans ?_
  by_cases hz : z∈physicalChart
  · have hs : phiEuler z=SourceScalarRadialContact.scalarEuler z+
        SourceScalarFlatJoint.scalarAxis SourceScalarVirialBulk.vacuumSlice := by
      apply Prod.ext
      · change (0 : Coframe)=0+0
        exact (zero_add _).symm
      · apply Prod.ext
        · exact add_comm _ _
        · change (0 : coordinateSlice)=0+0
          exact (zero_add _).symm
    have hd : GaussCoreDifferential.direction ((vacuum : Scalar),0) z=
        SourceScalarFlatJoint.scalarAxis SourceScalarVirialBulk.vacuumSlice := by
      have hi : GaussLiveMomentum.inverseL z ((vacuum : Scalar),0)=
          (0,(SourceScalarVirialBulk.vacuumSlice,0)) :=
        SourceScalarFlatJoint.native_scalar_slice_inverse ⟨z,hz⟩ SourceScalarVirialBulk.vacuumSlice
      rw [GaussCoreDifferential.direction,hi]
      rfl
    rw [hs,map_add,theta_euler_derivative,←hd,direction_theta _ _ _ ⟨z,hz⟩]
    apply PiLp.ext
    intro word
    change ((eulerCoefficient m ell z+thetaDerivative (vacuum,0) m ell z : ℝ) : ℂ)*f z word=
      (eulerCoefficient m ell z : ℂ)*f z word+
        Complex.I*((-Complex.I)*(thetaDerivative (vacuum,0) m ell z : ℂ)*f z word)
    push_cast
    linear_combination (thetaDerivative (vacuum,0) m ell z : ℂ)*f z word*Complex.I_mul_I
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    change _ • f z=(eulerCoefficient m ell z : ℂ) • f z+
      Complex.I • (((-Complex.I)*(thetaDerivative ((vacuum : Scalar),0) m ell z : ℂ)) • f z)
    rw [hf,smul_zero,smul_zero,smul_zero,smul_zero,add_zero]

private theorem real_inner_scaled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (r : ℝ) (x : E) :
    (inner ℂ (A ((r : ℂ) • x)) ((r : ℂ) • x)).re=r^2*(inner ℂ (A x) x).re := by
  rw [map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply,Complex.star_def,Complex.conj_ofReal]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

private theorem scalar_density (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart,ContDiffAt ℝ ∞ a z.val) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair (multiply a ha f) (multiply a ha f) z).re=
      (a z)^2*(densityPair f f z).re := by
  change (inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z) ((a z : ℂ) • f z))
    ((a z : ℂ) • f z)).re=_
  exact real_inner_scaled _ _ _

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) :
    0 ≤ (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · change 0 ≤ RCLike.re (inner ℂ (weight (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square _ (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

/-- The real scalar-Euler cutoff is dominated by two original half-index relative tails on the entire source core. -/
theorem actual_euler_norm_domination (m ell : ℕ) (hm : 1 ≤ m) (hell : m ≤ ell) (f : QuantumTest) :
    ‖embed (eulerAction m ell f)‖^2  ≤
      18*(‖relativeTail (m/2) m (embed f)‖^2+‖relativeTail (ell/2) ell (embed f)‖^2) := by
  have hi := (densityPair_integrable (SourceNativeCutoffContact.thetaAction (m/2) m f) (SourceNativeCutoffContact.thetaAction (m/2) m f)).re
  have hj := (densityPair_integrable (SourceNativeCutoffContact.thetaAction (ell/2) ell f) (SourceNativeCutoffContact.thetaAction (ell/2) ell f)).re
  have ha := (densityPair_integrable (eulerAction m ell f) (eulerAction m ell f)).re
  have ht (a b : ℕ) : embed (SourceNativeCutoffContact.thetaAction a b f)=relativeTail a b (embed f) := SourceNativeCutoffContact.theta_core a b f
  rw [←ht,←ht]
  rw [GaussBoundedMultiplier.norm_square_integral,GaussBoundedMultiplier.norm_square_integral,
    GaussBoundedMultiplier.norm_square_integral,←integral_add hi hj,←integral_const_mul]
  apply integral_mono ha ((hi.add hj).const_mul 18)
  intro z
  have h := mul_le_mul_of_nonneg_right (euler_domination m ell hm hell z) (density_nonnegative f z)
  change (densityPair (eulerAction m ell f) (eulerAction m ell f) z).re ≤
    18*((densityPair (SourceNativeCutoffContact.thetaAction (m/2) m f)
      (SourceNativeCutoffContact.thetaAction (m/2) m f) z).re+
      (densityPair (SourceNativeCutoffContact.thetaAction (ell/2) ell f)
        (SourceNativeCutoffContact.thetaAction (ell/2) ell f) z).re)
  simp only [eulerAction,SourceNativeCutoffContact.thetaAction,scalar_density]
  nlinarith

private theorem point_energy (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ≤ 18*(b+c)) :
    ENNReal.ofReal a ≤ ENNReal.ofReal 18*(ENNReal.ofReal b+ENNReal.ofReal c) := by
  rw [←ENNReal.ofReal_add hb hc,←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
  exact ENNReal.ofReal_le_ofReal h

/-- The actual varying finite-resolvent scalar-Euler cutoff has the original common full-frequency tail. -/
theorem actual_euler_retarded_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N  ≤  m → ∀ ell, m  ≤  ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (eulerAction m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2))  ≤  ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail μ hμ g (ε/36) (by positivity)
  refine ⟨2*N+2,fun m hm ell hell => ?_⟩
  have hm0 : 1 ≤ m := by omega
  have hmN : N ≤ m/2 := by omega
  have heN : N ≤ ell/2 := by omega
  filter_upwards [hN (m/2) hmN m (Nat.div_le_self m 2),
    hN (ell/2) heN ell (Nat.div_le_self ell 2)] with F hA hB
  have hb (w : ℝ) : ‖sourceRead F g (eulerAction m ell) (finiteResolvent F (line μ w) (g : H))‖^2 ≤
      18*(‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2+
          ‖relativeTail (ell/2) ell (finiteResolvent F (line μ w) (g : H))‖^2) := by
    have hz : (line μ w).im ≠ 0 := by simpa only [line_im] using hμ.ne'
    rw [source_read_resolvent F g (eulerAction m ell) (line μ w) hz]
    have h := actual_euler_norm_domination m ell hm0 hell (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))
    have hv : embed (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))=
        finiteResolvent F (line μ w) (g : H) :=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    simpa only [hv] using! h
  have hmA : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2)) :=
    ((((relativeTail (m/2) m).continuous.comp
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _  ≤  ∫⁻ w : ℝ, ENNReal.ofReal 18*(ENNReal.ofReal (‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2)+
        ENNReal.ofReal (‖relativeTail (ell/2) ell (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact point_energy _ _ _ (sq_nonneg _) (sq_nonneg _) (hb w)
    _ = ENNReal.ofReal 18*((∫⁻ w : ℝ, ENNReal.ofReal (‖relativeTail (m/2) m (finiteResolvent F (line μ w) (g : H))‖^2))+
        ∫⁻ w : ℝ, ENNReal.ofReal (‖relativeTail (ell/2) ell (finiteResolvent F (line μ w) (g : H))‖^2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hmA]
    _  ≤  ENNReal.ofReal 18*(ENNReal.ofReal (ε/36)+ENNReal.ofReal (ε/36)) := mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
      congr 1
      ring

private theorem vacuum_contact_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, ∀ hell : m ≤ ell, ∀ F : Index,
      (∫⁻ w : ℝ, ENNReal.ofReal (‖boundedContact ((vacuum : Scalar),0) m ell hell
        (finiteResolvent F (line μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := (2*‖vacuum‖)^2*(Real.pi/μ)*‖g‖^2
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hell F => (actual_contact_energy ((vacuum : Scalar),0) m ell hell F μ hμ g).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hmR : (N : ℝ) ≤ m := Nat.cast_le.mpr hm
  have hd : 0<(m+2 : ℝ) := by positivity
  have hdiv : C/ε<(m+2 : ℝ) := by linarith
  have hc : C<ε*(m+2 : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hdiv
    nlinarith
  have hs : (m+2 : ℝ) ≤ (m+2 : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hb : C/(m+2 : ℝ)^2 ≤ ε := (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    (hc.le.trans (mul_le_mul_of_nonneg_left hs hε.le))
  convert hb using 1
  dsimp [C]
  field_simp

private theorem two_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : ℝ → E) (hm : Measurable (fun w => ENNReal.ofReal (‖A w‖^2))) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖A w+B w‖^2)) ≤
      ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖A w‖^2))+
        ∫⁻ w : ℝ, ENNReal.ofReal (‖B w‖^2)) := by
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖A w‖^2)+ENNReal.ofReal (‖B w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
      apply ENNReal.ofReal_le_ofReal
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A w) (B w)) 2
      nlinarith [sq_nonneg (‖A w‖-‖B w‖)]
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hm]

/-- The true affine cutoff derivative pays both radial and vacuum terms on the actual varying source resolvent. -/
theorem actual_affine_retarded_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (affineCutoff m ell)
          (finiteResolvent F (line μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := actual_euler_retarded_tail μ hμ g (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := vacuum_contact_tail μ hμ (g : H) (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell] with F hE
  have hV := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell F
  have he (w : ℝ) : sourceRead F g (affineCutoff m ell) (finiteResolvent F (line μ w) (g : H))=
      sourceRead F g (eulerAction m ell) (finiteResolvent F (line μ w) (g : H))+
        Complex.I • boundedContact ((vacuum : Scalar),0) m ell hell
          (finiteResolvent F (line μ w) (g : H)) := by
    have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
    have h := congrArg (fun A : End => sourceRead F g A (finiteResolvent F (line μ w) (g : H)))
      (actual_affine_cutoff_return m ell)
    simp only [map_add,map_smul] at h
    have hc := source_read_resolvent F g (contactAction ((vacuum : Scalar),0) m ell) (line μ w) hz
    have hb := bounded_contact_core ((vacuum : Scalar),0) m ell hell
      (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))
    have hv : embed (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (line μ w) hz g))=
        finiteResolvent F (line μ w) (g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    rw [hv] at hb
    exact h.trans (congrArg (fun v : H =>
      sourceRead F g (eulerAction m ell) (finiteResolvent F (line μ w) (g : H))+Complex.I • v) (hc.trans hb.symm))
  have hmE : Measurable (fun w : ℝ => ENNReal.ofReal (‖sourceRead F g (eulerAction m ell)
      (finiteResolvent F (line μ w) (g : H))‖^2)) :=
    ((((sourceRead F g (eulerAction m ell)).continuous.comp
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  simp_rw [he]
  have hs := two_energy
    (fun w => sourceRead F g (eulerAction m ell) (finiteResolvent F (line μ w) (g : H)))
    (fun w => Complex.I • boundedContact ((vacuum : Scalar),0) m ell hell
      (finiteResolvent F (line μ w) (g : H))) hmE
  simp only [norm_smul,Complex.norm_I,one_mul] at hs
  apply hs.trans
  calc
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hV) (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
      congr 1
      ring

end LowEnergy.SourceScalarAffineCutoffTail
