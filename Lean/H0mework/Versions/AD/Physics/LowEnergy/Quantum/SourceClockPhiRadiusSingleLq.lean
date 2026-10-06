import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusClockSturm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusSingleLq
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open GaussNativePotential SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceCoframeVolume
open SourcePhysicalKineticSquare SourceScalarVirialBulk SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiRadiusClockSturm SourceClockYukawaCubicCurrent
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] SourceClockYukawaCubicCurrent.resolventCore
  GaussDiagonalHistory.diagonalAction SourceScalarPositiveBulkWard.state
private abbrev U : End := inverseVolumeAction
private abbrev E : End := SourceScalarVirialBulk.phiEulerAction
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev Q : End := 1-S
private abbrev profileS : End := S
private abbrev profileQ : End := Q
private abbrev profileTheta (m ell : ℕ) : End := phiThetaAction m ell
private abbrev profileFirst (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell
private abbrev profileSecond (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.phiSecondPeak m ell
private abbrev Htheta (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.thetaHessian m ell
private abbrev Hband (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.bandHessian m ell

private theorem inverse_pair (f g : QuantumTest) :
    sourcePair f (U g)=sourcePair (U f) g := multiply_pair _ _ f g

private theorem euler_inverse : Commute E U := by
  have h := SourceScalarInverseBulk.inverse_phi
  change E*U-U*E=0 at h
  exact sub_eq_zero.mp h

private theorem radius_inverse : r*S=(1:End) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

private theorem phi_inverse_radius_commute : Commute S r := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (phiReciprocal z:ℂ) (phiRadius z:ℂ) (f z)

private theorem inverse_radius : S*r=(1:End) :=
  phi_inverse_radius_commute.eq.trans radius_inverse

private theorem clock_mean_theta (m ell : ℕ) : Commute clockMean (phiThetaAction m ell) :=
  (((Commute.one_right clockMean).sub_right clock_mean_inverse).pow_right (m+1)).sub_right
    (((Commute.one_right clockMean).sub_right clock_mean_inverse).pow_right (ell+1))

private theorem phi_profile_bracket_product (A B C : End) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket
  noncomm_ring

private theorem phi_profile_theta_S (m ell : ℕ) : Commute (profileTheta m ell) profileS :=
  (((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (m+1)).sub_left
    (((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (ell+1))

private theorem phi_profile_first_S (m ell : ℕ) : Commute (profileFirst m ell) profileS :=
  ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left m).smul_left _)

private theorem phi_profile_second_S (m ell : ℕ) : Commute (profileSecond m ell) profileS :=
  ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (m-1)).smul_left _).sub_left
    ((((Commute.one_left profileS).sub_left (Commute.refl profileS)).pow_left (ell-1)).smul_left _)

private theorem phi_profile_theta_first (m ell : ℕ) :
    Commute (profileTheta m ell) (profileFirst m ell) := by
  have hQ : Commute (profileTheta m ell) profileQ :=
    (Commute.one_right _).sub_right (phi_profile_theta_S m ell)
  exact ((hQ.pow_right ell).smul_right _).sub_right ((hQ.pow_right m).smul_right _)

private theorem phi_first_radius (m ell : ℕ) : Commute (profileFirst m ell) r :=
  (((((Commute.one_left r).sub_left phi_inverse_radius_commute).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left r).sub_left phi_inverse_radius_commute).pow_left m).smul_left _))

private theorem phi_pair_one : GaussCoframeForm.Paired (1:End) 1 := by intro p q;rfl

private theorem phi_pair_add {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A+B) (A+B) := by
  intro p q
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_left,inner_add_right]
  exact congrArg₂ (·+·) (hA p q) (hB p q)

private theorem phi_pair_sub {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A-B) (A-B) := by
  intro p q
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right]
  exact congrArg₂ (·-·) (hA p q) (hB p q)

private theorem phi_pair_real {A : End} (c : ℝ) (hA : GaussCoframeForm.Paired A A) :
    GaussCoframeForm.Paired ((c:ℂ) • A) ((c:ℂ) • A) := by
  intro p q
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  exact congrArg ((c:ℂ)*·) (hA p q)

private theorem phi_pair_mul {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (hAB : Commute A B) :
    GaussCoframeForm.Paired (A*B) (A*B) := by
  intro p q
  change sourcePair p (A (B q))=sourcePair (A (B p)) q
  have hc := LinearMap.congr_fun hAB.eq p
  change A (B p)=B (A p) at hc
  rw [hA,hB,←hc]

private theorem phi_pair_pow {A : End} (hA : GaussCoframeForm.Paired A A) (n : ℕ) :
    GaussCoframeForm.Paired (A^n) (A^n) := by
  induction n with
  | zero => simpa only [pow_zero] using phi_pair_one
  | succ n ih =>
    rw [pow_succ]
    exact phi_pair_mul ih hA ((Commute.refl A).pow_left n)

private theorem phi_S_pair : GaussCoframeForm.Paired S S := multiply_pair _ _

private theorem phi_r_pair : GaussCoframeForm.Paired r r := multiply_pair _ _

private theorem phi_Q_pair : GaussCoframeForm.Paired Q Q := phi_pair_sub phi_pair_one phi_S_pair

private theorem phi_theta_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (phiThetaAction m ell) (phiThetaAction m ell) :=
  phi_pair_sub (phi_pair_pow phi_Q_pair (m+1)) (phi_pair_pow phi_Q_pair (ell+1))

private theorem phi_first_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (profileFirst m ell) (profileFirst m ell) := by
  unfold profileFirst SourceClockPhiRadiusResponseHessian.phiFirstPeak
  change GaussCoframeForm.Paired
    (((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m) : End)
    (((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m) : End)
  have h := phi_pair_sub (phi_pair_real (ell+1:ℝ) (phi_pair_pow phi_Q_pair ell))
    (phi_pair_real (m+1:ℝ) (phi_pair_pow phi_Q_pair m))
  simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] using h

private theorem phi_second_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (profileSecond m ell) (profileSecond m ell) := by
  unfold profileSecond SourceClockPhiRadiusResponseHessian.phiSecondPeak
  change GaussCoframeForm.Paired
    (((m*(m+1):ℂ) • Q^(m-1)-(ell*(ell+1):ℂ) • Q^(ell-1)) : End)
    (((m*(m+1):ℂ) • Q^(m-1)-(ell*(ell+1):ℂ) • Q^(ell-1)) : End)
  have h := phi_pair_sub (phi_pair_real ((m:ℝ)*(m+1)) (phi_pair_pow phi_Q_pair (m-1)))
    (phi_pair_real ((ell:ℝ)*(ell+1)) (phi_pair_pow phi_Q_pair (ell-1)))
  simpa only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] using h

private theorem phi_first_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (profileFirst m ell) A :=
  ((((Commute.one_left A).sub_left h).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left A).sub_left h).pow_left m).smul_left _)

private theorem phi_second_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (profileSecond m ell) A :=
  ((((Commute.one_left A).sub_left h).pow_left (m-1)).smul_left _).sub_left
    ((((Commute.one_left A).sub_left h).pow_left (ell-1)).smul_left _)

private theorem phi_theta_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (phiThetaAction m ell) A :=
  (((Commute.one_left A).sub_left h).pow_left (m+1)).sub_left
    (((Commute.one_left A).sub_left h).pow_left (ell+1))

private theorem phi_HT_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (Htheta m ell) A := by
  exact (((phi_second_commute h m ell).mul_left ((h.pow_left 4).sub_left (h.pow_left 6))).sub_left
    ((phi_first_commute h m ell).mul_left
      (((h.pow_left 3).smul_left (58:ℂ)).add_left ((h.pow_left 5).smul_left (3:ℂ))))).smul_left (1/4:ℂ)

private theorem phi_HB_commute {A : End} (h : Commute S A) (m ell : ℕ) :
    Commute (Hband m ell) A := by
  exact ((((phi_second_commute h m ell).mul_left ((h.pow_left 3).sub_left (h.pow_left 5))).sub_left
    ((phi_first_commute h m ell).mul_left
      (((h.pow_left 2).smul_left (60:ℂ)).add_left (h.pow_left 4)))).add_left
    ((phi_theta_commute h m ell).mul_left ((h.smul_left (60:ℂ)).add_left (h.pow_left 3)))).smul_left (1/4:ℂ)

private theorem phi_HT_pair (m ell : ℕ) : GaussCoframeForm.Paired (Htheta m ell) (Htheta m ell) := by
  unfold Htheta SourceClockPhiRadiusResponseHessian.thetaHessian
  change GaussCoframeForm.Paired
    ((1/4:ℂ) • (profileSecond m ell*(S^4-S^6)-
      profileFirst m ell*((58:ℂ) • S^3+(3:ℂ) • S^5)) : End)
    ((1/4:ℂ) • (profileSecond m ell*(S^4-S^6)-
      profileFirst m ell*((58:ℂ) • S^3+(3:ℂ) • S^5)) : End)
  have h1 := phi_pair_mul (phi_second_pair m ell)
    (phi_pair_sub (phi_pair_pow phi_S_pair 4) (phi_pair_pow phi_S_pair 6))
    (((phi_profile_second_S m ell).pow_right 4).sub_right ((phi_profile_second_S m ell).pow_right 6))
  have h2 := phi_pair_mul (phi_first_pair m ell)
    (phi_pair_add (phi_pair_real (58:ℝ) (phi_pair_pow phi_S_pair 3))
      (phi_pair_real (3:ℝ) (phi_pair_pow phi_S_pair 5)))
    ((((phi_profile_first_S m ell).pow_right 3).smul_right (58:ℂ)).add_right
      (((phi_profile_first_S m ell).pow_right 5).smul_right (3:ℂ)))
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    phi_pair_real (1/4:ℝ) (phi_pair_sub h1 h2)

private theorem phi_HB_pair (m ell : ℕ) : GaussCoframeForm.Paired (Hband m ell) (Hband m ell) := by
  unfold Hband SourceClockPhiRadiusResponseHessian.bandHessian
  change GaussCoframeForm.Paired
    ((1/4:ℂ) • (profileSecond m ell*(S^3-S^5)-
      profileFirst m ell*((60:ℂ) • S^2+S^4)+
      phiThetaAction m ell*((60:ℂ) • S+S^3)) : End)
    ((1/4:ℂ) • (profileSecond m ell*(S^3-S^5)-
      profileFirst m ell*((60:ℂ) • S^2+S^4)+
      phiThetaAction m ell*((60:ℂ) • S+S^3)) : End)
  have h1 := phi_pair_mul (phi_second_pair m ell)
    (phi_pair_sub (phi_pair_pow phi_S_pair 3) (phi_pair_pow phi_S_pair 5))
    (((phi_profile_second_S m ell).pow_right 3).sub_right ((phi_profile_second_S m ell).pow_right 5))
  have h2 := phi_pair_mul (phi_first_pair m ell)
    (phi_pair_add (phi_pair_real (60:ℝ) (phi_pair_pow phi_S_pair 2)) (phi_pair_pow phi_S_pair 4))
    ((((phi_profile_first_S m ell).pow_right 2).smul_right (60:ℂ)).add_right
      ((phi_profile_first_S m ell).pow_right 4))
  have h3 := phi_pair_mul (phi_theta_pair m ell)
    (phi_pair_add (phi_pair_real (60:ℝ) phi_S_pair) (phi_pair_pow phi_S_pair 3))
    (((phi_profile_theta_S m ell).smul_right (60:ℂ)).add_right ((phi_profile_theta_S m ell).pow_right 3))
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    phi_pair_real (1/4:ℝ) (phi_pair_add (phi_pair_sub h1 h2) h3)

private theorem phi_paired_self_im {A : End} (hA : GaussCoframeForm.Paired A A) (p : QuantumTest) :
    (sourcePair p (A p)).im=0 := by
  have h := congrArg Complex.im (pair_conjugate p (A p))
  rw [←hA p p] at h
  simp only [Complex.conj_im] at h
  linarith only [h]

private theorem phi_paired_diagonal_im {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (hAB : Commute A B) (p : QuantumTest) :
    (sourcePair (A p) (B p)).im=0 := by
  rw [←hA p (B p)]
  exact phi_paired_self_im (phi_pair_mul hA hB hAB) p

private theorem phi_moment_clock_self_im (s : QuantumTest) :
    (sourcePair s (clockMean ((r^2-(1:End)) s))).im=0 := by
  have hp := phi_pair_sub (phi_pair_pow phi_r_pair 2) phi_pair_one
  have hc : Commute clockMean (r^2-(1:End)) :=
    (clock_mean_radius.pow_right 2).sub_right (Commute.one_right clockMean)
  exact phi_paired_self_im (phi_pair_mul clock_mean_pair hp hc) s

private def phiRadialInput (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  (profileFirst m ell*S-phiThetaAction m ell) (resolventCore F z hz (coreEquiv.symm g))-
    (profileFirst m ell*S^2) (resolventCore F z hz (r (coreEquiv.symm g)))

private def phiCDensity (m ell : ℕ) : End :=
  S*(phiThetaAction m ell)^2*((60:ℂ) • 1+S^2)-
    (2:ℂ) • (profileFirst m ell*phiThetaAction m ell*S^2*(1-S^2))
private def phiMDensity (m ell : ℕ) : End :=
  -((profileFirst m ell)^2+phiThetaAction m ell*profileSecond m ell)*S^4*(1-S^2)+
    profileFirst m ell*phiThetaAction m ell*S^3*((58:ℂ) • 1+(3:ℂ) • S^2)

private theorem phi_C_density_source (m ell : ℕ) :
    bracket E (profileC m ell)+(61:ℂ) • profileC m ell=phiCDensity m ell :=
  phi_profile_euler_c m ell
private theorem phi_M_density_source (m ell : ℕ) :
    bracket E (profileM m ell)+(61:ℂ) • profileM m ell=phiMDensity m ell :=
  phi_profile_euler_M m ell

private theorem phi_inverse_square_pair : GaussCoframeForm.Paired (U*U) (U*U) := by
  simpa only [pow_two] using phi_pair_pow inverse_pair 2
private theorem phi_inverse_square_E : Commute E (U*U) := euler_inverse.mul_right euler_inverse
private theorem phi_M_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (profileM m ell) (profileM m ell) := by
  have hB := phi_pair_mul (phi_first_pair m ell) (phi_pair_pow phi_S_pair 3)
    ((phi_profile_first_S m ell).pow_right 3)
  have hBT : Commute (profileFirst m ell*S^3) (phiThetaAction m ell) :=
    (phi_profile_theta_first m ell).symm.mul_left ((phi_profile_theta_S m ell).symm.pow_left 3)
  exact phi_pair_mul hB (phi_theta_pair m ell) hBT
private theorem phi_S_inverse_square : Commute S (U*U) := by
  have h : Commute S U := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (phiReciprocal z:ℂ) (reciprocalVolume z:ℂ) (f z)
  exact h.mul_right h
private theorem phi_M_inverse_square (m ell : ℕ) : Commute (profileM m ell) (U*U) :=
  ((phi_first_commute phi_S_inverse_square m ell).mul_left
    (phi_S_inverse_square.pow_left 3)).mul_left (phi_theta_commute phi_S_inverse_square m ell)

private theorem phi_weighted_c_density (A : End) (hA : Commute E A) (m ell : ℕ) :
    bracket E (A*profileC m ell)+(61:ℂ) • (A*profileC m ell)=A*phiCDensity m ell := by
  have hz : bracket E A=0 := sub_eq_zero.mpr hA.eq
  calc
    _=A*(bracket E (profileC m ell)+(61:ℂ) • profileC m ell) := by
      rw [phi_profile_bracket_product,hz]
      simp only [zero_mul,zero_add,mul_add,mul_smul_comm]
    _=_ := by rw [phi_C_density_source]
private theorem phi_weighted_M_density (m ell : ℕ) :
    bracket E ((U*U)*profileM m ell)+(61:ℂ) • ((U*U)*profileM m ell)=
      (U*U)*phiMDensity m ell := by
  have hz : bracket E (U*U)=0 := sub_eq_zero.mpr phi_inverse_square_E.eq
  calc
    _=(U*U)*(bracket E (profileM m ell)+(61:ℂ) • profileM m ell) := by
      rw [phi_profile_bracket_product,hz]
      simp only [zero_mul,zero_add,mul_add,mul_smul_comm]
    _=_ := by rw [phi_M_density_source]

/-- E-Paired moves the sole q derivative with the actual K and actual c. -/
private theorem phi_clock_c_E_pair (m ell : ℕ) (q y : QuantumTest) :
    sourcePair q (clockMean (profileC m ell (E y)))=
      -sourcePair (E q) (clockMean (profileC m ell y))-
        sourcePair q (clockMean (phiCDensity m ell y)) := by
  have h := phi_profile_paired_derivative (clockMean*profileC m ell) q y
  rw [phi_weighted_c_density clockMean euler_clock_mean] at h
  exact h

/-- The same integration by parts retains the full U² multiplier. -/
private theorem phi_inverse_c_E_pair (m ell : ℕ) (q y : QuantumTest) :
    sourcePair q ((U*U) (profileC m ell (E y)))=
      -sourcePair (E q) ((U*U) (profileC m ell y))-
        sourcePair q ((U*U) (phiCDensity m ell y)) := by
  have h := phi_profile_paired_derivative ((U*U)*profileC m ell) q y
  rw [phi_weighted_c_density (U*U) phi_inverse_square_E] at h
  exact h

/-- Actual Paired closure removes the M E self-real term, including beta2. -/
private theorem phi_inverse_M_E_real (m ell : ℕ) (y : QuantumTest) :
    (sourcePair y ((U*U) (profileM m ell (E y)))).re=
      -(1/2:ℝ)*(sourcePair y ((U*U) (phiMDensity m ell y))).re := by
  let A : End := (U*U)*profileM m ell
  have hA : GaussCoframeForm.Paired A A :=
    phi_pair_mul phi_inverse_square_pair (phi_M_pair m ell) (phi_M_inverse_square m ell).symm
  have h := phi_profile_paired_derivative A y y
  have hc := pair_conjugate y (A (E y))
  rw [←hA (E y) y] at hc
  have hr := congrArg Complex.re h
  have hcr := congrArg Complex.re hc
  dsimp only [A] at hr hcr
  rw [phi_weighted_M_density] at hr
  change (sourcePair y ((U*U) (profileM m ell (E y)))).re=
    (-sourcePair (E y) ((U*U) (profileM m ell y))-
      sourcePair y ((U*U) (phiMDensity m ell y))).re at hr
  change ((starRingEnd ℂ) (sourcePair y ((U*U) (profileM m ell (E y))))).re=
    (sourcePair (E y) ((U*U) (profileM m ell y))).re at hcr
  simp only [Complex.neg_re,Complex.sub_re,Complex.conj_re] at hr hcr
  change (sourcePair y ((U*U) (profileM m ell (E y)))).re=
    -(1/2:ℝ)*(sourcePair y ((U*U) (phiMDensity m ell y))).re
  linarith only [hr,hcr]

private def phiLq (q : QuantumTest) : QuantumTest :=
  E q+(1/2:ℂ) • (((60:ℂ) • (1:End)+S^2) q)

/-- The same actual response written with one Lq and its complete boundary flux. -/
def phiSingleLqWord (m ell : ℕ) (q h : QuantumTest) : ℝ :=
  let y := r q-h
  (sourceTime 0/2)*(sourcePair y (clockMean (profileM m ell (E y)))).im+
    (sourceTime 0/2)*(sourcePair (phiLq q) (clockMean (profileC m ell y))).im+
    (sourceTime 0)^2/8*(sourcePair y ((U*U)
      (((profileFirst m ell)^2*S^4*(1-S^2) : End) y))).re-
    (sourceTime 0)^2/4*(sourcePair (phiLq q) ((U*U) (profileC m ell y))).re

private theorem phi_sturm_s_mismatch (m ell : ℕ) (q h : QuantumTest) :
    S ((profileFirst m ell*S-phiThetaAction m ell) q-(profileFirst m ell*S^2) h)=
      -(S*phiThetaAction m ell) q+(profileFirst m ell*S^3) (r q-h) := by
  have hS3 : S^3*r=S^2 := by rw [pow_succ S 2,mul_assoc,inverse_radius,mul_one]
  have hb := (phi_profile_first_S m ell).symm.eq
  have hq : S*(profileFirst m ell*S-phiThetaAction m ell)=
      -(S*phiThetaAction m ell)+profileFirst m ell*S^3*r := by
    calc
      _=(S*profileFirst m ell)*S-S*phiThetaAction m ell := by noncomm_ring
      _=profileFirst m ell*S^2-S*phiThetaAction m ell := by rw [hb,pow_two];noncomm_ring
      _=_ := by rw [mul_assoc (profileFirst m ell) (S^3) r,hS3];abel
  have hh : S*(profileFirst m ell*S^2)=profileFirst m ell*S^3 := by
    rw [←mul_assoc,hb,mul_assoc,←pow_succ']
  have hq' := LinearMap.congr_fun hq q
  have hh' := LinearMap.congr_fun hh h
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply,
    map_sub] at hq' hh' ⊢
  linear_combination (norm := module) hq'-hh'

private theorem phi_sturm_zero_mismatch (m ell : ℕ) (q h : QuantumTest) :
    Hband m ell q-Htheta m ell h=
      phiSturmCross m ell q+Htheta m ell (r q-h) := by
  have hc := original_phi_hessian_cross m ell
  have hr : Commute (Htheta m ell) r := phi_HT_commute phi_inverse_radius_commute m ell
  have he : Hband m ell=phiSturmCross m ell+Htheta m ell*r := by
    rw [←hc,hr.eq]
    abel
  rw [he]
  simp only [LinearMap.add_apply,Module.End.mul_apply,map_sub]
  abel

private theorem phi_sturm_fixedEuler_mismatch (m ell : ℕ) (q h : QuantumTest) :
    phiThetaAction m ell (r (E q)-E h)=
      phiThetaAction m ell (E (r q-h)-(r-S) q) := by
  have hr := LinearMap.congr_fun original_phi_euler_radius q
  change E (r q)-r (E q)=(r-S) q at hr
  congr 1
  simp only [map_sub]
  linear_combination (norm := module) -hr

private theorem phi_sturm_real_boundary_coefficient (m ell : ℕ) :
    (1/4:ℂ) • ((profileFirst m ell)^2*S^4*(1-S^2))+
      (1/2:ℂ) • (phiThetaAction m ell*Htheta m ell)+
      (1/8:ℂ) • phiMDensity m ell=
        (1/8:ℂ) • ((profileFirst m ell)^2*S^4*(1-S^2)) := by
  have hb (A : End) : profileFirst m ell*(phiThetaAction m ell*A)=
      phiThetaAction m ell*(profileFirst m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_first m ell).symm.eq,mul_assoc]
  unfold Htheta SourceClockPhiRadiusResponseHessian.thetaHessian phiMDensity
  change (1/4:ℂ) • ((profileFirst m ell)^2*S^4*(1-S^2))+
    (1/2:ℂ) • (phiThetaAction m ell*((1/4:ℂ) •
      (profileSecond m ell*(S^4-S^6)-profileFirst m ell*((58:ℂ) • S^3+(3:ℂ) • S^5))))+
    (1/8:ℂ) • (-((profileFirst m ell)^2+phiThetaAction m ell*profileSecond m ell)*S^4*(1-S^2)+
      profileFirst m ell*phiThetaAction m ell*S^3*((58:ℂ) • 1+(3:ℂ) • S^2))=_
  noncomm_ring [hb,(phi_profile_theta_first m ell).symm.eq]
  module

private theorem phi_sturm_real_cross_coefficient (m ell : ℕ) :
    (1/2:ℂ) • (phiThetaAction m ell*phiSturmCross m ell)-
      (1/4:ℂ) • (profileFirst m ell*phiThetaAction m ell*S^2*(1-S^2))-
      (1/4:ℂ) • phiCDensity m ell=
        (-1/8:ℂ) • (S*(phiThetaAction m ell)^2*((60:ℂ) • 1+S^2)) := by
  have ht (A : End) : phiThetaAction m ell*(S*A)=S*(phiThetaAction m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_S m ell).eq,mul_assoc]
  have hb (A : End) : profileFirst m ell*(phiThetaAction m ell*A)=
      phiThetaAction m ell*(profileFirst m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_first m ell).symm.eq,mul_assoc]
  unfold phiSturmCross phiCDensity
  noncomm_ring [ht,hb,(phi_profile_theta_S m ell).eq,(phi_profile_theta_first m ell).symm.eq]
  module

private theorem phi_sturm_clock_cross_coefficient (m ell : ℕ) :
    (1/2:ℂ) • phiCDensity m ell+
      (1/2:ℂ) • (profileFirst m ell*phiThetaAction m ell*S^2*(1-S^2))-
      phiThetaAction m ell*phiSturmCross m ell=
        (1/4:ℂ) • (profileC m ell*((60:ℂ) • 1+S^2)) := by
  have ht (A : End) : phiThetaAction m ell*(S*A)=S*(phiThetaAction m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_S m ell).eq,mul_assoc]
  have hb (A : End) : profileFirst m ell*(phiThetaAction m ell*A)=
      phiThetaAction m ell*(profileFirst m ell*A) := by
    rw [←mul_assoc,(phi_profile_theta_first m ell).symm.eq,mul_assoc]
  unfold phiCDensity phiSturmCross profileC
  noncomm_ring [ht,hb,(phi_profile_theta_S m ell).eq,(phi_profile_theta_first m ell).symm.eq]
  module

private theorem phi_pair_add_left (p q v : QuantumTest) :
    sourcePair (p+q) v=sourcePair p v+sourcePair q v := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem phi_pair_add_right (p q v : QuantumTest) :
    sourcePair p (q+v)=sourcePair p q+sourcePair p v := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem phi_pair_sub_left (p q v : QuantumTest) :
    sourcePair (p-q) v=sourcePair p v-sourcePair q v := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem phi_pair_sub_right (p q v : QuantumTest) :
    sourcePair p (q-v)=sourcePair p q-sourcePair p v := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem phi_pair_neg_left (p q : QuantumTest) : sourcePair (-p) q= -sourcePair p q := by
  simp only [sourcePair,map_neg,inner_neg_left]
private theorem phi_pair_neg_right (p q : QuantumTest) : sourcePair p (-q)= -sourcePair p q := by
  simp only [sourcePair,map_neg,inner_neg_right]
private theorem phi_commute_apply {A B : End} (h : Commute A B) (q : QuantumTest) :
    A (B q)=B (A q) := by
  simpa only [Module.End.mul_apply] using LinearMap.congr_fun h.eq q
private theorem phi_weighted_move (P A : End) (hA : GaussCoframeForm.Paired A A)
    (hPA : Commute P A) (p q : QuantumTest) :
    sourcePair (A p) (P q)=sourcePair p (P (A q)) := by
  rw [←hA p (P q),←phi_commute_apply hPA q]

private abbrev phiA (m ell : ℕ) : End := S*phiThetaAction m ell
private abbrev phiB (m ell : ℕ) : End := profileFirst m ell*S^3
private abbrev phiW : End := r^2-1
private abbrev phiJProfile (m ell : ℕ) : End :=
  profileFirst m ell*phiThetaAction m ell*S^2*(1-S^2)
private abbrev phiGProfile (m ell : ℕ) : End :=
  (profileFirst m ell)^2*S^4*(1-S^2)
private abbrev phiLProfile : End := (60:ℂ) • 1+S^2

private theorem phi_A_pair (m ell : ℕ) : GaussCoframeForm.Paired (phiA m ell) (phiA m ell) :=
  phi_pair_mul phi_S_pair (phi_theta_pair m ell) (phi_profile_theta_S m ell).symm
private theorem phi_B_pair (m ell : ℕ) : GaussCoframeForm.Paired (phiB m ell) (phiB m ell) :=
  phi_pair_mul (phi_first_pair m ell) (phi_pair_pow phi_S_pair 3) ((phi_profile_first_S m ell).pow_right 3)
private theorem phi_cross_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (phiSturmCross m ell) (phiSturmCross m ell) := by
  rw [←original_phi_hessian_cross]
  exact phi_pair_sub (phi_HB_pair m ell)
    (phi_pair_mul phi_r_pair (phi_HT_pair m ell) (phi_HT_commute phi_inverse_radius_commute m ell).symm)
private theorem phi_cross_commute {P : End} (h : Commute S P) (m ell : ℕ) :
    Commute (phiSturmCross m ell) P := by
  exact (((phi_first_commute h m ell).mul_left ((h.pow_left 2).sub_left (h.pow_left 4))).smul_left (-1/2:ℂ)).add_left
    (((phi_theta_commute h m ell).mul_left ((h.smul_left (60:ℂ)).add_left (h.pow_left 3))).smul_left (1/4:ℂ))

private theorem phi_sturm_products (m ell : ℕ) :
    phiA m ell*phiThetaAction m ell=profileC m ell ∧
    phiB m ell*phiThetaAction m ell=profileM m ell ∧
    phiW*phiA m ell=phiThetaAction m ell*(r-S) ∧
    phiA m ell*phiW*phiB m ell=phiJProfile m ell ∧
    phiB m ell*phiW*phiB m ell=phiGProfile m ell := by
  have htS (X : End) : phiThetaAction m ell*(S*X)=S*(phiThetaAction m ell*X) := by
    rw [←mul_assoc,(phi_profile_theta_S m ell).eq,mul_assoc]
  have hbS (X : End) : profileFirst m ell*(S*X)=S*(profileFirst m ell*X) := by
    rw [←mul_assoc,(phi_profile_first_S m ell).eq,mul_assoc]
  have htr (X : End) : phiThetaAction m ell*(r*X)=r*(phiThetaAction m ell*X) := by
    rw [←mul_assoc,(phi_theta_commute phi_inverse_radius_commute m ell).eq,mul_assoc]
  have hbr (X : End) : profileFirst m ell*(r*X)=r*(profileFirst m ell*X) := by
    rw [←mul_assoc,(phi_first_radius m ell).eq,mul_assoc]
  have hbt (X : End) : profileFirst m ell*(phiThetaAction m ell*X)=phiThetaAction m ell*(profileFirst m ell*X) := by
    rw [←mul_assoc,(phi_profile_theta_first m ell).symm.eq,mul_assoc]
  have hSr (X : End) : S*(r*X)=X := by rw [←mul_assoc,inverse_radius,one_mul]
  have hrS (X : End) : r*(S*X)=X := by rw [←mul_assoc,radius_inverse,one_mul]
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold phiA profileC
    change S*phiThetaAction m ell*phiThetaAction m ell=S*(phiThetaAction m ell)^2
    noncomm_ring
  · rfl
  · change (r^2-1)*(S*phiThetaAction m ell)=phiThetaAction m ell*(r-S)
    noncomm_ring [htS,htr,hSr,hrS,(phi_profile_theta_S m ell).eq,
      (phi_theta_commute phi_inverse_radius_commute m ell).eq,inverse_radius,radius_inverse]
  · change (S*phiThetaAction m ell)*(r^2-1)*(profileFirst m ell*S^3)=_
    unfold phiJProfile
    noncomm_ring [htS,hbS,htr,hbr,hbt,hSr,hrS,(phi_profile_theta_S m ell).eq,
      (phi_profile_first_S m ell).eq,(phi_first_radius m ell).eq,
      (phi_profile_theta_first m ell).symm.eq,inverse_radius,radius_inverse]
  · change (profileFirst m ell*S^3)*(r^2-1)*(profileFirst m ell*S^3)=_
    unfold phiGProfile
    noncomm_ring [hbS,hbr,hSr,hrS,(phi_profile_first_S m ell).eq,
      (phi_first_radius m ell).eq,inverse_radius,radius_inverse]

private theorem phi_raw_real_algebra (P A B C H T W : End)
    (hA : GaussCoframeForm.Paired A A) (hB : GaussCoframeForm.Paired B B)
    (hC : GaussCoframeForm.Paired C C) (hH : GaussCoframeForm.Paired H H)
    (hPA : Commute P A) (hPB : Commute P B) (hPC : Commute P C) (hPH : Commute P H)
    (q y d : QuantumTest) :
    (-1/4:ℂ)*sourcePair (-A q+B y) (P (T d-W (A q)))+
      (1/4:ℂ)*sourcePair (-A q+B y) (P (W (-A q+B y)))+
      (1/2:ℂ)*sourcePair (C q+H y) (P (T y))=
    (1/4:ℂ)*sourcePair q (P (A (T d)))-
      (1/4:ℂ)*sourcePair y (P (B (T d)))-
      (1/4:ℂ)*sourcePair q (P (A (W (B y))))+
      (1/4:ℂ)*sourcePair y (P (B (W (B y))))+
      (1/2:ℂ)*sourcePair q (P (C (T y)))+
      (1/2:ℂ)*sourcePair y (P (H (T y))) := by
  simp only [map_add,map_sub,map_neg,phi_pair_add_left,phi_pair_add_right,
    phi_pair_sub_right,phi_pair_neg_left,phi_pair_neg_right,
    phi_weighted_move P A hA hPA,phi_weighted_move P B hB hPB,
    phi_weighted_move P C hC hPC,phi_weighted_move P H hH hPH]
  ring

private theorem phi_reverse_clock_word (m ell : ℕ) (q y : QuantumTest) :
    (sourcePair y (clockMean (phiB m ell (phiW (phiA m ell q))))).im=
      -(sourcePair q (clockMean (phiA m ell (phiW (phiB m ell y))))).im := by
  have hW := phi_pair_sub (phi_pair_pow phi_r_pair 2) phi_pair_one
  have hKW : Commute clockMean phiW := (clock_mean_radius.pow_right 2).sub_right (Commute.one_right clockMean)
  have hKA : Commute clockMean (phiA m ell) := clock_mean_inverse.mul_right (clock_mean_theta m ell)
  have hKB : Commute clockMean (phiB m ell) :=
    (phi_first_commute clock_mean_inverse.symm m ell).symm.mul_right (clock_mean_inverse.pow_right 3)
  have he : sourcePair y (clockMean (phiB m ell (phiW (phiA m ell q))))=
      (starRingEnd ℂ) (sourcePair q (clockMean (phiA m ell (phiW (phiB m ell y))))) := by
    rw [clock_mean_pair,phi_B_pair m ell,hW,phi_A_pair m ell]
    rw [←phi_commute_apply hKB y,←phi_commute_apply hKW (phiB m ell y),
      ←phi_commute_apply hKA (phiW (phiB m ell y))]
    exact (pair_conjugate q (clockMean (phiA m ell (phiW (phiB m ell y))))).symm
  exact congrArg Complex.im he |>.trans (Complex.conj_im _)

private theorem phi_raw_clock_algebra (m ell : ℕ) (q y d : QuantumTest) :
    (1/2:ℝ)*(sourcePair (-phiA m ell q+phiB m ell y)
      (clockMean (phiThetaAction m ell d-phiW (phiA m ell q)))).im+
      (sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell (r q-y)))).im=
    -(1/2:ℝ)*(sourcePair q (clockMean (profileC m ell d))).im+
      (1/2:ℝ)*(sourcePair y (clockMean (profileM m ell d))).im+
      (1/2:ℝ)*(sourcePair q (clockMean (phiJProfile m ell y))).im-
      (sourcePair q (clockMean ((phiThetaAction m ell*phiSturmCross m ell) y))).im := by
  have hKA : Commute clockMean (phiA m ell) := clock_mean_inverse.mul_right (clock_mean_theta m ell)
  have hKB : Commute clockMean (phiB m ell) :=
    (phi_first_commute clock_mean_inverse.symm m ell).symm.mul_right (clock_mean_inverse.pow_right 3)
  have hzA := phi_moment_clock_self_im (phiA m ell q)
  have hTC : Commute (phiThetaAction m ell) (phiSturmCross m ell) :=
    (phi_cross_commute (phi_profile_theta_S m ell).symm m ell).symm
  have hCR : Commute (phiSturmCross m ell) r := phi_cross_commute phi_inverse_radius_commute m ell
  have hKCr : Commute clockMean (phiSturmCross m ell*r) :=
    (phi_cross_commute clock_mean_inverse.symm m ell).symm.mul_right clock_mean_radius
  have hdiag := phi_paired_diagonal_im (phi_theta_pair m ell)
    (phi_pair_mul clock_mean_pair (phi_pair_mul (phi_cross_pair m ell) phi_r_pair hCR) hKCr)
    ((clock_mean_theta m ell).symm.mul_right
      (hTC.mul_right (phi_theta_commute phi_inverse_radius_commute m ell))) q
  have hrev := phi_reverse_clock_word m ell q y
  have hp := phi_sturm_products m ell
  have hAC (w : QuantumTest) : phiA m ell (phiThetaAction m ell w)=profileC m ell w := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.1 w
  have hBC (w : QuantumTest) : phiB m ell (phiThetaAction m ell w)=profileM m ell w := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.2.1 w
  have hAWB (w : QuantumTest) : phiA m ell (phiW (phiB m ell w))=phiJProfile m ell w := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.2.2.2.1 w
  simp only [Module.End.mul_apply] at hdiag
  rw [hAWB] at hrev
  simp only [map_sub,phi_pair_add_left,phi_pair_sub_right,phi_pair_neg_left,
    phi_weighted_move clockMean (phiA m ell) (phi_A_pair m ell) hKA,
    phi_weighted_move clockMean (phiB m ell) (phi_B_pair m ell) hKB,hAC,hBC,
    Complex.add_im,Complex.sub_im,Complex.neg_im] at hzA ⊢
  have ht := phi_weighted_move clockMean (phiThetaAction m ell) (phi_theta_pair m ell)
    (clock_mean_theta m ell) q (phiSturmCross m ell y)
  have hti := congrArg Complex.im ht
  change (sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell y))).im=
    (sourcePair q (clockMean ((phiThetaAction m ell*phiSturmCross m ell) y))).im at hti
  linarith only [hzA,hdiag,hrev,hti]

private theorem phi_Lq_weighted_pair (P : End) (hPS : Commute P S) (m ell : ℕ)
    (q y : QuantumTest) :
    sourcePair (phiLq q) (P (profileC m ell y))=
      sourcePair (E q) (P (profileC m ell y))+
        (1/2:ℂ)*sourcePair q (P ((profileC m ell*phiLProfile) y)) := by
  have hL : GaussCoframeForm.Paired phiLProfile phiLProfile :=
    phi_pair_add (phi_pair_real (60:ℝ) phi_pair_one) (phi_pair_pow phi_S_pair 2)
  have hPL : Commute P phiLProfile :=
    ((Commute.one_right P).smul_right (60:ℂ)).add_right (hPS.pow_right 2)
  have hcS : Commute (profileC m ell) S :=
    (Commute.refl S).mul_left ((phi_profile_theta_S m ell).pow_left 2)
  have hcL : Commute (profileC m ell) phiLProfile :=
    ((Commute.one_right _).smul_right (60:ℂ)).add_right (hcS.pow_right 2)
  have hm := phi_weighted_move P phiLProfile hL hPL q (profileC m ell y)
  rw [←phi_commute_apply hcL y] at hm
  have hs : sourcePair ((1/2:ℂ) • phiLProfile q) (P (profileC m ell y))=
      (1/2:ℂ)*sourcePair (phiLProfile q) (P (profileC m ell y)) := by
    simp only [sourcePair,map_smul,inner_smul_left]
    norm_num only [map_div₀,map_one,map_ofNat]
  change sourcePair (E q+(1/2:ℂ) • phiLProfile q) (P (profileC m ell y))=_
  rw [phi_pair_add_left,hs,hm]
  rfl

private def phiPairLinear (P : End) (p q : QuantumTest) : End →ₗ[ℂ] ℂ where
  toFun A := sourcePair p (P (A q))
  map_add' A B := by
    simp only [LinearMap.add_apply,map_add,sourcePair,inner_add_right]
  map_smul' c A := by
    simp only [LinearMap.smul_apply,map_smul,sourcePair,inner_smul_right,smul_eq_mul,RingHom.id_apply]

private theorem phi_clock_lq_kernel (m ell : ℕ) (q y : QuantumTest) :
    (1/2:ℝ)*(sourcePair (-phiA m ell q+phiB m ell y)
      (clockMean (phiThetaAction m ell (E y)-phiW (phiA m ell q)))).im+
      (sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell (r q-y)))).im=
    (1/2:ℝ)*(sourcePair y (clockMean (profileM m ell (E y)))).im+
      (1/2:ℝ)*(sourcePair (phiLq q) (clockMean (profileC m ell y))).im := by
  have hr := phi_raw_clock_algebra m ell q y (E y)
  have hi := congrArg Complex.im (phi_clock_c_E_pair m ell q y)
  have hc0 := phi_sturm_clock_cross_coefficient m ell
  change (1/2:ℂ) • phiCDensity m ell+(1/2:ℂ) • phiJProfile m ell-
    phiThetaAction m ell*phiSturmCross m ell=
      (1/4:ℂ) • (profileC m ell*phiLProfile) at hc0
  have hc := congrArg (phiPairLinear clockMean q y) hc0
  simp only [map_add,map_sub,map_smul,smul_eq_mul] at hc
  change (1/2:ℂ)*sourcePair q (clockMean (phiCDensity m ell y))+
    (1/2:ℂ)*sourcePair q (clockMean (phiJProfile m ell y))-
      sourcePair q (clockMean ((phiThetaAction m ell*phiSturmCross m ell) y))=
    (1/4:ℂ)*sourcePair q (clockMean ((profileC m ell*phiLProfile) y)) at hc
  have hci := congrArg Complex.im hc
  have hl := congrArg Complex.im (phi_Lq_weighted_pair clockMean clock_mean_inverse m ell q y)
  simp only [Complex.neg_im,Complex.sub_im] at hi
  norm_num only [Complex.add_im,Complex.sub_im,Complex.mul_im,
    Complex.div_re,Complex.div_im,Complex.normSq_apply,Complex.neg_im,Complex.ofReal_ofNat,Complex.ofReal_one,
    Complex.re_ofNat,Complex.im_ofNat,Complex.one_re,Complex.one_im,
    add_zero,zero_add,mul_zero,zero_mul,div_zero,zero_div] at hci hl
  linarith only [hr,hi,hci,hl]

private theorem phi_real_lq_kernel (m ell : ℕ) (q y : QuantumTest) :
    -(1/4:ℝ)*(sourcePair (-phiA m ell q+phiB m ell y)
      ((U*U) (phiThetaAction m ell (E y)-phiW (phiA m ell q)))).re+
      (1/4:ℝ)*(sourcePair (-phiA m ell q+phiB m ell y)
        ((U*U) (phiW (-phiA m ell q+phiB m ell y)))).re+
      (1/2:ℝ)*(sourcePair (phiSturmCross m ell q+Htheta m ell y)
        ((U*U) (phiThetaAction m ell y))).re=
    (1/8:ℝ)*(sourcePair y ((U*U) (phiGProfile m ell y))).re-
      (1/4:ℝ)*(sourcePair (phiLq q) ((U*U) (profileC m ell y))).re := by
  have hPA : Commute (U*U) (phiA m ell) :=
    phi_S_inverse_square.symm.mul_right (phi_theta_commute phi_S_inverse_square m ell).symm
  have hPB : Commute (U*U) (phiB m ell) :=
    (phi_first_commute phi_S_inverse_square m ell).symm.mul_right (phi_S_inverse_square.symm.pow_right 3)
  have hr := congrArg Complex.re
    (phi_raw_real_algebra (U*U) (phiA m ell) (phiB m ell) (phiSturmCross m ell)
      (Htheta m ell) (phiThetaAction m ell) phiW
      (phi_A_pair m ell) (phi_B_pair m ell) (phi_cross_pair m ell) (phi_HT_pair m ell)
      hPA hPB (phi_cross_commute phi_S_inverse_square m ell).symm
      (phi_HT_commute phi_S_inverse_square m ell).symm q y (E y))
  have hp := phi_sturm_products m ell
  have hAT (w : QuantumTest) : phiA m ell (phiThetaAction m ell w)=profileC m ell w := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.1 w
  have hBT (w : QuantumTest) : phiB m ell (phiThetaAction m ell w)=profileM m ell w := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.2.1 w
  have hAWB (w : QuantumTest) : phiA m ell (phiW (phiB m ell w))=phiJProfile m ell w := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.2.2.2.1 w
  have hBWB (w : QuantumTest) : phiB m ell (phiW (phiB m ell w))=phiGProfile m ell w := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.2.2.2.2 w
  have hCT (w : QuantumTest) : phiSturmCross m ell (phiThetaAction m ell w)=
      (phiThetaAction m ell*phiSturmCross m ell) w :=
    phi_commute_apply (phi_cross_commute (phi_profile_theta_S m ell).symm m ell) w
  have hHT (w : QuantumTest) : Htheta m ell (phiThetaAction m ell w)=
      (phiThetaAction m ell*Htheta m ell) w :=
    phi_commute_apply (phi_HT_commute (phi_profile_theta_S m ell).symm m ell) w
  simp only [hAT,hBT,hAWB,hBWB,hCT,hHT] at hr
  have hi := congrArg Complex.re (phi_inverse_c_E_pair m ell q y)
  have hm := phi_inverse_M_E_real m ell y
  have hb0 := phi_sturm_real_boundary_coefficient m ell
  change (1/4:ℂ) • phiGProfile m ell+(1/2:ℂ) •
      (phiThetaAction m ell*Htheta m ell)+(1/8:ℂ) • phiMDensity m ell=
    (1/8:ℂ) • phiGProfile m ell at hb0
  have hb := congrArg (phiPairLinear (U*U) y y) hb0
  simp only [map_add,map_smul,smul_eq_mul] at hb
  change (1/4:ℂ)*sourcePair y ((U*U) (phiGProfile m ell y))+
    (1/2:ℂ)*sourcePair y ((U*U) ((phiThetaAction m ell*Htheta m ell) y))+
    (1/8:ℂ)*sourcePair y ((U*U) (phiMDensity m ell y))=
    (1/8:ℂ)*sourcePair y ((U*U) (phiGProfile m ell y)) at hb
  have hc0 := phi_sturm_real_cross_coefficient m ell
  change (1/2:ℂ) • (phiThetaAction m ell*phiSturmCross m ell)-
    (1/4:ℂ) • phiJProfile m ell-(1/4:ℂ) • phiCDensity m ell=
      (-1/8:ℂ) • (profileC m ell*phiLProfile) at hc0
  have hc := congrArg (phiPairLinear (U*U) q y) hc0
  simp only [map_sub,map_smul,smul_eq_mul] at hc
  change (1/2:ℂ)*sourcePair q ((U*U) ((phiThetaAction m ell*phiSturmCross m ell) y))-
    (1/4:ℂ)*sourcePair q ((U*U) (phiJProfile m ell y))-
    (1/4:ℂ)*sourcePair q ((U*U) (phiCDensity m ell y))=
    (-1/8:ℂ)*sourcePair q ((U*U) ((profileC m ell*phiLProfile) y)) at hc
  have hbr := congrArg Complex.re hb
  have hcr := congrArg Complex.re hc
  have hl := congrArg Complex.re
    (phi_Lq_weighted_pair (U*U) phi_S_inverse_square.symm m ell q y)
  simp only [Complex.neg_re,Complex.sub_re] at hi
  norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.neg_re,
    Complex.div_re,Complex.div_im,Complex.normSq_apply,Complex.neg_im,Complex.ofReal_ofNat,Complex.ofReal_one,
    Complex.re_ofNat,Complex.im_ofNat,Complex.one_re,Complex.one_im,
    add_zero,zero_add,mul_zero,zero_mul,div_zero,zero_div] at hr hbr hcr hl
  linarith only [hr,hi,hm,hbr,hcr,hl]

/-- The complete actual five-word source has one Lq and its unseparated boundary flux. -/
theorem actual_phi_scalar_single_Lq (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    phiScalarSturmWord m ell F z hz g=
      phiSingleLqWord m ell (resolventCore F z hz (coreEquiv.symm g))
        (resolventCore F z hz (r (coreEquiv.symm g))) := by
  let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
  let h : QuantumTest := resolventCore F z hz (r (coreEquiv.symm g))
  let y : QuantumTest := r q-h
  let s : QuantumTest := S (phiRadialInput m ell F z hz g)
  let e : QuantumTest := phiFixedEuler m ell F z hz g
  let v : QuantumTest := phiResponseCore m ell F z hz g
  let zero : QuantumTest := SourceClockPhiRadiusResponseHessian.zeroVector m ell F z hz g
  have hs : -phiA m ell q+phiB m ell y=s := (phi_sturm_s_mismatch m ell q h).symm
  have hp := phi_sturm_products m ell
  have hWA : phiW (phiA m ell q)=phiThetaAction m ell ((r-S) q) := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hp.2.2.1 q
  have he : phiThetaAction m ell (E y)-phiW (phiA m ell q)=e := by
    have h0 := phi_sturm_fixedEuler_mismatch m ell q h
    change e=phiThetaAction m ell (E y-(r-S) q) at h0
    rw [map_sub,←hWA] at h0
    exact h0.symm
  have hZ : phiSturmCross m ell q+Htheta m ell y=zero := (phi_sturm_zero_mismatch m ell q h).symm
  have hv : phiThetaAction m ell y=v := rfl
  have hh : r q-y=h := by dsimp only [y];module
  have hclock := phi_clock_lq_kernel m ell q y
  have hreal := phi_real_lq_kernel m ell q y
  simp only [hs,he,hZ,hv,hh] at hclock hreal
  have hsource : phiScalarSturmWord m ell F z hz g=
      sourceTime 0*((1/2:ℝ)*(sourcePair s (clockMean e)).im+
        (sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell h))).im)+
      (sourceTime 0)^2*(-(1/4:ℝ)*(sourcePair s ((U*U) e)).re+
        (1/4:ℝ)*(sourcePair s ((U*U) (phiW s))).re+
        (1/2:ℝ)*(sourcePair zero ((U*U) v)).re) := by
    change (sourceTime 0/2)*(sourcePair s (clockMean e)).im-
      (sourceTime 0)^2/4*(sourcePair s ((U*U) e)).re+
      (sourceTime 0)^2/4*(sourcePair s ((U*U) (phiW s))).re+
      sourceTime 0*(sourcePair (phiThetaAction m ell q) (clockMean (phiSturmCross m ell h))).im+
      (sourceTime 0)^2/2*(sourcePair zero ((U*U) v)).re=_
    ring
  have htarget : phiSingleLqWord m ell q h=
      sourceTime 0*((1/2:ℝ)*(sourcePair y (clockMean (profileM m ell (E y)))).im+
        (1/2:ℝ)*(sourcePair (phiLq q) (clockMean (profileC m ell y))).im)+
      (sourceTime 0)^2*((1/8:ℝ)*(sourcePair y ((U*U) (phiGProfile m ell y))).re-
        (1/4:ℝ)*(sourcePair (phiLq q) ((U*U) (profileC m ell y))).re) := by
    unfold phiSingleLqWord
    dsimp only [y,phiGProfile]
    ring
  change phiScalarSturmWord m ell F z hz g=phiSingleLqWord m ell q h
  rw [hsource,htarget,hclock,hreal]

end LowEnergy.SourceClockPhiRadiusSingleLq
