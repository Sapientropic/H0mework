import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusWeakSourceBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiRadiusSingleLq
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiWholeCFGreenSource
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockPhiEndpointNativePressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiWholeGreenGammaBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussNativePotential
open GaussYukawaCoefficient SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceScalarInverseBulk SourceCoframeVolumeCurrent
open SourceClockAcceleration SourceClockReflectedForm SourceScalarPositiveBulkWard
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockYukawaCubicCurrent SourceClockPhiRadiusResponsePositiveSource
open SourceMixedNativeReturn
open SourceClockPhiRadiusResponseNativeBudget SourceClockPhiRadiusResponseHessian
open SourceClockPhiRadiusClockSturm SourceClockPhiRadiusSingleLq
open SourceClockPhiScalarEndpointAcceleration SourceClockPhiZeroSeedEndpointTail
open SourceClockPhiWholeCFGreenSource SourceClockPhiEndpointNativePressure SourceClockYukawaQ8RadiusBudget
open SourceClockYukawaRadialGammaNativeBudget SourceFourPoleEnergyClosed
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceLocalizedInverseFormPayment
open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U : End := inverseVolumeAction
private abbrev D : End := dilation
private abbrev E : End := phiEulerAction
private abbrev S : End := phiInverseAction
private abbrev r : End := phiRadiusAction
private abbrev T : End := SourceClockPhiRadiusAcceleration.phiSquare
private abbrev B : End := bracket diagonalAction T
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] resolventCore diagonalAction compressionCore defectAction state

private theorem pair_add_l (p q v : QuantumTest) :
    sourcePair (p+q) v=sourcePair p v+sourcePair q v := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r (p q v : QuantumTest) :
    sourcePair p (q+v)=sourcePair p q+sourcePair p v := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_l (c : ℂ) (p q : QuantumTest) :
    sourcePair (c • p) q=(starRingEnd ℂ c)*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r (c : ℂ) (p q : QuantumTest) :
    sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem pair_sub_r (f k p : QuantumTest) :
    sourcePair f (k-p)=sourcePair f k-sourcePair f p := by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem inverse_D : D*U-U*D=(2*Complex.I) • U := by
  have h := congrArg (fun A : End => (-2*Complex.I/3) • A)
    SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (D*U-U*D))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi : (-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring
private theorem endpoint_clock :
    (n/2:ℂ) • clockMean-(Complex.I*(n:ℂ)^2/4) • (U*U)=
      ((n:ℂ)^2/8) • endpointWord := by
  have h1 := congrArg (fun A : End => U*A) inverse_D
  have h2 := congrArg (fun A : End => A*U) inverse_D
  unfold clockMean endpointWord
  change (n/2:ℂ) • (1/2:ℂ) • (U*clockCurrent+clockCurrent*U)-
    (Complex.I*(n:ℂ)^2/4) • (U*U)=
    ((n:ℂ)^2/8) • (U*U*((3:ℂ) • D+(4*Complex.I) • (1:End)))
  rw [original_clock_current]
  change (n/2:ℂ) • (1/2:ℂ) •
    (U*((3*(n:ℂ)/8) • (U*D+D*U))+((3*(n:ℂ)/8) • (U*D+D*U))*U)-
    (Complex.I*(n:ℂ)^2/4) • (U*U)=
    ((n:ℂ)^2/8) • (U*U*((3:ℂ) • D+(4*Complex.I) • (1:End)))
  simp only [smul_add,smul_smul]
  linear_combination (norm := (noncomm_ring;module)) (9*(n:ℂ)^2/32) • h1+
    (3*(n:ℂ)^2/32) • h2

private def scalarForce (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  phiNativeDivergence m ell F z hz g+(-(n:ℂ)/2) • (U (zeroVector m ell F z hz g))
private def Lq (q : QuantumTest) : QuantumTest := E q+(1/2:ℂ) • (((60:ℂ) • (1:End)+S^2) q)
private theorem Lq_source (q : QuantumTest) : Lq q=sourceLq q := by
  simp only [Lq,sourceLq,SourceScalarAffineScaleTransport.generator,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply]
  module

/-- Both boundary sectors stay beside the original field/damping word before the single clip. -/
def boundaryField (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  let q := resolventCore F z hz (coreEquiv.symm g)
  let h := resolventCore F z hz (r (coreEquiv.symm g))
  let y := r q-h
  let v := phiResponseCore m ell F z hz g
  n/2*(sourcePair y (clockMean (profileM m ell (E y)))).im+
    n^2/8*(sourcePair y ((U*U)
      (((phiFirstPeak m ell)^2*S^4*(1-S^2) : End) y))).re-
    2*z.im*(sourcePair v (clockCurrent v)).re+
    n/2*z.re*(sourcePair v (U v)).re+
    n^2*spinForm (U v)+n^2*densityForm (U v)-n*gaugeForm (U v)-n*spatialForm (U v)

private def scalarBoundary (m ell : ℕ) (q h : QuantumTest) : ℝ :=
  let y := r q-h
  n/2*(sourcePair y (clockMean (profileM m ell (E y)))).im+
    n^2/8*(sourcePair y ((U*U) (((phiFirstPeak m ell)^2*S^4*(1-S^2) : End) y))).re
private def scalarEndpoint (m ell : ℕ) (q h : QuantumTest) : ℝ :=
  n^2/8*(sourcePair (sourceLq q) (endpointWord (profileC m ell (r q-h)))).im
private theorem scalar_endpoint_kernel (m ell : ℕ) (q h : QuantumTest) :
    phiSingleLqWord m ell q h=scalarEndpoint m ell q h+scalarBoundary m ell q h := by
  let y := r q-h
  let p := profileC m ell y
  have hC := LinearMap.congr_fun endpoint_clock p
  have hpair := congrArg (sourcePair (sourceLq q)) hC
  have hn1 : (n/2:ℂ)=((n/2:ℝ):ℂ) := by push_cast;ring
  have hn2 : ((n:ℂ)^2/4)=((n^2/4:ℝ):ℂ) := by push_cast;ring
  have hn3 : ((n:ℂ)^2/8)=((n^2/8:ℝ):ℂ) := by push_cast;ring
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_r,pair_smul_r,hn1,hn3] at hpair
  have hphase : Complex.I*(n:ℂ)^2/4=Complex.I*((n^2/4:ℝ):ℂ) := by
    rw [←hn2];ring
  rw [hphase] at hpair
  have hi := congrArg Complex.im hpair
  simp only [Complex.sub_im,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im] at hi
  unfold phiSingleLqWord scalarEndpoint scalarBoundary
  change n/2*(sourcePair y (clockMean (profileM m ell (E y)))).im+
    n/2*(sourcePair (Lq q) (clockMean p)).im+
    n^2/8*(sourcePair y ((U*U) (((phiFirstPeak m ell)^2*S^4*(1-S^2) : End) y))).re-
    n^2/4*(sourcePair (Lq q) ((U*U) p)).re=_
  rw [Lq_source]
  dsimp only [p,y] at hi ⊢
  linear_combination (norm := ring) hi
private theorem scalar_endpoint (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    phiScalarSturmWord m ell F z hz g=
      n^2/8*(sourcePair (sourceLq (resolventCore F z hz (coreEquiv.symm g)))
        (endpointWord (endpointState m ell F z hz g))).im+
      scalarBoundary m ell (resolventCore F z hz (coreEquiv.symm g))
        (resolventCore F z hz (r (coreEquiv.symm g))) := by
  let q : QuantumTest := resolventCore F z hz (coreEquiv.symm g)
  let h : QuantumTest := resolventCore F z hz (r (coreEquiv.symm g))
  have hp : profileC m ell (r q-h)=endpointState m ell F z hz g := by
    simp only [endpointState,phiResponseCore,profileC,bracket,
      LinearMap.sub_apply,Module.End.mul_apply,pow_two]
    rfl
  rw [actual_phi_scalar_single_Lq]
  have he := scalar_endpoint_kernel m ell q h
  unfold scalarEndpoint at he
  rw [hp] at he
  exact he

private def fieldNoether (z : ℂ) (v : QuantumTest) : ℝ :=
  -2*z.im*(sourcePair v (clockCurrent v)).re+n/2*z.re*(sourcePair v (U v)).re+
    n^2*spinForm (U v)+n^2*densityForm (U v)-n*gaugeForm (U v)-n*spatialForm (U v)
private def rawPrice (z : ℂ) (v f : QuantumTest) : ℝ :=
  2*(sourcePair f (clockCurrent v)).im+n/2*(sourcePair (U v) f).re+fieldNoether z v
private theorem weak_price_kernel (z : ℂ) (α : ℝ) (v f sf dc : QuantumTest)
    (hf : f=sf+dc) :
    2*α*rawPrice z v f-(sourcePair v dc).im=
      2*α*(2*(sourcePair sf (clockCurrent v)).im+n/2*(sourcePair (U v) sf).re)-
      (sourcePair (v+(4*α:ℂ) • clockCurrent v+(Complex.I*(α:ℂ)*(n:ℂ)) • U v) dc).im+
      2*α*fieldNoether z v := by
  unfold rawPrice
  rw [hf]
  have hc := congrArg Complex.im (GaussNativeForm.pair_conjugate (clockCurrent v) dc)
  simp only [Complex.conj_im] at hc
  simp only [pair_add_l,pair_add_r,pair_smul_l,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal,
    Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat] at hc ⊢
  linear_combination (norm := ring) (-4*α)*hc

private theorem positive_price_read (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    phiPositivePrice m ell F z hz g=rawPrice z (phiResponseCore m ell F z hz g)
      (phiResponseSource m ell F z hz g) := by
  let v : QuantumTest := phiResponseCore m ell F z hz g
  let f : QuantumTest := phiResponseSource m ell F z hz g
  change 2*(sourcePair f (clockCurrent v)).im-2*z.im*(sourcePair v (clockCurrent v)).re+
    n/2*(sourcePair (U v) f).re+n/2*z.re*(sourcePair v (U v)).re+
    n^2*spinForm (U v)+n^2*densityForm (U v)-n*gaugeForm (U v)-n*spatialForm (U v)=
    rawPrice z v f
  unfold rawPrice fieldNoether
  ring
private theorem tested_read (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) :
    testedEndpoint m ell F z hz g α=
      2*α*(n^2/8*(sourcePair (sourceLq (resolventCore F z hz (coreEquiv.symm g)))
        (endpointWord (endpointState m ell F z hz g))).im)-
      (sourcePair (phiResponseCore m ell F z hz g+
        (4*α:ℂ) • clockCurrent (phiResponseCore m ell F z hz g)+
        (Complex.I*(α:ℂ)*(n:ℂ)) • U (phiResponseCore m ell F z hz g))
        (phiCoherentDefect m ell F z hz g)).im := rfl
private theorem boundary_read (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    boundaryField m ell F z hz g=scalarBoundary m ell
      (resolventCore F z hz (coreEquiv.symm g)) (resolventCore F z hz (r (coreEquiv.symm g)))+
      fieldNoether z (phiResponseCore m ell F z hz g) := by
  unfold boundaryField scalarBoundary fieldNoether
  ring

/-- The weak Gamma price consumes the exact scalar endpoint and the complete coherent tester. -/
theorem actual_weak_green_word (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) :
    SourceClockPhiRadiusWeakSourceBudget.remainingPrice m ell F z hz g (2*α)=
      testedEndpoint m ell F z hz g α+2*α*boundaryField m ell F z hz g := by
  let v : QuantumTest := phiResponseCore m ell F z hz g
  let sf : QuantumTest := scalarForce m ell F z hz g
  let dc : QuantumTest := phiCoherentDefect m ell F z hz g
  let f : QuantumTest := phiResponseSource m ell F z hz g
  have hs := actual_phi_scalar_sturm_pair m ell F z hz g
  change 2*(sourcePair sf (clockCurrent v)).im+n/2*(sourcePair (U v) sf).re=
    phiScalarSturmWord m ell F z hz g at hs
  have hf := actual_phi_full_sturm_source m ell F z hz g
  change f=sf+dc at hf
  have hk := weak_price_kernel z α v f sf dc hf
  rw [hs,scalar_endpoint] at hk
  unfold SourceClockPhiRadiusWeakSourceBudget.remainingPrice
  rw [positive_price_read,tested_read,boundary_read]
  change 2*α*rawPrice z v f-(sourcePair v dc).im=
    2*α*(n^2/8*(sourcePair (sourceLq (resolventCore F z hz (coreEquiv.symm g)))
      (endpointWord (endpointState m ell F z hz g))).im)-
    (sourcePair (v+(4*α:ℂ) • clockCurrent v+(Complex.I*(α:ℂ)*(n:ℂ)) • U v) dc).im+
      2*α*(scalarBoundary m ell (resolventCore F z hz (coreEquiv.symm g))
        (resolventCore F z hz (r (coreEquiv.symm g)))+fieldNoether z v)
  linear_combination (norm := ring) hk

/-- This real price retains the negative response, positive boundary Gram and all fields in one word. -/
def greenGammaPrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) : ℝ :=
  firstOrderRemainder m ell F z hz g α+2*α*boundaryField m ell F z hz g-
    4*α*z.im^2*‖embed (phiResponseCore m ell F z hz g)‖^2

private theorem radius_square_pair (f k : QuantumTest) : sourcePair f (T k)=sourcePair (T f) k := by
  have hr (a b : QuantumTest) : sourcePair a (r b)=sourcePair (r a) b := multiply_pair _ _ _ _
  change sourcePair f ((r^2) k)=sourcePair ((r^2) f) k
  simp only [pow_two,Module.End.mul_apply]
  rw [hr,hr]
private theorem pair_sub_l (f k p : QuantumTest) :
    sourcePair (f-k) p=sourcePair f p-sourcePair k p := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem B_pair (f k : QuantumTest) : sourcePair f (B k)= -sourcePair (B f) k := by
  change sourcePair f (diagonalAction (T k)-T (diagonalAction k))=
    -sourcePair (diagonalAction (T f)-T (diagonalAction f)) k
  rw [pair_sub_r,pair_sub_l,diagonalAction_pair f (T k),radius_square_pair f (diagonalAction k),
    ←radius_square_pair (diagonalAction f) k,←diagonalAction_pair (T f) k]
  ring
private theorem inverse_radius : S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem inverse_theta (m ell : ℕ) : Commute S (phiThetaAction m ell) :=
  (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (m+1)).sub_right
    (((Commute.one_right S).sub_right (Commute.refl S)).pow_right (ell+1))
private theorem radius_theta (m ell : ℕ) : Commute r (phiThetaAction m ell) := by
  have hrS : Commute r S := by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
    exact smul_comm (phiRadius x:ℂ) (phiReciprocal x:ℂ) (f x)
  exact (((Commute.one_right r).sub_right hrS).pow_right (m+1)).sub_right
    (((Commute.one_right r).sub_right hrS).pow_right (ell+1))
private theorem endpoint_expansion (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    endpointState m ell F z hz g=
      ((phiThetaAction m ell)^2) (resolventCore F z hz (coreEquiv.symm g))-
      (S*(phiThetaAction m ell)^2) (resolventCore F z hz (r (coreEquiv.symm g))) := by
  have hSr : S*(phiThetaAction m ell)^2*r=(phiThetaAction m ell)^2 := by
    rw [mul_assoc,←((radius_theta m ell).pow_right 2).eq,←mul_assoc,inverse_radius,one_mul]
  have he := LinearMap.congr_fun hSr (resolventCore F z hz (coreEquiv.symm g))
  simp only [Module.End.mul_apply] at he
  unfold endpointState phiResponseCore bracket
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,pow_two] at he ⊢
  rw [he]
private def greenError (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) : ℝ :=
  4*α*z.im^2*‖embed (phiThetaAction m ell (resolventCore F z hz (r (coreEquiv.symm g))))‖^2+
    2*α*(‖embed (B (coreEquiv.symm g))‖+2*|z.im| *‖embed (T (coreEquiv.symm g))‖)*
      ‖embed (endpointState m ell F z hz g)‖
private theorem green_point_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) (hα : 0 ≤ α) :
    testedEndpoint m ell F z hz g α+4*α*z.im^2*‖embed (phiResponseCore m ell F z hz g)‖^2≤
      wholeRemainder m ell F z hz g α+greenError m ell F z hz g α := by
  let v := phiResponseCore m ell F z hz g
  let t := phiThetaAction m ell (resolventCore F z hz (r (coreEquiv.symm g)))
  let p := endpointState m ell F z hz g
  have hcross : -(sourcePair t v).re≤‖embed t‖*‖embed v‖ :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  have hdiag : -8*α*z.im^2*‖embed v‖^2-8*α*z.im^2*(sourcePair t v).re+
      4*α*z.im^2*‖embed v‖^2≤4*α*z.im^2*‖embed t‖^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4*α*z.im^2 by positivity)
      (sq_nonneg (‖embed t‖-‖embed v‖)),
      mul_le_mul_of_nonneg_left hcross (show 0 ≤ 8*α*z.im^2 by positivity)]
  have hb : (sourcePair (coreEquiv.symm g) (B p)).re≤
      ‖embed (B (coreEquiv.symm g))‖*‖embed p‖ := by
    rw [B_pair,Complex.neg_re]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  have ht : |(sourcePair (coreEquiv.symm g) (T p)).im|≤
      ‖embed (T (coreEquiv.symm g))‖*‖embed p‖ := by
    rw [radius_square_pair]
    exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hti : 2*z.im*(sourcePair (coreEquiv.symm g) (T p)).im≤
      2*|z.im| *‖embed (T (coreEquiv.symm g))‖*‖embed p‖ := by
    have h := le_abs_self (z.im*(sourcePair (coreEquiv.symm g) (T p)).im)
    rw [abs_mul] at h
    have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg z.im)
    nlinarith
  have hfix := mul_le_mul_of_nonneg_left (add_le_add hb hti) (show 0 ≤ 2*α by positivity)
  rw [actual_phi_whole_green_source]
  dsimp only [greenError]
  dsimp only [v,t,p] at hdiag hfix
  linarith only [hdiag,hfix]

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem frequency_im (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (actualFrequency advanced μ w).im^2=μ^2 ∧ |(actualFrequency advanced μ w).im|=μ := by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_sq,abs_neg,abs_of_pos hμ,and_self]
private theorem finite_star (F : Index) (z : ℂ) :
    finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have h : (fun w : ℝ => finiteResolvent F (actualFrequency true μ w))=
        fun w : ℝ => (finiteResolvent F (line μ w)).adjoint := by
      funext w;exact finite_star F _
    exact h ▸ (ContinuousLinearMap.adjoint.continuous.comp
      (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))
private theorem read_core (F : Index) (f : QuantumTest) (A : End) (z : ℂ) (hz : z.im≠0) :
    sourceRead F (coreEquiv f) A (finiteResolvent F z (embed f))=embed (A (resolventCore F z hz f)) := by
  have h := source_read_resolvent F (coreEquiv f) A z hz
  have he : ((coreEquiv f : Core) : H)=embed f := rfl
  rw [he] at h
  simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,state] using h
private theorem theta_continuous (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (advanced : Bool) :
    Continuous (fun w : ℝ => embed (phiThetaAction m ell
      (resolventCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
        (r (coreEquiv.symm g))))) := by
  simp_rw [←read_core]
  exact (sourceRead F (coreEquiv (r (coreEquiv.symm g))) (phiThetaAction m ell)).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)
private theorem endpoint_continuous (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (advanced : Bool) :
    Continuous (fun w : ℝ => embed (endpointState m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)) := by
  simp_rw [endpoint_expansion,map_sub,←read_core]
  exact ((sourceRead F (coreEquiv (coreEquiv.symm g)) ((phiThetaAction m ell)^2)).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).sub
    ((sourceRead F (coreEquiv (r (coreEquiv.symm g))) (S*(phiThetaAction m ell)^2)).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const))
private theorem error_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (α : ℝ) (advanced : Bool) :
    Measurable (fun w : ℝ => ENNReal.ofReal (greenError m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g α)) := by
  simp_rw [greenError,(frequency_im advanced μ hμ _).1,(frequency_im advanced μ hμ _).2]
  exact (((continuous_const.mul ((theta_continuous m ell F μ hμ g advanced).norm.pow 2)).add
    (continuous_const.mul (endpoint_continuous m ell F μ hμ g advanced).norm)).measurable).ennreal_ofReal
private theorem error_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (α : ℝ) (hα : 0 < α) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (greenError m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g α))≤ENNReal.ofReal ε := by
  intro ε hε
  let C1 : ℝ := 4*α*μ^2
  let C2 : ℝ := 2*α*(‖embed (B (coreEquiv.symm g))‖+2*μ*‖embed (T (coreEquiv.symm g))‖)
  have hC1 : 0 ≤ C1 := by dsimp only [C1];positivity
  have hC2 : 0 ≤ C2 := by dsimp only [C2];positivity
  let δ : ℝ := ε/(C1+C2+1)
  have hδ : 0 < δ := by dsimp only [δ];positivity
  obtain ⟨N1,h1⟩ := actual_phi_theta_common_tail μ hμ (phiRadiusSource g) δ hδ
  obtain ⟨N2,h2⟩ := actual_endpoint_absolute_common_tail μ hμ g δ hδ
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (le_trans (le_max_left _ _) hm) ell hml,
    h2 m (le_trans (le_max_right _ _) hm) ell hml] with F hF1 hF2
  intro advanced
  let X : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖embed (phiThetaAction m ell
    (resolventCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
      (r (coreEquiv.symm g))))‖^2)
  let Y : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖embed (endpointState m ell F
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)‖)
  have hmX : Measurable X := ((theta_continuous m ell F μ hμ g advanced).norm.pow 2).measurable.ennreal_ofReal
  have hX : (∫⁻ w,X w)≤ENNReal.ofReal δ := by
    simpa only [X,resolventCore,LinearMap.coe_mk,AddHom.coe_mk,phiRadiusSource] using hF1 advanced
  have hY : (∫⁻ w,Y w)≤ENNReal.ofReal δ := hF2 advanced
  have he (w : ℝ) : ENNReal.ofReal (greenError m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g α)=ENNReal.ofReal C1*X w+ENNReal.ofReal C2*Y w := by
    simp only [greenError,(frequency_im advanced μ hμ w).1,(frequency_im advanced μ hμ w).2]
    change ENNReal.ofReal (C1*_+C2*_)=_
    rw [ENNReal.ofReal_add (mul_nonneg hC1 (sq_nonneg _)) (mul_nonneg hC2 (norm_nonneg _)),
      ENNReal.ofReal_mul hC1,ENNReal.ofReal_mul hC2]
  calc
    _=ENNReal.ofReal C1*(∫⁻ w,X w)+ENNReal.ofReal C2*(∫⁻ w,Y w) := by
      simp_rw [he]
      have hmCX : Measurable (fun w => ENNReal.ofReal C1*X w) := measurable_const.mul hmX
      rw [lintegral_add_left hmCX,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _≤ENNReal.ofReal C1*ENNReal.ofReal δ+ENNReal.ofReal C2*ENNReal.ofReal δ := by
      gcongr
    _≤ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC1,←ENNReal.ofReal_mul hC2,
        ←ENNReal.ofReal_add (mul_nonneg hC1 hδ.le) (mul_nonneg hC2 hδ.le)]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [δ]
      rw [←add_mul,←mul_div_assoc]
      apply (div_le_iff₀ (show 0 < C1+C2+1 by positivity)).mpr
      nlinarith


private theorem weak_point_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (α : ℝ) (hα : 0 < α) :
    SourceClockPhiRadiusWeakSourceBudget.remainingPrice m ell F z hz g (2*α) ≤
      greenGammaPrice m ell F z hz g α+greenError m ell F z hz g α := by
  have hg := green_point_price m ell F z hz g α hα.le
  rw [actual_weak_green_word]
  unfold greenGammaPrice
  rw [actual_whole_native_pressure] at hg
  linarith only [hg]

def greenGammaBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (α : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (greenGammaPrice m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g α)

private theorem weak_green_payment (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain)
    (α : ℝ) (hα : 0 < α) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        SourceClockPhiRadiusWeakSourceBudget.remainingBudget m ell F μ hμ g (2*α) ≤
          ENNReal.ofReal ε+greenGammaBudget m ell F μ hμ g α := by
  intro ε hε
  obtain ⟨N,hN⟩ := error_common_tail μ hμ g α hα ε hε
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  let X : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (greenError m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g α)
  let R : ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (greenGammaPrice m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g α)
  have hmX : Measurable X := by
    simpa only [X,actualFrequency,Bool.false_eq_true,ite_false] using
      error_measurable m ell F μ hμ g α false
  have hx : (∫⁻ w,X w)≤ENNReal.ofReal ε := by
    simpa only [X,actualFrequency,Bool.false_eq_true,ite_false] using hF false
  unfold SourceClockPhiRadiusWeakSourceBudget.remainingBudget greenGammaBudget
  change (∫⁻ w : ℝ,ENNReal.ofReal (SourceClockPhiRadiusWeakSourceBudget.remainingPrice m ell F
    (line μ w) (by simpa only [line_im] using hμ.ne') g (2*α)))≤ENNReal.ofReal ε+∫⁻ w,R w
  calc
    _ ≤ ∫⁻ w,X w+R w := by
      apply lintegral_mono
      intro w
      dsimp only [X,R]
      have hp := weak_point_price m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g α hα
      exact (ENNReal.ofReal_le_ofReal hp).trans (by
        rw [add_comm]
        exact ENNReal.ofReal_add_le)
    _=(∫⁻ w,X w)+∫⁻ w,R w := lintegral_add_left hmX _
    _≤ENNReal.ofReal ε+∫⁻ w,R w := add_le_add hx le_rfl

/-- Original two-sharp Gamma consumes the negative response and the complete native/boundary/field word. -/
theorem actual_original_phi_green_Gamma_budget (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain)
    (α : ℝ) (hα : 0 < α) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (24*sourceMuFactor μ k*radiusPrice)*
            greenGammaBudget m ell F μ hμ g α := by
  intro ε hε
  let C : ℝ := 24*sourceMuFactor μ k*radiusPrice
  have hC : 0 ≤ C := by dsimp [C];unfold sourceMuFactor radiusPrice;positivity
  let δ : ℝ := ε/(2*(C+1))
  have hδ : 0 < δ := by dsimp [δ];positivity
  obtain ⟨N1,h1⟩ := SourceClockPhiRadiusWeakSourceBudget.actual_original_phi_weak_Gamma_budget
    μ hμ g k (2*α) (by positivity) (ε/2) (by positivity)
  obtain ⟨N2,h2⟩ := weak_green_payment μ hμ g α hα δ hδ
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  filter_upwards [h1 m (le_trans (le_max_left _ _) hm) ell hml,
    h2 m (le_trans (le_max_right _ _) hm) ell hml] with F hg hp
  intro sharp
  have hb := (hg sharp).trans (add_le_add le_rfl (mul_le_mul le_rfl hp zero_le zero_le))
  have he : ε/2+C*δ ≤ ε := by
    have h : C*δ≤ε/2 := by
      dsimp [δ]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (show 0 < 2*(C+1) by positivity)).mpr
      nlinarith only [hε]
    linarith only [h]
  change _≤ENNReal.ofReal (ε/2)+ENNReal.ofReal C*
    (ENNReal.ofReal δ+greenGammaBudget m ell F μ hμ g α) at hb
  calc
    _≤ENNReal.ofReal (ε/2)+ENNReal.ofReal C*
      (ENNReal.ofReal δ+greenGammaBudget m ell F μ hμ g α) := hb
    _=ENNReal.ofReal (ε/2+C*δ)+ENNReal.ofReal C*greenGammaBudget m ell F μ hμ g α := by
      rw [mul_add,←add_assoc,←ENNReal.ofReal_mul hC,
        ←ENNReal.ofReal_add (by positivity) (mul_nonneg hC hδ.le)]
    _≤_ := add_le_add (ENNReal.ofReal_le_ofReal he) le_rfl

end LowEnergy.SourceClockPhiWholeGreenGammaBudget
