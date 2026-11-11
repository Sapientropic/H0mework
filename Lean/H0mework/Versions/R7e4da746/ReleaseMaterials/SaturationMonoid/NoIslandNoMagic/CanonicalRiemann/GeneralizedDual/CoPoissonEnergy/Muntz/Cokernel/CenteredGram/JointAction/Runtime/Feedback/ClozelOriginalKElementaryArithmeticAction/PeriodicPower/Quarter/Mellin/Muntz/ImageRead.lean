import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.TateApprox
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageRead
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.TateApprox
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.CountedLimit
open scoped Topology
open private forward_reindex channel from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward

private theorem even_mass (test:SchwartzMap ℝ ℂ) (even:∀x,test (-x)=test x):
    (∫x:ℝ,test x)=2*∫x:ℝ in Ioi 0,test x:=by
  have negative:(∫x:ℝ in Iic 0,test x)=∫x:ℝ in Ioi 0,test x:=by
    calc
      _=∫x:ℝ in Iic 0,test (-x):=setIntegral_congr_fun measurableSet_Iic (fun x _=>(even x).symm)
      _=_:=by simpa only [neg_zero] using integral_comp_neg_Iic 0 (fun x:ℝ=>test x)
  rw [←setIntegral_univ,←Iic_union_Ioi (a:=(0:ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      test.integrable.integrableOn test.integrable.integrableOn,negative]
  ring

private theorem even_source_mellin (test:SchwartzMap ℝ ℂ) (even:∀x,test (-x)=test x) (w:ℂ):
    coPoissonMuntzEvenSourceMellin test w=2*mellin test w:=by
  have source:coPoissonMuntzEvenSource test=(fun x:ℝ=>(2:ℂ) • test x):=by
    funext x
    rw [coPoissonMuntzEvenSource,even,smul_eq_mul]
    ring
  rw [coPoissonMuntzEvenSourceMellin,source,mellin_const_smul,smul_eq_mul]

private theorem counted_remainder (test:SchwartzMap ℝ ℂ) (even:∀x,test (-x)=test x)
    (x:ℝ) (positive:0<x):
    countedImage test x=(1/2:ℂ)*(x:ℂ)⁻¹*coPoissonMuntzScaleRemainder test x⁻¹:=by
  have theta:coPoissonMuntzThetaNonzero test x⁻¹=
      2*(∑'n:ℕ,test ((n+1:ℕ)/x)):=by
    rw [coPoissonMuntzThetaNonzero_eq_positive_tsum test (inv_ne_zero positive.ne')]
    simp only [coPoissonMuntzEvenSource,even,←two_mul,div_eq_mul_inv]
    exact tsum_mul_left
  rw [coPoissonMuntzScaleRemainder_eq test (inv_pos.mpr positive),theta,even_mass test even]
  simp only [inv_inv,Complex.real_smul]
  unfold countedImage
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']

private theorem counted_mellin (test:SchwartzMap ℝ ℂ) (even:∀x,test (-x)=test x)
    (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (countedImage test) w=riemannZeta (1-w)*mellin test (1-w):=by
  calc
    _=mellin (fun x:ℝ=>(1/2:ℂ) • ((x:ℂ)^(-1:ℂ) •
        coPoissonMuntzScaleRemainder test x⁻¹)) w:=by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (x:ℂ)^(w-1) • countedImage test x=_
      dsimp only
      rw [counted_remainder test even x hx,Complex.cpow_neg_one]
      simp only [smul_eq_mul]
      ring
    _=(1/2:ℂ) • mellin (coPoissonMuntzScaleRemainder test) (1-w):=by
      rw [mellin_const_smul,mellin_cpow_smul,mellin_comp_inv]
      congr 2
      ring
    _=riemannZeta (1-w)*mellin test (1-w):=by
      rw [coPoissonMuntzScaleRemainder_mellin_factorization test
        (by simp only [sub_re,one_re];linarith) (by simp only [sub_re,one_re];linarith),
        even_source_mellin test even,smul_eq_mul]
      ring

def forwardImage (test:ℝ→ℂ) (x:ℝ):ℂ:=
  burnolInnerGapForward test x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*test u

private theorem reciprocal_mellin (test:ℝ→ℂ):
    mellin test 0=∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*test u:=by
  simp only [mellin,zero_sub,Complex.cpow_neg_one,smul_eq_mul]

private theorem mass_mellin (test:ℝ→ℂ):
    mellin test 1=∫u:ℝ in Ioi 0,test u:=by
  simp only [mellin,sub_self,Complex.cpow_zero,one_smul]

private theorem actual_forward_counted_tate (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (x:ℝ) (positive:0<x):
    forwardImage (schwartzApprox c zero h nonnegative N) x=
      countedImage (tateApprox c zero h nonnegative N) x:=by
  have mean:(∫u:ℝ in Ioi 0,tateApprox c zero h nonnegative N u)=
      ∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*schwartzApprox c zero h nonnegative N u:=by
    rw [←mass_mellin,actual_tate_mellin,sub_self,reciprocal_mellin]
  rw [forwardImage,countedImage,mean,forward_reindex,←tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  have index:(0:ℝ)<(n+1:ℕ):=by positivity
  have argPositive:0<((n+1:ℕ):ℝ)/x:=div_pos index positive
  dsimp only [channel]
  change ((n+1:ℕ):ℂ)⁻¹*schwartzApprox c zero h nonnegative N (x/(n+1:ℕ))=
    (x:ℂ)⁻¹*tateRaw c zero h nonnegative N ((n+1:ℕ)/x)
  rw [tateRaw,if_neg argPositive.ne',abs_of_pos argPositive,inv_div,Complex.ofReal_div]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne',show (n:ℂ)+1≠0 by exact_mod_cast (Nat.succ_ne_zero n)]

theorem actual_cutoff_counted_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (countedImage (schwartzApprox c zero h nonnegative N)) w=
      riemannZeta (1-w)*mellin (schwartzApprox c zero h nonnegative N) (1-w):=
  counted_mellin _ (actual_schwartz_even c zero h nonnegative N) w positive below

theorem actual_cutoff_forward_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) (N:ℕ) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    mellin (forwardImage (schwartzApprox c zero h nonnegative N)) w=
      riemannZeta (1-w)*mellin (schwartzApprox c zero h nonnegative N) w:=by
  calc
    _=mellin (countedImage (tateApprox c zero h nonnegative N)) w:=by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [actual_forward_counted_tate c zero h nonnegative N x hx]
    _=riemannZeta (1-w)*mellin (tateApprox c zero h nonnegative N) (1-w):=
      counted_mellin _ (actual_tate_even c zero h nonnegative N) w positive below
    _=_:=by rw [actual_tate_mellin];congr 2;ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Muntz.ImageRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
