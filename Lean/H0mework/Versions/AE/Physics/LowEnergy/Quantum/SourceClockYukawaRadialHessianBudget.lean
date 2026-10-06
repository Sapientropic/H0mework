import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeAbsorption
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialHessianBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockReflectedForm SourcePhysicalKineticSquare
open SourceClockYukawaRadialNativeBudget SourceClockYukawaRadialMixedClock
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialCoefficient SourceLocalizedInverseFormPayment
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail SourceClockYukawaTail
open SourceClockYukawaNormalizedCurrent SourceCutoffDilationWard
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] state fullAction inverseRadius normalizedAction finiteResolvent
  GaussGradedCompression.compression actualIncrement correctedCutoffCore mixedState mixedPrice

private theorem inverse_increment (sharp : Bool) (m ell : ℕ) :
    inverseRadius*actualIncrement sharp m ell=sourceB sharp*relativeTail m ell := by
  apply GaussYukawaGrade.core_ext
  intro f
  change inverseRadius (actualIncrement sharp m ell (embed f))=
    sourceB sharp (relativeTail m ell (embed f))
  rw [literal_increment_core,literal_full_return,Module.End.mul_apply,inverse_core,
    SourceMixedNativeReturn.theta_core]
  simpa only [normalizedAction,Module.End.mul_apply] using
    (original_normalized_core sharp (thetaAction m ell f)).symm


private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem response_commutator (C S : Op) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) :
    FullYSourceResolventGraphSplice.resolvent C z*(C*S-S*C)*FullYSourceResolventGraphSplice.resolvent C z=
      S*FullYSourceResolventGraphSplice.resolvent C z-FullYSourceResolventGraphSplice.resolvent C z*S := by
  have hl := resolvent_compression C hC z hz
  have hr : C*FullYSourceResolventGraphSplice.resolvent C z=1+z • FullYSourceResolventGraphSplice.resolvent C z := by
    have h := resolvent_right C hC z hz
    simp only [sub_mul,smul_mul_assoc,one_mul] at h
    exact sub_eq_iff_eq_add.mp h
  calc
    _=(FullYSourceResolventGraphSplice.resolvent C z*C)*S*FullYSourceResolventGraphSplice.resolvent C z-
        FullYSourceResolventGraphSplice.resolvent C z*S*(C*FullYSourceResolventGraphSplice.resolvent C z) := by noncomm_ring
    _=_ := by
      rw [hl,hr]
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,mul_assoc]
      abel

private theorem cutoff_response_difference (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (cutoffResponseCore sharp m ell F z hz g)=
      actualIncrement sharp m ell (finiteResolvent F z (g:H))-
        finiteResolvent F z (actualIncrement sharp m ell (g:H)) := by
  rw [cutoffResponseCore,state_embed]
  change finiteResolvent F z (embed (correctedCutoffCore sharp m ell F (state F z hz g)))=_
  rw [←actual_cutoff_current_source,state_embed]
  have h := congrArg (fun A : Op => A (g:H)) (response_commutator
    (GaussGradedCompression.compression F) (actualIncrement sharp m ell)
    (GaussGradedCompression.compression_selfAdjoint F) z hz)
  simpa only [SourceClockYukawaRadialMixedGamma.cutoffCurrent,finiteResolvent,mul_apply_eq_comp,sub_apply] using h

private theorem increment_fixed (sharp : Bool) (m ell : ℕ) (h : diagonal.domain) :
    actualIncrement sharp m ell (h:H)=relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp h:H) := by
  have hy : Commute (fullAction sharp) inverseAction := by
    unfold fullAction
    cases sharp
    · exact GaussRadialHamiltonian.original_commutes
    · exact GaussRadialHamiltonian.adjoint_commutes
  have ht : Commute (fullAction sharp) (thetaAction m ell) := by
    unfold thetaAction
    exact (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _).sub_right
      (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _)
  have he : embed (coreEquiv.symm h)=(h:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply h)
  have hc := LinearMap.congr_fun ht.eq (coreEquiv.symm h)
  change fullAction sharp (thetaAction m ell (coreEquiv.symm h))=
    thetaAction m ell (fullAction sharp (coreEquiv.symm h)) at hc
  rw [←he,literal_increment_core,literal_full_return,Module.End.mul_apply,hc,←SourceMixedNativeReturn.theta_core]
  rfl


def weightCore : End := (58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5
def weightOp : Op := (58:ℂ) • inverseRadius^3+(3:ℂ) • inverseRadius^5
private def column (sharp : Bool) : Op := ((58:ℂ) • inverseRadius^2+(3:ℂ) • inverseRadius^4)*sourceB sharp
attribute [local irreducible] weightCore weightOp column

private theorem inverse_power_core (j : ℕ) (f : QuantumTest) :
    (inverseRadius^j) (embed f)=embed ((inverseAction^j) f) := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [pow_succ',pow_succ']
    change inverseRadius ((inverseRadius^j) (embed f))=_
    rw [ih,inverse_core]
    rfl

private theorem weight_core (f : QuantumTest) : weightOp (embed f)=embed (weightCore f) := by
  simp only [weightOp,weightCore,add_apply,smul_apply,LinearMap.add_apply,LinearMap.smul_apply,
    map_add,map_smul,inverse_power_core]

private theorem weight_increment (sharp : Bool) (m ell : ℕ) :
    weightOp*actualIncrement sharp m ell=column sharp*relativeTail m ell := by
  have h3 : inverseRadius^3=inverseRadius^2*inverseRadius := by rw [←pow_succ]
  have h5 : inverseRadius^5=inverseRadius^4*inverseRadius := by rw [←pow_succ]
  simp only [weightOp,h3,h5,add_mul,smul_mul_assoc,mul_assoc,inverse_increment sharp m ell]
  simp only [column,add_mul,smul_mul_assoc,mul_assoc]

private theorem derivative_core (a : ScalarIndex) (f : QuantumTest) :
    inverseDerivative a (embed f)=embed (inverseDerivativeCore a f) := by
  simp only [inverseDerivative,inverseDerivativeCore,pow_two,mul_apply_eq_comp,Module.End.mul_apply,
    inverse_core,original_direction_core]

/-- These are exactly the full radial Hessian and the original fullX source term, before pairing. -/
def localVector (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  (1/8:ℂ) • weightCore (cutoffResponseCore sharp m ell F z hz g)-
    ∑ a : ScalarIndex,inverseDerivativeCore a
      (PositiveScalarWeakBudget.coefficient sharp a m ell (state F z hz g))

private def localResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g : diagonal.domain) : H :=
  (1/8:ℂ) • (column sharp (relativeTail m ell (finiteResolvent F z (g:H)))-
    weightOp (finiteResolvent F z (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))))-
    ∑ a : ScalarIndex,inverseDerivative a
      (boundedCoefficient sharp a m ell (finiteResolvent F z (g:H)))

attribute [local irreducible] localResponse localVector

private theorem local_vector_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : embed (localVector sharp m ell F z hz g)=localResponse sharp m ell F z g := by
  simp only [localVector,map_sub,map_smul,map_sum,←weight_core,←derivative_core,
    ←original_bounded_coefficient_core,state_embed,cutoff_response_difference,map_sub,increment_fixed]
  have h := congrArg (fun A : Op => A (finiteResolvent F z (g:H))) (weight_increment sharp m ell)
  change weightOp (actualIncrement sharp m ell (finiteResolvent F z (g:H)))=
    column sharp (relativeTail m ell (finiteResolvent F z (g:H))) at h
  rw [h]
  unfold localResponse
  rfl

private theorem two_square (x y : H) : ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]

private def columnPrice (sharp : Bool) : ℝ := 4*‖column sharp‖^2
private def weightPrice : ℝ := 4*‖weightOp‖^2
private def derivativePrice : ℝ := 2*∑ a : ScalarIndex,‖inverseDerivative a‖^2
attribute [local irreducible] columnPrice weightPrice derivativePrice

private theorem local_response_bound (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (g : diagonal.domain) :
    ‖localResponse sharp m ell F z g‖^2  ≤
      columnPrice sharp*‖relativeTail m ell (finiteResolvent F z (g:H))‖^2+
      weightPrice*‖finiteResolvent F z (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))‖^2+
      derivativePrice*(∑ a : ScalarIndex,‖boundedCoefficient sharp a m ell (finiteResolvent F z (g:H))‖^2) := by
  unfold localResponse
  let x := relativeTail m ell (finiteResolvent F z (g:H))
  let y := finiteResolvent F z (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))
  let Z (a : ScalarIndex) := boundedCoefficient sharp a m ell (finiteResolvent F z (g:H))
  have hsum := (norm_sum_le Finset.univ (fun a : ScalarIndex => inverseDerivative a (Z a))).trans
    (Finset.sum_le_sum (fun a _ => (inverseDerivative a).le_opNorm (Z a)))
  have hs := (pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖inverseDerivative a‖) (fun a => ‖Z a‖))
  have hx := pow_le_pow_left₀ (norm_nonneg _) ((column sharp).le_opNorm x) 2
  have hy := pow_le_pow_left₀ (norm_nonneg _) (weightOp.le_opNorm y) 2
  rw [mul_pow] at hx hy
  have ht := two_square (column sharp x) (weightOp y)
  have hsmall : ‖(1/8:ℂ) • (column sharp x-weightOp y)‖^2  ≤  ‖column sharp x-weightOp y‖^2 := by
    rw [norm_smul,mul_pow]
    have hc : ‖(1/8:ℂ)‖^2  ≤  1 := by norm_num
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans_eq (one_mul _)
  have hwhole := two_square ((1/8:ℂ) • (column sharp x-weightOp y)) (∑ a : ScalarIndex,inverseDerivative a (Z a))
  change ‖(1/8:ℂ) • (column sharp x-weightOp y)-(∑ a : ScalarIndex,inverseDerivative a (Z a))‖^2 ≤ _
  unfold columnPrice weightPrice derivativePrice
  change _  ≤  4*‖column sharp‖^2*‖x‖^2+4*‖weightOp‖^2*‖y‖^2+
    (2*∑ a : ScalarIndex,‖inverseDerivative a‖^2)*(∑ a : ScalarIndex,‖Z a‖^2)
  nlinarith only [hs,hx,hy,ht,hsmall,hwhole]

private theorem local_response_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    Continuous (fun w : ℝ => localResponse sharp m ell F (line μ w) g) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  unfold localResponse
  apply Continuous.sub
  · exact ((((column sharp).continuous.comp ((relativeTail m ell).continuous.comp
      (hr.clm_apply continuous_const))).sub (weightOp.continuous.comp
        (hr.clm_apply continuous_const))).const_smul (1/8:ℂ))
  · apply continuous_finsetSum
    intro a _
    exact (inverseDerivative a).continuous.comp ((boundedCoefficient sharp a m ell).continuous.comp
      (hr.clm_apply continuous_const))

private theorem local_response_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N  ≤  m → ∀ ell,m  ≤  ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖localResponse sharp m ell F (line μ w) g‖^2))  ≤  ENNReal.ofReal ε := by
  intro ε hε
  let C := columnPrice sharp+weightPrice+derivativePrice
  have hP : 0 ≤ columnPrice sharp := by unfold columnPrice;positivity
  have hQ : 0 ≤ weightPrice := by unfold weightPrice;positivity
  have hD : 0 ≤ derivativePrice := by
    unfold derivativePrice
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hC : 0 ≤ C := add_nonneg (add_nonneg hP hQ) hD
  let δ := ε/(C+1)
  have hδ : 0 < δ := by dsimp [δ];positivity
  obtain ⟨N₁,h₁⟩ := actual_theta_full_frequency_tail μ hμ g δ hδ
  obtain ⟨N₂,h₂⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:Op)
    (SourceClockYukawaCurrent.yukawaSource sharp g:H) δ hδ
  obtain ⟨N₃,h₃⟩ := actual_coefficient_full_frequency_tail sharp false μ hμ (g:H) δ hδ
  refine ⟨max (max N₁ N₂) N₃,fun m hm ell hml => ?_⟩
  have hm₁ : N₁ ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hm₂ : N₂ ≤ m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hm₃ : N₃ ≤ m := (le_max_right _ _).trans hm
  filter_upwards [h₁ m hm₁ ell hml,h₃ m hm₃ ell hml] with F hx hz
  have hy := h₂ m hm₂ ell hml F
  simp only [one_apply_eq_self] at hy
  simp only [actualFrequency,Bool.false_eq_true,if_false] at hz
  let X (w : ℝ) := ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2)
  let Y (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w)
    (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))‖^2)
  let Z (w : ℝ) := ENNReal.ofReal (∑ a : ScalarIndex,‖boundedCoefficient sharp a m ell (finiteResolvent F (line μ w) (g:H))‖^2)
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hymeas : Measurable (fun w => ENNReal.ofReal weightPrice*Y w) :=
    ((((hr.clm_apply continuous_const).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  have hzcont : Continuous (fun w : ℝ => ∑ a : ScalarIndex,‖boundedCoefficient sharp a m ell (finiteResolvent F (line μ w) (g:H))‖^2) := by
    apply continuous_finsetSum
    intro a _
    exact (((boundedCoefficient sharp a m ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2)
  have hzmeas : Measurable (fun w => ENNReal.ofReal derivativePrice*Z w) :=
    hzcont.measurable.ennreal_ofReal.const_mul _
  calc
    _  ≤  ∫⁻ w : ℝ,ENNReal.ofReal (columnPrice sharp)*X w+ENNReal.ofReal weightPrice*Y w+ENNReal.ofReal derivativePrice*Z w := by
      apply lintegral_mono
      intro w
      dsimp only [X,Y,Z]
      apply (ENNReal.ofReal_le_ofReal (local_response_bound sharp m ell F (line μ w) g)).trans
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,←ENNReal.ofReal_mul hD]
      exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le (le_refl _))
    _ = ENNReal.ofReal (columnPrice sharp)*(∫⁻ w : ℝ,X w)+ENNReal.ofReal weightPrice*(∫⁻ w : ℝ,Y w)+
        ENNReal.ofReal derivativePrice*(∫⁻ w : ℝ,Z w) := by
      rw [lintegral_add_right _ hzmeas,lintegral_add_right _ hymeas,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _  ≤  ENNReal.ofReal (columnPrice sharp)*ENNReal.ofReal δ+ENNReal.ofReal weightPrice*ENNReal.ofReal δ+
        ENNReal.ofReal derivativePrice*ENNReal.ofReal δ := by gcongr
    _  ≤  ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,←ENNReal.ofReal_mul hD,
        ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have he : columnPrice sharp*δ+weightPrice*δ+derivativePrice*δ=C*(ε/(C+1)) := by dsimp [C,δ];ring
      rw [he,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < C+1)).mpr
      nlinarith only [hε]

open SourceClockYukawaRadialNativeDivergence SourceClockYukawaRadialNativeHessian
open SourceClockYukawaRadialNativeAbsorption (inputSource mixedNormEnergy)

/-- The source term paid here is the entire inverse Hessian together with the original fullX term. -/
def paidForce (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  let rA := cutoffResponseCore sharp m ell F z hz (inputSource g)
  let q := state F z hz (inputSource g)
  (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,inverseZeroCore a rA)+
    ∑ a : ScalarIndex,multiply scalarWeight scalarWeight_smooth
      (inverseCoefficientCore a (PositiveScalarWeakBudget.coefficient sharp a m ell q))

def reducedForce (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  let q := state F z hz (inputSource g)
  let rS := SourceClockYukawaRadialCoefficient.radialCore F z hz (inputSource g)
  let rA := cutoffResponseCore sharp m ell F z hz (inputSource g)
  ((bracket GaussMatterCore.matterAction (fullAction sharp)+SourceInverseNeutralSpinCurrent.reducedSpinCurrent sharp)*thetaAction m ell) rS+
    (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,joinedZeroCore sharp a m ell rS)-
    bracket (defectAction F) (SourceCutoffDilationWard.literalIncrementAction sharp m ell) rS-
    bracket (defectAction F) inverseAction rA+
    bracket (bracket (defectAction F) inverseAction)
      (SourceCutoffDilationWard.literalIncrementAction sharp m ell) q

private theorem reduced_forcing_split (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    SourceClockYukawaRadialNativeAbsorption.remainingForce sharp m ell F z hz g=
      paidForce sharp m ell F z hz g+reducedForce sharp m ell F z hz g := by
  simp only [SourceClockYukawaRadialNativeAbsorption.remainingForce,paidForce,reducedForce,sourceZeroOrderWord,
    Finset.sum_add_distrib,smul_add]
  abel

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

/-- Source scalar61 and the original native sum produce the exact bounded coefficient pairing. -/
theorem actual_local_force_source (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    paidForce sharp m ell F z hz g=(sourceTime 0:ℂ) • inverseVolumeAction
      (localVector sharp m ell F z hz (inputSource g)) := by
  have hi := LinearMap.congr_fun original_inverse_hessian_source
    (cutoffResponseCore sharp m ell F z hz (inputSource g))
  rw [show (58:ℂ) • inverseAction^3+(3:ℂ) • inverseAction^5=weightCore by unfold weightCore;rfl] at hi
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply] at hi
  simp only [paidForce,hi,weight_inverse,LinearMap.smul_apply,←Finset.smul_sum,
    ←map_sum,localVector,map_sub,map_smul,smul_sub,smul_smul]
  have hc : (-Complex.I/2)*(Complex.I*(sourceTime 0:ℂ)/4)=(sourceTime 0:ℂ)*(1/8:ℂ) := by
    calc _= -(Complex.I*Complex.I)*(sourceTime 0:ℂ)/8 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hc]
  change _+(-(sourceTime 0:ℂ)) • inverseVolumeAction
    (∑ a : ScalarIndex,inverseDerivativeCore a (PositiveScalarWeakBudget.coefficient sharp a m ell
      (state F z hz (inputSource g))))=_
  module

private theorem young (a b η : ℝ) (hη : 0 < η) : a*b  ≤  η*a^2+b^2/(4*η) := by
  have he : (4*η)*(b^2/(4*η))=b^2 := by field_simp
  nlinarith [sq_nonneg (2*η*a-b)]

/-- The same mixed response's coframe25 floor pays the complete local pair. -/
theorem actual_local_force_price (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    ‖sourcePair (mixedState sharp m ell F z hz g) (paidForce sharp m ell F z hz g)‖  ≤
      η*mixedPrice sharp m ell F z hz g+
        ‖localResponse sharp m ell F z (inputSource g)‖^2/(25*η) := by
  let p := mixedState sharp m ell F z hz g
  let v := localVector sharp m ell F z hz (inputSource g)
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp : sourcePair p (inverseVolumeAction v)=sourcePair (inverseVolumeAction p) v := multiply_pair _ _ _ _
  rw [actual_local_force_source]
  change ‖sourcePair p ((sourceTime 0:ℂ) • inverseVolumeAction v)‖  ≤  _
  rw [show sourcePair p ((sourceTime 0:ℂ) • inverseVolumeAction v)=
    (sourceTime 0:ℂ)*sourcePair p (inverseVolumeAction v) by simp only [sourcePair,map_smul,inner_smul_right]]
  rw [hp,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
  have hi := mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) (embed (inverseVolumeAction p)) (embed v)) hn.le
  have hf := mul_le_mul_of_nonneg_left (SourceClockSourceTail.original_inverse_coframe_floor (inverseVolumeAction p))
    (show 0 ≤ (sourceTime 0)^2/4 by positivity)
  have hpos := (actual_mixed_positive_payment sharp m ell F z hz g).1
  have hy := young (5*sourceTime 0/2*‖embed (inverseVolumeAction p)‖) (2/5*‖embed v‖) η hη
  have he : (2/5*‖embed v‖)^2/(4*η)=‖embed v‖^2/(25*η) := by field_simp;ring
  rw [he] at hy
  have hv : ‖embed v‖^2=‖localResponse sharp m ell F z (inputSource g)‖^2 := by
    change ‖embed (localVector sharp m ell F z hz (inputSource g))‖^2=_
    rw [local_vector_embed]
  rw [←hv]
  change sourceTime 0*‖sourcePair (inverseVolumeAction p) v‖  ≤  _
  change (sourceTime 0)^2/4*coframeGram (inverseVolumeAction p)  ≤  _ at hpos
  have hb := mul_le_mul_of_nonneg_left (hf.trans hpos) hη.le
  change sourceTime 0*‖sourcePair (inverseVolumeAction p) v‖ ≤
    sourceTime 0*(‖embed (inverseVolumeAction p)‖*‖embed v‖) at hi
  nlinarith only [hi,hy,hb]

def reducedPrice (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) : ℝ :=
  η*mixedPrice sharp m ell F z hz g-(sourcePair (mixedState sharp m ell F z hz g)
    (reducedForce sharp m ell F z hz g)).im

def reducedBudget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (η : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (reducedPrice sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η)

private theorem remaining_reduced_point (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    SourceClockYukawaRadialNativeAbsorption.remainingPrice sharp m ell F z hz g (η/2)  ≤
      reducedPrice sharp m ell F z hz g η+‖localResponse sharp m ell F z (inputSource g)‖^2/(25*(η/2)) := by
  have h := congrArg (fun f => (sourcePair (mixedState sharp m ell F z hz g) f).im)
    (reduced_forcing_split sharp m ell F z hz g)
  simp only [sourcePair,map_add,inner_add_right,Complex.add_im] at h
  have hp := actual_local_force_price sharp m ell F z hz g (η/2) (by positivity)
  have hi := (neg_le_abs (sourcePair (mixedState sharp m ell F z hz g)
    (paidForce sharp m ell F z hz g)).im).trans (Complex.abs_im_le_norm _)
  unfold SourceClockYukawaRadialNativeAbsorption.remainingPrice reducedPrice
  change (sourcePair (mixedState sharp m ell F z hz g)
    (SourceClockYukawaRadialNativeAbsorption.remainingForce sharp m ell F z hz g)).im=
    (sourcePair (mixedState sharp m ell F z hz g) (paidForce sharp m ell F z hz g)).im+
    (sourcePair (mixedState sharp m ell F z hz g) (reducedForce sharp m ell F z hz g)).im at h
  linarith only [h,hp,hi]

private theorem remaining_reduced_integral (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    SourceClockYukawaRadialNativeAbsorption.remainingBudget sharp m ell F μ hμ g (η/2)  ≤
      reducedBudget sharp m ell F μ hμ g η+ENNReal.ofReal (1/(25*(η/2)))*
        (∫⁻ w : ℝ,ENNReal.ofReal (‖localResponse sharp m ell F (line μ w) (inputSource g)‖^2)) := by
  let E (w : ℝ) := ENNReal.ofReal (‖localResponse sharp m ell F (line μ w) (inputSource g)‖^2)
  let Q (w : ℝ) := ENNReal.ofReal (reducedPrice sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η)
  have hE : Measurable (fun w => ENNReal.ofReal (1/(25*(η/2)))*E w) :=
    (((local_response_continuous sharp m ell F μ hμ (inputSource g)).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  calc
    _  ≤  ∫⁻ w : ℝ,Q w+ENNReal.ofReal (1/(25*(η/2)))*E w := by
      apply lintegral_mono
      intro w
      have h := remaining_reduced_point sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g η hη
      apply (ENNReal.ofReal_le_ofReal h).trans
      have ha := ENNReal.ofReal_add_le (p := reducedPrice sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g η)
        (q := ‖localResponse sharp m ell F (line μ w) (inputSource g)‖^2/(25*(η/2)))
      have he (a : ℝ) : ENNReal.ofReal (a/(25*(η/2)))=ENNReal.ofReal (1/(25*(η/2)))*ENNReal.ofReal a := by
        rw [show a/(25*(η/2))=(1/(25*(η/2)))*a by ring,ENNReal.ofReal_mul (by positivity)]
      rw [he (‖localResponse sharp m ell F (line μ w) (inputSource g)‖^2)] at ha
      simpa only [Q,E] using ha
    _=_ := by rw [lintegral_add_right _ hE,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top];rfl

/-- The original common cutoff pays the entire inverse Hessian and fullX source term for both branches.
Only the joined rS source word and the complete three compression defects remain signed. -/
theorem actual_reduced_mu_remaining_budget (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (η : ℝ) (hη : 0 < η) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N  ≤  m → ∀ ell,m  ≤  ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        mixedNormEnergy sharp m ell F μ hμ g  ≤  ENNReal.ofReal ε+reducedBudget sharp m ell F μ hμ g η := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := SourceClockYukawaRadialNativeAbsorption.actual_mixed_mu_remaining_budget μ hμ g (η/2)
    (by positivity) (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := local_response_tail false μ hμ (inputSource g) (25*η*ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := local_response_tail true μ hμ (inputSource g) (25*η*ε/4) (by positivity)
  refine ⟨max N₀ (max N₁ N₂),fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m ((le_max_left _ _).trans hm) ell hml,
    h₁ m ((le_max_left _ _).trans ((le_max_right _ _).trans hm)) ell hml,
    h₂ m ((le_max_right _ _).trans ((le_max_right _ _).trans hm)) ell hml] with F hM hf ht sharp
  have hE : (∫⁻ w : ℝ,ENNReal.ofReal (‖localResponse sharp m ell F (line μ w) (inputSource g)‖^2))  ≤
      ENNReal.ofReal (25*η*ε/4) := by cases sharp <;> assumption
  have hconst : ENNReal.ofReal (1/(25*(η/2)))*ENNReal.ofReal (25*η*ε/4)=ENNReal.ofReal (ε/2) := by
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  have hb := remaining_reduced_integral sharp m ell F μ hμ g η hη
  have hpay := (mul_le_mul (le_refl (ENNReal.ofReal (1/(25*(η/2))))) hE zero_le zero_le).trans_eq hconst
  calc
    _  ≤  ENNReal.ofReal (ε/2)+SourceClockYukawaRadialNativeAbsorption.remainingBudget sharp m ell F μ hμ g (η/2) := hM sharp
    _  ≤  ENNReal.ofReal (ε/2)+(reducedBudget sharp m ell F μ hμ g η+ENNReal.ofReal (ε/2)) :=
      add_le_add (le_refl _) (hb.trans (add_le_add (le_refl _) hpay))
    _=ENNReal.ofReal ε+reducedBudget sharp m ell F μ hμ g η := by
      have hs : ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2)=ENNReal.ofReal ε := by
        rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      calc
        _=(ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2))+reducedBudget sharp m ell F μ hμ g η := by ac_rfl
        _=_ := by rw [hs]

end LowEnergy.SourceClockYukawaRadialHessianBudget
