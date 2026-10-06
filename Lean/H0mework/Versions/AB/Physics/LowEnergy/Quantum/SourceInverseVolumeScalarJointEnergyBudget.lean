import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarCoefficientDecay
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralSpinTail
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarRetardedGram
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeNativeSeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarJointEnergyBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceMixedNativeReturn SourceNativeCutoffContact SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarRetardedGram SourceInverseNeutralSpinTail
open SourceScalarNativeComparison SourceScalarPositiveBulkWard PositiveScalarCoefficientDecay
open SourceInverseNeutralScalarCurrent PositiveScalarWeakBudget
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ContDiff ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (fullAction sharp g)=sourcePair (fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField z))
      (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z))
      (c z : ℂ) (f z)).symm

private theorem real_constant (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (a : ScalarIndex) :
    Commute (multiply c hc) (constantAction sharp (scalarDirection a).1) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarDirection a).1)
      (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarDirection a).1)
      (c z : ℂ) (f z)).symm

private theorem real_real (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) :
    Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem coefficient_pair (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (coefficient sharp a m ell q)=sourcePair (coefficient (!sharp) a m ell p) q := by
  have ht (b : Bool) : Commute (SourceMixedNativeReturn.thetaAction m ell)
      (constantAction b (scalarDirection a).1) := by
    rw [SourceMixedNativeReturn.thetaAction,←theta_action_polynomial]
    exact real_constant _ _ b a
  have hd (b : Bool) : Commute (derivativeAction a m ell) (fullAction b) :=
    real_full _ _ b
  have tp (f g : QuantumTest) : sourcePair f (SourceMixedNativeReturn.thetaAction m ell g)=
      sourcePair (SourceMixedNativeReturn.thetaAction m ell f) g := by
    rw [SourceMixedNativeReturn.thetaAction,←theta_action_polynomial]
    exact multiply_pair _ _ _ _
  rw [original_coefficient_split,original_coefficient_split]
  simp only [sourcePair,map_add,inner_add_right,inner_add_left]
  change sourcePair p (SourceMixedNativeReturn.thetaAction m ell (constantAction sharp (scalarDirection a).1 q))+
    sourcePair p (derivativeAction a m ell (fullAction sharp q))=_
  rw [tp,constant_pair,show derivativeAction a m ell= multiply _ _ from rfl,
    multiply_pair,full_pair]
  have h1 := congrArg (fun A : End => sourcePair (A p) q) (ht (!sharp)).eq
  have h2 := congrArg (fun A : End => sourcePair (A p) q) (hd (!sharp)).eq
  simp only [Module.End.mul_apply] at h1 h2
  exact congrArg₂ (·+·) h1.symm h2.symm

private theorem real_coefficient (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    Commute (multiply c hc) (coefficient sharp a m ell) := by
  have ht : Commute (multiply c hc) (SourceMixedNativeReturn.thetaAction m ell) := by
    rw [SourceMixedNativeReturn.thetaAction,←theta_action_polynomial]
    exact real_real _ _ _ _
  have hd : Commute (multiply c hc) (derivativeAction a m ell) := real_real _ _ _ _
  have he : coefficient sharp a m ell=SourceMixedNativeReturn.thetaAction m ell*
      constantAction sharp (scalarDirection a).1+derivativeAction a m ell*fullAction sharp := by
    apply LinearMap.ext
    intro f
    exact original_coefficient_split sharp a m ell f
  rw [he]
  exact (ht.mul_right (real_constant _ _ sharp a)).add_right (hd.mul_right (real_full _ _ sharp))

private theorem gram_bound (p q : ScalarIndex → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤
      (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ScalarIndex)
      (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem half_add_bound (a b : ℂ) :
    ‖(-Complex.I/2 : ℂ)*(a+b)‖^2 ≤ (1/2 : ℝ)*(‖a‖^2+‖b‖^2) := by
  have h := norm_add_le a b
  rw [norm_mul,mul_pow]
  norm_num
  nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]

/-- The original negative scalar weight stays on a zero-order leg. -/
def weightedCoefficient (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) : End :=
  multiply scalarWeight scalarWeight_smooth*coefficient sharp a m ell

def coefficientEnergy (sharp : Bool) (m ell : ℕ) (f : QuantumTest) : ℝ :=
  ∑ a : ScalarIndex,‖embed (weightedCoefficient sharp a m ell f)‖^2

def jointBudget (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) : ℝ :=
  (1/2 : ℝ)*(nativeScalarEnergy p*coefficientEnergy sharp m ell q+
    coefficientEnergy (!sharp) m ell p*nativeScalarEnergy q)

/-- Exact weak form: both momenta act on their own test, and the dual of Z has positive sign. -/
theorem original_scalar_pair (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (scalarOnlyCurrent sharp m ell q)=(-Complex.I/2 : ℂ)*
      ((∑ a : ScalarIndex,sourcePair (covariantMomentum (scalarDirection a) p)
        (weightedCoefficient sharp a m ell q))+
      ∑ a : ScalarIndex,sourcePair (weightedCoefficient (!sharp) a m ell p)
        (covariantMomentum (scalarDirection a) q)) := by
  have he := congrArg (fun A : End => sourcePair p (A q)) (original_scalar_two_leg_join sharp m ell)
  change sourcePair p (scalarOnlyCurrent sharp m ell q)=_ at he
  rw [he]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply,
    sourcePair,map_smul,map_sum,map_add,inner_smul_right,inner_sum,inner_add_right]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  change sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a)
      (multiply scalarWeight scalarWeight_smooth (coefficient sharp a m ell q)))+
    sourcePair p (coefficient sharp a m ell (multiply scalarWeight scalarWeight_smooth
      (covariantMomentum (scalarDirection a) q)))=_
  rw [GaussNativeForm.adjoint_pair,coefficient_pair]
  exact congrArg₂ (·+·) rfl (multiply_pair _ _ _ _)

/-- Native seventy-row Cauchy pays the complete scalar/radial first current. -/
theorem original_scalar_joint_energy (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    ‖sourcePair p (scalarOnlyCurrent sharp m ell q)‖^2≤jointBudget sharp m ell p q := by
  rw [original_scalar_pair]
  exact (half_add_bound _ _).trans (mul_le_mul_of_nonneg_left
    (add_le_add (gram_bound _ _) (gram_bound _ _)) (by norm_num))

/-- These zero-order source readers contain no cutoff and retain the signed scalar weight. -/
def sourceMoment (sharp : Bool) (f : QuantumTest) : ℝ :=
  ∑ a : ScalarIndex,
    (‖embed (GaussYukawaOperator.radiusAction
      (constantAction sharp (scalarDirection a).1 (multiply scalarWeight scalarWeight_smooth f)))‖^2+
      4*‖embed (fullAction sharp (multiply scalarWeight scalarWeight_smooth f))‖^2)

private theorem coefficient_energy_decay (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (f : QuantumTest) :
    coefficientEnergy sharp m ell f≤(2/(m+2 : ℝ)^2)*sourceMoment sharp f := by
  rw [sourceMoment,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have he := congrArg (fun A : End => A f) (real_coefficient scalarWeight scalarWeight_smooth sharp a m ell).eq
  change weightedCoefficient sharp a m ell f=coefficient sharp a m ell (multiply scalarWeight scalarWeight_smooth f) at he
  change ‖embed (weightedCoefficient sharp a m ell f)‖^2≤_
  rw [he]
  exact original_coefficient_energy sharp a m ell hle _

def sourceJointPrice (sharp : Bool) (p q : QuantumTest) : ℝ :=
  nativeScalarEnergy p*sourceMoment sharp q+sourceMoment (!sharp) p*nativeScalarEnergy q

/-- The entire first-order scalar current gains the generated cutoff square,
with no derivative of theta on either momentum leg. -/
theorem original_scalar_source_decay (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (p q : QuantumTest) :
    ‖sourcePair p (scalarOnlyCurrent sharp m ell q)‖^2≤
      (1/(m+2 : ℝ)^2)*sourceJointPrice sharp p q := by
  apply (original_scalar_joint_energy sharp m ell p q).trans
  have h1 := mul_le_mul_of_nonneg_left (coefficient_energy_decay sharp m ell hle q)
    (show 0≤nativeScalarEnergy p by unfold nativeScalarEnergy;positivity)
  have h2 := mul_le_mul_of_nonneg_right (coefficient_energy_decay (!sharp) m ell hle p)
    (show 0≤nativeScalarEnergy q by unfold nativeScalarEnergy;positivity)
  exact (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num : (0:ℝ)≤1/2)).trans_eq (by
    unfold sourceJointPrice
    ring)

private theorem left_energy (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    nativeScalarEnergy (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)=
      signedNativeCost F z hz g k 1 0 := by
  rw [actual_joint_native_cost,jointState,one_smul,zero_smul,add_zero]
  rfl

private theorem right_energy (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    nativeScalarEnergy (state F z hz g)=signedNativeCost F z hz g k 0 1 := by
  rw [actual_joint_native_cost,jointState,zero_smul,one_smul,zero_add]
  rfl

/-- The price is generated by the complete signed H/non-scalar/defect equations
at the actual advanced and retarded states. It contains no radial cutoff. -/
def signedSourcePrice (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) : ℝ :=
  signedNativeCost F z hz g k 1 0*sourceMoment sharp (state F z hz g)+
    sourceMoment (!sharp) (state F (star z)
      (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)*
    signedNativeCost F z hz g k 0 1

/-- The actual bilateral response consumes the original source energy equations,
without identifying its two independent dual legs. -/
theorem actual_scalar_signed_decay (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    ‖inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g
      (scalarOnlyCurrent sharp m ell)*finiteResolvent F z) (g : H))‖^2≤
      (1/(m+2 : ℝ)^2)*signedSourcePrice sharp F z hz g k := by
  rw [SourceInverseDefectCurrentResponse.actual_read_pair F z hz]
  have h := original_scalar_source_decay sharp m ell hle
    (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (state F z hz g)
  simpa only [sourceJointPrice,left_energy F z hz g k,right_energy F z hz g k,signedSourcePrice] using h

open SourceInverseCoframeNativeSeed

def nativePrice (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) : QuantumTest → QuantumTest → ℕ → ℝ
  | f,k,0 => signedSourcePrice sharp F z hz (coreEquiv f) (coreEquiv k)
  | f,k,n+1 => 2*(nativePrice sharp F z hz (SourceGaugeCoframeJets.K f) k n+
      nativePrice sharp F z hz f (SourceGaugeCoframeJets.K k) n)

private theorem two_sub_square (a b : ℂ) : ‖-a-b‖^2≤2*(‖a‖^2+‖b‖^2) := by
  have h := norm_sub_le (-a) b
  rw [norm_neg] at h
  nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (-a-b),norm_nonneg a,norm_nonneg b]

/-- Every fixed coframe order uses the original differentiated inputs, with a
single cutoff square and no cutoff in the remaining source price. -/
theorem actual_native_scalar_decay (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (F : Index)
    (z : ℂ) (hz : z.im≠0) (n : ℕ) (f k : QuantumTest) :
    ‖nativeResponse F z hz (scalarOnlyCurrent sharp m ell) f k n‖^2≤
      (1/(m+2 : ℝ)^2)*nativePrice sharp F z hz f k n := by
  induction n generalizing f k with
  | zero =>
    have h := actual_scalar_signed_decay sharp m ell hle F z hz (coreEquiv f) (coreEquiv k)
    rw [SourceInverseDefectCurrentResponse.actual_read_pair F z hz] at h
    exact h
  | succ n ih =>
    rw [nativeResponse,nativePrice]
    exact (two_sub_square _ _).trans ((mul_le_mul_of_nonneg_left
      (add_le_add (ih _ _) (ih _ _)) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))

/-- One original finite source-prefix event works before all radial windows,
frequencies and left test inputs. -/
theorem actual_coframe_scalar_decay (sharp : Bool) (n : ℕ) (f : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (seed : diagonal.domain) (m ell : ℕ) (_hle : m≤ell)
      (μ : ℝ) (hμ : 0<μ) (w : ℝ) (k : QuantumTest),
      ‖SourceInverseCoframeCompressionBudget.coframeProfile F seed (line μ w) (scalarOnlyCurrent sharp m ell) f k n 0‖^2≤
        (1/(m+2 : ℝ)^2)*nativePrice sharp F (line μ w) (by simpa only [line_im] using hμ.ne') f k n := by
  filter_upwards [actual_native_current_return n f] with F hF seed m ell hle μ hμ w k
  rw [hF seed _ μ hμ w k]
  exact actual_native_scalar_decay sharp m ell hle F _ _ n f k

/-- The original mass normalization and the whole frequency line consume the
same source-generated price. No uniform-in-F moment bound is assumed. -/
theorem actual_native_scalar_full_frequency (sharp : Bool) (m ell : ℕ) (hle : m≤ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (n : ℕ) (f k : QuantumTest) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖(SourceScalarForceBudget.oscillatorMass : ℂ)⁻¹*
      nativeResponse F (line μ w) (by simpa only [line_im] using hμ.ne')
        (scalarOnlyCurrent sharp m ell) f k n‖^2))≤
      ∫⁻ w : ℝ,ENNReal.ofReal ((SourceScalarForceBudget.oscillatorMass : ℝ)⁻¹^2*
        (1/(m+2 : ℝ)^2)*nativePrice sharp F (line μ w)
          (by simpa only [line_im] using hμ.ne') f k n) := by
  apply lintegral_mono
  intro w
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,←abs_inv,sq_abs]
  exact (mul_le_mul_of_nonneg_left (actual_native_scalar_decay sharp m ell hle F _ _ n f k)
    (sq_nonneg _)).trans_eq (by ring)

end LowEnergy.SourceScalarJointEnergyBudget
