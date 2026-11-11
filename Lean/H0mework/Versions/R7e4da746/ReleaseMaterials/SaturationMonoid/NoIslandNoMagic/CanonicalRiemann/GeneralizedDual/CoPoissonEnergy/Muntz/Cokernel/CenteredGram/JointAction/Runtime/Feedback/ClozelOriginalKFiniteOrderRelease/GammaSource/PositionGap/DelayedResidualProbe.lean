import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.ScaledPolynomialProbe
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedWordSeparation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe

open BurnolPhysicalState Finset Polynomial
open scoped BigOperators Polynomial InnerProductSpace

open private anchor_right observed_resolvent_word historyPrefix historyPrefix_eval from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedWordSeparation
open private observed_jet from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers
open private fixed_analytic from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierParameterGerm
open private sourcePrices actual_mixture_price from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private raw_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback

local notation "R" => burnolDirectRightResolventCLM
local notation "S" => burnolDirectRightResolvent
local notation "seed" => (burnolPaCombApproximation 0:BurnolL2)

abbrev Read := BurnolL2 →L[ℂ] ℂ

def reader (c : BurnolCompletedMellinCoordinate) : Read :=
  innerSL ℂ (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2))

def word (c : BurnolCompletedMellinCoordinate) (base count : Nat)
    (a : Fin (count+1) → ℂ) : BurnolL2 :=
  ∑ j, a j • ((R c)^(base+j.val)) seed

private def term (count : Nat) (a : Fin (count+1) → ℂ) (j : Fin (count+1)) : ℂ[X] :=
  C (a j)*X^(count-j.val)

private def denominator (count : Nat) (a : Fin (count+1) → ℂ) : ℂ[X] :=
  ∑ j, term count a j

private def numerator (c : BurnolCompletedMellinCoordinate) (base count : Nat)
    (a : Fin (count+1) → ℂ) : ℂ[X] :=
  ∑ j, term count a j * historyPrefix (reader c) c (base+j.val)

private theorem history_coeff (read : Read) (c : BurnolCompletedMellinCoordinate) (length slot : Nat) :
    (historyPrefix read c length).coeff slot =
      if slot < length then read (((R c)^(slot+1)) seed) else 0 := by
  classical
  simp [historyPrefix,finsetSum_coeff]

private theorem term_coeff (c : BurnolCompletedMellinCoordinate) (base count : Nat)
    (a : Fin (count+1) → ℂ) (j : Fin (count+1)) (slot : Nat) :
    (term count a j * historyPrefix (reader c) c (base+j.val)).coeff slot =
      a j * (if count-j.val ≤ slot then
        if slot-(count-j.val) < base+j.val then
          reader c (((R c)^(slot-(count-j.val)+1)) seed) else 0 else 0) := by
  rw [term,mul_assoc,coeff_C_mul,coeff_X_pow_mul',history_coeff]

private theorem numerator_degree (c : BurnolCompletedMellinCoordinate) (base count : Nat)
    (a : Fin (count+1) → ℂ) :
    (numerator c base count a).degree < ((base+count+1 : Nat) : WithBot Nat) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro slot beyond
  rw [numerator,finsetSum_coeff]
  apply sum_eq_zero
  intro j _
  have index : j.val ≤ count := Nat.le_of_lt_succ j.isLt
  have large : ¬ slot-(count-j.val) < base+j.val := by omega
  rw [term_coeff]
  by_cases bound : count-j.val ≤ slot <;> simp [bound,large]

private theorem shifted_right (c : BurnolCompletedMellinCoordinate) {x : ℝ} (positive : 0 ≤ x) :
    (1/4 : ℝ) < (c.value/2+(x:ℂ)).re := by
  simp only [Complex.add_re,Complex.ofReal_re]
  linarith [anchor_right c]

private def shiftedAction (c : BurnolCompletedMellinCoordinate) (x : ℝ) (nonnegative : 0 ≤ x) :
    BurnolL2 →ₗ[ℂ] BurnolL2 where
  toFun := S (c.value/2+(x:ℂ))
  map_add' := fun u v => by
    have sum := burnolDirectRightResolvent_sub (c.value/2+(x:ℂ)) (shifted_right c nonnegative) u (-v)
    have neg : S (c.value/2+(x:ℂ)) (-v) = -S (c.value/2+(x:ℂ)) v := by
      simpa only [neg_one_smul] using burnolDirectRightResolvent_smul (c.value/2+(x:ℂ)) (-1) v
    simpa only [sub_neg_eq_add,neg] using sum
  map_smul' := burnolDirectRightResolvent_smul (c.value/2+(x:ℂ))

def probedWord (c : BurnolCompletedMellinCoordinate) (base count : Nat)
    (a : Fin (count+1) → ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^(base+count) * reader c (S (c.value/2+(x:ℂ)) (word c base count a))

/-- Each probe is the existing source resolvent equation on the complete finite original word. -/
theorem actual_probe_equation (c : BurnolCompletedMellinCoordinate) (base count : Nat)
    (a : Fin (count+1) → ℂ) {x : ℝ} (nonnegative : 0 ≤ x) :
    probedWord c base count a x =
      (denominator count a).eval (x:ℂ) * reader c (S (c.value/2+(x:ℂ)) seed) -
        (numerator c base count a).eval (x:ℂ) := by
  let A := shiftedAction c x nonnegative
  let h := reader c (S (c.value/2+(x:ℂ)) seed)
  change (x:ℂ)^(base+count) * reader c (A (word c base count a)) = _
  simp only [word,map_sum,map_smul,smul_eq_mul,mul_sum]
  calc
    _ = ∑ j : Fin (count+1), (term count a j).eval (x:ℂ) *
        (h-(historyPrefix (reader c) c (base+j.val)).eval (x:ℂ)) := by
      apply sum_congr rfl
      intro j _
      have index : count-j.val+(base+j.val) = base+count := by
        have bound : j.val ≤ count := Nat.le_of_lt_succ j.isLt
        omega
      have action := observed_resolvent_word (reader c) c (x:ℂ) (shifted_right c nonnegative) seed (base+j.val)
      change (x:ℂ)^(base+j.val) * reader c (A (((R c)^(base+j.val)) seed)) = _ at action
      rw [← historyPrefix_eval] at action
      rw [← index,pow_add]
      simp only [term,eval_mul,eval_C,eval_X_pow]
      dsimp only [h]
      linear_combination ((a j)*(x:ℂ)^(count-j.val))*action
    _ = _ := by
      simp only [h,denominator,numerator,eval_finsetSum,eval_mul,mul_sub,sum_sub_distrib,sum_mul]

private def amplitude (c : BurnolCompletedMellinCoordinate) (count : Nat)
    (a : Fin (count+1) → ℂ) : ℝ :=
  (∑ j, ‖a j‖) * delayBudget c

private theorem amplitude_nonneg (c : BurnolCompletedMellinCoordinate) (count : Nat)
    (a : Fin (count+1) → ℂ) : 0 ≤ amplitude c count a :=
  mul_nonneg (sum_nonneg fun _ _ => norm_nonneg _) (delayBudget_nonneg c)

private theorem tail_bound (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (base count : Nat) (a : Fin (count+1) → ℂ) {x : ℝ} (one : 1 ≤ x) :
    ‖(denominator count a).eval (x:ℂ) * reader c (S (c.value/2+(x:ℂ)) seed)‖ ≤
      amplitude c count a * x^(base+count) * Real.exp (-x*combDelay) := by
  have nonnegative : 0 ≤ x := zero_le_one.trans one
  have bounded : ‖(denominator count a).eval (x:ℂ)‖ ≤ (∑ j, ‖a j‖) * x^(base+count) := by
    simp only [denominator,term,eval_finsetSum,eval_mul,eval_C,eval_X_pow]
    calc
      _ ≤ ∑ j : Fin (count+1), ‖a j * (x:ℂ)^(count-j.val)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin (count+1), ‖a j‖*x^(base+count) := by
        apply sum_le_sum
        intro j _
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg nonnegative]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one (by omega)) (norm_nonneg _)
      _ = _ := (sum_mul _ _ _).symm
  rw [norm_mul]
  have decay := actual_delayed_rightward_price c zero nonnegative
  change ‖reader c (S (c.value/2+(x:ℂ)) seed)‖ ≤ _ at decay
  calc
    _ ≤ ((∑ j, ‖a j‖) * x^(base+count)) * (Real.exp (-x*combDelay) * delayBudget c) :=
      mul_le_mul bounded decay (norm_nonneg _) (by positivity)
    _ = _ := by unfold amplitude; ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

def xiOpening : ℂ := reader c (((R c)^m) seed)

include nontrivial in
private theorem price_below_opening (slot : Nat) (before : slot+1 < m) :
    reader c (((R c)^(slot+1)) seed) = 0 := by
  have order := actual_fixed_price_order observation nontrivial half
  have vanishes := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (fixed_analytic c c)).mp
    (show ((m-1 : Nat):ℕ∞) ≤ analyticOrderAt (fixedPrice c) (c).value by rw [order])
    slot (by omega)
  have jet := observed_jet (reader c) c seed slot
  change iteratedDeriv slot (fixedPrice c) (c).value =
    ((slot.factorial : ℂ)/(2:ℂ)^slot) • reader c (((R c)^(slot+1)) seed) at jet
  rw [jet] at vanishes
  exact (smul_eq_zero.mp vanishes).resolve_left
    (div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (pow_ne_zero _ (by norm_num)))

include nontrivial in
private theorem first_numerator_coefficient (base count : Nat) (a : Fin (count+1) → ℂ)
    (reachable : m ≤ base+count) :
    (numerator c base count a).coeff (m-1) = a (Fin.last count)*xiOpening observation half := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have next : m-1+1=m := by omega
  rw [numerator,finsetSum_coeff,Fin.sum_univ_castSucc]
  have older : (∑ j : Fin count,
      (term count a j.castSucc * historyPrefix (reader c) c (base+j.castSucc.val)).coeff (m-1)) = 0 := by
    apply sum_eq_zero
    intro j _
    rw [term_coeff]
    have before : j.val < count := j.isLt
    simp only [Fin.val_castSucc]
    split_ifs with h inside
    · rw [price_below_opening observation nontrivial half _ (by omega),mul_zero]
    · exact mul_zero _
    · exact mul_zero _
  rw [older,zero_add,term_coeff]
  simp only [Fin.val_last,Nat.sub_self,zero_le,if_true,Nat.sub_zero,
    if_pos (show m-1 < base+count by omega),next,xiOpening]

def probeScale (base count : Nat) (a : Fin (count+1) → ℂ) : ℝ :=
  SourceGeneratedPolynomialProbe.scale (base+count) (m-1)
    (amplitude c count a) combDelay (a (Fin.last count)*xiOpening observation half)

def weightedProbe (base count : Nat) (a : Fin (count+1) → ℂ) : ℂ :=
  SourceGeneratedPolynomialProbe.extract (base+count+1) (m-1) (fun i =>
    probedWord c base count a (probeScale observation half base count a * SourceGeneratedPolynomialProbe.node i))

include nontrivial in
/-- The original Xi first price pays a finite margin on a word with a nonzero highest coefficient. -/
theorem actual_word_probe_margin (base count : Nat) (a : Fin (count+1) → ℂ)
    (reachable : m ≤ base+count) (leading : a (Fin.last count) ≠ 0) :
    ‖a (Fin.last count)*xiOpening observation half‖/2 ≤
      ‖weightedProbe observation half base count a‖ := by
  have coefficient := first_numerator_coefficient observation nontrivial half base count a reachable
  have opening : xiOpening observation half ≠ 0 :=
    FixedFourierKFeedback.original_opening_price_ne_zero observation nontrivial half
  have alive : (numerator c base count a).coeff (m-1) ≠ 0 := by
    rw [coefficient]
    exact mul_ne_zero leading opening
  have source := SourceGeneratedPolynomialProbe.finite_residue_margin (base+count) (m-1)
    (numerator c base count a) (numerator_degree c base count a) alive
    (amplitude c count a) combDelay (amplitude_nonneg c count a) combDelay_pos
    (fun x => (denominator count a).eval (x:ℂ) * reader c (S ((c).value/2+(x:ℂ)) seed))
    (fun _ one => tail_bound c observation.mathlibZero base count a one)
  dsimp only at source
  rw [coefficient] at source
  let L := probeScale observation half base count a
  have one : 1 ≤ L := SourceGeneratedPolynomialProbe.scale_ge_one (base+count) (m-1)
    (amplitude_nonneg c count a) combDelay_pos _
  let x (i : Fin (base+count+1)) := L*SourceGeneratedPolynomialProbe.node i
  have readEq : (fun i => probedWord c base count a (x i)) =
      (fun i => (denominator count a).eval (x i:ℂ) * reader c (S ((c).value/2+(x i:ℂ)) seed) -
        (numerator c base count a).eval (x i:ℂ)) := by
    funext i
    apply actual_probe_equation
    exact mul_nonneg (zero_le_one.trans one) (by unfold SourceGeneratedPolynomialProbe.node; positivity)
  change ‖a (Fin.last count)*xiOpening observation half‖/2 ≤
    ‖SourceGeneratedPolynomialProbe.extract (base+count+1) (m-1) (fun i => probedWord c base count a (x i))‖
  rw [readEq]
  exact source

namespace Sparse
export SourceGeneratedFiniteGram.CofinalRecord (priorFit birthResidual)
end Sparse

local notation "source" => sourcePrices observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth

private def oldFit (start count : Nat) : Record.Values count :=
  Sparse.priorFit (source start) (schedule start count).val

/-- The residual coefficients are the old exact fit with a literal unit birth. -/
def fittedCoefficients (start count : Nat) : Fin (count+1) → ℂ :=
  Fin.snoc (fun j => -oldFit observation nontrivial half depth start count j) 1

def probeBase (start cutoff : Nat) : Nat := m+(start+cutoff+2)

include nontrivial in
theorem actual_fitted_probe_margin (start count cutoff : Nat) :
    ‖xiOpening observation half‖/2 ≤
      ‖weightedProbe observation half (probeBase observation start cutoff) count
        (fittedCoefficients observation nontrivial half depth start count)‖ := by
  let a := fittedCoefficients observation nontrivial half depth start count
  have monic : a (Fin.last count) = 1 := by simp [a,fittedCoefficients]
  have margin := actual_word_probe_margin observation nontrivial half (probeBase observation start cutoff) count a
    (by unfold probeBase; omega) (by rw [monic]; exact one_ne_zero)
  rw [monic,one_mul] at margin
  exact margin

private theorem fitted_word (start count cutoff : Nat) :
    word c (probeBase observation start cutoff) count
        (fittedCoefficients observation nontrivial half depth start count) =
      ((R c)^cutoff) ((∑ j : Fin count, (-oldFit observation nontrivial half depth start count j) •
        raw (start+j.val)) + raw (start+count)) := by
  have powered (j : Nat) :
      ((R c)^cutoff) (raw (start+j)) = ((R c)^(probeBase observation start cutoff+j)) seed := by
    rw [raw_power,← mul_apply_eq_comp,← pow_add]
    rw [show cutoff+(m+(start+j+2)) = probeBase observation start cutoff+j by unfold probeBase; omega]
  simp only [word,Fin.sum_univ_castSucc,fittedCoefficients,Fin.snoc_castSucc,Fin.snoc_last,
    Fin.val_castSucc,Fin.val_last,one_smul,map_add,map_sum,map_smul,powered]

/-- Every unshifted price of the probed field is the old decoder's actual residual at that later address. -/
theorem actual_fitted_residual_price (start count cutoff time : Nat) :
    nativePriceAt observation half
        (word c (probeBase observation start cutoff) count
          (fittedCoefficients observation nontrivial half depth start count)) time =
      Sparse.birthResidual (source start) (schedule start count).val (cutoff+time) := by
  let fit := oldFit observation nontrivial half depth start count
  let a : Record.Values count := -fit
  let field : BurnolL2 := (∑ j : Fin count, a j • raw (start+j.val)) + (1 : ℂ) • raw (start+count)
  rw [fitted_word]
  have lifted :
      nativePriceAt observation half (((R c)^cutoff) field) time =
      nativePriceAt observation half field (cutoff+time) := by
    unfold nativePriceAt
    rw [← mul_apply_eq_comp,← pow_add,Nat.add_comm time cutoff]
  have price := congrFun (actual_mixture_price observation nontrivial half depth start count a 1) (cutoff+time)
  change nativePriceAt observation half field (cutoff+time) = _ at price
  have fieldEq :
      field = (∑ j : Fin count, (-fit j) • raw (start+j.val)) + raw (start+count) := by
    simp only [field,a,WithLp.ofLp_neg,Pi.neg_apply,one_smul]
  rw [← fieldEq,lifted,price]
  simp only [Record.withBirth,Record.replay,Sparse.birthResidual,a,fit,oldFit,
    WithLp.ofLp_neg,Pi.neg_apply,neg_mul,sum_neg_distrib,one_mul,sub_eq_add_neg,add_comm]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
