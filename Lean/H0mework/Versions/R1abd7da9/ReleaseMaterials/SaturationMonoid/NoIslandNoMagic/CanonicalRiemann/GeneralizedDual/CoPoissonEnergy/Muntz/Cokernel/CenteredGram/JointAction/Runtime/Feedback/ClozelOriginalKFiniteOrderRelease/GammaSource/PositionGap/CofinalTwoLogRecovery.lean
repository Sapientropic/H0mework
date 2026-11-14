import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.ActionFirstMoment
import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CayleyLogClock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogHeadInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock.CofinalWindow

open BurnolPhysicalState Filter Finset Polynomial
open SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open BurnolPhysicalState.OriginalRSourceJointContact.CayleyLogClock
open BurnolPhysicalState.OriginalRSourceJointContact.LogAction
open CombConductor
open OriginalGamma.Source.RelativeConductorGapReadback
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open scoped BigOperators Polynomial Topology lp

open private log_pair_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private conductor_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private gamma_graph from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogStockAction
open private literal_raw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor

local notation "R" => burnolDirectRightResolventCLM
local notation "d" => sourceDamping
local notation "κ" => (-(1/2 : ℂ))

private theorem gamma_written (c : BurnolCompletedMellinCoordinate) (x : Whole) :
    gamma (advance c x) = R c (gamma x) := by
  have graph := gamma_graph (advance c x)
  rw [advance_field] at graph
  exact conductor_unique _ _ _ graph (actual_Gamma_R c _ _ (gamma_graph x))

private theorem log_written (c : BurnolCompletedMellinCoordinate) (x : Whole) :
    positionLog (advance c x) = R c (positionLog x) + κ • (((R c)^2) (field x)) := by
  have right : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have graph := (log_pairs (advance c x)).1
  rw [advance_field] at graph
  have generated := actual_direct_R_log (c.value/2) right _ _ (log_pairs x).1
  rw [directLogMoment_eq_half_square (c.value/2) right] at generated
  have unique := log_pair_unique _ _ _ graph generated
  change positionLog (advance c x) = R c (positionLog x) - (1/2 : ℂ) • R c (R c (field x)) at unique
  simpa only [pow_two, mul_apply_eq_comp, sub_eq_add_neg, neg_smul] using unique

private theorem inverse_read (x : Whole) :
    inverseLog x = fourierL2.symm (gamma x - positionLog x) := by
  change inverseLog x = fourierL2.symm (positionLog x + fourierL2 (inverseLog x) - positionLog x)
  rw [add_sub_cancel_left, LinearIsometryEquiv.symm_apply_apply]

private def seedStock : Whole :=
  let s := burnolPaCombApproximation 0
  ofLogs ⟨(s : BurnolL2), s.property.1.1, s.property.2⟩ seedPositionLog seedInverseLog
    actual_comb_seed_position_log actual_comb_seed_inverse_log

private theorem read_field_power (c : BurnolCompletedMellinCoordinate) (x : Whole) (n : Nat) :
    field (((advance c)^n) x) = ((R c)^n) (field x) := by
  simpa only [aeval_X_pow] using
    read_polynomial (advance c) (R c) field (advance_field c) ((X:ℂ[X])^n) x

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "A" => advance c
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "current" => actualAt observation nontrivial half depth

private theorem original_graph_power (ordinal : Nat) :
    current ordinal = (A^(m+(ordinal+2))) seedStock := by
  apply field_injective
  rw [read_field_power]
  change OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal =
    ((R c)^(m+(ordinal+2))) (burnolPaCombApproximation 0 : BurnolL2)
  exact literal_raw observation nontrivial half depth ordinal

private def preceding (ordinal : Nat) : Whole := (A^(m+(ordinal+1))) seedStock

private theorem preceding_writes (ordinal : Nat) :
    A (preceding observation half ordinal) = current ordinal := by
  rw [original_graph_power observation nontrivial half depth]
  have index : m+(ordinal+2) = (m+(ordinal+1))+1 := by omega
  change A ((A^(m+(ordinal+1))) seedStock) = _
  rw [index, pow_succ', mul_apply_eq_comp]

private theorem future_power (ordinal n : Nat) : (A^n) (current ordinal) = current (ordinal+n) := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self, Nat.add_zero]
  | succ n previous =>
    simp only [pow_succ', mul_apply_eq_comp, previous, actual_graph_next, Nat.add_assoc]

/-- Same weights and actual slots for the complete original closed graph. -/
def word (ordinal cutoff length : Nat) : Whole :=
  let p := smoothWeights (d c) cutoff (length+1)
  ∑ j ∈ range (p.natDegree+1), p.coeff j • current (ordinal+cutoff+j)

theorem actual_word_eval (ordinal cutoff length : Nat) :
    word observation nontrivial half depth ordinal cutoff length =
      aeval A (smoothPolynomial (d c) cutoff (length+1)) (current ordinal) := by
  rw [smooth_written A (d c) cutoff (length+1) (Nat.succ_pos _) (current ordinal)]
  simp only [word, future_power observation nontrivial half depth, Nat.add_assoc]

/-- The actual R writes every slot in the weighted word to its same literal successor. -/
theorem actual_word_next (ordinal cutoff length : Nat) :
    A (word observation nontrivial half depth ordinal cutoff length) =
      word observation nontrivial half depth (ordinal+1) cutoff length := by
  unfold word
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_smul, actual_graph_next]
  rw [show ordinal+cutoff+j+1 = ordinal+1+cutoff+j by omega]

private theorem length_budget_zero (parameter : BurnolCompletedMellinCoordinate) (b : ℝ) :
    Tendsto (fun n : Nat => b / (((n+1 : Nat) : ℝ) * d parameter)) atTop (𝓝 0) := by
  have large : Tendsto (fun n : Nat => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have limit : Tendsto (fun n : Nat => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp large
  simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_zero] using
    limit.const_mul (b * (d parameter)⁻¹)

private theorem range_limit (parameter : BurnolCompletedMellinCoordinate) (cutoff : Nat) (w : BurnolL2) :
    Tendsto (fun n : Nat => aeval (R parameter) (smoothPolynomial (d parameter) cutoff (n+1)) (R parameter w))
      atTop (𝓝 (R parameter w)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have bound (n : Nat) := (smooth_window_error (R parameter) (sourceCayley parameter) (d parameter) rfl
    (sourceCayley_norm parameter) (sourceDamping_pos parameter) cutoff (n+1) (Nat.succ_pos _) w 0).1
  exact squeeze_zero (fun _ => norm_nonneg _) bound
    (by simpa only [mul_div_assoc] using length_budget_zero parameter (((2:ℝ)^cutoff-1)*(2*‖w‖)))

private theorem moment_limit (parameter : BurnolCompletedMellinCoordinate) (cutoff : Nat) (x : BurnolL2) :
    Tendsto (fun n : Nat => aeval (R parameter) (derivative (smoothPolynomial (d parameter) cutoff (n+1))) (((R parameter)^2) x))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have bound (n : Nat) := (smooth_window_error (R parameter) (sourceCayley parameter) (d parameter) rfl
    (sourceCayley_norm parameter) (sourceDamping_pos parameter) cutoff (n+1) (Nat.succ_pos _) 0 x).2
  exact squeeze_zero (fun _ => norm_nonneg _) bound
    (by simpa only [mul_div_assoc] using
      length_budget_zero parameter (((cutoff : ℝ)*(2:ℝ)^(cutoff-1))*(4*(2*‖x‖))))

private theorem graph_limit {value : Nat → Whole} {x : Whole}
    (raw : Tendsto (fun n => field (value n)) atTop (𝓝 (field x)))
    (pos : Tendsto (fun n => positionLog (value n)) atTop (𝓝 (positionLog x)))
    (inv : Tendsto (fun n => inverseLog (value n)) atTop (𝓝 (inverseLog x))) :
    Tendsto value atTop (𝓝 x) := by
  apply tendsto_subtype_rng.mpr
  have logs : Tendsto (fun n => WithLp.toLp 2 (positionLog (value n), inverseLog (value n))) atTop
      (𝓝 (WithLp.toLp 2 (positionLog x, inverseLog x))) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BurnolL2 BurnolL2).symm.continuous.tendsto _).comp
      (pos.prodMk_nhds inv)
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ BurnolL2 LogSlots).symm.continuous.tendsto _).comp
    (raw.prodMk_nhds logs)

/-- The same finite tail recovers the complete two-log graph and its actual native successor. -/
theorem actual_cofinal_two_log_recovery (ordinal cutoff : Nat) :
    Tendsto (word observation nontrivial half depth ordinal cutoff) atTop (𝓝 (current ordinal)) ∧
    Tendsto (word observation nontrivial half depth (ordinal+1) cutoff) atTop (𝓝 (current (ordinal+1))) := by
  let x := current ordinal
  let w := preceding observation half ordinal
  let p (n : Nat) := smoothPolynomial (d c) cutoff (n+1)
  let fit (n : Nat) := aeval A (p n) x
  have prior : A w = x := preceding_writes observation nontrivial half depth ordinal
  have direct (read : Whole →L[ℂ] BurnolL2) (action : ∀ y, read (A y) = R c (read y)) :
      Tendsto (fun n => read (fit n)) atTop (𝓝 (read x)) := by
    have range : read x = R c (read w) := by rw [← prior, action]
    simpa only [fit, p, read_polynomial A (R c) read action, range] using range_limit c cutoff (read w)
  have ambient := direct field (advance_field c)
  have conductor := direct gamma (gamma_written c)
  have posImage : positionLog x = R c (positionLog w + κ • R c (field w)) := by
    rw [← prior, log_written, map_add, map_smul, pow_two, mul_apply_eq_comp]
  have posBase : Tendsto (fun n => aeval (R c) (p n) (positionLog x)) atTop (𝓝 (positionLog x)) := by
    rw [posImage]
    exact range_limit c cutoff (positionLog w + κ • R c (field w))
  have position : Tendsto (fun n => positionLog (fit n)) atTop (𝓝 (positionLog x)) := by
    have written := posBase.add ((moment_limit c cutoff (field x)).const_smul κ)
    simpa only [fit, p, read_polynomial_first_moment A (R c) field positionLog κ
      (advance_field c) (log_written c), smul_zero, add_zero] using written
  have inverse : Tendsto (fun n => inverseLog (fit n)) atTop (𝓝 (inverseLog x)) := by
    have read := (fourierL2.symm.continuous.tendsto (gamma x - positionLog x)).comp (conductor.sub position)
    change Tendsto (fun n => fourierL2.symm (gamma (fit n) - positionLog (fit n))) atTop
      (𝓝 (fourierL2.symm (gamma x - positionLog x))) at read
    simpa only [← inverse_read] using read
  have complete := graph_limit ambient position inverse
  have wordLimit : Tendsto (word observation nontrivial half depth ordinal cutoff) atTop (𝓝 (current ordinal)) := by
    change Tendsto (fun n => word observation nontrivial half depth ordinal cutoff n) atTop (𝓝 (current ordinal))
    simp only [actual_word_eval]
    exact complete
  have next := ((A).continuous.tendsto (current ordinal)).comp wordLimit
  change Tendsto (fun n => A (word observation nontrivial half depth ordinal cutoff n)) atTop
    (𝓝 (A (current ordinal))) at next
  refine ⟨wordLimit, ?_⟩
  simpa only [actual_graph_next, actual_word_next] using next

theorem actual_graph_in_closed_tail (ordinal cutoff : Nat) :
    current ordinal ∈ closure (Submodule.span ℂ
      (Set.range fun j : Nat => current (ordinal+cutoff+j)) : Set Whole) := by
  refine mem_closure_of_tendsto
    (actual_cofinal_two_log_recovery observation nontrivial half depth ordinal cutoff).1 ?_
  exact Eventually.of_forall fun length => by
    unfold word
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock.CofinalWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
