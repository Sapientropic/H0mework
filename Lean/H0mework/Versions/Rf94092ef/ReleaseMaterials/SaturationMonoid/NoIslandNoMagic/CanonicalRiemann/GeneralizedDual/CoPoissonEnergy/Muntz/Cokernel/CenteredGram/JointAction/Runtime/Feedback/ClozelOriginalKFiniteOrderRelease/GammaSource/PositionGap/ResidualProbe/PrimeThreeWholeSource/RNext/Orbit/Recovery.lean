import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit.Consumer
import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalTwoLogRecovery

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit

open Filter Finset Polynomial BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Install
open scoped BigOperators Polynomial Topology InnerProductSpace

open private range_limit moment_limit graph_limit inverse_read log_written gamma_written from
  H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalTwoLogRecovery
open private gap_width from
  H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.Consumer
open private gap_restrict from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.ClockReconstruction

namespace Prior
export OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer
  (fullSource full_source_value actual_gap)
end Prior

private def stockOfSource (source : CS.Source) (gap : source.value ∈ locallyConstantFace Math.scale⁻¹) :
    Whole :=
  ofLogs ⟨source.value, gap_restrict gap_width.le gap, mem_evenL2ClosedFace_iff.mpr source.even⟩
    source.position source.inverse source.position_graph source.inverse_graph

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ j : Nat, observation.coordinate = -2 * (j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth width start : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R₀" => burnolDirectRightResolventCLM c
local notation "V" => Orbit.value observation nontrivial half depth width start
local notation "X" => fullSource observation nontrivial half depth start
local notation "A" => advance c
local notation "δ" => sourceDamping c

/-- The existing closed graph reads the field and both logs of this literal born. -/
def stock (k : Nat) : Whole :=
  stockOfSource (X k) (by
    rw [actual_full_source observation nontrivial half depth width start k]
    exact (actual_gap_and_live observation nontrivial half depth width start k).1)

local notation "W" => stock observation nontrivial half depth width start

theorem stock_field (k : Nat) : field (W k) = V k :=
  actual_full_source observation nontrivial half depth width start k

theorem stock_logs (k : Nat) :
    positionLog (W k) = (X k).position ∧ inverseLog (W k) = (X k).inverse ∧
      gamma (W k) = (X k).gamma := ⟨rfl, rfl, rfl⟩

/-- The original writer's next is the next in the existing closed graph. -/
theorem actual_stock_next (k : Nat) : A (W k) = W (k+1) := by
  apply field_injective
  rw [advance_field, stock_field, stock_field, actual_direct_R observation nontrivial half depth width start k]

private theorem stock_has_predecessor (k : Nat) : ∃ prior : Whole, W k = A prior := by
  cases k with
  | zero =>
    let original := Prior.fullSource observation nontrivial half depth start
    have gap : original.value ∈ locallyConstantFace Math.scale⁻¹ := by
      unfold original
      rw [Prior.full_source_value observation nontrivial half depth start width]
      exact Prior.actual_gap observation nontrivial half depth start width
    let prior := stockOfSource original gap
    refine ⟨prior, field_injective ?_⟩
    rw [stock_field, advance_field, initial_value, ← First.full_source_value observation nontrivial half depth width start]
    exact Material.resolve_value c original
  | succ k => exact ⟨W k, (actual_stock_next observation nontrivial half depth width start k).symm⟩

private theorem actual_stock_power (k n : Nat) : (A^n) (W k) = W (k+n) := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self, Nat.add_zero]
  | succ n previous =>
    rw [pow_succ', mul_apply_eq_comp, previous, actual_stock_next, Nat.add_assoc]

/-- The existing weights are applied only to the actual born stock at the listed later slots. -/
def finiteTail (k cutoff length : Nat) : Whole :=
  let p := smoothWeights δ cutoff (length+1)
  ∑ j ∈ range (p.natDegree+1), p.coeff j • W (k+cutoff+j)

local notation "tail" => finiteTail observation nontrivial half depth width start

theorem actual_finite_tail_next (k cutoff length : Nat) :
    A (tail k cutoff length) = tail (k+1) cutoff length := by
  unfold finiteTail
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_smul, actual_stock_next]
  rw [show k+cutoff+j+1 = k+1+cutoff+j by omega]

private theorem finite_tail_eval (k cutoff length : Nat) :
    tail k cutoff length = aeval A (smoothPolynomial δ cutoff (length+1)) (W k) := by
  rw [smooth_written A δ cutoff (length+1) (Nat.succ_pos _) (W k)]
  simp only [finiteTail, actual_stock_power, Nat.add_assoc]

private theorem tail_limit (k cutoff : Nat) : Tendsto (tail k cutoff) atTop (𝓝 (W k)) := by
  let x := W k
  let p (n : Nat) := smoothPolynomial δ cutoff (n+1)
  let fit (n : Nat) := aeval A (p n) x
  obtain ⟨prior, source⟩ := stock_has_predecessor observation nontrivial half depth width start k
  change x = A prior at source
  have direct (read : Whole →L[ℂ] BurnolL2) (action : ∀ y, read (A y) = R₀ (read y)) :
      Tendsto (fun n => read (fit n)) atTop (𝓝 (read x)) := by
    have range : read x = R₀ (read prior) := by rw [source, action]
    simpa only [fit, p, read_polynomial A R₀ read action, range] using range_limit c cutoff (read prior)
  have ambient := direct field (advance_field c)
  have conductor := direct gamma (gamma_written c)
  have posImage : positionLog x = R₀ (positionLog prior - (1/2 : ℂ) • R₀ (field prior)) := by
    rw [source, log_written, map_sub, map_smul, pow_two, mul_apply_eq_comp, sub_eq_add_neg, neg_smul]
  have posBase : Tendsto (fun n => aeval R₀ (p n) (positionLog x)) atTop (𝓝 (positionLog x)) := by
    rw [posImage]
    exact range_limit c cutoff (positionLog prior - (1/2 : ℂ) • R₀ (field prior))
  have position : Tendsto (fun n => positionLog (fit n)) atTop (𝓝 (positionLog x)) := by
    have written := posBase.add ((moment_limit c cutoff (field x)).const_smul (-(1/2 : ℂ)))
    simpa only [fit, p, read_polynomial_first_moment A R₀ field positionLog (-(1/2 : ℂ))
      (advance_field c) (log_written c), smul_zero, add_zero] using written
  have inverse : Tendsto (fun n => inverseLog (fit n)) atTop (𝓝 (inverseLog x)) := by
    have read := (fourierL2.symm.continuous.tendsto (gamma x - positionLog x)).comp (conductor.sub position)
    change Tendsto (fun n => fourierL2.symm (gamma (fit n) - positionLog (fit n))) atTop
      (𝓝 (fourierL2.symm (gamma x - positionLog x))) at read
    simpa only [← inverse_read] using read
  exact (graph_limit ambient position inverse).congr' (Eventually.of_forall fun n =>
    (finite_tail_eval observation nontrivial half depth width start k cutoff n).symm)

/-- Every later actual window recovers this born and the next complete born. -/
theorem actual_cofinal_stock_recovery (k cutoff : Nat) :
    Tendsto (tail k cutoff) atTop (𝓝 (W k)) ∧ Tendsto (tail (k+1) cutoff) atTop (𝓝 (W (k+1))) :=
  ⟨tail_limit observation nontrivial half depth width start k cutoff,
    tail_limit observation nontrivial half depth width start (k+1) cutoff⟩

/-- The original K reads the next recovered physical field against the actual prior whole field. -/
theorem actual_cofinal_K_price (k cutoff : Nat) :
    let K : BurnolL2 := burnolCompletedMellinRieszVector c
    Tendsto (fun n => inner ℂ K (field (physical (tail (k+1) cutoff n)))) atTop
      (𝓝 (inner ℂ ((R₀).adjoint K) (V k))) := by
  let K : BurnolL2 := burnolCompletedMellinRieszVector c
  let read : Whole →L[ℂ] ℂ := (innerSL ℂ K).comp (field.comp physical)
  have limit := (read.continuous.tendsto (W (k+1))).comp
    (actual_cofinal_stock_recovery observation nontrivial half depth width start k cutoff).2
  change Tendsto (fun n => inner ℂ K (field (physical (tail (k+1) cutoff n)))) atTop
    (𝓝 (inner ℂ K (field (physical (W (k+1)))))) at limit
  rw [physical_field, stock_field, actual_K_price observation nontrivial half depth width start k] at limit
  exact limit

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
