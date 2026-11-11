import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CenteredLogRank
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideLogWrite
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalConductorEnergy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.WidePositionGapAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank

open BurnolPhysicalState UnitPowerJordanSource HilbertInventory
open OutsideQuarterAction DivisionConductor ConductorFaithfulness
open OriginalGamma.Source.RelativeConductorGapReadback (GammaPair)
open scoped ComplexOrder InnerProductSpace

open private literal_raw sourceIndex from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor
open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private current from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
open private input_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionBranchSecondConductor

local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "BI" => burnolMeanZeroBlockInverse
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Z" => OriginalRieszSource.Constructor.zeroMean
local notation "F₂" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)

private theorem log_coefficients_independent (c : BurnolCompletedMellinCoordinate) :
    LinearIndependent ℂ (logCoefficients c) := by
  classical
  rw [linearIndependent_iff']
  intro indices a erased i included
  by_contra nonzero
  let active := indices.filter (fun j => a j ≠ 0)
  have nonempty : active.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨included,nonzero⟩⟩
  let k := active.max' nonempty
  have present : k ∈ active := Finset.max'_mem _ _
  have live := Finset.mem_filter.mp present
  let read : LogStock →ₗ[ℂ] ℂ := Finsupp.lapply k
  have evaluated := congrArg read erased
  have scalar : (∑ j ∈ indices, a j * logCoefficients c j k) = 0 := by
    simpa only [read, map_sum, map_smul, map_zero, Finsupp.lapply_apply, smul_eq_mul] using evaluated
  have collapse : (∑ j ∈ indices, a j * logCoefficients c j k) = a k * logCoefficients c k k := by
    apply Finset.sum_eq_single k
    · intro j member apart
      rcases lt_or_gt_of_ne apart with earlier | later
      · rw [log_coefficients_above c j k earlier, mul_zero]
      · have gone : a j = 0 := by
          by_contra visible
          exact (not_le_of_gt later) (Finset.le_max' active j (Finset.mem_filter.mpr ⟨member,visible⟩))
        rw [gone, zero_mul]
    · exact fun missing => (missing live.1).elim
  rw [collapse, log_coefficients_top] at scalar
  exact mul_ne_zero live.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) (first_outside_price_ne_zero c)) scalar

/-- The original B block and the original exterior embedding synthesize the complete outside field. -/
def outsideSynthesis (c : BurnolCompletedMellinCoordinate) : LogStock →ₗ[ℂ] BurnolL2 :=
  (outsideEmbedding.comp BI).toLinearMap.comp (logSynthesis (barC c))

private theorem outside_synthesis_injective (c : BurnolCompletedMellinCoordinate) :
    Function.Injective (outsideSynthesis c) := by
  intro a b same
  apply (linearIndependent_iff_injective_finsuppLinearCombination.mp (centered_log_columns_linearIndependent (barC c)))
  have equal := outsideEmbedding_injective same
  have read (x : M) : burnolMeanZeroOneMinusSquare (BI x) = x := by
    have paid := congrArg (fun f : M →L[ℂ] M => f x) burnolMeanZeroBlockInverse_right
    exact paid
  change BI (logSynthesis (barC c) a) = BI (logSynthesis (barC c) b) at equal
  exact (read _).symm.trans ((congrArg (fun x : M => burnolMeanZeroOneMinusSquare x) equal).trans (read _))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "first" => branchGammaAt observation nontrivial half depth
local notation "second" => branchSecondAt observation nontrivial half depth

/-- The finite written log inventory recovers the outside slot of its own literal Division. -/
theorem actual_outside_log_synthesis (ordinal : Nat) :
    (input ordinal).2 = outsideSynthesis c (logCoefficients c (ordinal+1)) := by
  let source := current observation nontrivial half depth ordinal
  have center :
      centeredFourier c ((basis c).repr source) = logSynthesis (barC c) (logCoefficients c (ordinal+1)) := by
    rw [actual_fourier_log_inventory]
    change Z (burnolQuarterRestriction
      (F₂ (((basis c).repr.symm ((basis c).repr source)) : BurnolL2))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    change Z (burnolQuarterRestriction (F₂ (raw ordinal))) = centeredFourierPower c (xiOrder c+1+(ordinal+1))
    rw [literal_raw observation nontrivial half depth]
    have index : sourceIndex observation ordinal = xiOrder c+1+(ordinal+1) := by
      change generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate + (ordinal+2) =
        generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate + 1 + (ordinal+1)
      omega
    rw [index]
    rfl
  have paid := actual_original_B_outside c (coefficientsAt observation nontrivial half depth ordinal)
  change OriginalKCombPhysicalAction.physicalRemainder
      ((basis c).repr.symm ((basis c).repr source) : BurnolL2) =
    outsideEmbedding (BI (centeredFourier c ((basis c).repr source))) at paid
  rw [LinearIsometryEquiv.symm_apply_apply, center] at paid
  exact (congrArg Prod.snd (literal_split observation nontrivial half depth ordinal)).symm.trans paid

/-- Every original outside slot contributes a new independent field through the original B solve. -/
theorem actual_division_outside_linearIndependent : LinearIndependent ℂ (fun n : Nat => (input n).2) := by
  have indexed := (log_coefficients_independent c).comp (fun n : Nat => n+1) Nat.succ_injective
  have written := indexed.map' (outsideSynthesis c) (LinearMap.ker_eq_bot.mpr (outside_synthesis_injective c))
  have same : (fun n : Nat => (input n).2) =
      fun n : Nat => outsideSynthesis c ((logCoefficients c ∘ fun n : Nat => n+1) n) := by
    funext ordinal
    exact actual_outside_log_synthesis observation nontrivial half depth ordinal
  rw [same]
  exact written

theorem actual_division_outside_gram_positive (indices : Finset Nat) :
    Matrix.PosDef (Matrix.gram ℂ (fun i : indices => (input i.val).2)) :=
  Matrix.posDef_gram_of_linearIndependent
    ((actual_division_outside_linearIndependent observation nontrivial half depth).comp _ Subtype.val_injective)

/-- The actual second conductor pays a positive definite two-slot Gram, including its cross terms. -/
theorem actual_division_branch_second_gram_positive (ordinal : Nat) :
    let x := input ordinal;
    let s := second ordinal;
    Matrix.PosDef (Matrix.of (fun i j : Fin 2 => inner ℂ (![x.1,x.2] i) (![s.1,s.2] j))) := by
  let x := input ordinal
  let g := first ordinal
  let S := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  let P := OriginalKCombPhysicalAction.physicalProjection
  let O := OriginalKCombPhysicalAction.physicalRemainder
  have split := literal_split observation nontrivial half depth ordinal
  have phys := congrArg Prod.fst split
  have out := congrArg Prod.snd split
  change P (raw ordinal) = x.1 at phys
  change O (raw ordinal) = x.2 at out
  have pMem : x.1 ∈ S := by
    rw [← phys]
    exact (burnolEvenAmbientProjection (raw ordinal)).property
  have oMem : x.2 ∈ Sᗮ := by
    rw [← out]
    exact Sᗮ.starProjection_apply_mem _
  have pFixed : P x.1 = x.1 := S.starProjection_eq_self_iff.mpr pMem
  have pZero : P x.2 = 0 := by
    change S.starProjection x.2 = 0
    rw [Submodule.starProjection_apply, S.orthogonalProjectionOnto_apply_of_mem_orthogonal oMem]
    rfl
  have liveP := WidePositionGap.actual_division_physical_ne_zero observation nontrivial half depth ordinal
  have liveO := (actual_division_outside_linearIndependent observation nontrivial half depth).ne_zero ordinal
  have even := input_even observation nontrivial half depth ordinal
  have physicalGap : x.1 ∈ locallyConstantFace (1/4 : ℝ) := pMem.1.1
  have outsideGap : x.2 ∈ locallyConstantFace (1/4 : ℝ) := by
    have residual : x.2 = raw ordinal - x.1 := by
      change x.2 = x.1 + x.2 - x.1
      simp
    rw [residual]
    exact (locallyConstantFace (1/4 : ℝ)).sub_mem
      (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal) physicalGap
  have firstGraph : GammaPair x.1 g.1 ∧ GammaPair x.2 g.2 :=
    actual_division_branch_conductor observation nontrivial half depth ordinal
  have independent : LinearIndependent ℂ ![g.1,g.2] := by
    apply Fintype.linearIndependent_iff.mpr
    intro a silent
    rw [Fin.sum_univ_two] at silent
    change a 0 • g.1 + a 1 • g.2 = 0 at silent
    have graph : GammaPair (a 0 • x.1 + a 1 • x.2) (a 0 • g.1 + a 1 • g.2) := by
      intro test
      simp only [inner_add_right, inner_smul_right, firstGraph.1 test, firstGraph.2 test]
    rw [silent] at graph
    let gap := locallyConstantFace (1/4 : ℝ)
    have erased := zero_of_even_position_gap_conductor _
      (by rw [map_add, map_smul, map_smul, even.1, even.2])
      (gap.add_mem (gap.smul_mem _ physicalGap) (gap.smul_mem _ outsideGap)) graph
    have projected := congrArg P erased
    rw [map_add, map_smul, map_smul, pFixed, pZero, smul_zero, add_zero, map_zero] at projected
    have firstZero : a 0 = 0 := (smul_eq_zero.mp projected).resolve_right liveP
    rw [firstZero, zero_smul, zero_add] at erased
    have secondZero : a 1 = 0 := (smul_eq_zero.mp erased).resolve_right liveO
    intro i
    fin_cases i
    · exact firstZero
    · exact secondZero
  dsimp only
  rw [actual_division_branch_second_gram observation nontrivial half depth ordinal]
  exact Matrix.posDef_gram_of_linearIndependent independent

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
