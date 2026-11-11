import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OutsideSelfLogOrbit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory

open BurnolPhysicalState Finset
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource OriginalKSourceResolventReconstruction
open scoped BigOperators InnerProductSpace

namespace Gram
export SourceGeneratedFiniteGram (Coordinates action)
export SourceGeneratedFiniteGram.Projection (synthesis gram rhs action_read kernel_synthesis coefficients equation)
end Gram

open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private literal_raw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "V" => physicalOutsideColumn
local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector

private theorem full_outside_write (parameter : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    O (R parameter x) = selfAction parameter (O x) +
      (-2 * inner ℂ (fourierL2 (K parameter : BurnolL2)) x) • V parameter := by
  have inventory : (P x:BurnolL2) + O x = x :=
    Submodule.starProjection_add_starProjection_orthogonal x
  have acted := congrArg (fun v : BurnolL2 => O (R parameter v)) inventory
  rw [map_add, map_add] at acted
  have paid := original_R_projected_outside_source parameter x
  rw [generatedK_eq_original] at paid
  change O (R parameter (P x:BurnolL2)) =
    (-2 * inner ℂ (fourierL2 (K parameter : BurnolL2)) (P x:BurnolL2)) • V parameter at paid
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_left
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K parameter)) x
  change inner ℂ (fourierL2 (K parameter : BurnolL2)) (P x:BurnolL2) =
    inner ℂ (fourierL2 (K parameter : BurnolL2)) x at physical
  rw [physical] at paid
  rw [paid] at acted
  exact acted.symm.trans (add_comm _ _)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "seed" => (burnolPaCombApproximation 0:BurnolL2)
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

/-- Chronological prices on the actual original power sequence beginning at the Xi-order actor. -/
def sourcePrice (k : Nat) : ℂ := inner ℂ (fourierL2 (K c:BurnolL2)) (((R c)^(m+k)) seed)

private def history (k : Nat) : BurnolL2 := O (((R c)^(m+1+k)) seed)

local notation "price" => sourcePrice observation half
local notation "field" => history observation half

include nontrivial in
private theorem first_outside : field 0 = (-2 * price 0) • V c := by
  have inside := actor_physical observation nontrivial half.down 0 m le_rfl
  change ((R c)^m) seed ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius at inside
  have gone : O (((R c)^m) seed) = 0 := Submodule.starProjection_orthogonal_apply_eq_zero inside
  have actual := full_outside_write c (((R c)^m) seed)
  rw [gone, map_zero, zero_add] at actual
  simpa only [history, sourcePrice, Nat.add_zero, pow_succ', mul_apply_eq_comp] using actual

private theorem history_next (k : Nat) :
    field (k+1) = selfAction c (field k) + (-2 * price (k+1)) • V c := by
  have index : m+1+(k+1) = (m+1+k)+1 := by omega
  have head : m+(k+1) = m+1+k := by omega
  unfold history sourcePrice
  rw [index, pow_succ' (R c) (m+1+k), mul_apply_eq_comp, head]
  exact full_outside_write c (((R c)^(m+1+k)) seed)

private theorem literal_outside (ordinal : Nat) : (input ordinal).2 = field (ordinal+1) := by
  have outside := (congrArg Prod.snd (literal_split observation nontrivial half depth ordinal)).symm
  change (input ordinal).2 = O (raw ordinal) at outside
  rw [outside, literal_raw observation nontrivial half depth]
  change O (((R c)^(m+(ordinal+2))) seed) = O (((R c)^(m+1+(ordinal+1))) seed)
  rw [show m+(ordinal+2) = m+1+(ordinal+1) by omega]

private theorem latest_price (ordinal : Nat) :
    price (ordinal+2) = FixedFourierKFeedback.price observation nontrivial half depth ordinal := by
  unfold sourcePrice
  rw [← literal_raw observation nontrivial half depth ordinal]
  exact FixedFourierKFeedback.actual_whole_price observation nontrivial half depth ordinal

include nontrivial in
private theorem history_word (k : Nat) :
    field k = ∑ j ∈ range (k+1), (-2 * price (k-j)) • column c j := by
  induction k with
  | zero =>
    simpa only [Nat.zero_add, sum_range_one, Nat.sub_zero, column, pow_zero, one_apply_eq_self] using
      first_outside observation nontrivial half
  | succ n prior =>
    rw [history_next, prior, map_sum]
    have next (j : Nat) : selfAction c (column c j) = column c (j+1) := by
      unfold column
      rw [pow_succ', mul_apply_eq_comp]
    have start : column c 0 = V c := by simp only [column, pow_zero, one_apply_eq_self]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [map_smul, next, Nat.sub_zero, Nat.add_sub_add_right, start]

local notation "cols" => (fun (parameter : BurnolCompletedMellinCoordinate) (k : Nat)
  (j : Fin (k+1)) => column parameter (j : Nat))

private theorem coefficients_exact (parameter : BurnolCompletedMellinCoordinate) (k : Nat)
    (a : Gram.Coordinates (Fin (k+1))) :
    Gram.coefficients (cols parameter k) (Gram.synthesis (cols parameter k) a) = a := by
  have independent := (column_linearIndependent parameter).comp
    (Fin.val : Fin (k+1) → Nat) Fin.val_injective
  have injective : Function.Injective (Gram.action (Gram.gram (cols parameter k))) := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro v silent
    have erased : Gram.synthesis (cols parameter k) v = 0 := Gram.kernel_synthesis (cols parameter k) silent
    have each := (Fintype.linearIndependent_iff.mp independent) (fun j => v j) erased
    change v = 0
    ext j
    exact each j
  apply injective
  rw [Gram.equation]
  ext j
  exact (Gram.action_read (cols parameter k) a j).symm

/-- A single exterior field is read in the finite original self-action basis. Lag zero is the latest injection. -/
def decodedLag (parameter : BurnolCompletedMellinCoordinate) (k : Nat)
    (value : BurnolL2) (j : Fin (k+1)) : ℂ :=
  -(Gram.coefficients (cols parameter k) value j) / 2

include nontrivial in
private theorem history_decodes (k : Nat) (j : Fin (k+1)) :
    decodedLag c k (field k) j = price (k-j.val) := by
  let a : Gram.Coordinates (Fin (k+1)) :=
    WithLp.toLp 2 fun i => -2 * price (k-i.val)
  have word : field k = Gram.synthesis (cols c k) a := by
    change field k = ∑ i : Fin (k+1), (-2 * price (k-i.val)) • column c i.val
    exact (history_word observation nontrivial half k).trans
      (Fin.sum_univ_eq_sum_range (fun i : Nat => (-2 * price (k-i)) • column c i) (k+1)).symm
  unfold decodedLag
  rw [word, coefficients_exact]
  change -(-2 * price (k-j.val)) / 2 = _
  ring

/-- The literal exterior slot recovers every fixed original price that wrote it. -/
theorem actual_single_outside_history (ordinal : Nat) (j : Fin (ordinal+2)) :
    decodedLag c (ordinal+1) (input ordinal).2 j = price (ordinal+1-j.val) := by
  rw [literal_outside observation nontrivial half depth ordinal]
  exact history_decodes observation nontrivial half (ordinal+1) j

/-- The native next has the new actual Q price at lag zero and carries all previous prices by one. -/
theorem actual_outside_history_next (ordinal : Nat) :
    decodedLag c (ordinal+2) (input (ordinal+1)).2 0 =
      FixedFourierKFeedback.price observation nontrivial half depth ordinal ∧
    ∀ j : Fin (ordinal+2),
      decodedLag c (ordinal+2) (input (ordinal+1)).2 j.succ =
        decodedLag c (ordinal+1) (input ordinal).2 j := by
  constructor
  · rw [actual_single_outside_history observation nontrivial half depth (ordinal+1), Fin.val_zero, Nat.sub_zero]
    exact latest_price observation nontrivial half depth ordinal
  · intro j
    rw [actual_single_outside_history observation nontrivial half depth (ordinal+1),
      actual_single_outside_history observation nontrivial half depth ordinal, Fin.val_succ]
    congr 1
    omega

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.SelfOrbit.FeedbackHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
