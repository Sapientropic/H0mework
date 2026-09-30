import H0mework.Fock.CopyGraph.LossSource
import H0mework.Probability.Recovery.Collision

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceGeneratedAtomicObservation SourceUniformFibreVariance SourceHistoryGrowth
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead newRead)
open scoped Classical
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem novel_fibre (depth : Nat) (read : Nat → Observed)
    (novel : read (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth read)) (actor : Fin (depth + 2)) :
    newRead depth read actor = read (depth + 1) ↔ actor = Fin.last (depth + 1) := by
  constructor
  · intro same
    by_contra different
    have prior : actor.val < depth + 1 := by
      have bound := actor.isLt
      have unequal : actor.val ≠ depth + 1 := fun equal => different (Fin.ext equal)
      omega
    let before : Fin (depth + 1) := ⟨actor.val, prior⟩
    have supported := observed_supported (historyPMF depth) (oldRead depth read) before (source_positive depth before)
    have present := (atoms_iff (historyPMF depth) (oldRead depth read) _).mpr supported
    exact novel (same ▸ present)
  · intro same
    subst actor
    rfl

theorem novel_decoder_source (depth : Nat) (read : Nat → Observed)
    (novel : read (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth read)) :
    pullback (historyPMF (depth + 1)) (newRead depth read)
      (decoderValue (historyPMF (depth + 1)) (newRead depth read) (fun atom => if atom = read (depth + 1) then 1 else 0)) =
        cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)) := by
  apply MeasureTheory.Lp.ext
  apply Filter.Eventually.of_forall
  intro actor
  rw [pullback_at _ _ _ actor (source_positive (depth + 1) actor), decoderValue_at _ _ _ _
    (observed_supported _ _ actor (source_positive (depth + 1) actor)), cotest_value, novel_fibre depth read novel actor]
  split_ifs <;> rfl

theorem novel_direction_zero (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (novel : read (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth read)) : direction depth index read = 0 := by
  have restored : SourceWeightedRecovery.residual (historyPMF (depth + 1)) (newRead depth read)
      (cotest (historyPMF (depth + 1)) (Fin.last (depth + 1))) = 0 :=
    (IsometricRetainedTransfer.residual_zero_iff (pullback (historyPMF (depth + 1)) (newRead depth read)) _).mpr
      ⟨decoderValue (historyPMF (depth + 1)) (newRead depth read) (fun atom => if atom = read (depth + 1) then 1 else 0),
        novel_decoder_source depth read novel⟩
  exact (SourceConditionalGraphDecoder.recovery_zero_iff (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (newRead depth read) (cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)))).mpr restored

theorem collision_cost (depth : Nat) (index : Index depth) (read : Nat → Observed) (actor : Fin (depth + 1))
    (collision : read actor.val = read (depth + 1)) :
    (1 : ℝ) / (2 * (depth + 2 : ℝ)) ≤ ‖direction depth index read‖ ^ 2 := by
  let task := cotest (historyPMF (depth + 1)) (Fin.last (depth + 1))
  have distinct : includeActor (Nat.le_succ depth) actor ≠ Fin.last (depth + 1) := by
    intro same
    exact (Nat.ne_of_lt actor.isLt) (congrArg (fun point : Fin (depth + 2) => point.val) same)
  have equalWeight : (historyPMF (depth + 1) (includeActor (Nat.le_succ depth) actor)).toReal =
      (historyPMF (depth + 1) (Fin.last (depth + 1))).toReal := by rw [source_weight, source_weight]
  have paid := equal_weight_pair_lower_bound (historyPMF (depth + 1)) (newRead depth read) (fun point => task point)
    (optimalDecoder (historyPMF (depth + 1)) (newRead depth read) (fun point => task point))
    (includeActor (Nat.le_succ depth) actor) (Fin.last (depth + 1)) distinct collision equalWeight
  have restored : taskValue (historyPMF (depth + 1)) (fun point => task point) = task :=
    MeasureTheory.Lp.toLp_coeFn task (task_memLp (historyPMF (depth + 1)) _)
  rw [optimal_attains, restored] at paid
  dsimp only [task] at paid
  rw [cotest_value, if_neg distinct, cotest_value, if_pos rfl, zero_sub, norm_neg, norm_one, one_pow, mul_one, source_weight] at paid
  have original := SourceConditionalGraphDecoder.retained_lower (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (newRead depth read) task
  have combined := paid.trans original
  have weights : (1 : ℝ) / ((depth + 1 : Nat) + 1 : ℝ) / 2 = 1 / (2 * (depth + 2 : ℝ)) := by
    rw [div_div]
    congr 1
    push_cast
    ring
  rw [weights] at combined
  with_unfolding_all exact combined

theorem direction_zero_iff_novel (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    direction depth index read = 0 ↔ read (depth + 1) ∉ atoms (historyPMF depth) (oldRead depth read) := by
  constructor
  · intro zero present
    have supported := (atoms_iff (historyPMF depth) (oldRead depth read) _).mp present
    obtain ⟨actor, _, same⟩ := (PMF.mem_support_map_iff (oldRead depth read) (historyPMF depth) (read (depth + 1))).mp supported
    have paid := collision_cost depth index read actor same
    rw [zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at paid
    have positive : (0 : ℝ) < 1 / (2 * (depth + 2 : ℝ)) := by positivity
    exact (not_le_of_gt positive) paid
  · exact novel_direction_zero depth index read

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
