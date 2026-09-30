import H0mework.Fock.PrimeFieldJoint.JointQueries
import H0mework.Probability.HistoryWord.Lift

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionJoint

open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift Filter
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Topology
noncomputable section

theorem inventory_strictMono : StrictMono (fun round => inventoryBound (roundRuntime round)) :=
  strictMono_nat_of_lt_succ round_inventory_grows

theorem inventory_cofinal : Tendsto (fun round => inventoryBound (roundRuntime round)) atTop atTop :=
  inventory_strictMono.tendsto_atTop

theorem inventory_gain (round steps : Nat) :
    inventoryBound (roundRuntime round) + steps ≤ inventoryBound (roundRuntime (round + steps)) := by
  induction steps with
  | zero => simp
  | succ steps previous =>
      have actual := round_inventory_grows (round + steps)
      simp only [Nat.add_assoc] at actual
      omega

def demand (round : Nat) (sourceWord : Nat →₀ ℂ) : Nat :=
  sourceWord.support.sup id - inventoryBound (roundRuntime round)

def sourceRound (round : Nat) (sourceWord : Nat →₀ ℂ) : LivingRuntimeState process :=
  roundRuntime (round + demand round sourceWord)

def realizeWord (round : Nat) (sourceWord : Nat →₀ ℂ) :
    FieldSpace (depth (sourceRound round sourceWord)) (inventoryBound (sourceRound round sourceWord)) :=
  Actor.currentTransfer _ _ (SourceHistoryWord.lift _ sourceWord)

theorem source_round_current (round : Nat) (sourceWord : Nat →₀ ℂ)
    (present : sourceWord.support.sup id ≤ inventoryBound (roundRuntime round)) :
    sourceRound round sourceWord = roundRuntime round := by
  simp only [sourceRound, demand, Nat.sub_eq_zero_of_le present, Nat.add_zero]

theorem realization_word (round : Nat) (sourceWord : Nat →₀ ℂ) :
    word (depth (sourceRound round sourceWord)) (inventoryBound (sourceRound round sourceWord))
      (realizeWord round sourceWord) = sourceWord := by
  rw [realizeWord, word_from_actor]
  apply SourceHistoryWord.word_lift
  intro index present
  have within : index ≤ sourceWord.support.sup id := Finset.le_sup (f := id) present
  have generated := inventory_gain round (demand round sourceWord)
  change inventoryBound (roundRuntime round) + demand round sourceWord ≤
    inventoryBound (sourceRound round sourceWord) at generated
  unfold demand at generated
  omega

theorem realization_joint (round : Nat) (sourceWord : Nat →₀ ℂ) :
    joint (depth (sourceRound round sourceWord)) (inventoryBound (sourceRound round sourceWord))
      (realizeWord round sourceWord) = SourceMassCompletion.jointRead sourceWord :=
  congrArg SourceMassCompletion.jointRead (realization_word round sourceWord)

theorem source_round_after (round : Nat) (sourceWord : Nat →₀ ℂ) :
    (roundRuntime round).advance
      (inventoryBound (sourceRound round sourceWord) - inventoryBound (roundRuntime round)) =
        sourceRound round sourceWord := by
  have generated := inventory_gain round (demand round sourceWord)
  change inventoryBound (roundRuntime round) + demand round sourceWord ≤
    inventoryBound (sourceRound round sourceWord) at generated
  have counted : inventoryBound (roundRuntime round) +
      (inventoryBound (sourceRound round sourceWord) - inventoryBound (roundRuntime round)) =
        inventoryBound (sourceRound round sourceWord) := by omega
  rw [advance_original, ← inventory_bound (roundRuntime round), counted, inventory_bound]
  exact (runtime_eq (sourceRound round sourceWord)).symm

theorem whole_joint_closure (round : Nat) :
    (⨆ future : Nat, LinearMap.range (joint (depth (roundRuntime (round + future)))
      (inventoryBound (roundRuntime (round + future))))).topologicalClosure = ⊤ := by
  have sourceIncluded : SourceMassCompletion.jointRead.range ≤
      ⨆ future : Nat, LinearMap.range (joint (depth (roundRuntime (round + future)))
        (inventoryBound (roundRuntime (round + future)))) := by
    rintro _ ⟨sourceWord, rfl⟩
    exact (le_iSup (fun future : Nat => LinearMap.range (joint (depth (roundRuntime (round + future)))
      (inventoryBound (roundRuntime (round + future))))) (demand round sourceWord))
        ⟨realizeWord round sourceWord, realization_joint round sourceWord⟩
  apply top_unique
  rw [← SourceMassCompletion.range_jointRead_closure_eq_top]
  exact Submodule.topologicalClosure_mono sourceIncluded

theorem packet_tendsto :
    Tendsto (fun round => packet (roundRuntime round)) atTop
      (𝓝 (WithLp.toLp 2 ((0 : H), (1 : ℂ)))) := by
  have original := SourceMassCompletion.source_mean_tendsto.comp inventory_cofinal
  simpa only [Function.comp_def, packet_original] using original

theorem hilbert_density_tendsto :
    Tendsto (fun round => hilbert (depth (roundRuntime round)) (inventoryBound (roundRuntime round))
      (sourceDensity (roundRuntime round))) atTop (𝓝 (0 : H)) := by
  have original := SourceMassCompletion.firstRead.continuous.continuousAt.tendsto.comp packet_tendsto
  change Tendsto (fun round => SourceMassCompletion.firstRead (packet (roundRuntime round))) atTop (𝓝 (0 : H)) at original
  exact original

end
end SourceGeneratedAcquisitionJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
