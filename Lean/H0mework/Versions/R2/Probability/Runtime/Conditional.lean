import H0mework.Probability.Source.Conditional
import H0mework.Versions.R2.Probability.Runtime.History

/-! Conditions retain all actual occurrence indices of one sealed material history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalHistory.Runtime

open SourceGeneratedRuntimeHistoryProbability

noncomputable section

universe u v

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable (runtime : LivingRuntimeState process) (bound : Nat)
variable {B : Type v} (read : process.State → B)

def observation (index : Fin (bound + 1)) : B := read (sample runtime bound index)

abbrev observed : PMF B :=
  SourceConditionalHistory.observed (historyPMF bound) (observation runtime bound read)

abbrev conditional (value : B) (supported : value ∈ (observed runtime bound read).support) :
    PMF (Fin (bound + 1)) :=
  SourceConditionalHistory.conditional (historyPMF bound) (observation runtime bound read) value supported

theorem query_supported (index : Fin (bound + 1)) :
    observation runtime bound read index ∈ (observed runtime bound read).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨index, by simp [historyPMF], rfl⟩

theorem observed_eq_state_map : observed runtime bound read = (statePMF runtime bound).map read := by
  rw [statePMF, PMF.map_comp]
  rfl

theorem conditional_support_iff (value : B) (supported : value ∈ (observed runtime bound read).support)
    (index : Fin (bound + 1)) :
    index ∈ (conditional runtime bound read value supported).support ↔
      read (sample runtime bound index) = value := by
  rw [SourceConditionalHistory.conditional_support]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, historyPMF, PMF.mem_support_uniformOfFintype,
    and_true, observation]

theorem recombine_indices :
    (observed runtime bound read).bindOnSupport (conditional runtime bound read) = historyPMF bound :=
  SourceConditionalHistory.recombine (historyPMF bound) (observation runtime bound read)

theorem recombine_states :
    (observed runtime bound read).bindOnSupport
        (fun value supported => (conditional runtime bound read value supported).map (sample runtime bound)) =
      statePMF runtime bound :=
  SourceConditionalHistory.recombine_map (historyPMF bound) (observation runtime bound read) (sample runtime bound)

theorem conditional_index_factorizes (value : B)
    (supported : value ∈ (observed runtime bound read).support) (index : Fin (bound + 1))
    (member : index ∈ (conditional runtime bound read value supported).support) :
    let stage := (history runtime bound).stageAt index
    read (sample runtime bound index) = value ∧
      (process.toAnswerNextCausalWorld.emitted (ULift.up (sample runtime bound index)) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          (runtime.advance index.val).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
            (runtime.advance index.val).current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          ((runtime.advance index.val).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtime.advance index.val).current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) :=
  ⟨(conditional_support_iff runtime bound read value supported index).mp member,
    sample_factorizes runtime bound index⟩

end
end SourceConditionalHistory.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
