import Mathlib.Probability.Distributions.Uniform
import H0mework.Versions.R2.Foundation.Runtime.Activation

/-! Finite probability is generated from the indices of one sealed actual history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRuntimeHistoryProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

def history (runtime : LivingRuntimeState process) (bound : Nat) :
    SourceGeneratedRuntimeMaterialHistoryAt runtime (bound + 1) :=
  .generate runtime (bound + 1)

def historyPMF (bound : Nat) : PMF (Fin (bound + 1)) :=
  PMF.uniformOfFintype (Fin (bound + 1))

def stageState {runtime : LivingRuntimeState process}
    (_stage : SourceGeneratedRuntimeMaterialStageAt runtime) : process.State :=
  runtime.state

def sample (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) : process.State :=
  stageState ((history runtime bound).stageAt index)

@[simp] theorem sample_eq_advance (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) :
    sample runtime bound index = (runtime.advance index.val).state := rfl

def statePMF (runtime : LivingRuntimeState process) (bound : Nat) : PMF process.State :=
  (historyPMF bound).map (sample runtime bound)

@[simp] theorem historyPMF_apply (bound : Nat) (index : Fin (bound + 1)) :
    historyPMF bound index = ((bound + 1 : Nat) : ENNReal)⁻¹ := by
  simp [historyPMF]

theorem statePMF_support_iff (runtime : LivingRuntimeState process) (bound : Nat)
    (value : process.State) :
    value ∈ (statePMF runtime bound).support ↔
      ∃ index : Fin (bound + 1), sample runtime bound index = value := by
  rw [statePMF, PMF.mem_support_map_iff]
  simp only [historyPMF, PMF.mem_support_uniformOfFintype, true_and]

theorem sample_factorizes (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) :
    let stage := (history runtime bound).stageAt index
    process.toAnswerNextCausalWorld.emitted (ULift.up (sample runtime bound index)) =
        ULift.up stage.activated.generated ∧
      stage.activated.generated.occurrence =
        (runtime.advance index.val).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtime.advance index.val).current.visit.current ∧
      HEq stage.wholeLedgerWriteBack
        ((runtime.advance index.val).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtime.advance index.val).current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent :=
  ((history runtime bound).stageAt index).factorizes

end
end SourceGeneratedRuntimeHistoryProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
