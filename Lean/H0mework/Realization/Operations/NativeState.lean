import H0mework.Foundation.Runtime.Activation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Complete native states enter the existing free integral module before any observer projection. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative

noncomputable section

universe u v

variable {N : WorldRelationNetwork.{u}}

abbrev Carrier (process : SourceNativeLivingRootProcess N) := process.State →₀ ℤ

def statePoint (process : SourceNativeLivingRootProcess N) (state : process.State) : Carrier process :=
  Finsupp.single state 1

def point {process : SourceNativeLivingRootProcess N} (runtime : LivingRuntimeState process) :
    Carrier process := statePoint process runtime.state

theorem statePoint_injective (process : SourceNativeLivingRootProcess N) :
    Function.Injective (statePoint process) :=
  Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)

theorem point_injective (process : SourceNativeLivingRootProcess N) :
    Function.Injective (point (process := process)) := by
  intro left right same
  exact LivingRuntimeState.ext (statePoint_injective process same)

/-- Linear pushforward of the already fixed native successor. -/
def sourceAction (process : SourceNativeLivingRootProcess N) : Carrier process →ₗ[ℤ] Carrier process :=
  Finsupp.lmapDomain ℤ ℤ process.successor

@[simp] theorem sourceAction_statePoint (process : SourceNativeLivingRootProcess N) (state : process.State) :
    sourceAction process (statePoint process state) = statePoint process (process.successor state) := by
  simp only [sourceAction, statePoint, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

@[simp] theorem sourceAction_point {process : SourceNativeLivingRootProcess N}
    (runtime : LivingRuntimeState process) :
    sourceAction process (point runtime) = point runtime.tick.next :=
  sourceAction_statePoint process runtime.state

variable (process : SourceNativeLivingRootProcess N)
variable {B : Type v} [AddCommGroup B]

/-- The existing free-module extension accepts an arbitrary native observer. -/
def observer (read : process.State → B) : Carrier process →ₗ[ℤ] B :=
  Finsupp.linearCombination ℤ read

def observerAddHom (read : process.State → B) : Carrier process →+ B :=
  (observer process read).toAddMonoidHom

@[simp] theorem observer_statePoint (read : process.State → B) (state : process.State) :
    observer process read (statePoint process state) = read state := by
  simp only [observer, statePoint, Finsupp.linearCombination_single, one_smul]

variable {process}

@[simp] theorem observer_point (read : process.State → B) (runtime : LivingRuntimeState process) :
    observer process read (point runtime) = read runtime.state :=
  observer_statePoint process read runtime.state

theorem observer_unique (read : process.State → B) (candidate : Carrier process →ₗ[ℤ] B)
    (agrees : ∀ state, candidate (statePoint process state) = read state) :
    candidate = observer process read := by
  apply Finsupp.lhom_ext'
  intro state
  apply LinearMap.ext_ring
  exact (agrees state).trans (observer_statePoint process read state).symm

theorem observer_sourceAction (read : process.State → B) :
    (observer process read).comp (sourceAction process) =
      observer process (fun state => read (process.successor state)) := by
  unfold observer sourceAction
  rw [Finsupp.linearCombination_comp_lmapDomain]
  rfl

/-- The native point and its action read the same occurrence, whole ledger and next. -/
theorem point_factorizes (runtime : LivingRuntimeState process) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    sourceAction process (point runtime) = point runtime.tick.next ∧
      process.stateAt runtime.state = runtime.current ∧
      (process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) := by
  exact ⟨sourceAction_point runtime, rfl, (SourceGeneratedRuntimeMaterialStageAt.generate runtime).factorizes⟩

end
end SourceOperationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
