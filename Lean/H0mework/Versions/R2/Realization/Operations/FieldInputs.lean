import H0mework.Versions.R2.Realization.Operations.NativeState
import H0mework.Versions.R2.Realization.Operations.RuntimeCharacter

/-! Complete native states and their actual action enter the existing operation and character field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Field

open SourceOperationEffects SourceOperationScalarRelations

noncomputable section

universe u v

variable {N : WorldRelationNetwork.{u}}

abbrev Value (process : SourceNativeLivingRootProcess N) : PUnit.{u + 1} → Type u :=
  fun _ => SourceOperationNative.Carrier process

abbrev Var (_process : SourceNativeLivingRootProcess N) : PUnit.{u + 1} → Type u :=
  fun _ => PUnit.{u + 1}

def environment (process : SourceNativeLivingRootProcess N) :
    SourceOperationNative.Carrier process →+ Env (Value process) (Var process) where
  toFun material := fun _ _ => material
  map_zero' := rfl
  map_add' _ _ := rfl

def word (process : SourceNativeLivingRootProcess N) :
    SourceOperationRuntime.FormalCarrier ℤ (Value process) (Var process) PUnit.unit :=
  Finsupp.single (.var PUnit.unit) 1

def actionWord (process : SourceNativeLivingRootProcess N) :
    SourceOperationRuntime.FormalCarrier ℤ (Value process) (Var process) PUnit.unit :=
  Finsupp.single (.linear (s := PUnit.unit) (sourceAction process).toAddMonoidHom (.var PUnit.unit)) 1

variable {process : SourceNativeLivingRootProcess N}

def sourceValue (runtime : LivingRuntimeState process) :=
  SourceOperationRuntime.Character.sourceMap (R := ℤ) (s := PUnit.unit)
    (statePoint process) (environment process) runtime (word process)

def actionValue (runtime : LivingRuntimeState process) :=
  SourceOperationRuntime.Character.sourceMap (R := ℤ) (s := PUnit.unit)
    (statePoint process) (environment process) runtime (actionWord process)

def read (runtime : LivingRuntimeState process) (bound : Nat) :=
  SourceOperationRuntime.Character.stageRead (R := ℤ) (s := PUnit.unit)
    (statePoint process) (environment process) runtime bound

theorem sourceValue_read (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) :
    read runtime bound (sourceValue runtime) index =
      (point (runtime.advance index.val),
        point (runtime.advance index.val).tick.next - point (runtime.advance index.val)) := by
  unfold read sourceValue
  rw [SourceOperationRuntime.Character.source_reads_actual_stage]
  change updateInventory (R := ℤ) (environment process (point (runtime.advance index.val)))
    (environment process (point (runtime.advance index.val).tick.next - point (runtime.advance index.val)))
    (word process) = _
  simp only [updateInventory, evaluation, effectEvaluator, word, LinearMap.prod_apply, Function.prod, Finsupp.linearCombination_single,
    one_smul, Expr.eval, Expr.effect, environment]
  rfl

theorem actionValue_read (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) :
    read runtime bound (actionValue runtime) index =
      (point (runtime.advance index.val).tick.next,
        point (runtime.advance index.val).tick.next.tick.next - point (runtime.advance index.val).tick.next) := by
  unfold read actionValue
  rw [SourceOperationRuntime.Character.source_reads_actual_stage]
  change updateInventory (R := ℤ) (environment process (point (runtime.advance index.val)))
    (environment process (point (runtime.advance index.val).tick.next - point (runtime.advance index.val)))
    (actionWord process) = _
  simp only [updateInventory, evaluation, effectEvaluator, actionWord, LinearMap.prod_apply, Function.prod, Finsupp.linearCombination_single,
    one_smul, Expr.eval, Expr.effect, environment]
  change (sourceAction process (point (runtime.advance index.val)),
    sourceAction process (point (runtime.advance index.val).tick.next - point (runtime.advance index.val))) = _
  rw [map_sub, sourceAction_point, sourceAction_point]

/-- The native witness is the already generated next runtime, never a decoded linear combination. -/
def nextWitness (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) :
    Σ target : LivingRuntimeState process,
      PLift (point target = (read runtime bound (actionValue runtime) index).1) :=
  ⟨(runtime.advance index.val).tick.next, ⟨(congrArg Prod.fst (actionValue_read runtime bound index)).symm⟩⟩

theorem nextWitness_is_actual (runtime : LivingRuntimeState process) (bound : Nat)
    (index : Fin (bound + 1)) :
    (nextWitness runtime bound index).1 =
      ((SourceOperationRuntime.materialHistory runtime bound).stageAt index).next := rfl

def nativeObserver {A : Type v} (readout : process.State → A) :
    SourceOperationNative.Carrier process →ₗ[ℤ] (A →₀ ℤ) :=
  observer process (fun state => Finsupp.single (readout state) 1)

theorem nativeObserver_point {A : Type v} (readout : process.State → A)
    (runtime : LivingRuntimeState process) :
    nativeObserver readout (point runtime) = Finsupp.single (readout runtime.state) 1 :=
  observer_point (fun state => Finsupp.single (readout state) 1) runtime

/-- The arbitrary native output is read from the retained actual runtime witness. -/
def nativeReadWitness {A : Type v} (readout : process.State → A)
    (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) :
    Σ value : A, PLift (Finsupp.single value 1 =
      nativeObserver readout (read runtime bound (actionValue runtime) index).1) :=
  let target := nextWitness runtime bound index
  ⟨readout target.1.state, ⟨(nativeObserver_point readout target.1).symm.trans
    (congrArg (nativeObserver readout) target.2.down)⟩⟩

end
end SourceOperationNative.Field
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
