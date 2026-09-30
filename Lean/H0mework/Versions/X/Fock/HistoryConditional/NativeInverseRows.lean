import H0mework.Fock.HistoryConditional.NativeInverseActor
import H0mework.Versions.X.Fock.HistoryConditional.NativeInverseSource
import H0mework.Versions.X.Fock.HistoryConditional.CopyHistoryMaterialRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

theorem actor_execute (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1) (actor : Fin (bound + 1)) :
    decodeActor bound program (SourceCopyWordAffine.execute program (actor.val + 1)) = some actor := by
  rw [decodeActor, decode_execute program positive]
  dsimp only
  rw [dif_pos ⟨by omega, by have := actor.isLt; omega⟩]
  rfl

theorem row_execute (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1) (actor : Fin (bound + 1)) :
    row bound program (SourceCopyWordAffine.execute program (actor.val + 1)) =
      (fun candidate : Fin (bound + 1) => if candidate = actor then 1 else 0) := by
  funext candidate
  rw [row, actor_execute bound program positive]
  simp only [Option.some.injEq, eq_comm]

theorem actor_some_iff (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1)
    (target : Nat) (actor : Fin (bound + 1)) :
    decodeActor bound program target = some actor ↔ SourceCopyWordAffine.execute program (actor.val + 1) = target := by
  constructor
  · intro result
    unfold decodeActor at result
    cases raw : decode program target with
    | none => simp only [raw] at result; cases result
    | some state =>
        simp only [raw] at result
        split at result
        next inside =>
          have equal := congrArg Fin.val (Option.some.inj result)
          change state - 1 = actor.val at equal
          have state_eq : state = actor.val + 1 := by omega
          have generated := (decode_some_iff program positive target state).mp raw
          simpa only [state_eq] using generated
        next outside => cases result
  · intro generated
    rw [← generated]
    exact actor_execute bound program positive actor

theorem actor_none_iff (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1) (target : Nat) :
    decodeActor bound program target = none ↔
      target ∉ Set.range (fun actor : Fin (bound + 1) => SourceCopyWordAffine.execute program (actor.val + 1)) := by
  constructor
  · rintro missing ⟨actor, generated⟩
    have restored := (actor_some_iff bound program positive target actor).mpr generated
    rw [missing] at restored
    cases restored
  · intro outside
    cases result : decodeActor bound program target with
    | none => rfl
    | some actor => exact (outside ⟨actor, (actor_some_iff bound program positive target actor).mp result⟩).elim

theorem row_none (bound : Nat) (program : Nat × Nat) (target : Nat)
    (missing : decodeActor bound program target = none) : row bound program target = (fun _ => 0) := by
  funext actor
  simp only [row, missing, reduceCtorEq, if_false]

noncomputable section

theorem material_execute (bound : Nat) (program : Nat × Nat) (positive : 0 < program.1) (actor : Fin (bound + 1)) :
    SourceCopyNativeHistory.recoverMaterial bound (row bound program (SourceCopyWordAffine.execute program (actor.val + 1))) =
      some ⟨actor, (history runtimeSeed bound).stageAt actor⟩ := by
  rw [row_execute bound program positive]
  have original : (SourceConditionalNativeObservers.generate (SourceCopyNativeHistory.read bound) bound
      (SourceCopyNativeHistory.read bound actor.val)).2 = (fun candidate : Fin (bound + 1) => if candidate = actor then 1 else 0) :=
    congrArg Prod.snd (SourceCopyNativeHistory.native_row bound actor)
  rw [← original]
  exact SourceCopyNativeHistory.recovered_material bound actor

theorem material_none (bound : Nat) (program : Nat × Nat) (target : Nat)
    (missing : decodeActor bound program target = none) :
    SourceCopyNativeHistory.recoverMaterial bound (row bound program target) = none := by
  rw [row_none bound program target missing, SourceCopyNativeHistory.recoverMaterial, SourceCopyNativeHistory.decoded_empty]
  rfl

end
end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
