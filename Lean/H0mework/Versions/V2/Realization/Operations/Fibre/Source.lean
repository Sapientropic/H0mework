import H0mework.Versions.R2.Realization.Operations.RuntimeRelations
import H0mework.Versions.R2.Realization.Operations.RuntimeEvolution
import H0mework.Realization.Logic.FibreLift

/-! The complete current kernel is the intersection of its actual first
old/effect kernel and the full generated next kernel. The source square
uses the existing successor and keeps the original formal carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationRuntime.Fibre
open SourceOperationEffects SourceOperationLogic SourceOperationLogic.FibreLift
open SourceGeneratedScalarDifferentialResidual
noncomputable section
universe r u m n
variable {N : WorldRelationNetwork.{n}} {process : SourceNativeLivingRootProcess N}
variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}
variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

def evaluation (runtime : LivingRuntimeState process) :
    FormalCarrier R Value Var s →ₗ[R] completion (R := R) (s := s) readMaterial environment runtime :=
  (completionMap (R := R) (s := s) readMaterial environment runtime).hom

def firstStage (runtime : LivingRuntimeState process) :
    FormalCarrier R Value Var s →ₗ[R] Value s × Value s :=
  stageInventory (R := R) (s := s) readMaterial environment (SourceGeneratedRuntimeMaterialStageAt.generate runtime)

def actualMorphism (runtime : LivingRuntimeState process) :
    SourceGeneratedScalarDifferentialResidual.Morphism
      (evaluation (R := R) (s := s) readMaterial environment runtime)
      (evaluation (R := R) (s := s) readMaterial environment runtime.tick.next) where
  sourceMap := LinearMap.id
  targetMap := successor (R := R) (s := s) readMaterial environment runtime
  commutes := by
    apply LinearMap.ext
    intro word
    exact successor_source (R := R) (s := s) readMaterial environment runtime word

theorem current_zero_iff (runtime : LivingRuntimeState process) (word : FormalCarrier R Value Var s) :
    evaluation (R := R) (s := s) readMaterial environment runtime word = 0 ↔
      firstStage (R := R) (s := s) readMaterial environment runtime word = 0 ∧
      evaluation (R := R) (s := s) readMaterial environment runtime.tick.next word = 0 := by
  constructor
  · intro currentZero
    constructor
    · have fromSource := completion_source_to_actual_stage (R := R) (s := s)
        readMaterial environment runtime 0 word (0 : Fin 1)
      have observed := congrFun (congrArg
        (stageRead (R := R) (s := s) readMaterial environment runtime 0) currentZero) (0 : Fin 1)
      exact fromSource.symm.trans (observed.trans
        (congrFun (map_zero (stageRead (R := R) (s := s) readMaterial environment runtime 0)) 0))
    · have nextRead := successor_source (R := R) (s := s) readMaterial environment runtime word
      exact nextRead.symm.trans ((congrArg
        (successor (R := R) (s := s) readMaterial environment runtime) currentZero).trans
          (map_zero (successor (R := R) (s := s) readMaterial environment runtime)))
  · rintro ⟨firstZero, nextZero⟩
    apply ((completion_fibre_iff (R := R) (s := s) readMaterial environment runtime word 0).mpr ?_).trans
      (map_zero (evaluation (R := R) (s := s) readMaterial environment runtime))
    intro bound index
    apply Eq.trans ?_ (map_zero (stageInventory (R := R) (s := s) readMaterial environment
      ((materialHistory runtime bound).stageAt index))).symm
    change stageInventory (R := R) (s := s) readMaterial environment
      (SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance index.val)) word = 0
    cases depth : index.val with
    | zero =>
        exact firstZero
    | succ previous =>
        have nextReadings := (completion_fibre_iff (R := R) (s := s)
          readMaterial environment runtime.tick.next word 0).mp
            (nextZero.trans (map_zero (evaluation (R := R) (s := s)
              readMaterial environment runtime.tick.next)).symm)
        have nextRead := (nextReadings previous
          (⟨previous, Nat.lt_succ_self previous⟩ : Fin (previous + 1))).trans
            (map_zero (stageInventory (R := R) (s := s) readMaterial environment
              ((materialHistory runtime.tick.next previous).stageAt
                (⟨previous, Nat.lt_succ_self previous⟩ : Fin (previous + 1)))))
        change stageInventory (R := R) (s := s) readMaterial environment
          (SourceGeneratedRuntimeMaterialStageAt.generate (runtime.tick.next.advance previous)) word = 0 at nextRead
        rw [runtime_tail] at nextRead
        exact nextRead

def firstOnNextKernel (runtime : LivingRuntimeState process) :
    LinearMap.ker (evaluation (R := R) (s := s) readMaterial environment runtime.tick.next) →ₗ[R]
      Value s × Value s :=
  (firstStage (R := R) (s := s) readMaterial environment runtime).comp
    (LinearMap.ker (evaluation (R := R) (s := s) readMaterial environment runtime.tick.next)).subtype

theorem firstOnNextKernel_balanced (runtime : LivingRuntimeState process)
    (direction : LinearMap.ker (evaluation (R := R) (s := s) readMaterial environment runtime.tick.next)) :
    (firstOnNextKernel (R := R) (s := s) readMaterial environment runtime direction).1 +
      (firstOnNextKernel (R := R) (s := s) readMaterial environment runtime direction).2 = 0 := by
  have nextFirstZero := ((current_zero_iff (R := R) (s := s)
    readMaterial environment runtime.tick.next direction.val).mp direction.property).1
  have updated := stageInventory_next_old (R := R) (s := s) readMaterial environment
    (SourceGeneratedRuntimeMaterialStageAt.generate runtime) direction.val
  exact updated.symm.trans (congrArg Prod.fst nextFirstZero)

private theorem range_kernelMap_of_first_next
    {C Old Next J : Type*} [AddCommGroup C] [Module R C]
    [AddCommGroup Old] [Module R Old] [AddCommGroup Next] [Module R Next]
    [AddCommGroup J] [Module R J]
    (old : C →ₗ[R] Old) (next : C →ₗ[R] Next) (first : C →ₗ[R] J)
    (morphism : SourceGeneratedScalarDifferentialResidual.Morphism old next)
    (identity : morphism.sourceMap = LinearMap.id)
    (split : ∀ value, old value = 0 ↔ first value = 0 ∧ next value = 0) :
    LinearMap.range (kernelMap morphism) =
      LinearMap.ker (first.comp (LinearMap.ker next).subtype) := by
  ext direction
  constructor
  · rintro ⟨oldDirection, rfl⟩
    change first (kernelMap morphism oldDirection).val = 0
    exact (congrArg first ((kernelMap_val morphism oldDirection).trans
      (LinearMap.congr_fun identity oldDirection.val))).trans
        ((split oldDirection.val).mp oldDirection.property).1
  · intro firstZero
    change first direction.val = 0 at firstZero
    have oldZero := (split direction.val).mpr ⟨firstZero, direction.property⟩
    refine ⟨⟨direction.val, oldZero⟩, ?_⟩
    apply Subtype.ext
    exact (kernelMap_val morphism ⟨direction.val, oldZero⟩).trans
      (LinearMap.congr_fun identity direction.val)

theorem kernelMap_range (runtime : LivingRuntimeState process) :
    LinearMap.range (kernelMap (actualMorphism (R := R) (s := s) readMaterial environment runtime)) =
      LinearMap.ker (firstOnNextKernel (R := R) (s := s) readMaterial environment runtime) :=
  range_kernelMap_of_first_next
    (evaluation (R := R) (s := s) readMaterial environment runtime)
    (evaluation (R := R) (s := s) readMaterial environment runtime.tick.next)
    (firstStage (R := R) (s := s) readMaterial environment runtime)
    (actualMorphism (R := R) (s := s) readMaterial environment runtime) rfl
    (current_zero_iff (R := R) (s := s) readMaterial environment runtime)

end
end SourceOperationRuntime.Fibre
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
