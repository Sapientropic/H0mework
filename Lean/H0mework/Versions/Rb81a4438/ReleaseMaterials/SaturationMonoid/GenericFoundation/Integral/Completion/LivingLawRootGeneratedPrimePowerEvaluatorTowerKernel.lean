import H0mework.Realization.Perfectification.Integral.Completion.LivingLawRootGeneratedPrimePowerCompletionNaturalityKernel
import H0mework.Realization.ScalarCofinal.KernelCompletion
import H0mework.Foundation.Cofinal.KernelCompletion

/-!
# Integral evaluator towers over prime-power completion

An actual additive evaluator history is linearized over `ℤ` and fed directly
to the existing scalar cofinal-kernel completion.  At each stage its kernel
either refines the actual `p^(n+1)` range, producing the canonical map to the
prime-power quotient, or retains an explicit coordinate that the proposed
finite language loses.  Compatible positive stages induce a map of inverse
limits.  The source square factors through the already generated faithful
prime-power coimage, whose universal property supplies every compatible dual
target map.

No root occurrence, source material, finite generation, projectivity,
determinant, or dual nondegeneracy is manufactured here.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedPrimePowerEvaluatorTower

open CategoryTheory CategoryTheory.Limits
open CofinalKernelCompletion
open SourceGeneratedPrimePowerCompletion

noncomputable section

universe u d

variable {L : Type u} [AddCommGroup L]
variable {Carrier : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier stage)]

/-- Canonical `ℤ`-linear form of the existing additive cofinal evaluator
interface. -/
def linearizedData
    (data : AdditiveCofinalEvaluatorData L Carrier) :
    SourceGeneratedScalarCofinalKernelCompletion.Data
      (R := ℤ) (Generator := L) (Carrier := Carrier) where
  evaluator stage := (data.evaluator stage).toIntLinearMap
  transition stage := (data.transition stage).toIntLinearMap

/-- The actual strict commuting law of the additive evaluator history. -/
def StrictCompatible
    (data : AdditiveCofinalEvaluatorData L Carrier) : Prop :=
  ∀ stage, (data.transition stage).comp (data.evaluator (stage + 1)) =
    data.evaluator stage

theorem linearizedCompatible
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (compatible : StrictCompatible data) :
    (linearizedData data).Compatible := by
  intro stage
  apply LinearMap.ext
  intro value
  exact DFunLike.congr_fun (compatible stage) value

def StageKernelRefinesPower
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (stage : Nat) : Prop :=
  (linearizedData data).stageKernel stage ≤ powerRange (L := L) prime stage

/-- Exact coordinate killed by the evaluator but retained by the actual
prime-power observation. -/
structure StageKernelResidual
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (stage : Nat) where
  coordinate : L
  evaluator_zero : data.evaluator stage coordinate = 0
  outside_powerRange : coordinate ∉ powerRange (L := L) prime stage

inductive StageKernelDisposition
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (stage : Nat) : Type u where
  | factors (refines : StageKernelRefinesPower prime data stage)
  | representationResidual
      (residual : StageKernelResidual prime data stage)

noncomputable def settleStageKernel
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (stage : Nat) : StageKernelDisposition prime data stage := by
  classical
  by_cases refines : StageKernelRefinesPower prime data stage
  · exact .factors refines
  · rw [StageKernelRefinesPower, SetLike.not_le_iff_exists] at refines
    let coordinate : L := Classical.choose refines
    have coordinateSpec := Classical.choose_spec refines
    exact .representationResidual
      { coordinate := coordinate
        evaluator_zero := by
          exact LinearMap.mem_ker.mp coordinateSpec.1
        outside_powerRange := coordinateSpec.2 }

theorem stageKernelDisposition_total
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (stage : Nat) : Nonempty (StageKernelDisposition prime data stage) :=
  ⟨settleStageKernel prime data stage⟩

/-- Canonical stage map generated on the positive kernel-refinement branch. -/
def stageToPrime
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (stage : Nat)
    (refines : StageKernelRefinesPower prime data stage) :
    (linearizedData data).StageQuotient stage →ₗ[ℤ]
      StageResidual (L := L) prime stage :=
  ((linearizedData data).stageKernel stage).liftQ
    (stageProjection (L := L) prime stage) (by
      intro value kernelMembership
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact refines kernelMembership)

@[simp] theorem stageToPrime_quotientMap
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (stage : Nat)
    (refines : StageKernelRefinesPower prime data stage) :
    (stageToPrime prime data stage refines).comp
        ((linearizedData data).quotientMap stage) =
      stageProjection (L := L) prime stage := by
  unfold stageToPrime
    SourceGeneratedScalarCofinalKernelCompletion.Data.quotientMap
  exact Submodule.liftQ_mkQ _ _ _

def AllStageKernelsRefinePower
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier) : Prop :=
  ∀ stage, StageKernelRefinesPower prime data stage

theorem stageToPrime_transition
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (compatible : StrictCompatible data)
    (refines : AllStageKernelsRefinePower prime data)
    (stage : Nat) :
    (stageToPrime prime data stage (refines stage)).comp
        ((linearizedData data).quotientTransition
          (linearizedCompatible data compatible) stage) =
      (transition (L := L) prime stage).comp
        (stageToPrime prime data (stage + 1) (refines (stage + 1))) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ := Submodule.mkQ_surjective
    ((linearizedData data).stageKernel (stage + 1)) quotient
  rfl

noncomputable def towerToPrime
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (compatible : StrictCompatible data)
    (refines : AllStageKernelsRefinePower prime data) :
    (linearizedData data).quotientTower
        (linearizedCompatible data compatible) ⟶ tower (L := L) prime :=
  NatTrans.ofOpSequence
    (fun stage ↦ ModuleCat.ofHom
      (stageToPrime prime data stage (refines stage)))
    (fun stage ↦ by
      simp only [SourceGeneratedScalarCofinalKernelCompletion.Data.quotientTower,
        tower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact stageToPrime_transition prime data compatible refines stage)

/-- The actual evaluator-kernel completion maps canonically to the already
closed prime-power completion. -/
noncomputable def completionToPrime
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (compatible : StrictCompatible data)
    (refines : AllStageKernelsRefinePower prime data) :
    (linearizedData data).Completion (linearizedCompatible data compatible) ⟶
      Completion (L := L) prime :=
  limMap (towerToPrime prime data compatible refines)

theorem completionToPrime_restriction
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (compatible : StrictCompatible data)
    (refines : AllStageKernelsRefinePower prime data)
    (stage : Nat) :
    completionToPrime prime data compatible refines ≫
        restriction (L := L) prime stage =
      (linearizedData data).restriction
          (linearizedCompatible data compatible) stage ≫
        ModuleCat.ofHom (stageToPrime prime data stage (refines stage)) :=
  limMap_π (towerToPrime prime data compatible refines) (Opposite.op stage)

theorem completionToPrime_source_naturality
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (compatible : StrictCompatible data)
    (refines : AllStageKernelsRefinePower prime data) :
    (linearizedData data).completionMap (linearizedCompatible data compatible) ≫
        completionToPrime prime data compatible refines =
      canonicalMap (L := L) prime := by
  apply (limit.isLimit (tower (L := L) prime)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  calc
    ((linearizedData data).completionMap
          (linearizedCompatible data compatible) ≫
        completionToPrime prime data compatible refines) ≫
          restriction (L := L) prime stage =
        (linearizedData data).completionMap
            (linearizedCompatible data compatible) ≫
          (completionToPrime prime data compatible refines ≫
            restriction (L := L) prime stage) := by rw [Category.assoc]
    _ = ModuleCat.ofHom (stageProjection (L := L) prime stage) := by
      rw [completionToPrime_restriction, ← Category.assoc,
        SourceGeneratedScalarCofinalKernelCompletion.Data.completionMap_restriction]
      apply ModuleCat.hom_ext
      exact stageToPrime_quotientMap prime data stage (refines stage)
    _ = canonicalMap (L := L) prime ≫
          restriction (L := L) prime stage := by
      rw [canonicalMap_restriction]

/-- The same source square reaches the prime completion through its generated
faithful coimage; this is not a retraction from the completed ambient. -/
theorem completionToPrime_source_coimage
    (prime : Nat.Primes)
    (data : AdditiveCofinalEvaluatorData L Carrier)
    (compatible : StrictCompatible data)
    (refines : AllStageKernelsRefinePower prime data) :
    (linearizedData data).completionMap (linearizedCompatible data compatible) ≫
        completionToPrime prime data compatible refines =
      ModuleCat.ofHom (coimageProjection (L := L) prime) ≫
        ModuleCat.ofHom (coimageRealization (L := L) prime) := by
  rw [completionToPrime_source_naturality]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact (LinearMap.congr_fun
    (coimageRealization_projection (L := L) prime) value).symm

/-! ## Universal compatible dual target -/

structure CompatibleDualTarget
    (prime : Nat.Primes) (DualTarget : Type d)
    [AddCommGroup DualTarget] where
  evaluation : L →ₗ[ℤ] Module.Dual ℤ DualTarget
  killsSeparation : SeparationKernel (L := L) prime ≤
    LinearMap.ker evaluation

def dualTargetMap
    (prime : Nat.Primes)
    {DualTarget : Type d} [AddCommGroup DualTarget]
    (target : CompatibleDualTarget (L := L) prime DualTarget) :
    FaithfulCoimage (L := L) prime →ₗ[ℤ] Module.Dual ℤ DualTarget :=
  coimageFactor prime target.evaluation target.killsSeparation

@[simp] theorem dualTargetMap_readback
    (prime : Nat.Primes)
    {DualTarget : Type d} [AddCommGroup DualTarget]
    (target : CompatibleDualTarget (L := L) prime DualTarget) :
    (dualTargetMap prime target).comp (coimageProjection (L := L) prime) =
      target.evaluation :=
  coimageFactor_projection prime target.evaluation target.killsSeparation

theorem dualTargetMap_universal
    (prime : Nat.Primes)
    {DualTarget : Type d} [AddCommGroup DualTarget]
    (target : CompatibleDualTarget (L := L) prime DualTarget) :
    ∃! factor : FaithfulCoimage (L := L) prime →ₗ[ℤ]
        Module.Dual ℤ DualTarget,
      factor.comp (coimageProjection (L := L) prime) = target.evaluation :=
  coimage_universal prime target.evaluation target.killsSeparation

end
end SourceGeneratedPrimePowerEvaluatorTower
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
