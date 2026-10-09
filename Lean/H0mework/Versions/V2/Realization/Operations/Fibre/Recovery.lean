import H0mework.Versions.V2.Realization.Operations.Fibre.Source

/-! The original reverse lifting residual is linearly equivalent to the
actual first-stage image on the next kernel. No representative is chosen,
and both old and effect coordinates are retained. -/

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

private def quotientRangeEquiv
    {K U J : Type*} [AddCommGroup K] [Module R K]
    [AddCommGroup U] [Module R U] [AddCommGroup J] [Module R J]
    (inclusion : U →ₗ[R] K) (read : K →ₗ[R] J)
    (same : LinearMap.range inclusion = LinearMap.ker read) :
    (K ⧸ LinearMap.range inclusion) ≃ₗ[R] LinearMap.range read :=
  (Submodule.quotEquivOfEq (LinearMap.range inclusion) (LinearMap.ker read) same).trans
    (SourceGeneratedScalarDifferentialResidual.residualEquivRange read)

def residualEquiv (runtime : LivingRuntimeState process) :
    LiftingResidual (actualMorphism (R := R) (s := s) readMaterial environment runtime) ≃ₗ[R]
      LinearMap.range (firstOnNextKernel (R := R) (s := s) readMaterial environment runtime) :=
  quotientRangeEquiv
    (kernelMap (actualMorphism (R := R) (s := s) readMaterial environment runtime))
    (firstOnNextKernel (R := R) (s := s) readMaterial environment runtime)
    (kernelMap_range (R := R) (s := s) readMaterial environment runtime)

def recover (runtime : LivingRuntimeState process) :
    LiftingResidual (actualMorphism (R := R) (s := s) readMaterial environment runtime) →ₗ[R] Value s × Value s :=
  (LinearMap.range (firstOnNextKernel (R := R) (s := s) readMaterial environment runtime)).subtype.comp
    (residualEquiv (R := R) (s := s) readMaterial environment runtime).toLinearMap

theorem recover_liftingResidual (runtime : LivingRuntimeState process)
    (source : FormalCarrier R Value Var s)
    (target : SourceOperationLogic.Fibre
      (evaluation (R := R) (s := s) readMaterial environment runtime.tick.next)
      (SourceOperationLogic.q (evaluation (R := R) (s := s) readMaterial environment runtime.tick.next) source)) :
    recover (R := R) (s := s) readMaterial environment runtime
      (liftingResidual (actualMorphism (R := R) (s := s) readMaterial environment runtime) source target) =
        firstStage (R := R) (s := s) readMaterial environment runtime (target.val - source) := by
  unfold recover residualEquiv quotientRangeEquiv liftingResidual
  rw [LinearMap.comp_apply]
  change (((Submodule.quotEquivOfEq _ _ (kernelMap_range (R := R) (s := s) readMaterial environment runtime)).trans
    (residualEquivRange (firstOnNextKernel (R := R) (s := s) readMaterial environment runtime)))
      (Submodule.Quotient.mk (targetCoordinate (actualMorphism (R := R) (s := s) readMaterial environment runtime) source target))).val = _
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

theorem recover_injective (runtime : LivingRuntimeState process) :
    Function.Injective (recover (R := R) (s := s) readMaterial environment runtime) := by
  intro first last same
  apply (residualEquiv (R := R) (s := s) readMaterial environment runtime).injective
  exact Subtype.ext same

theorem recover_balanced (runtime : LivingRuntimeState process)
    (residual : LiftingResidual (actualMorphism (R := R) (s := s) readMaterial environment runtime)) :
    (recover (R := R) (s := s) readMaterial environment runtime residual).1 +
      (recover (R := R) (s := s) readMaterial environment runtime residual).2 = 0 := by
  rcases (residualEquiv (R := R) (s := s) readMaterial environment runtime residual).property with
    ⟨direction, pairEq⟩
  change (residualEquiv (R := R) (s := s) readMaterial environment runtime residual).val.1 +
    (residualEquiv (R := R) (s := s) readMaterial environment runtime residual).val.2 = 0
  rw [← pairEq]
  exact firstOnNextKernel_balanced (R := R) (s := s) readMaterial environment runtime direction

end
end SourceOperationRuntime.Fibre
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
