import H0mework.Fock.HistoryPolynomial.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B)

abbrev ObservedModel := Module.AEval'
  (modelAction nativeAction (SourceOperationNative.observer process read))

def retainObserved : Model nativeAction (SourceOperationNative.observer process read) ≃ₗ[ℤ] ObservedModel read :=
  Module.AEval'.of (modelAction nativeAction (SourceOperationNative.observer process read))

def project : DynamicSource →ₗ[Polynomial ℤ] ObservedModel read :=
  LinearMap.ofAEval nativeAction
    ((retainObserved read).toLinearMap.comp (projection nativeAction (SourceOperationNative.observer process read)))
    (fun word =>
      (congrArg (retainObserved read)
        (modelAction_source nativeAction (SourceOperationNative.observer process read) word).symm).trans
      (Module.AEval'.X_smul_of (modelAction nativeAction (SourceOperationNative.observer process read))
        (projection nativeAction (SourceOperationNative.observer process read) word)).symm)

def relations : Submodule (Polynomial ℤ) DynamicSource := LinearMap.ker (project read)

theorem project_source (word : SourceOperationNative.Carrier process) :
    project read (retained word) = retainObserved read
      (projection nativeAction (SourceOperationNative.observer process read) word) := rfl

theorem relations_source (word : SourceOperationNative.Carrier process) :
    retained word ∈ relations read ↔
      ∀ step : Nat, SourceOperationNative.observer process read ((nativeAction ^ step) word) = 0 := by
  change project read (retained word) = 0 ↔ _
  rw [project_source, map_eq_zero_iff _ (retainObserved read).injective]
  simpa only [map_zero] using model_fibre_iff nativeAction (SourceOperationNative.observer process read) word 0

theorem relations_finite : (relations read).FG := IsNoetherian.noetherian _

def relationIdeal : Ideal (Polynomial ℤ) := (relations read).map polynomialEquiv.toLinearMap

theorem ideal_is_source (polynomial : Polynomial ℤ) :
    polynomial ∈ relationIdeal read ↔
      ∀ step : Nat, SourceOperationNative.observer process read ((nativeAction ^ step) (program polynomial)) = 0 := by
  rw [← relations_source]
  constructor
  · rintro ⟨word, member, same⟩
    have original : word = retained (program polynomial) :=
      polynomialEquiv.injective (same.trans (polynomial_program polynomial).symm)
    exact original ▸ member
  · intro member
    exact ⟨retained (program polynomial), member, polynomial_program polynomial⟩

theorem ideal_finite : (relationIdeal read).FG := Ideal.fg_of_isNoetherianRing _

theorem prime_ideal_zero : relationIdeal rawField = ⊥ := by
  apply le_antisymm
  · intro polynomial member
    have invisible := (ideal_is_source rawField polynomial).mp member
    have sourceZero : program polynomial = 0 := by
      have inKernel := (mem_kernel_iff nativeAction observation (program polynomial)).mpr invisible
      rw [kernel_zero sourceOwner] at inKernel
      exact inKernel
    apply (Submodule.mem_bot (R := Polynomial ℤ)).mpr
    apply program_injective
    have zeroProgram : program 0 = 0 := by unfold program; rw [map_zero]; rfl
    exact sourceZero.trans zeroProgram.symm
  · exact bot_le

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
