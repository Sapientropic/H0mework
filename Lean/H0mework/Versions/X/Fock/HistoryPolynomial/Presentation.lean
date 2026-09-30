import H0mework.Versions.X.Fock.HistoryPolynomial.Relations
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B)

theorem project_surjective : Function.Surjective (project read) := by
  intro value
  obtain ⟨word, same⟩ := Submodule.mkQ_surjective
    (LinearMap.ker (sourceMap nativeAction (SourceOperationNative.observer process read))) ((retainObserved read).symm value)
  refine ⟨retained word, ?_⟩
  rw [project_source]
  exact (congrArg (retainObserved read) same).trans ((retainObserved read).apply_symm_apply value)

def present : Polynomial ℤ →ₗ[Polynomial ℤ] ObservedModel read :=
  (project read).comp polynomialEquiv.symm.toLinearMap

theorem present_source (polynomial : Polynomial ℤ) :
    present read polynomial = retainObserved read
      (projection nativeAction (SourceOperationNative.observer process read) (program polynomial)) := by
  have same : polynomialEquiv.symm polynomial = retained (program polynomial) :=
    polynomialEquiv.injective ((polynomialEquiv.apply_symm_apply polynomial).trans (polynomial_program polynomial).symm)
  exact (congrArg (project read) same).trans (project_source read (program polynomial))

theorem present_surjective : Function.Surjective (present read) :=
  (project_surjective read).comp polynomialEquiv.symm.surjective

theorem presentation_kernel : LinearMap.ker (present read) = relationIdeal read := by
  ext polynomial
  change present read polynomial = 0 ↔ polynomial ∈ relationIdeal read
  have actual : present read polynomial = project read (retained (program polynomial)) :=
    (present_source read polynomial).trans (project_source read (program polynomial)).symm
  rw [actual]
  exact (relations_source read (program polynomial)).trans (ideal_is_source read polynomial).symm

def originalPresentation : (Polynomial ℤ ⧸ relationIdeal read) ≃ₗ[Polynomial ℤ] ObservedModel read :=
  (Submodule.quotEquivOfEq _ _ (presentation_kernel read).symm).trans
    (LinearMap.quotKerEquivOfSurjective (present read) (present_surjective read))

theorem presentation_reads (polynomial : Polynomial ℤ) :
    originalPresentation read (Submodule.Quotient.mk polynomial) =
      retainObserved read (projection nativeAction (SourceOperationNative.observer process read) (program polynomial)) := by
  change present read polynomial = _
  exact present_source read polynomial

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
