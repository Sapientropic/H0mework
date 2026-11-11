import H0mework.Realization.ScalarCofinal.ExactEnvelope
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Observation.LivingLawRootGeneratedScalarObservationDispositionKernel

/-!
# Observation disposition on a scalar cofinal exact envelope

Every `R`-linear observation of the exact envelope of a rooted cofinal
completion is classified without deleting either side of its inverse fibre.
An observation may be exact, kernel-only, coverage-only, or carry both
explicit residual coordinates.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalObservationDisposition

open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarCofinalExactEnvelope
open SourceGeneratedScalarObservationDisposition

noncomputable section

universe r u w d o

variable {R : Type r} [CommRing R]
variable {Root : Type w}
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {StageCarrier : Nat → Type u}
variable [∀ stage, AddCommGroup (StageCarrier stage)]
variable [∀ stage, Module R (StageCarrier stage)]
variable {rootOccurrence : RootedAccountedUnfolding
  (Root × Data (R := R) (Generator := Generator) (Carrier := StageCarrier))}
variable (face : Face rootOccurrence)
variable (calculation : Face.GeneratedCompatibilityCalculationAt face)
variable {DualTarget : Type d}
variable [AddCommGroup DualTarget] [Module R DualTarget]
variable (evaluation : face.completion calculation →ₗ[R]
  Module.Dual R DualTarget)
variable {Observation : Type o}
variable [AddCommGroup Observation] [Module R Observation]
variable (observation :
  SourceGeneratedScalarCofinalExactEnvelope.Carrier
      face calculation evaluation →ₗ[R] Observation)

abbrev Disposition :=
  SourceGeneratedScalarObservationDisposition.Disposition observation

/-- Total four-way inverse-fibre disposition of the bounded observation. -/
noncomputable def settle :
    Disposition face calculation evaluation observation :=
  SourceGeneratedScalarObservationDisposition.settle observation

theorem total :
    Nonempty (Disposition face calculation evaluation observation) :=
  ⟨settle face calculation evaluation observation⟩

/-- The observation seen directly from the original source. -/
def sourceObservation : Generator →ₗ[R] Observation :=
  observation.comp
    (SourceGeneratedScalarCofinalExactEnvelope.sourceMap
      face calculation evaluation)

theorem sourceObservation_factorization :
    sourceObservation face calculation evaluation observation =
      observation.comp
        (SourceGeneratedScalarCofinalExactEnvelope.sourceMap
          face calculation evaluation) :=
  rfl

theorem exact_iff_bijective :
    (∃ equivalence :
        SourceGeneratedScalarCofinalExactEnvelope.Carrier
            face calculation evaluation ≃ₗ[R] Observation,
      settle face calculation evaluation observation = .exact equivalence) ↔
      Function.Bijective observation :=
  SourceGeneratedScalarObservationDisposition.settle_exact_iff_bijective
    observation

end
end SourceGeneratedScalarCofinalObservationDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
