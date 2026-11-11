import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Bounded.LivingLawRootGeneratedScalarBoundedObservationDispositionKernel
import H0mework.Realization.ScalarCofinal.ExactEnvelope

/-!
# Bounded disposition of a scalar cofinal exact envelope

This junction applies the source-neutral six-way bounded observation
classifier to the exact envelope of one rooted scalar cofinal completion.
Finite/projective evidence is still generated only inside the exact branch;
the cofinal source supplies no boundedness or determinant premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalBoundedDisposition

open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarCofinalExactEnvelope
open SourceGeneratedScalarBoundedObservationDisposition

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
  SourceGeneratedScalarBoundedObservationDisposition.Disposition
    evaluation observation

noncomputable def settle :
    Disposition face calculation evaluation observation :=
  SourceGeneratedScalarBoundedObservationDisposition.settle
    evaluation observation

theorem total :
    Nonempty (Disposition face calculation evaluation observation) :=
  ⟨settle face calculation evaluation observation⟩

theorem preserves_root :
    face.root = rootOccurrence.map Prod.fst :=
  rfl

end
end SourceGeneratedScalarCofinalBoundedDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
