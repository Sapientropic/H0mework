import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalBoundedDispositionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarBoundedProjectiveDeterminantDispositionKernel

/-!
# Projective determinant disposition of a scalar cofinal envelope

The same rooted scalar cofinal completion now reaches the full rank/Picard
determinant producer.  No finite, projective, constant-rank, free, frame or
determinant evidence is supplied by the caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalProjectiveDeterminantDisposition

open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarCofinalExactEnvelope
open SourceGeneratedScalarCofinalBoundedDisposition

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

abbrev BoundedDisposition :=
  SourceGeneratedScalarCofinalBoundedDisposition.Disposition
    face calculation evaluation observation

noncomputable def bounded :
    BoundedDisposition face calculation evaluation observation :=
  SourceGeneratedScalarCofinalBoundedDisposition.settle
    face calculation evaluation observation

abbrev DeterminantDisposition :=
  SourceGeneratedScalarBoundedProjectiveDeterminantDisposition.Disposition
    (bounded face calculation evaluation observation)

noncomputable def settle :
    DeterminantDisposition face calculation evaluation observation :=
  SourceGeneratedScalarBoundedProjectiveDeterminantDisposition.settle
    (bounded face calculation evaluation observation)

theorem total :
    Nonempty
      (DeterminantDisposition face calculation evaluation observation) :=
  ⟨settle face calculation evaluation observation⟩

theorem preserves_root : face.root = rootOccurrence.map Prod.fst :=
  rfl

end
end SourceGeneratedScalarCofinalProjectiveDeterminantDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
