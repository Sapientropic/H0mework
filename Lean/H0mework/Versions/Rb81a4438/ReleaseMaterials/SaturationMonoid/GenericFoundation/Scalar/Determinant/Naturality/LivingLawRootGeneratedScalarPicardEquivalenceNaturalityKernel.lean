import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.Naturality.LivingLawRootGeneratedScalarDeterminantEquivalenceNaturalityKernel

/-!
# Scalar Picard disposition equivalence naturality

The generated determinant-line equivalence preserves invertibility, the
actual Picard coordinate, global freeness, and the complete trivialized-or-
nontrivial Picard disposition.  No frame is chosen: the positive branch
transports only the proposition that a frame exists, while the negative
branch transports the actual nontrivial Picard coordinate.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarPicardEquivalenceNaturality

open SourceGeneratedScalarConstantRankDeterminant
open SourceGeneratedScalarDeterminantEquivalenceNaturality

noncomputable section

universe r m n p

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]
variable {N : Type n} [AddCommGroup N] [Module R N]
variable {P : Type p} [AddCommGroup P] [Module R P]

/-- Invertibility of the generated determinant line is invariant under the
same source equivalence. -/
theorem determinantLine_invertible_iff
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    Module.Invertible R readout.determinantLine ↔
      Module.Invertible R
        (transportReadout readout equivalence).determinantLine := by
  constructor
  · intro sourceInvertible
    letI : Module.Invertible R readout.determinantLine := sourceInvertible
    exact Module.Invertible.congr (determinantLineEquiv readout equivalence)
  · intro targetInvertible
    letI : Module.Invertible R
        (transportReadout readout equivalence).determinantLine :=
      targetInvertible
    exact Module.Invertible.congr
      (determinantLineEquiv readout equivalence).symm

@[simp] theorem determinantLine_invertible_iff_refl
    (readout : ConstantRankReadout (R := R) M) :
    determinantLine_invertible_iff readout (LinearEquiv.refl R M) =
      Iff.rfl :=
  Subsingleton.elim _ _

theorem determinantLine_invertible_iff_trans
    (readout : ConstantRankReadout (R := R) M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    determinantLine_invertible_iff readout (first.trans second) =
      Iff.trans (determinantLine_invertible_iff readout first)
        (determinantLine_invertible_iff
          (transportReadout readout first) second) :=
  Subsingleton.elim _ _

/-- The transported determinant line is generated as invertible without a
global frame. -/
theorem transported_determinantLine_invertible
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    Module.Invertible R
      (transportReadout readout equivalence).determinantLine :=
  (transportReadout readout equivalence).determinantLine_invertible

/-- Actual Picard coordinates agree under the generated determinant-line
equivalence. -/
theorem determinantPic_natural
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    readout.determinantPic =
      (transportReadout readout equivalence).determinantPic := by
  letI : Module.Invertible R readout.determinantLine :=
    readout.determinantLine_invertible
  letI : Module.Invertible R
      (transportReadout readout equivalence).determinantLine :=
    (transportReadout readout equivalence).determinantLine_invertible
  change CommRing.Pic.mk R readout.determinantLine =
    CommRing.Pic.mk R
      (transportReadout readout equivalence).determinantLine
  exact CommRing.Pic.mk_eq_mk_iff.mpr
    ⟨determinantLineEquiv readout equivalence⟩

@[simp] theorem determinantPic_natural_refl
    (readout : ConstantRankReadout (R := R) M) :
    determinantPic_natural readout (LinearEquiv.refl R M) = rfl :=
  Subsingleton.elim _ _

theorem determinantPic_natural_trans
    (readout : ConstantRankReadout (R := R) M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    determinantPic_natural readout (first.trans second) =
      (determinantPic_natural readout first).trans
        (determinantPic_natural
          (transportReadout readout first) second) :=
  Subsingleton.elim _ _

/-- A global determinant frame exists after transport exactly when it exists
before transport.  No frame value is exposed. -/
theorem determinantLine_free_iff
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    Module.Free R (transportReadout readout equivalence).determinantLine ↔
      Module.Free R readout.determinantLine := by
  constructor
  · intro targetFree
    letI : Module.Free R
        (transportReadout readout equivalence).determinantLine := targetFree
    exact Module.Free.of_equiv
      (determinantLineEquiv readout equivalence).symm
  · intro sourceFree
    letI : Module.Free R readout.determinantLine := sourceFree
    exact Module.Free.of_equiv (determinantLineEquiv readout equivalence)

namespace PicardDisposition

/-- The Picard disposition is proof-irrelevant: the two constructors cannot
coexist because the nontrivial branch explicitly contains nonfreeness. -/
theorem eq_all {readout : ConstantRankReadout (R := R) M}
    (left right : readout.PicardDisposition) : left = right := by
  cases left with
  | trivialized leftFree =>
      cases right with
      | trivialized rightFree =>
          congr
      | nontrivial residual =>
          exact False.elim (residual.nonfree leftFree)
  | nontrivial leftResidual =>
      cases right with
      | trivialized rightFree =>
          exact False.elim (leftResidual.nonfree rightFree)
      | nontrivial rightResidual =>
          congr

instance {readout : ConstantRankReadout (R := R) M} :
    Subsingleton readout.PicardDisposition :=
  ⟨eq_all⟩

end PicardDisposition

/-- Transport the complete Picard disposition, preserving either existence
of a global frame or the explicit nontrivial Picard residual. -/
noncomputable def transportPicardDisposition
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    readout.PicardDisposition →
      (transportReadout readout equivalence).PicardDisposition
  | .trivialized free => .trivialized
      ((determinantLine_free_iff readout equivalence).mpr free)
  | .nontrivial residual => .nontrivial
      { nonfree := fun targetFree => residual.nonfree
          ((determinantLine_free_iff readout equivalence).mp targetFree)
        class_ne_one := fun targetTrivial => residual.class_ne_one
          ((determinantPic_natural readout equivalence).trans
            targetTrivial) }

@[simp] theorem transportPicardDisposition_refl
    (readout : ConstantRankReadout (R := R) M)
    (disposition : readout.PicardDisposition) :
    transportPicardDisposition readout (LinearEquiv.refl R M)
        disposition = disposition :=
  Subsingleton.elim _ _

theorem transportPicardDisposition_trans
    (readout : ConstantRankReadout (R := R) M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P)
    (disposition : readout.PicardDisposition) :
    transportPicardDisposition readout (first.trans second) disposition =
      transportPicardDisposition (transportReadout readout first) second
        (transportPicardDisposition readout first disposition) :=
  Subsingleton.elim _ _

/-- Automatic Picard settlement commutes with source equivalence. -/
theorem transportPicardDisposition_settle
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    transportPicardDisposition readout equivalence readout.settle =
      (transportReadout readout equivalence).settle :=
  Subsingleton.elim _ _

end

end SourceGeneratedScalarPicardEquivalenceNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
