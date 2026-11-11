import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Bounded.LivingLawRootGeneratedScalarFiniteProjectiveDualityKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarPicardBoundaryKernel
import H0mework.Realization.Determinant.GradedIntegralLine

/-!
# Scalar finite-free top exterior line

A finite-projective-free bounded readout generates its top exterior line over
any commutative ring.  Rank one is asserted only when the coefficient ring is
nontrivial; the line itself remains defined over the zero ring.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarFiniteFreeTopExterior

open SourceGeneratedScalarFiniteProjectiveDuality

noncomputable section

universe r o

variable {R : Type r} [CommRing R]
variable {O : Type o} [AddCommGroup O] [Module R O]

structure Readout where
  finite : Module.Finite R O
  projective : Module.Projective R O
  duality : TensorDuality (R := R) O
  free : Module.Free R O

namespace Readout

abbrev determinantLine (readout : Readout (R := R) (O := O)) :=
  let _ : Module.Finite R O := readout.finite
  let _ : Module.Free R O := readout.free
  ⋀[R]^(Module.finrank R O) O

theorem determinantLine_finrank (readout : Readout (R := R) (O := O))
    (nontrivial : Nontrivial R) :
    Module.finrank R readout.determinantLine = 1 := by
  letI : Nontrivial R := nontrivial
  letI : Module.Finite R O := readout.finite
  letI : Module.Free R O := readout.free
  rw [determinantLine, exteriorPower.finrank_eq]
  simp

theorem determinantLine_invertible
    (readout : Readout (R := R) (O := O)) :
    Module.Invertible R readout.determinantLine := by
  letI : Module.Finite R O := readout.finite
  letI : Module.Free R O := readout.free
  exact SourceGeneratedScalarPicardBoundary.freeTopExteriorInvertible

noncomputable def determinantPic
    (readout : Readout (R := R) (O := O)) : CommRing.Pic R := by
  letI : Module.Finite R O := readout.finite
  letI : Module.Free R O := readout.free
  letI : Module.Invertible R readout.determinantLine :=
    readout.determinantLine_invertible
  exact CommRing.Pic.mk R readout.determinantLine

theorem determinantPic_eq_one
    (readout : Readout (R := R) (O := O)) :
    readout.determinantPic = 1 := by
  unfold determinantPic
  letI : Module.Finite R O := readout.finite
  letI : Module.Free R O := readout.free
  letI : Module.Free R readout.determinantLine := inferInstance
  letI : Module.Invertible R readout.determinantLine :=
    readout.determinantLine_invertible
  exact CommRing.Pic.mk_eq_one R readout.determinantLine

end Readout

end
end SourceGeneratedScalarFiniteFreeTopExterior
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
