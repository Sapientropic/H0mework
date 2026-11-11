import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarFiniteFreeTopExteriorKernel

/-!
# Total scalar determinant frame torsor

The determinant-frame carrier and its unit torsor exist over every
commutative ring.  A nontrivial ring uses the rank-one top-exterior theorem;
a subsingleton ring transports its unique scalar basis to the determinant
line.  The zero ring is therefore a free determinant branch, not a residual.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarDeterminantFrameTorsor

open Module
open GradedIntegralDeterminantLine
open SourceGeneratedScalarFiniteFreeTopExterior

noncomputable section

universe r o

variable {R : Type r} [CommRing R]
variable {O : Type o} [AddCommGroup O] [Module R O]

private noncomputable def internalFrame (readout : Readout (R := R) (O := O)) :
    DeterminantFrame R readout.determinantLine := by
  classical
  by_cases nontrivial : Nontrivial R
  · letI : Nontrivial R := nontrivial
    letI : Module.Finite R O := readout.finite
    letI : Module.Free R O := readout.free
    exact internalRankOneFrame (readout.determinantLine_finrank nontrivial)
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp nontrivial
    letI : Subsingleton readout.determinantLine :=
      Module.subsingleton R readout.determinantLine
    exact (Basis.singleton Unit R).map
      (LinearEquiv.ofSubsingleton R readout.determinantLine)

noncomputable def unitTorsor (readout : Readout (R := R) (O := O)) :
    CanonicalUnitTorsor R readout.determinantLine :=
  { framesNonempty := ⟨internalFrame readout⟩
    act := unitAct
    one_act := one_unitAct
    mul_act := mul_unitAct
    simplyTransitive := existsUnique_unitAct_eq }

theorem frame_nonempty (readout : Readout (R := R) (O := O)) :
    Nonempty (DeterminantFrame R readout.determinantLine) :=
  (unitTorsor readout).framesNonempty

theorem torsor_nonempty (readout : Readout (R := R) (O := O)) :
    Nonempty (CanonicalUnitTorsor R readout.determinantLine) :=
  ⟨unitTorsor readout⟩

end
end SourceGeneratedScalarDeterminantFrameTorsor
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
