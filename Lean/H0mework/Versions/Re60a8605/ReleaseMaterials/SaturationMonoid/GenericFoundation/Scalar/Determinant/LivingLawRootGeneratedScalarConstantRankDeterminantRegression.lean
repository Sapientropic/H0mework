import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarConstantRankDeterminantKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarNontrivialPicardLineRegression

/-!
# Scalar constant-rank determinant regression

The same generic producer is exercised on a trivial free line and on the
actual nontrivial elliptic Picard line.  The first generates a global frame;
the second generates a nontrivial Picard residual.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarConstantRankDeterminantRegression

open SourceGeneratedScalarConstantRankDeterminant
open SourceGeneratedScalarNontrivialPicardLineRegression

noncomputable section

namespace FreeIntegerLine

noncomputable def readout : Readout (R := ℤ) (M := ℤ) where
  finite := inferInstance
  projective := inferInstance
  rank := 1
  constantRank := invertible_rankAtStalk

theorem determinantPic_trivial : readout.determinantPic = 1 := by
  apply readout.determinantPic_eq_one_iff_free.mpr
  infer_instance

theorem settles_trivialized :
    ∃ free : Module.Free ℤ readout.determinantLine,
      readout.settle = .trivialized free := by
  let free : Module.Free ℤ readout.determinantLine := inferInstance
  refine ⟨free, ?_⟩
  simp [SourceGeneratedScalarConstantRankDeterminant.Readout.settle, free]

end FreeIntegerLine

namespace EllipticPicardLine

noncomputable def readout :
    Readout (R := RationalRing) (M := RationalPicLine) where
  finite := inferInstance
  projective := inferInstance
  rank := 1
  constantRank := invertible_rankAtStalk

theorem determinantLine_not_free :
    ¬ Module.Free RationalRing readout.determinantLine := by
  change ¬ Module.Free RationalRing (⋀[RationalRing]^1 RationalPicLine)
  intro free
  letI : Module.Free RationalRing (⋀[RationalRing]^1 RationalPicLine) := free
  letI : Module.Free RationalRing RationalPicLine :=
    Module.Free.of_equiv (exteriorPower.oneEquiv RationalRing RationalPicLine)
  exact rationalPointPic_not_free inferInstance

theorem determinantPic_nontrivial : readout.determinantPic ≠ 1 := by
  intro classTrivial
  exact determinantLine_not_free
    (readout.determinantPic_eq_one_iff_free.mp classTrivial)

theorem settles_nontrivial :
    ∃ residual : Readout.NontrivialPicardResidual readout,
      readout.settle = .nontrivial residual := by
  let residual : Readout.NontrivialPicardResidual readout :=
    { nonfree := determinantLine_not_free
      class_ne_one := determinantPic_nontrivial }
  refine ⟨residual, ?_⟩
  simp [SourceGeneratedScalarConstantRankDeterminant.Readout.settle,
    determinantLine_not_free]

end EllipticPicardLine

end
end SourceGeneratedScalarConstantRankDeterminantRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarProjectiveExteriorLocalization.projectiveExteriorLocalizationEquiv_ιMulti
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarConstantRankDeterminant.Readout.determinantLine_rankAtStalk
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarConstantRankDeterminant.Readout.determinantLine_invertible
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarConstantRankDeterminantRegression.FreeIntegerLine.settles_trivialized
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarConstantRankDeterminantRegression.EllipticPicardLine.settles_nontrivial
