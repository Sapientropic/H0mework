import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarProjectiveExteriorKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarProjectiveExteriorLocalizationKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarRankOneProjectiveInvertibleKernel

/-!
# Scalar constant-rank projective determinants

A finite projective carrier with an actual constant stalk-rank law generates
its top exterior determinant line, an invertibility proof, and therefore an
actual Picard coordinate.  The coordinate is trivial exactly when a global
frame exists; otherwise its nontriviality is retained as the residual.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarConstantRankDeterminant

open Module
open SourceGeneratedScalarProjectiveExterior
open SourceGeneratedScalarProjectiveExteriorLocalization
open SourceGeneratedScalarRankOneProjectiveInvertible

noncomputable section

universe r m

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]

/-- Every invertible module has actual stalk rank one. -/
theorem invertible_rankAtStalk
    [Module.Invertible R M] :
    Module.rankAtStalk M = fun _ : PrimeSpectrum R => 1 := by
  funext prime
  letI : Module.Free (Localization.AtPrime prime.asIdeal)
      (LocalizedModule prime.asIdeal.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  exact Module.Invertible.finrank_eq_one _ _

structure Readout where
  finite : Module.Finite R M
  projective : Module.Projective R M
  rank : ℕ
  constantRank : Module.rankAtStalk M =
    fun _ : PrimeSpectrum R => rank

namespace Readout

abbrev determinantLine (readout : Readout (R := R) (M := M)) :=
  ⋀[R]^readout.rank M

theorem determinantLine_finite
    (readout : Readout (R := R) (M := M)) :
    Module.Finite R readout.determinantLine :=
  finiteProjective_exteriorPower_finite readout.finite readout.rank

theorem determinantLine_projective
    (readout : Readout (R := R) (M := M)) :
    Module.Projective R readout.determinantLine :=
  finiteProjective_exteriorPower_projective
    readout.finite readout.projective readout.rank

/-- The determinant line has actual stalk rank one. -/
theorem determinantLine_rankAtStalk
    (readout : Readout (R := R) (M := M)) :
    Module.rankAtStalk readout.determinantLine =
      fun _ : PrimeSpectrum R => 1 := by
  funext prime
  letI : Module.Finite R M := readout.finite
  letI : Module.Projective R M := readout.projective
  letI : Module.Free (Localization.AtPrime prime.asIdeal)
      (LocalizedModule prime.asIdeal.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  change Module.finrank (Localization.AtPrime prime.asIdeal)
      (LocalizedModule prime.asIdeal.primeCompl readout.determinantLine) = 1
  rw [(projectiveExteriorLocalizationEquiv
    readout.projective prime.asIdeal.primeCompl readout.rank).finrank_eq]
  rw [exteriorPower.finrank_eq]
  have localRank := congrFun readout.constantRank prime
  change Module.finrank (Localization.AtPrime prime.asIdeal)
      (LocalizedModule prime.asIdeal.primeCompl M) = readout.rank at localRank
  rw [localRank, Nat.choose_self]

/-- Constant-rank projectivity generates the invertible determinant line. -/
theorem determinantLine_invertible
    (readout : Readout (R := R) (M := M)) :
    Module.Invertible R readout.determinantLine := by
  letI : Module.Finite R readout.determinantLine :=
    readout.determinantLine_finite
  letI : Module.Projective R readout.determinantLine :=
    readout.determinantLine_projective
  exact finiteProjectiveRankOne_invertible readout.determinantLine_rankAtStalk

/-- The actual Picard coordinate of the generated determinant line. -/
noncomputable def determinantPic
    (readout : Readout (R := R) (M := M)) : CommRing.Pic R := by
  letI : Module.Invertible R readout.determinantLine :=
    readout.determinantLine_invertible
  exact CommRing.Pic.mk R readout.determinantLine

theorem determinantPic_eq_one_iff_free
    (readout : Readout (R := R) (M := M)) :
    readout.determinantPic = 1 ↔
      Module.Free R readout.determinantLine := by
  unfold determinantPic
  letI : Module.Invertible R readout.determinantLine :=
    readout.determinantLine_invertible
  exact CommRing.Pic.mk_eq_one_iff_free

structure NontrivialPicardResidual
    (readout : Readout (R := R) (M := M)) : Prop where
  nonfree : ¬ Module.Free R readout.determinantLine
  class_ne_one : readout.determinantPic ≠ 1

inductive PicardDisposition
    (readout : Readout (R := R) (M := M)) : Type (max r m) where
  | trivialized (free : Module.Free R readout.determinantLine)
  | nontrivial (residual : NontrivialPicardResidual readout)

/-- Exact automatic disposition: a global frame or an explicit nontrivial
Picard coordinate. -/
noncomputable def settle
    (readout : Readout (R := R) (M := M)) :
    PicardDisposition readout := by
  classical
  by_cases free : Module.Free R readout.determinantLine
  · exact .trivialized free
  · exact .nontrivial
      { nonfree := free
        class_ne_one := by
          intro classTrivial
          exact free (readout.determinantPic_eq_one_iff_free.mp classTrivial) }

theorem settle_total
    (readout : Readout (R := R) (M := M)) :
    Nonempty (PicardDisposition readout) :=
  ⟨readout.settle⟩

end Readout

end
end SourceGeneratedScalarConstantRankDeterminant
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
