import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDFullPointCochainLocalization
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDNTorsionCohomology

/-!
# Universal BSD finite-place torsion cochain square

For every elliptic curve over `Q`, every natural number `n`, and every finite rational prime,
this module constructs the actual restriction of `E[n](Qbar)` to the local Galois group, its
coefficient map into `E(Qbar_q)`, and the resulting commuting square of homogeneous cochain maps.
The same square is extended to integer degrees.  Its local coefficient leg then generates the
literal mapping cocone that carries the finite-place Kummer obstruction.
-/

namespace SaturationMonoid
namespace UniversalBSDFinitePlaceNTorsionCohomology

open CategoryTheory
open CategoryTheory.Limits
open UniversalBSDGeometricGalois
open UniversalBSDGeometricNTorsion
open UniversalBSDSelmerCohomology
open UniversalBSDNTorsionCohomology
open UniversalBSDFinitePlaceFullPoint

noncomputable section

/-- The actual global `E[n]` coefficient restricted to `G_{Q_q}`. -/
abbrev FiniteLocalNTorsionTopRep
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :=
  TopRep.res (localToGlobalGaloisHom q).toMonoidHom
    (geometricNTorsionIntTopRep source n)

/-- Actual local homogeneous cochains with restricted `E[n]` coefficients. -/
abbrev FiniteLocalNTorsionCochainComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :=
  TopRep.homogeneousCochains (FiniteLocalNTorsionTopRep source n q)

/-- Actual local homogeneous cochains with full geometric-point coefficients. -/
abbrev FinitePointCochainComplex
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :=
  TopRep.homogeneousCochains (finiteGeometricPointTopRep source q)

/-- The restricted global torsion coefficient maps into actual local full points. -/
noncomputable def finiteNTorsionToPointTopRepHom
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    FiniteLocalNTorsionTopRep source n q ⟶
      finiteGeometricPointTopRep source q :=
  ((TopRep.resFunctor (localToGlobalGaloisHom q).toMonoidHom).map
      (geometricNTorsionToGeometricPointTopRepHom source n)) ≫
    globalGeometricPointToFiniteTopRepHom source q

/-- Global-to-local restriction on actual `E[n]` cochains. -/
noncomputable def nTorsionRestrictionCochainMap
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    NTorsionContinuousCochainComplex source n ⟶
      FiniteLocalNTorsionCochainComplex source n q :=
  ContinuousCohomology.cochainsMap
    (localToGlobalGaloisHom q)
    (𝟙 (FiniteLocalNTorsionTopRep source n q))

/-- Local coefficient inclusion from restricted `E[n]` into actual local full points. -/
noncomputable def finiteNTorsionToPointCochainMap
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    FiniteLocalNTorsionCochainComplex source n q ⟶
      FinitePointCochainComplex source q :=
  ContinuousCohomology.cochainsMap
    (ContinuousMonoidHom.id
      (Field.absoluteGaloisGroup (FiniteLocalField q)))
    (finiteNTorsionToPointTopRepHom source n q)

/-- The global coefficient-inclusion/localization square commutes at chain level. -/
theorem nTorsionCochainLocalization_commutes
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    nTorsionToPointCochainMap source n ≫
        fullPointCochainLocalization source q =
      nTorsionRestrictionCochainMap source n q ≫
        finiteNTorsionToPointCochainMap source n q := by
  let phi := localToGlobalGaloisHom q
  let globalTorsion := geometricNTorsionIntTopRep source n
  let globalPoints := geometricPointTopRep source
  let localTorsion := FiniteLocalNTorsionTopRep source n q
  let localPoints := finiteGeometricPointTopRep source q
  let inclusion := geometricNTorsionToGeometricPointTopRepHom source n
  let localization := globalGeometricPointToFiniteTopRepHom source q
  have hleft := ContinuousCohomology.cochainsMap_comp
    (X := globalTorsion) (Y := globalPoints) (Z := localPoints)
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ)) phi
    inclusion localization
  have hright := ContinuousCohomology.cochainsMap_comp
    (X := globalTorsion) (Y := localTorsion) (Z := localPoints)
    phi (ContinuousMonoidHom.id
      (Field.absoluteGaloisGroup (FiniteLocalField q)))
    (𝟙 localTorsion)
    (((TopRep.resFunctor phi.toMonoidHom).map inclusion) ≫ localization)
  have hmaps := hleft.symm.trans hright
  change
    ContinuousCohomology.cochainsMap
          (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ)) inclusion ≫
        ContinuousCohomology.cochainsMap phi localization =
      ContinuousCohomology.cochainsMap phi (𝟙 localTorsion) ≫
        ContinuousCohomology.cochainsMap
          (ContinuousMonoidHom.id
            (Field.absoluteGaloisGroup (FiniteLocalField q)))
          (((TopRep.resFunctor phi.toMonoidHom).map inclusion) ≫ localization)
  exact hmaps

/-- Integer-degree extension of local restricted-torsion cochains. -/
noncomputable abbrev FiniteLocalNTorsionCochainComplexZ
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :=
  (FiniteLocalNTorsionCochainComplex source n q).extend
    ComplexShape.embeddingUpNat

/-- Integer-degree extension of local full-point cochains. -/
noncomputable abbrev FinitePointCochainComplexZ
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :=
  (FinitePointCochainComplex source q).extend ComplexShape.embeddingUpNat

/-- Integer-degree global-to-local restriction on `E[n]` cochains. -/
noncomputable def nTorsionRestrictionCochainMapZ
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat ⟶
      FiniteLocalNTorsionCochainComplexZ source n q :=
  HomologicalComplex.extendMap (nTorsionRestrictionCochainMap source n q)
    ComplexShape.embeddingUpNat

/-- Integer-degree local coefficient inclusion. -/
noncomputable def finiteNTorsionToPointCochainMapZ
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    FiniteLocalNTorsionCochainComplexZ source n q ⟶
      FinitePointCochainComplexZ source q :=
  HomologicalComplex.extendMap (finiteNTorsionToPointCochainMap source n q)
    ComplexShape.embeddingUpNat

/-- Integer-degree localization of the full geometric-point cochains. -/
noncomputable def fullPointCochainLocalizationZ
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    GlobalContinuousCochainComplexZ source ⟶
      FinitePointCochainComplexZ source q :=
  HomologicalComplex.extendMap (fullPointCochainLocalization source q)
    ComplexShape.embeddingUpNat

/-- The same source-generated localization square commutes after extension to integer degrees. -/
theorem nTorsionCochainLocalizationZ_commutes
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    nTorsionToPointCochainMapZ source n ≫
        fullPointCochainLocalizationZ source q =
      nTorsionRestrictionCochainMapZ source n q ≫
        finiteNTorsionToPointCochainMapZ source n q := by
  change
    HomologicalComplex.extendMap (nTorsionToPointCochainMap source n)
          ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap (fullPointCochainLocalization source q)
          ComplexShape.embeddingUpNat =
      HomologicalComplex.extendMap (nTorsionRestrictionCochainMap source n q)
          ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap (finiteNTorsionToPointCochainMap source n q)
          ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp,
    ← HomologicalComplex.extendMap_comp,
    nTorsionCochainLocalization_commutes]

/-- The actual local Kummer obstruction complex `Cone(E[n] → E(Qbar_q))[-1]`. -/
noncomputable def finiteKummerObstructionComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    CochainComplex (TopModuleCat ℤ) ℤ :=
  CochainComplex.mappingCocone
    (finiteNTorsionToPointCochainMapZ source n q)

/-- The canonical map from the local Kummer obstruction complex back to local `E[n]` cochains. -/
noncomputable def finiteKummerObstructionToNTorsion
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    finiteKummerObstructionComplex source n q ⟶
      FiniteLocalNTorsionCochainComplexZ source n q :=
  CochainComplex.mappingCocone.fst
    (finiteNTorsionToPointCochainMapZ source n q)

/-- The source of the single-place Selmer comparison: global cochains plus the actual local
Kummer condition complex. -/
abbrev SinglePlaceSelmerInputComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :=
  ((NTorsionContinuousCochainComplex source n).extend
      ComplexShape.embeddingUpNat) ⊞
    finiteKummerObstructionComplex source n q

/-- The standard comparison `global restriction - local condition` at one finite place. -/
noncomputable def singlePlaceSelmerComparisonMap
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    SinglePlaceSelmerInputComplex source n q ⟶
      FiniteLocalNTorsionCochainComplexZ source n q :=
  biprod.desc
    (nTorsionRestrictionCochainMapZ source n q)
    (-finiteKummerObstructionToNTorsion source n q)

/-- The actual one-finite-place Selmer mapping cocone
`Cone(global E[n] ⊕ local Kummer⁺ → local E[n])[-1]`. -/
noncomputable def singlePlaceRawSelmerComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    CochainComplex (TopModuleCat ℤ) ℤ :=
  CochainComplex.mappingCocone
    (singlePlaceSelmerComparisonMap source n q)

end

end UniversalBSDFinitePlaceNTorsionCohomology
end SaturationMonoid
