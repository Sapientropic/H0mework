import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDNTorsionCohomology
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDRealPlaceFullPoint

/-!
# Universal BSD real-place torsion cohomology

The real decomposition morphism and actual full-point coefficient generate the restricted
`E[n]` homogeneous-cochain square, its integer-degree extension, and the real Kummer
`Cone(E[n] → E(Rbar))[-1]`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDAllPlaceSelmerComplex

open CategoryTheory
open CategoryTheory.Limits
open UniversalBSDGeometricGalois
open UniversalBSDGeometricNTorsion
open UniversalBSDSelmerCohomology
open UniversalBSDNTorsionCohomology

noncomputable section
/-! ## Restricted `E[n]` real-place cochain square -/

/-- Global `E[n]` restricted to the real absolute Galois group. -/
abbrev RealLocalNTorsionTopRep
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  TopRep.res realToGlobalGaloisHom.toMonoidHom
    (geometricNTorsionIntTopRep source n)

abbrev RealLocalNTorsionCochainComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  TopRep.homogeneousCochains (RealLocalNTorsionTopRep source n)

abbrev RealPointCochainComplex
    (source : RationalEllipticCurveSource) :=
  TopRep.homogeneousCochains (realGeometricPointTopRep source)

/-- Restricted global torsion maps into actual real full points. -/
noncomputable def realNTorsionToPointTopRepHom
    (source : RationalEllipticCurveSource) (n : ℕ) :
    RealLocalNTorsionTopRep source n ⟶
      realGeometricPointTopRep source :=
  ((TopRep.resFunctor realToGlobalGaloisHom.toMonoidHom).map
      (geometricNTorsionToGeometricPointTopRepHom source n)) ≫
    globalGeometricPointToRealTopRepHom source

/-- Global-to-real restriction on actual `E[n]` cochains. -/
noncomputable def nTorsionRealRestrictionCochainMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    NTorsionContinuousCochainComplex source n ⟶
      RealLocalNTorsionCochainComplex source n :=
  ContinuousCohomology.cochainsMap
    realToGlobalGaloisHom
    (𝟙 (RealLocalNTorsionTopRep source n))

/-- Local coefficient inclusion into actual real full-point cochains. -/
noncomputable def realNTorsionToPointCochainMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    RealLocalNTorsionCochainComplex source n ⟶
      RealPointCochainComplex source :=
  ContinuousCohomology.cochainsMap
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℝ))
    (realNTorsionToPointTopRepHom source n)

/-- Full geometric-point cochain localization at the real place. -/
noncomputable def fullPointRealCochainLocalization
    (source : RationalEllipticCurveSource) :
    GlobalContinuousCochainComplex source ⟶
      RealPointCochainComplex source :=
  ContinuousCohomology.cochainsMap
    realToGlobalGaloisHom
    (globalGeometricPointToRealTopRepHom source)

/-- Global coefficient inclusion and real localization commute at chain level. -/
theorem nTorsionRealCochainLocalization_commutes
    (source : RationalEllipticCurveSource) (n : ℕ) :
    nTorsionToPointCochainMap source n ≫
        fullPointRealCochainLocalization source =
      nTorsionRealRestrictionCochainMap source n ≫
        realNTorsionToPointCochainMap source n := by
  let phi := realToGlobalGaloisHom
  let globalTorsion := geometricNTorsionIntTopRep source n
  let globalPoints := geometricPointTopRep source
  let localTorsion := RealLocalNTorsionTopRep source n
  let localPoints := realGeometricPointTopRep source
  let inclusion := geometricNTorsionToGeometricPointTopRepHom source n
  let localization := globalGeometricPointToRealTopRepHom source
  have hleft := ContinuousCohomology.cochainsMap_comp
    (X := globalTorsion) (Y := globalPoints) (Z := localPoints)
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ)) phi
    inclusion localization
  have hright := ContinuousCohomology.cochainsMap_comp
    (X := globalTorsion) (Y := localTorsion) (Z := localPoints)
    phi (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℝ))
    (𝟙 localTorsion)
    (((TopRep.resFunctor phi.toMonoidHom).map inclusion) ≫ localization)
  have hmaps := hleft.symm.trans hright
  change
    ContinuousCohomology.cochainsMap
          (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ)) inclusion ≫
        ContinuousCohomology.cochainsMap phi localization =
      ContinuousCohomology.cochainsMap phi (𝟙 localTorsion) ≫
        ContinuousCohomology.cochainsMap
          (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℝ))
          (((TopRep.resFunctor phi.toMonoidHom).map inclusion) ≫ localization)
  exact hmaps

/-- Degree-one real localization is the literal homology readout of the same
full-point cochain occurrence. -/
theorem fullPointRealH1Readout_eq_map
    (source : RationalEllipticCurveSource) :
    HomologicalComplex.homologyMap
        (fullPointRealCochainLocalization source) 1 =
      ContinuousCohomology.map realToGlobalGaloisHom
        (globalGeometricPointToRealTopRepHom source) 1 :=
  rfl

/-! ## Integer degrees and the real Kummer condition -/

noncomputable abbrev RealLocalNTorsionCochainComplexZ
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  (RealLocalNTorsionCochainComplex source n).extend
    ComplexShape.embeddingUpNat

noncomputable abbrev RealPointCochainComplexZ
    (source : RationalEllipticCurveSource) :=
  (RealPointCochainComplex source).extend ComplexShape.embeddingUpNat

noncomputable def nTorsionRealRestrictionCochainMapZ
    (source : RationalEllipticCurveSource) (n : ℕ) :
    (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat ⟶
      RealLocalNTorsionCochainComplexZ source n :=
  HomologicalComplex.extendMap
    (nTorsionRealRestrictionCochainMap source n)
    ComplexShape.embeddingUpNat

noncomputable def realNTorsionToPointCochainMapZ
    (source : RationalEllipticCurveSource) (n : ℕ) :
    RealLocalNTorsionCochainComplexZ source n ⟶
      RealPointCochainComplexZ source :=
  HomologicalComplex.extendMap
    (realNTorsionToPointCochainMap source n)
    ComplexShape.embeddingUpNat

noncomputable def fullPointRealCochainLocalizationZ
    (source : RationalEllipticCurveSource) :
    GlobalContinuousCochainComplexZ source ⟶
      RealPointCochainComplexZ source :=
  HomologicalComplex.extendMap
    (fullPointRealCochainLocalization source)
    ComplexShape.embeddingUpNat

theorem nTorsionRealCochainLocalizationZ_commutes
    (source : RationalEllipticCurveSource) (n : ℕ) :
    nTorsionToPointCochainMapZ source n ≫
        fullPointRealCochainLocalizationZ source =
      nTorsionRealRestrictionCochainMapZ source n ≫
        realNTorsionToPointCochainMapZ source n := by
  change
    HomologicalComplex.extendMap (nTorsionToPointCochainMap source n)
          ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap (fullPointRealCochainLocalization source)
          ComplexShape.embeddingUpNat =
      HomologicalComplex.extendMap (nTorsionRealRestrictionCochainMap source n)
          ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap (realNTorsionToPointCochainMap source n)
          ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp,
    ← HomologicalComplex.extendMap_comp,
    nTorsionRealCochainLocalization_commutes]

/-- Actual real Kummer obstruction `Cone(E[n] → E(Rbar))[-1]`. -/
noncomputable def realKummerObstructionComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :
    CochainComplex (TopModuleCat ℤ) ℤ :=
  CochainComplex.mappingCocone
    (realNTorsionToPointCochainMapZ source n)

/-- Canonical real local-condition map back to restricted `E[n]` cochains. -/
noncomputable def realKummerObstructionToNTorsion
    (source : RationalEllipticCurveSource) (n : ℕ) :
    realKummerObstructionComplex source n ⟶
      RealLocalNTorsionCochainComplexZ source n :=
  CochainComplex.mappingCocone.fst
    (realNTorsionToPointCochainMapZ source n)

end

end UniversalBSDAllPlaceSelmerComplex
end SaturationMonoid
