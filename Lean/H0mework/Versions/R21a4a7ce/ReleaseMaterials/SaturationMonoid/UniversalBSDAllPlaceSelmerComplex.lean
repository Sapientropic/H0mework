import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDAllFiniteSelmerComplex
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDRealPlaceNTorsionCohomology

/-!
# Universal BSD all-place raw Selmer complex

For every elliptic curve over `Q` and natural number `n`, the product over all finite-place
Kummer conditions and the real Kummer condition are combined before one final comparison and
one final mapping cocone.  No perfectness, Sha, rank, or BSD equality premise is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDAllPlaceSelmerComplex

open CategoryTheory
open CategoryTheory.Limits
open UniversalBSDGeometricGalois
open UniversalBSDNTorsionCohomology
open UniversalBSDAllFiniteSelmerComplex

noncomputable section
/-! ## One all-place comparison and one final mapping cocone -/

/-- All finite local restricted-torsion cochains together with the real one. -/
abbrev AllPlaceLocalNTorsionCochainComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  AllFiniteLocalNTorsionCochainComplex source n ⊞
    RealLocalNTorsionCochainComplexZ source n

/-- All finite Kummer conditions together with the real Kummer condition. -/
abbrev AllPlaceKummerObstructionComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  AllFiniteKummerObstructionComplex source n ⊞
    realKummerObstructionComplex source n

/-- Global restriction into the finite product and the real occurrence. -/
noncomputable def allPlaceNTorsionRestrictionMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat ⟶
      AllPlaceLocalNTorsionCochainComplex source n :=
  biprod.lift
    (allFiniteNTorsionRestrictionMap source n)
    (nTorsionRealRestrictionCochainMapZ source n)

@[reassoc (attr := simp)]
theorem allPlaceNTorsionRestrictionMap_fst
    (source : RationalEllipticCurveSource) (n : ℕ) :
    allPlaceNTorsionRestrictionMap source n ≫ biprod.fst =
      allFiniteNTorsionRestrictionMap source n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem allPlaceNTorsionRestrictionMap_snd
    (source : RationalEllipticCurveSource) (n : ℕ) :
    allPlaceNTorsionRestrictionMap source n ≫ biprod.snd =
      nTorsionRealRestrictionCochainMapZ source n :=
  biprod.lift_snd _ _

/-- Product of the finite and real local-condition maps. -/
noncomputable def allPlaceKummerToNTorsionMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    AllPlaceKummerObstructionComplex source n ⟶
      AllPlaceLocalNTorsionCochainComplex source n :=
  biprod.map
    (allFiniteKummerToNTorsionMap source n)
    (realKummerObstructionToNTorsion source n)

@[reassoc (attr := simp)]
theorem allPlaceKummerToNTorsionMap_fst
    (source : RationalEllipticCurveSource) (n : ℕ) :
    allPlaceKummerToNTorsionMap source n ≫ biprod.fst =
      biprod.fst ≫ allFiniteKummerToNTorsionMap source n :=
  biprod.map_fst _ _

@[reassoc (attr := simp)]
theorem allPlaceKummerToNTorsionMap_snd
    (source : RationalEllipticCurveSource) (n : ℕ) :
    allPlaceKummerToNTorsionMap source n ≫ biprod.snd =
      biprod.snd ≫ realKummerObstructionToNTorsion source n :=
  biprod.map_snd _ _

/-- Global cochains plus `(all finite Kummer⁺ × real Kummer⁺)`. -/
abbrev AllPlaceSelmerInputComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  ((NTorsionContinuousCochainComplex source n).extend
      ComplexShape.embeddingUpNat) ⊞
    AllPlaceKummerObstructionComplex source n

/-- Standard all-place comparison `global restriction - local conditions`. -/
noncomputable def allPlaceSelmerComparisonMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    AllPlaceSelmerInputComplex source n ⟶
      AllPlaceLocalNTorsionCochainComplex source n :=
  biprod.desc
    (allPlaceNTorsionRestrictionMap source n)
    (-allPlaceKummerToNTorsionMap source n)

/-- Actual all-place raw Selmer complex
`Cone(global ⊕ (∏ finite Kummer⁺ ⊕ real Kummer⁺)
  → (∏ finite E[n] ⊕ real E[n]))[-1]`. -/
noncomputable def allPlaceRawSelmerComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :
    CochainComplex (TopModuleCat ℤ) ℤ :=
  CochainComplex.mappingCocone
    (allPlaceSelmerComparisonMap source n)

end

end UniversalBSDAllPlaceSelmerComplex
end SaturationMonoid
