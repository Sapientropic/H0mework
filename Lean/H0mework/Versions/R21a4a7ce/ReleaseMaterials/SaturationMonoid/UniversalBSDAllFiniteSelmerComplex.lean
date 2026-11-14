import Mathlib.CategoryTheory.Limits.Shapes.Products
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDFinitePlaceNTorsionCohomology

/-!
# Universal BSD all-finite-place raw Selmer complex

For every elliptic curve over `Q` and every natural number `n`, this module takes the categorical
product of the actual local `E[n]` and Kummer-condition complexes over all finite rational primes.
The global restriction and local-condition maps then generate the standard all-finite-place
Selmer mapping cocone.  No finite-support, perfectness, Sha, rank, or BSD equality premise is used.
-/

namespace SaturationMonoid
namespace UniversalBSDAllFiniteSelmerComplex

open CategoryTheory
open CategoryTheory.Limits
open UniversalBSDGeometricGalois
open UniversalBSDNTorsionCohomology
open UniversalBSDFinitePlaceNTorsionCohomology

noncomputable section

/-- Product of actual local restricted-`E[n]` cochain complexes over all finite primes. -/
abbrev AllFiniteLocalNTorsionCochainComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  ∏ᶜ (fun q : Nat.Primes ↦
    FiniteLocalNTorsionCochainComplexZ source n q)

/-- Product of actual local Kummer obstruction complexes over all finite primes. -/
abbrev AllFiniteKummerObstructionComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  ∏ᶜ (fun q : Nat.Primes ↦
    finiteKummerObstructionComplex source n q)

/-- Global restriction into every finite-place `E[n]` cochain occurrence. -/
noncomputable def allFiniteNTorsionRestrictionMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat ⟶
      AllFiniteLocalNTorsionCochainComplex source n :=
  Pi.lift (fun q ↦ nTorsionRestrictionCochainMapZ source n q)

@[reassoc (attr := simp)]
theorem allFiniteNTorsionRestrictionMap_π
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    allFiniteNTorsionRestrictionMap source n ≫
        Pi.π (fun v : Nat.Primes ↦
          FiniteLocalNTorsionCochainComplexZ source n v) q =
      nTorsionRestrictionCochainMapZ source n q :=
  Pi.lift_π _ q

/-- Product of the canonical local-condition maps back to local `E[n]` cochains. -/
noncomputable def allFiniteKummerToNTorsionMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    AllFiniteKummerObstructionComplex source n ⟶
      AllFiniteLocalNTorsionCochainComplex source n :=
  Limits.Pi.map (fun q ↦ finiteKummerObstructionToNTorsion source n q)

@[reassoc (attr := simp)]
theorem allFiniteKummerToNTorsionMap_π
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    allFiniteKummerToNTorsionMap source n ≫
        Pi.π (fun v : Nat.Primes ↦
          FiniteLocalNTorsionCochainComplexZ source n v) q =
      Pi.π (fun v : Nat.Primes ↦
          finiteKummerObstructionComplex source n v) q ≫
        finiteKummerObstructionToNTorsion source n q :=
  Limits.Pi.map_π _ q

/-- Global cochains together with all finite-place Kummer local conditions. -/
abbrev AllFiniteSelmerInputComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  ((NTorsionContinuousCochainComplex source n).extend
      ComplexShape.embeddingUpNat) ⊞
    AllFiniteKummerObstructionComplex source n

/-- Standard all-finite comparison `global restriction - local conditions`. -/
noncomputable def allFiniteSelmerComparisonMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    AllFiniteSelmerInputComplex source n ⟶
      AllFiniteLocalNTorsionCochainComplex source n :=
  biprod.desc
    (allFiniteNTorsionRestrictionMap source n)
    (-allFiniteKummerToNTorsionMap source n)

/-- The actual all-finite-place raw Selmer complex
`Cone(global E[n] ⊕ ∏ local Kummer⁺ → ∏ local E[n])[-1]`. -/
noncomputable def allFiniteRawSelmerComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :
    CochainComplex (TopModuleCat ℤ) ℤ :=
  CochainComplex.mappingCocone
    (allFiniteSelmerComparisonMap source n)

end

end UniversalBSDAllFiniteSelmerComplex
end SaturationMonoid
