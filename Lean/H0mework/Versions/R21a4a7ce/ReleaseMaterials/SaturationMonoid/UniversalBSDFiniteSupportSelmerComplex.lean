import Mathlib.CategoryTheory.Limits.Shapes.Products
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDAllPlaceSelmerComplex

/-!
# Universal BSD source-generated finite-support Selmer complex

This module derives a finite set of rational primes from the chosen Weierstrass equation and a
coefficient prime.  It then assembles the corresponding finite-local-plus-real raw Selmer cone.
It does not identify this finite-support cone with the all-place Selmer complex; that comparison
requires the separate outside-support unramified/Kummer producer.
-/

namespace SaturationMonoid
namespace UniversalBSDFiniteSupportSelmer

open CategoryTheory
open CategoryTheory.Limits
open UniversalBSDGeometricGalois
open UniversalBSDNTorsionCohomology
open UniversalBSDFinitePlaceNTorsionCohomology
open UniversalBSDAllPlaceSelmerComplex

noncomputable section

/-- Prime factors of a natural number, bundled as actual rational primes. -/
noncomputable def primeFactorsAsPrimes (N : ℕ) : Finset Nat.Primes :=
  N.primeFactors.attach.image fun q ↦
    ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩

theorem mem_primeFactorsAsPrimes_iff (N : ℕ) (q : Nat.Primes) :
    q ∈ primeFactorsAsPrimes N ↔ (q : ℕ) ∈ N.primeFactors := by
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨r, hr, hqr⟩
    simpa only [Subtype.ext_iff] using hqr ▸ r.property
  · intro hq
    apply Finset.mem_image.mpr
    refine ⟨⟨(q : ℕ), hq⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- A nonzero natural carrying every denominator of the chosen equation and its discriminant. -/
def equationSupportNat (source : RationalEllipticCurveSource) : ℕ :=
  source.curve.a₁.den * source.curve.a₂.den * source.curve.a₃.den *
    source.curve.a₄.den * source.curve.a₆.den * source.curve.Δ.den *
      source.curve.Δ.num.natAbs

theorem equationSupportNat_ne_zero (source : RationalEllipticCurveSource) :
    equationSupportNat source ≠ 0 := by
  unfold equationSupportNat
  apply mul_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero source.curve.a₁.den_ne_zero source.curve.a₂.den_ne_zero)
            source.curve.a₃.den_ne_zero)
          source.curve.a₄.den_ne_zero)
        source.curve.a₆.den_ne_zero)
      source.curve.Δ.den_ne_zero
  · exact Int.natAbs_ne_zero.mpr
      (Rat.num_ne_zero.mpr source.curve.isUnit_Δ.ne_zero)

/-- Finite equation support enlarged by the selected coefficient prime and by
`2`.  The latter keeps every outside-support local occurrence in the odd
residue-characteristic range required by the source-generated Lang face. -/
noncomputable def finitePrimeSupport
    (source : RationalEllipticCurveSource) (p : Nat.Primes) :
    Finset Nat.Primes :=
  insert (⟨2, Nat.prime_two⟩ : Nat.Primes)
    (insert p (primeFactorsAsPrimes (equationSupportNat source)))

@[simp]
theorem coefficientPrime_mem_finitePrimeSupport
    (source : RationalEllipticCurveSource) (p : Nat.Primes) :
    p ∈ finitePrimeSupport source p :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

@[simp]
theorem two_mem_finitePrimeSupport
    (source : RationalEllipticCurveSource) (p : Nat.Primes) :
    (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ finitePrimeSupport source p :=
  Finset.mem_insert_self _ _

/-- Supported arithmetic places: the generated finite primes plus the real place. -/
abbrev SupportedArithmeticPlace
    (source : RationalEllipticCurveSource) (p : Nat.Primes) :=
  Option ↥(finitePrimeSupport source p)

/-- Local restricted-torsion cochains at a supported finite or real place. -/
abbrev supportedLocalNTorsionAt
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :
    SupportedArithmeticPlace source p → CochainComplex (TopModuleCat ℤ) ℤ
  | none => RealLocalNTorsionCochainComplexZ source n
  | some q => FiniteLocalNTorsionCochainComplexZ source n q.1

/-- Kummer local-condition complexes at a supported finite or real place. -/
abbrev supportedKummerAt
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :
    SupportedArithmeticPlace source p → CochainComplex (TopModuleCat ℤ) ℤ
  | none => realKummerObstructionComplex source n
  | some q => finiteKummerObstructionComplex source n q.1

noncomputable def supportedRestrictionAt
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes)
    (v : SupportedArithmeticPlace source p) :
    (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat ⟶
      supportedLocalNTorsionAt source n p v :=
  match v with
  | none => nTorsionRealRestrictionCochainMapZ source n
  | some q => nTorsionRestrictionCochainMapZ source n q.1

noncomputable def supportedKummerToLocalAt
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes)
    (v : SupportedArithmeticPlace source p) :
    supportedKummerAt source n p v ⟶
      supportedLocalNTorsionAt source n p v :=
  match v with
  | none => realKummerObstructionToNTorsion source n
  | some q => finiteKummerObstructionToNTorsion source n q.1

/-- Finite categorical product of all generated supported local coefficients. -/
abbrev SupportedLocalNTorsionComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :=
  ∏ᶜ (supportedLocalNTorsionAt source n p)

/-- Finite categorical product of all generated supported Kummer conditions. -/
abbrev SupportedKummerComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :=
  ∏ᶜ (supportedKummerAt source n p)

noncomputable def supportedRestrictionMap
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :
    (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat ⟶
      SupportedLocalNTorsionComplex source n p :=
  Pi.lift (supportedRestrictionAt source n p)

@[reassoc (attr := simp)]
theorem supportedRestrictionMap_π
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes)
    (v : SupportedArithmeticPlace source p) :
    supportedRestrictionMap source n p ≫
        Pi.π (supportedLocalNTorsionAt source n p) v =
      supportedRestrictionAt source n p v :=
  Pi.lift_π _ v

noncomputable def supportedKummerToLocalMap
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :
    SupportedKummerComplex source n p ⟶
      SupportedLocalNTorsionComplex source n p :=
  Limits.Pi.map (supportedKummerToLocalAt source n p)

@[reassoc (attr := simp)]
theorem supportedKummerToLocalMap_π
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes)
    (v : SupportedArithmeticPlace source p) :
    supportedKummerToLocalMap source n p ≫
        Pi.π (supportedLocalNTorsionAt source n p) v =
      Pi.π (supportedKummerAt source n p) v ≫
        supportedKummerToLocalAt source n p v :=
  Limits.Pi.map_π _ v

abbrev FiniteSupportSelmerInputComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :=
  ((NTorsionContinuousCochainComplex source n).extend
      ComplexShape.embeddingUpNat) ⊞
    SupportedKummerComplex source n p

noncomputable def finiteSupportSelmerComparisonMap
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :
    FiniteSupportSelmerInputComplex source n p ⟶
      SupportedLocalNTorsionComplex source n p :=
  biprod.desc
    (supportedRestrictionMap source n p)
    (-supportedKummerToLocalMap source n p)

/-- Source-generated finite-support raw Selmer probe.  No all-place comparison is claimed. -/
noncomputable def finiteSupportRawSelmerComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (p : Nat.Primes) :
    CochainComplex (TopModuleCat ℤ) ℤ :=
  CochainComplex.mappingCocone
    (finiteSupportSelmerComparisonMap source n p)

end

end UniversalBSDFiniteSupportSelmer
end SaturationMonoid
