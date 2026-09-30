import H0mework.Versions.Y.Arithmetic.Mellin.PositiveMellinTate
import H0mework.Versions.Y.Arithmetic.RiemannMellinOrbit.ZeroMellinOrbit

/-!
# Full positive-dilation Mellin orbit and q-rich comparison

The positive-domain relation is closed under every positive dilation.  Its
quotient carries the descended Mellin functional.  Restriction from the
earlier whole-line q-rich orbit maps every generated q-rich relation into this
full orbit, producing the canonical q-rich-to-positive comparison without
choosing representatives.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open QRich

noncomputable section

def positiveDomainMellinOrbitRelation
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z) :
    Submodule ℂ (positiveMellinConvergentSubmodule z) :=
  Submodule.span ℂ <| Set.range fun a : PositiveMellinReal =>
    positiveMellinDilation z a.1 a.2 relation

theorem positiveRelation_mem_positiveDomainOrbit
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z) :
    relation ∈ positiveDomainMellinOrbitRelation z relation := by
  apply Submodule.subset_span
  refine ⟨⟨1, zero_lt_one⟩, ?_⟩
  apply Subtype.ext
  funext t
  change relation.1 ⟨1 * t.1, mul_pos zero_lt_one t.2⟩ = relation.1 t
  exact congrArg relation.1 (Subtype.ext (by simp))

theorem positiveDomainMellinOrbitRelation_le_ker
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z)
    (annihilated : positiveMellinFunctional z relation = 0) :
    positiveDomainMellinOrbitRelation z relation ≤
      LinearMap.ker (positiveMellinFunctional z) := by
  rw [positiveDomainMellinOrbitRelation, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  change positiveMellinFunctional z
      (positiveMellinDilation z a.1 a.2 relation) = 0
  rw [positiveMellinFunctional_dilation,
    annihilated, smul_zero]

theorem positiveMellinDilation_comp_apply
    (z : ℂ) (a b : ℝ) (aPositive : 0 < a) (bPositive : 0 < b)
    (f : positiveMellinConvergentSubmodule z) :
    positiveMellinDilation z a aPositive
        (positiveMellinDilation z b bPositive f) =
      positiveMellinDilation z (b * a)
        (mul_pos bPositive aPositive) f := by
  apply Subtype.ext
  funext t
  change f.1 ⟨b * (a * t.1), _⟩ = f.1 ⟨(b * a) * t.1, _⟩
  exact congrArg f.1 (Subtype.ext (by ring))

theorem positiveMellinDilation_maps_positiveDomainOrbit
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z)
    (a : ℝ) (positive : 0 < a) :
    (positiveDomainMellinOrbitRelation z relation).map
        (positiveMellinDilation z a positive) ≤
      positiveDomainMellinOrbitRelation z relation := by
  rw [Submodule.map_le_iff_le_comap]
  rw [positiveDomainMellinOrbitRelation, Submodule.span_le]
  intro element membership
  change positiveMellinDilation z a positive element ∈
    positiveDomainMellinOrbitRelation z relation
  rcases membership with ⟨b, rfl⟩
  rw [positiveMellinDilation_comp_apply]
  apply Submodule.subset_span
  exact ⟨⟨b.1 * a, mul_pos b.2 positive⟩, rfl⟩

abbrev PositiveDomainMellinOrbitQuotient
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z) :=
  positiveMellinConvergentSubmodule z ⧸
    positiveDomainMellinOrbitRelation z relation

def positiveDomainMellinOrbitQuotientDilation
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z)
    (a : ℝ) (positive : 0 < a) :
    PositiveDomainMellinOrbitQuotient z relation →ₗ[ℂ]
      PositiveDomainMellinOrbitQuotient z relation :=
  Submodule.mapQ
    (positiveDomainMellinOrbitRelation z relation)
    (positiveDomainMellinOrbitRelation z relation)
    (positiveMellinDilation z a positive)
    ((Submodule.map_le_iff_le_comap).mp
      (positiveMellinDilation_maps_positiveDomainOrbit
        z relation a positive))

@[simp] theorem positiveDomainMellinOrbitQuotientDilation_mkQ
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z)
    (a : ℝ) (positive : 0 < a)
    (f : positiveMellinConvergentSubmodule z) :
    positiveDomainMellinOrbitQuotientDilation z relation a positive
        ((positiveDomainMellinOrbitRelation z relation).mkQ f) =
      (positiveDomainMellinOrbitRelation z relation).mkQ
        (positiveMellinDilation z a positive f) := by
  rfl

def positiveDomainMellinOrbitQuotientFunctional
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z)
    (annihilated : positiveMellinFunctional z relation = 0) :
    PositiveDomainMellinOrbitQuotient z relation →ₗ[ℂ] ℂ :=
  (positiveDomainMellinOrbitRelation z relation).liftQ
    (positiveMellinFunctional z)
    (positiveDomainMellinOrbitRelation_le_ker
      z relation annihilated)

theorem positiveDomainMellinOrbitQuotientFunctional_dilation
    (z : ℂ) (relation : positiveMellinConvergentSubmodule z)
    (annihilated : positiveMellinFunctional z relation = 0)
    (a : ℝ) (positive : 0 < a)
    (value : PositiveDomainMellinOrbitQuotient z relation) :
    positiveDomainMellinOrbitQuotientFunctional z relation annihilated
        (positiveDomainMellinOrbitQuotientDilation
          z relation a positive value) =
      (a : ℂ) ^ (-z) •
        positiveDomainMellinOrbitQuotientFunctional
          z relation annihilated value := by
  refine Submodule.Quotient.induction_on
    (positiveDomainMellinOrbitRelation z relation) value ?_
  intro representative
  change positiveMellinFunctional z
      (positiveMellinDilation z a positive representative) =
    (a : ℂ) ^ (-z) • positiveMellinFunctional z representative
  exact positiveMellinFunctional_dilation z a positive representative

def positiveClozelLowCorrectionElement
    (z : ℂ) (positive : 0 < z.re) :
    positiveMellinConvergentSubmodule z :=
  restrictPositiveMellin z (clozelLowCorrectionElement z positive)

theorem positiveMellinFunctional_positiveClozelLowCorrectionElement
    (z : ℂ) (positive : 0 < z.re) :
    positiveMellinFunctional z
        (positiveClozelLowCorrectionElement z positive) = 1 / z := by
  rw [positiveClozelLowCorrectionElement,
    positiveMellinFunctional_restrictPositive,
    mellinFunctional_clozelLowCorrectionElement]

def positiveNormalizedLowCorrectionClass
    (z : ℂ) (positive : 0 < z.re)
    (relation : positiveMellinConvergentSubmodule z) :
    PositiveDomainMellinOrbitQuotient z relation :=
  (positiveDomainMellinOrbitRelation z relation).mkQ
    (z • positiveClozelLowCorrectionElement z positive)

theorem positiveDomainMellinOrbitQuotientFunctional_normalizedLow
    (z : ℂ) (positive : 0 < z.re)
    (relation : positiveMellinConvergentSubmodule z)
    (annihilated : positiveMellinFunctional z relation = 0) :
    positiveDomainMellinOrbitQuotientFunctional z relation annihilated
        (positiveNormalizedLowCorrectionClass z positive relation) = 1 := by
  change positiveMellinFunctional z
      (z • positiveClozelLowCorrectionElement z positive) = 1
  rw [map_smul,
    positiveMellinFunctional_positiveClozelLowCorrectionElement]
  have zNe : z ≠ 0 := by
    intro equality
    rw [equality, zero_re] at positive
    exact lt_irrefl 0 positive
  simp [smul_eq_mul, one_div, zNe]

theorem positiveDomainMellinOrbitQuotientFunctional_dilation_normalizedLow
    (z : ℂ) (positive : 0 < z.re)
    (relation : positiveMellinConvergentSubmodule z)
    (annihilated : positiveMellinFunctional z relation = 0)
    (a : ℝ) (aPositive : 0 < a) :
    positiveDomainMellinOrbitQuotientFunctional z relation annihilated
        (positiveDomainMellinOrbitQuotientDilation z relation a aPositive
          (positiveNormalizedLowCorrectionClass z positive relation)) =
      (a : ℂ) ^ (-z) := by
  rw [positiveDomainMellinOrbitQuotientFunctional_dilation,
    positiveDomainMellinOrbitQuotientFunctional_normalizedLow,
    smul_eq_mul, mul_one]

theorem positiveDomainMellinOrbitQuotientFunctional_ne_zero
    (z : ℂ) (positive : 0 < z.re)
    (relation : positiveMellinConvergentSubmodule z)
    (annihilated : positiveMellinFunctional z relation = 0) :
    positiveDomainMellinOrbitQuotientFunctional
        z relation annihilated ≠ 0 := by
  intro functionalZero
  have evaluated := LinearMap.congr_fun functionalZero
    ((positiveDomainMellinOrbitRelation z relation).mkQ
      (positiveClozelLowCorrectionElement z positive))
  rw [LinearMap.zero_apply] at evaluated
  change positiveMellinFunctional z
      (positiveClozelLowCorrectionElement z positive) = 0 at evaluated
  rw [positiveMellinFunctional_positiveClozelLowCorrectionElement] at evaluated
  have zNe : z ≠ 0 := by
    intro equality
    rw [equality, zero_re] at positive
    exact lt_irrefl 0 positive
  exact (one_div_ne_zero zNe) evaluated

theorem restrictPositiveMellin_qRichDilation
    (z : ℂ) (stage : Nat)
    (f : mellinConvergentSubmodule z) :
    restrictPositiveMellin z (qRichMellinDilation z stage f) =
      positiveMellinDilation z
        (blockQRichSuccessorScale stage : ℝ) (by
          rw [blockQRichSuccessorScale_eq_stage_add_three]
          positivity)
        (restrictPositiveMellin z f) := by
  apply Subtype.ext
  funext t
  rfl

theorem restrictPositiveMellin_maps_qRichOrbit
    (z : ℂ) (relation : mellinConvergentSubmodule z) :
    qRichMellinOrbitRelation z relation ≤
      Submodule.comap (restrictPositiveMellin z)
        (positiveDomainMellinOrbitRelation z
          (restrictPositiveMellin z relation)) := by
  rw [qRichMellinOrbitRelation, Submodule.span_le]
  intro element membership
  rcases membership with equality | ⟨stage, equality⟩
  · rw [equality]
    exact positiveRelation_mem_positiveDomainOrbit z
      (restrictPositiveMellin z relation)
  · rw [← equality]
    change restrictPositiveMellin z
        (qRichMellinDilation z stage relation) ∈
      positiveDomainMellinOrbitRelation z
        (restrictPositiveMellin z relation)
    rw [restrictPositiveMellin_qRichDilation]
    apply Submodule.subset_span
    refine ⟨⟨(blockQRichSuccessorScale stage : ℝ), ?_⟩, rfl⟩
    rw [blockQRichSuccessorScale_eq_stage_add_three]
    positivity

def qRichToPositiveDomainMellinOrbit
    (z : ℂ) (relation : mellinConvergentSubmodule z) :
    QRichMellinOrbitQuotient z relation →ₗ[ℂ]
      PositiveDomainMellinOrbitQuotient z
        (restrictPositiveMellin z relation) :=
  Submodule.mapQ
    (qRichMellinOrbitRelation z relation)
    (positiveDomainMellinOrbitRelation z
      (restrictPositiveMellin z relation))
    (restrictPositiveMellin z)
    (restrictPositiveMellin_maps_qRichOrbit z relation)

theorem positiveDomainFunctional_qRichComparison
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (annihilated : mellinFunctional z relation = 0)
    (value : QRichMellinOrbitQuotient z relation) :
    positiveDomainMellinOrbitQuotientFunctional z
        (restrictPositiveMellin z relation) (by
          simpa [positiveMellinFunctional_restrictPositive] using annihilated)
        (qRichToPositiveDomainMellinOrbit z relation value) =
      qRichMellinOrbitQuotientFunctional z relation annihilated value := by
  refine Submodule.Quotient.induction_on
    (qRichMellinOrbitRelation z relation) value ?_
  intro representative
  change positiveMellinFunctional z
      (restrictPositiveMellin z representative) =
    mellinFunctional z representative
  exact positiveMellinFunctional_restrictPositive z representative

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
