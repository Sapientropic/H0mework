import Mathlib.LinearAlgebra.Quotient.Basic
import H0mework.Arithmetic.Mellin.MellinDilationAction

/-!
# Q-rich Mellin orbit quotient

Starting from a Mellin-convergent relation annihilated by its Mellin
functional, this module spans the relation and all existing q-rich scale
dilates.  The span lies in the functional kernel, is stable under every
q-rich dilation, and therefore produces a quotient carrying both the action
and a descended nonzero eigenfunctional.
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

def qRichMellinOrbitRelation
    (z : ℂ) (relation : mellinConvergentSubmodule z) :
    Submodule ℂ (mellinConvergentSubmodule z) :=
  Submodule.span ℂ <| Set.insert relation <| Set.range fun stage : Nat =>
    qRichMellinDilation z stage relation

theorem qRichMellinOrbitRelation_le_ker
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (annihilated : mellinFunctional z relation = 0) :
    qRichMellinOrbitRelation z relation ≤
      LinearMap.ker (mellinFunctional z) := by
  rw [qRichMellinOrbitRelation, Submodule.span_le]
  intro element membership
  rcases membership with rfl | ⟨stage, rfl⟩
  · exact annihilated
  · change mellinFunctional z
        (qRichMellinDilation z stage relation) = 0
    rw [mellinFunctional_qRichMellinDilation,
      annihilated, smul_zero]

theorem qRichMellinDilation_maps_orbitRelation
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (stage : Nat) :
    (qRichMellinOrbitRelation z relation).map
        (qRichMellinDilation z stage) ≤
      qRichMellinOrbitRelation z relation := by
  rw [Submodule.map_le_iff_le_comap]
  rw [qRichMellinOrbitRelation, Submodule.span_le]
  intro element membership
  change qRichMellinDilation z stage element ∈
    qRichMellinOrbitRelation z relation
  rcases membership with rfl | ⟨second, rfl⟩
  · exact Submodule.subset_span <|
      Set.mem_insert_of_mem _ ⟨stage, rfl⟩
  · rw [qRichMellinDilation_comp_apply]
    exact Submodule.subset_span <|
      Set.mem_insert_of_mem _
        ⟨qRichScaleProductStage stage second, rfl⟩

abbrev QRichMellinOrbitQuotient
    (z : ℂ) (relation : mellinConvergentSubmodule z) :=
  mellinConvergentSubmodule z ⧸ qRichMellinOrbitRelation z relation

def qRichMellinOrbitQuotientDilation
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (stage : Nat) :
    QRichMellinOrbitQuotient z relation →ₗ[ℂ]
      QRichMellinOrbitQuotient z relation :=
  Submodule.mapQ
    (qRichMellinOrbitRelation z relation)
    (qRichMellinOrbitRelation z relation)
    (qRichMellinDilation z stage)
    ((Submodule.map_le_iff_le_comap).mp
      (qRichMellinDilation_maps_orbitRelation z relation stage))

@[simp] theorem qRichMellinOrbitQuotientDilation_mkQ
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (stage : Nat) (f : mellinConvergentSubmodule z) :
    qRichMellinOrbitQuotientDilation z relation stage
        ((qRichMellinOrbitRelation z relation).mkQ f) =
      (qRichMellinOrbitRelation z relation).mkQ
        (qRichMellinDilation z stage f) := by
  rfl

def qRichMellinOrbitQuotientFunctional
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (annihilated : mellinFunctional z relation = 0) :
    QRichMellinOrbitQuotient z relation →ₗ[ℂ] ℂ :=
  (qRichMellinOrbitRelation z relation).liftQ
    (mellinFunctional z)
    (qRichMellinOrbitRelation_le_ker z relation annihilated)

theorem qRichMellinOrbitQuotientFunctional_mkQ
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (annihilated : mellinFunctional z relation = 0)
    (f : mellinConvergentSubmodule z) :
    qRichMellinOrbitQuotientFunctional z relation annihilated
        ((qRichMellinOrbitRelation z relation).mkQ f) =
      mellinFunctional z f := by
  rfl

theorem qRichMellinOrbitQuotientFunctional_dilation
    (z : ℂ) (relation : mellinConvergentSubmodule z)
    (annihilated : mellinFunctional z relation = 0)
    (stage : Nat) (value : QRichMellinOrbitQuotient z relation) :
    qRichMellinOrbitQuotientFunctional z relation annihilated
        (qRichMellinOrbitQuotientDilation z relation stage value) =
      (blockQRichSuccessorScale stage : ℂ) ^ (-z) •
        qRichMellinOrbitQuotientFunctional z relation annihilated value := by
  refine Submodule.Quotient.induction_on
    (qRichMellinOrbitRelation z relation) value ?_
  intro representative
  change mellinFunctional z
      (qRichMellinDilation z stage representative) =
    (blockQRichSuccessorScale stage : ℂ) ^ (-z) •
      mellinFunctional z representative
  exact mellinFunctional_qRichMellinDilation z stage representative

theorem qRichMellinOrbitQuotient_relation_eq_zero
    (z : ℂ) (relation : mellinConvergentSubmodule z) :
    (qRichMellinOrbitRelation z relation).mkQ relation = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Set.mem_insert _ _)

def clozelLowCorrectionElement
    (z : ℂ) (positive : 0 < z.re) :
    mellinConvergentSubmodule z :=
  ⟨clozelLowCorrection,
    (hasMellin_clozelLowCorrection positive).1⟩

theorem mellinFunctional_clozelLowCorrectionElement
    (z : ℂ) (positive : 0 < z.re) :
    mellinFunctional z (clozelLowCorrectionElement z positive) =
      1 / z :=
  (hasMellin_clozelLowCorrection positive).2

theorem qRichMellinOrbitQuotientFunctional_ne_zero
    (z : ℂ) (positive : 0 < z.re)
    (relation : mellinConvergentSubmodule z)
    (annihilated : mellinFunctional z relation = 0) :
    qRichMellinOrbitQuotientFunctional z relation annihilated ≠ 0 := by
  intro functionalZero
  have evaluated := LinearMap.congr_fun functionalZero
    ((qRichMellinOrbitRelation z relation).mkQ
      (clozelLowCorrectionElement z positive))
  rw [LinearMap.zero_apply,
    qRichMellinOrbitQuotientFunctional_mkQ,
    mellinFunctional_clozelLowCorrectionElement] at evaluated
  have zNe : z ≠ 0 := by
    intro equality
    rw [equality, zero_re] at positive
    exact lt_irrefl 0 positive
  exact (one_div_ne_zero zNe) evaluated

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
