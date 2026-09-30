import H0mework.Versions.Y.Arithmetic.EulerDualBlock.GlobalDeterminantSection
import H0mework.Realization.Completion.SectionZeroFibre

/-!
# Formal zero fibre of the generated prime-dual block section

The frozen zero-fibre functor consumes the already generated global block
section.  This file exposes its universal coefficient inclusion and local
restriction laws.  It does not select a point and does not identify a finite
stage `AdjoinRoot (C D_n)` with a Mathlib zeta-zero coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalZeroFiber

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalDeterminantSection
open CofinalPolynomialSectionZeroFiber
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

abbrev GlobalBlockZeroFiberDiagram :=
  zeroFiberDiagram globalBlockSectionFace

abbrev GlobalBlockZeroFiberRing :=
  CofinalPolynomialSectionZeroFiber.GlobalZeroFiberRing
    globalBlockSectionFace

/-- The outer `AdjoinRoot` parameter is auxiliary: the determinant equation
is carried by the included block coefficients. -/
noncomputable def universalAuxiliaryParameter : GlobalBlockZeroFiberRing :=
  globalUniversalParameter globalBlockSectionFace

/-- Universal inclusion of the common prime-dual coordinate ring into the
global formal zero fibre. -/
noncomputable def universalBlockCoefficient
    (coefficient : BlockCoordinateRing) : GlobalBlockZeroFiberRing :=
  globalUniversalInclusion globalBlockSectionFace (Polynomial.C coefficient)

theorem universalAuxiliaryParameter_restriction (stage : Nat) :
    limit.π GlobalBlockZeroFiberDiagram (Opposite.op stage)
        universalAuxiliaryParameter =
      AdjoinRoot.root
        (GlobalBlockDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial :=
  globalUniversalParameter_restriction globalBlockSectionFace stage

theorem universalBlockCoefficient_restriction
    (stage : Nat) (coefficient : BlockCoordinateRing) :
    limit.π GlobalBlockZeroFiberDiagram (Opposite.op stage)
        (universalBlockCoefficient coefficient) =
      AdjoinRoot.mk
        (GlobalBlockDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial (Polynomial.C coefficient) := by
  have restriction := ConcreteCategory.congr_hom
    (globalUniversalInclusion_restriction globalBlockSectionFace stage)
    (Polynomial.C coefficient)
  exact restriction

noncomputable def universalA (prime : Nat.Primes) :
    GlobalBlockZeroFiberRing :=
  universalBlockCoefficient (blockA prime)

noncomputable def universalB (prime : Nat.Primes) :
    GlobalBlockZeroFiberRing :=
  universalBlockCoefficient (blockB prime)

theorem universalA_restriction (stage : Nat) (prime : Nat.Primes) :
    limit.π GlobalBlockZeroFiberDiagram (Opposite.op stage)
        (universalA prime) =
      AdjoinRoot.mk
        (GlobalBlockDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial (Polynomial.C (blockA prime)) := by
  exact universalBlockCoefficient_restriction stage (blockA prime)

theorem universalB_restriction (stage : Nat) (prime : Nat.Primes) :
    limit.π GlobalBlockZeroFiberDiagram (Opposite.op stage)
        (universalB prime) =
      AdjoinRoot.mk
        (GlobalBlockDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial (Polynomial.C (blockB prime)) := by
  exact universalBlockCoefficient_restriction stage (blockB prime)

/-- At every generated stage, the included actual block determinant
coefficient is zero. -/
theorem localBlockDeterminantCoefficient_vanishes (stage : Nat) :
    limit.π GlobalBlockZeroFiberDiagram (Opposite.op stage)
        (universalBlockCoefficient
          (blockDeterminantSection seedOccurrence.root stage)) = 0 := by
  rw [universalBlockCoefficient_restriction]
  let localPolynomial :=
    (GlobalBlockDeterminantSectionDiagram.obj
      (Opposite.op stage)).polynomial
  have localPolynomial_eq :
      localPolynomial =
        Polynomial.C
          (blockDeterminantSection seedOccurrence.root stage) :=
    globalBlockSection_local_restriction stage
  change AdjoinRoot.mk localPolynomial
      (Polynomial.C
        (blockDeterminantSection seedOccurrence.root stage)) = 0
  rw [← localPolynomial_eq]
  exact AdjoinRoot.mk_self

def globalBlockZeroFiberOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      (BlockCoordinateRing →+* GlobalBlockZeroFiberRing)) :=
  seedOccurrence.map fun owner =>
    (owner,
      (globalUniversalInclusion globalBlockSectionFace).hom.comp
        Polynomial.C)

theorem globalBlockZeroFiberOccurrence_projects :
    globalBlockZeroFiberOccurrence.map Prod.fst = seedOccurrence := by
  unfold globalBlockZeroFiberOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem globalBlockZeroFiberOccurrence_reads_universal_coefficient
    (coefficient : BlockCoordinateRing) :
    globalBlockZeroFiberOccurrence.root.2 coefficient =
      universalBlockCoefficient coefficient := by
  rfl

theorem preserves_generated_block_D_before_formal_zero_fibre :
    globalBlockSectionFace.cofinalFace.root = seedOccurrence ∧
      globalBlockZeroFiberOccurrence.map Prod.fst = seedOccurrence ∧
      (∀ stage : Nat,
        limit.π GlobalBlockZeroFiberDiagram (Opposite.op stage)
            (universalBlockCoefficient
              (blockDeterminantSection seedOccurrence.root stage)) = 0) := by
  exact ⟨globalBlockSectionFace
      |>.preserves_root_local_successor_and_global_section |>.1,
    globalBlockZeroFiberOccurrence_projects,
    localBlockDeterminantCoefficient_vanishes⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockGlobalZeroFiber
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
