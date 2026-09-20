import H0mework.Arithmetic.EulerGlobal.DeterminantSection
import H0mework.Realization.Completion.SectionZeroFibre

/-!
# Universal zero fibre of the generated full-Euler global section

The framework zero-fibre functor consumes the already generated global
determinant-section diagram and produces only its universal scalar parameter
and restriction laws.  No dual coordinate or reversal is invented here;
those must be generated from the same actual reversal-equivariant action
occurrence downstream.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection
open CofinalPolynomialSectionZeroFiber
open CategoryTheory.Limits

noncomputable section

abbrev GlobalZeroFiberDiagram :=
  zeroFiberDiagram globalSectionFace

abbrev GlobalZeroFiberRing :=
  CofinalPolynomialSectionZeroFiber.GlobalZeroFiberRing globalSectionFace

noncomputable def universalDeterminantParameter : GlobalZeroFiberRing :=
  globalUniversalParameter globalSectionFace

theorem universalParameter_restriction (stage : Nat) :
    limit.π GlobalZeroFiberDiagram (Opposite.op stage)
        universalDeterminantParameter =
      AdjoinRoot.root
        (GlobalDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial :=
  globalUniversalParameter_restriction globalSectionFace stage

/-- Every local restriction is genuinely on the zero fibre of the generated
local action determinant. -/
theorem localDeterminantSection_vanishes (stage : Nat) :
    (GlobalDeterminantSectionDiagram.obj
        (Opposite.op stage)).polynomial.eval₂
        (AdjoinRoot.of
          (GlobalDeterminantSectionDiagram.obj
            (Opposite.op stage)).polynomial)
        (limit.π GlobalZeroFiberDiagram (Opposite.op stage)
          universalDeterminantParameter) = 0 := by
  rw [universalParameter_restriction]
  exact AdjoinRoot.eval₂_root _

theorem preserves_generated_D_before_zero_fibre :
    globalSectionFace.cofinalFace.root = seedOccurrence ∧
      (∀ stage : Nat,
        (GlobalDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial =
            determinantPolynomial seedOccurrence.root stage) ∧
      (∀ stage : Nat,
        (GlobalDeterminantSectionDiagram.obj
            (Opposite.op stage)).polynomial.eval₂
          (AdjoinRoot.of
            (GlobalDeterminantSectionDiagram.obj
              (Opposite.op stage)).polynomial)
          (limit.π GlobalZeroFiberDiagram (Opposite.op stage)
            universalDeterminantParameter) = 0) := by
  exact ⟨globalSectionFace
      |>.preserves_root_local_successor_and_global_section |>.1,
    globalSection_local_restriction,
    localDeterminantSection_vanishes⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
