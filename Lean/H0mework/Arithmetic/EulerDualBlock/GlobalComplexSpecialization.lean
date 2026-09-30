import H0mework.Arithmetic.EulerDualBlock.GlobalComplexLine
import H0mework.Arithmetic.EulerAnalytic.TautologicalReadback

/-!
# Fixedness-free realization of the determinant-line point

A point of the installed two-chart determinant line specializes the exact
pair coefficient ring already used by the source-generated block-action
cofiber.  Scalar extension then carries the literal existing endpoint
cofiber element to `ℂ`; no second cofiber, evaluator, endpoint equality, or
fixedness premise is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization

open CategoryTheory
open CochainComplex.HomComplex
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointCofiberElement
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticTautologicalReadback
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open scoped ChangeOfRings

noncomputable section

abbrev DeterminantLinePoint :=
  CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine.Point
    installedWholeBlockComplexDeterminantLine

/-- The coefficient quotient already used by the block-action cofiber is
literally the principal coordinate quotient of the newly generated
determinant-line section.  This is an identification, not a second zero
fibre. -/
theorem existingAnalyticZeroIdeal_eq_installedLineSection :
    analyticZeroIdeal installedOwner =
      Ideal.span
        {(installedWholeBlockComplexDeterminantLine.lineSection
          ).analyticCoordinate} :=
  rfl

theorem blockCoordinateToPairZeroFiber_reads_installedLineSection :
    blockCoordinateToPairZeroFiber =
      (Ideal.Quotient.mk
        (Ideal.span
          {(installedWholeBlockComplexDeterminantLine.lineSection
            ).analyticCoordinate})).comp commonCoordinateBaseChange :=
  rfl

/-- A point of the installed two-chart determinant line induces the
coefficient specialization already used by the actual block-action cofiber.
No new quotient or evaluator is constructed. -/
def toActionCoefficientPoint (point : DeterminantLinePoint) :
    CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate.Point
      installedOwner :=
  ⟨point.pair, by
    change riemannZeta point.pair.1 * riemannZeta point.pair.2 = 0
    exact point.sectionZero⟩

@[simp] theorem toActionCoefficientPoint_pair
    (point : DeterminantLinePoint) :
    (toActionCoefficientPoint point).pair = point.pair :=
  rfl

@[simp] theorem toActionCoefficientPoint_reversal
    (point : DeterminantLinePoint) :
    toActionCoefficientPoint point.reversal =
      (toActionCoefficientPoint point).reversal := by
  cases point
  rfl

def actionCoefficientSpecialization (point : DeterminantLinePoint) :
    PairCoefficientRing →+* ℂ :=
  (toActionCoefficientPoint point).specialization

@[simp] theorem actionCoefficientSpecialization_universalLeft
    (point : DeterminantLinePoint) :
    actionCoefficientSpecialization point
        (universalLeftCoordinate installedOwner) = point.pair.1 :=
  rfl

@[simp] theorem actionCoefficientSpecialization_universalRight
    (point : DeterminantLinePoint) :
    actionCoefficientSpecialization point
        (universalRightCoordinate installedOwner) = point.pair.2 :=
  rfl

/-- Evaluation after the installed coefficient swap at the reversed point
is the original evaluation.  This is the point-level reversal square on the
same coefficient ring used by the actual cofiber. -/
theorem actionCoefficientSpecialization_reversal_square
    (point : DeterminantLinePoint) :
    (actionCoefficientSpecialization point.reversal).comp
        (zeroFiberSwap installedOwner).toRingHom =
      actionCoefficientSpecialization point := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro function
  rfl

theorem actionCoefficientSpecialization_reversal_apply
    (point : DeterminantLinePoint) (coefficient : PairCoefficientRing) :
    actionCoefficientSpecialization point.reversal
        (zeroFiberSwap installedOwner coefficient) =
      actionCoefficientSpecialization point coefficient := by
  exact DFunLike.congr_fun
    (actionCoefficientSpecialization_reversal_square point) coefficient

/-- The specialization is on the same common-frame action coefficients: the
square is definitionally the installed evaluation at the determinant-line
point. -/
theorem actionCoefficientSpecialization_blockCoordinate
    (point : DeterminantLinePoint) (coefficient :
      CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame.BlockCoordinateRing) :
    actionCoefficientSpecialization point
        (blockCoordinateToPairZeroFiber coefficient) =
      CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDeterminantSection.installedBlockEvaluation
        coefficient point.pair := by
  rfl

abbrev PointExtensionFunctor (point : DeterminantLinePoint) :=
  (ModuleCat.extendScalars
      (actionCoefficientSpecialization point)).mapHomologicalComplex
    (ComplexShape.up ℤ)

noncomputable abbrev PointBlockGlobalState (point : DeterminantLinePoint) :=
  (PointExtensionFunctor point).obj PairBlockGlobalState

noncomputable abbrev PointBlockActionCofiber (point : DeterminantLinePoint) :=
  (PointExtensionFunctor point).obj PairBlockActionCofiber

abbrev PointBlockActionCofiberDegreeOne (point : DeterminantLinePoint) :=
  (ModuleCat.extendScalars
    (actionCoefficientSpecialization point)).obj
      (PairBlockActionCofiber.X 1)

abbrev PointBlockGlobalStateDegreeZero (point : DeterminantLinePoint) :=
  (ModuleCat.extendScalars
    (actionCoefficientSpecialization point)).obj
      (PairBlockGlobalState.X 0)

def pairBlockCofiberReversalDegreeOne :
    PairBlockActionCofiber.X 1 →ₗ[PairCoefficientRing]
      PairBlockActionCofiber.X 1 :=
  (pairBlockCofiberReversal.f 1).hom

def pairBlockCofiberSourceReadbackDegreeOne :
    PairBlockActionCofiber.X 1 →ₗ[PairCoefficientRing]
      PairBlockGlobalState.X 0 :=
  ((CochainComplex.mappingCocone.snd
      pairBlockGlobalEulerOperator).v 1 0 (by omega)).hom

/-- Literal image of the already generated derived universal endpoint class.
This is a scalar realization of that class, not a second cofiber. -/
def pointDerivedEndpointClass (point : DeterminantLinePoint) :
    PointBlockActionCofiberDegreeOne point :=
  (1 : ℂ) ⊗ₜ[PairCoefficientRing, actionCoefficientSpecialization point]
    pairBlockEndpointCofiberElement

def pointGlobalEndpointSection (point : DeterminantLinePoint) :
    PointBlockGlobalStateDegreeZero point :=
  (1 : ℂ) ⊗ₜ[PairCoefficientRing, actionCoefficientSpecialization point]
    pairBlockGlobalEndpointSection

noncomputable def pointCofiberReversal (point : DeterminantLinePoint) :
    PointBlockActionCofiberDegreeOne point →ₗ[ℂ]
      PointBlockActionCofiberDegreeOne point :=
  ((ModuleCat.extendScalars
      (actionCoefficientSpecialization point)).map
    (ModuleCat.ofHom pairBlockCofiberReversalDegreeOne)).hom

def pointReversedEndpointClass (point : DeterminantLinePoint) :
    PointBlockActionCofiberDegreeOne point :=
  (1 : ℂ) ⊗ₜ[PairCoefficientRing, actionCoefficientSpecialization point]
    (pairBlockTautologicalInclusion.1.v 0 1 (by omega)).hom
      pairBlockReversedEndpointSection

theorem pointDerivedEndpointClass_reversal
    (point : DeterminantLinePoint) :
    pointCofiberReversal point (pointDerivedEndpointClass point) =
      pointReversedEndpointClass point := by
  rw [pointCofiberReversal, pointDerivedEndpointClass,
    pointReversedEndpointClass, ModuleCat.ExtendScalars.map_tmul]
  exact congrArg
    (fun value =>
      (1 : ℂ) ⊗ₜ[PairCoefficientRing, actionCoefficientSpecialization point]
        value)
    pairBlockEndpointCofiberElement_reversal

noncomputable def pointCofiberSourceReadback (point : DeterminantLinePoint) :
    PointBlockActionCofiberDegreeOne point →ₗ[ℂ]
      PointBlockGlobalStateDegreeZero point :=
  ((ModuleCat.extendScalars
      (actionCoefficientSpecialization point)).map
    (ModuleCat.ofHom pairBlockCofiberSourceReadbackDegreeOne)).hom

theorem pointDerivedEndpointClass_source_readback
    (point : DeterminantLinePoint) :
    pointCofiberSourceReadback point (pointDerivedEndpointClass point) =
      pointGlobalEndpointSection point := by
  rw [pointCofiberSourceReadback, pointDerivedEndpointClass,
    pointGlobalEndpointSection, ModuleCat.ExtendScalars.map_tmul]
  exact congrArg
    (fun value =>
      (1 : ℂ) ⊗ₜ[PairCoefficientRing, actionCoefficientSpecialization point]
        value)
    pairBlockEndpointSourceReadback_eq_section

def pointDerivedEndpointClassOccurrence (point : DeterminantLinePoint) :
    RootedAccountedUnfolding
      (FactorizationPayload × PointBlockActionCofiberDegreeOne point) :=
  seedOccurrence.map fun owner => (owner, pointDerivedEndpointClass point)

theorem pointDerivedEndpointClassOccurrence_projects
    (point : DeterminantLinePoint) :
    (pointDerivedEndpointClassOccurrence point).map Prod.fst =
      seedOccurrence := by
  unfold pointDerivedEndpointClassOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem preserves_same_derived_class_and_fixedness_free_point_specialization
    (point : DeterminantLinePoint) :
    (pointDerivedEndpointClassOccurrence point).map Prod.fst = seedOccurrence ∧
      actionCoefficientSpecialization point
          (universalLeftCoordinate installedOwner) = point.pair.1 ∧
      actionCoefficientSpecialization point
          (universalRightCoordinate installedOwner) = point.pair.2 ∧
      pointCofiberReversal point (pointDerivedEndpointClass point) =
        pointReversedEndpointClass point ∧
      pointCofiberSourceReadback point (pointDerivedEndpointClass point) =
        pointGlobalEndpointSection point := by
  exact ⟨pointDerivedEndpointClassOccurrence_projects point,
    actionCoefficientSpecialization_universalLeft point,
    actionCoefficientSpecialization_universalRight point,
    pointDerivedEndpointClass_reversal point,
    pointDerivedEndpointClass_source_readback point⟩

end
end CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
