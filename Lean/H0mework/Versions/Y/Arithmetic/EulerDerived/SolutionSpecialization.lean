import H0mework.Versions.Y.Arithmetic.EulerDerived.SolutionCofinal
import H0mework.Versions.Y.Arithmetic.EulerDualBlock.GlobalComplexSpecialization
import H0mework.Versions.Y.Arithmetic.RiemannLineage.DerivedFullRowLineageSuccessor
import H0mework.Versions.Y.Arithmetic.RiemannLineage.FullRowSeparatorPoint

/-!
# Same-object determinant-line points on the generated block derived solution

The corrected endpoint fibre is first globalized over the actual block
coefficient ring by the generic one-successor process.  It is then base
changed along the already installed pair determinant zero fibre.  The two
universal coefficient functions weight the same generated left and right
derived endpoint maps.  Finally an installed determinant-line point performs
the ordinary quotient specialization.

Thus a Mathlib zero now produces a point of the same global derived
whole/relation solution, rather than an unrelated strict kernel or a raw
endpoint evaluator.  No endpoint equality, fixedness, coordinate existence
or analytic continuation theorem enters this construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization

open CategoryTheory
open CategoryTheory.Limits
open CofinalProcessDiagram
open CofinalProcessDiagram.RootGeneratedCofinalProcessDiagramAt
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticGlobalActionCofiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiberEndpointAtom
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockDeterminantLineCoordinate
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization
open scoped ChangeOfRings TensorProduct
open NoIslandNoMagic
open CanonicalRiemann
open QRich
open CochainMappingCoconeMappedBoundaryAtomOver

noncomputable section

def blockDerivedSolutionProcess :
    CofinalDiagramSuccessorProcessAt
      (CochainComplex (ModuleCat BlockCoordinateRing) ℤ) where
  State := Nat
  seed := 0
  next := Nat.succ
  object := LocalDerivedSolution
  transition := localCorrectedEndpointRestriction

@[simp] theorem blockDerivedSolutionProcess_stateAt (stage : Nat) :
    blockDerivedSolutionProcess.stateAt stage = stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      change Nat.succ (blockDerivedSolutionProcess.stateAt stage) = stage + 1
      rw [inductionHypothesis]

@[simp] theorem blockDerivedSolutionProcess_stateAt_succ (stage : Nat) :
    blockDerivedSolutionProcess.stateAt (stage + 1) =
      Nat.succ (blockDerivedSolutionProcess.stateAt stage) :=
  rfl

def blockDerivedSolutionProcessOccurrence : RootedAccountedUnfolding
    (FactorizationPayload ×
      CofinalDiagramSuccessorProcessAt
        (CochainComplex (ModuleCat BlockCoordinateRing) ℤ)) :=
  seedOccurrence.map fun owner => (owner, blockDerivedSolutionProcess)

theorem blockDerivedSolutionProcessOccurrence_projects :
    blockDerivedSolutionProcessOccurrence.map Prod.fst = seedOccurrence := by
  unfold blockDerivedSolutionProcessOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change seedOccurrence.map id = seedOccurrence
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem blockDerivedSolutionProcessOccurrence_process :
    blockDerivedSolutionProcessOccurrence.root.2 =
      blockDerivedSolutionProcess :=
  rfl

def blockDerivedSolutionDiagramFace :
    RootGeneratedCofinalProcessDiagramAt seedOccurrence
      blockDerivedSolutionProcessOccurrence
      blockDerivedSolutionProcessOccurrence_projects :=
  RootGeneratedCofinalProcessDiagramAt.generate

theorem blockDerivedSolutionDiagramFace_object (stage : Nat) :
    blockDerivedSolutionDiagramFace.actualDiagram.obj (Opposite.op stage) =
      LocalDerivedSolution stage := by
  change LocalDerivedSolution
      (blockDerivedSolutionProcess.stateAt stage) =
        LocalDerivedSolution stage
  rw [blockDerivedSolutionProcess_stateAt]

abbrev BlockGlobalDerivedSolution :=
  limit blockDerivedSolutionDiagramFace.actualDiagram

noncomputable def generatedBlockLocalLeftDerivedPoint (stage : Nat) :
    CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing) ⟶
      blockDerivedSolutionDiagramFace.actualDiagram.obj
        (Opposite.op stage) :=
  localLeftDerivedPoint
      (blockDerivedSolutionProcess.stateAt stage) ≫
    eqToHom (blockDerivedSolutionDiagramFace.actualDiagram_obj stage).symm

noncomputable def generatedBlockLocalRightDerivedPoint (stage : Nat) :
    CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing) ⟶
      blockDerivedSolutionDiagramFace.actualDiagram.obj
        (Opposite.op stage) :=
  localRightDerivedPoint
      (blockDerivedSolutionProcess.stateAt stage) ≫
    eqToHom (blockDerivedSolutionDiagramFace.actualDiagram_obj stage).symm

theorem generatedBlockLocalLeftDerivedPoint_successor (stage : Nat) :
    generatedBlockLocalLeftDerivedPoint stage =
      generatedBlockLocalLeftDerivedPoint (stage + 1) ≫
        blockDerivedSolutionDiagramFace.actualDiagram.map
          ((homOfLE (Nat.le_succ stage)).op) := by
  rw [blockDerivedSolutionDiagramFace.actualDiagram_succ]
  unfold generatedBlockLocalLeftDerivedPoint
  simp only [RootGeneratedCofinalProcessDiagramAt.actualDiagram_obj,
    eqToHom_refl, Category.comp_id,
    RootGeneratedCofinalProcessDiagramAt.actualProcess,
    blockDerivedSolutionDiagramFace,
    blockDerivedSolutionProcessOccurrence_process,
    blockDerivedSolutionProcess_stateAt_succ]
  change localLeftDerivedPoint
      (blockDerivedSolutionProcess.stateAt stage) =
    localLeftDerivedPoint
        (Nat.succ (blockDerivedSolutionProcess.stateAt stage)) ≫
      localCorrectedEndpointRestriction
        (blockDerivedSolutionProcess.stateAt stage)
  simpa only [Nat.succ_eq_add_one] using
    (localLeftDerivedPoint_successor
      (blockDerivedSolutionProcess.stateAt stage)).symm

theorem generatedBlockLocalRightDerivedPoint_successor (stage : Nat) :
    generatedBlockLocalRightDerivedPoint stage =
      generatedBlockLocalRightDerivedPoint (stage + 1) ≫
        blockDerivedSolutionDiagramFace.actualDiagram.map
          ((homOfLE (Nat.le_succ stage)).op) := by
  rw [blockDerivedSolutionDiagramFace.actualDiagram_succ]
  unfold generatedBlockLocalRightDerivedPoint
  simp only [RootGeneratedCofinalProcessDiagramAt.actualDiagram_obj,
    eqToHom_refl, Category.comp_id,
    RootGeneratedCofinalProcessDiagramAt.actualProcess,
    blockDerivedSolutionDiagramFace,
    blockDerivedSolutionProcessOccurrence_process,
    blockDerivedSolutionProcess_stateAt_succ]
  change localRightDerivedPoint
      (blockDerivedSolutionProcess.stateAt stage) =
    localRightDerivedPoint
        (Nat.succ (blockDerivedSolutionProcess.stateAt stage)) ≫
      localCorrectedEndpointRestriction
        (blockDerivedSolutionProcess.stateAt stage)
  simpa only [Nat.succ_eq_add_one] using
    (localRightDerivedPoint_successor
      (blockDerivedSolutionProcess.stateAt stage)).symm

noncomputable def blockGlobalLeftDerivedPointCone :
    Cone blockDerivedSolutionDiagramFace.actualDiagram where
  pt := CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
    (R := BlockCoordinateRing)
  π := NatTrans.ofOpSequence generatedBlockLocalLeftDerivedPoint
    (fun stage => by
      simpa only [Functor.const_obj_map] using
        (Category.id_comp
          (generatedBlockLocalLeftDerivedPoint stage)).trans
            (generatedBlockLocalLeftDerivedPoint_successor stage))

noncomputable def blockGlobalRightDerivedPointCone :
    Cone blockDerivedSolutionDiagramFace.actualDiagram where
  pt := CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
    (R := BlockCoordinateRing)
  π := NatTrans.ofOpSequence generatedBlockLocalRightDerivedPoint
    (fun stage => by
      simpa only [Functor.const_obj_map] using
        (Category.id_comp
          (generatedBlockLocalRightDerivedPoint stage)).trans
            (generatedBlockLocalRightDerivedPoint_successor stage))

noncomputable def blockGlobalLeftDerivedPoint :
    CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing) ⟶ BlockGlobalDerivedSolution :=
  limit.lift blockDerivedSolutionDiagramFace.actualDiagram
    blockGlobalLeftDerivedPointCone

noncomputable def blockGlobalRightDerivedPoint :
    CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
        (R := BlockCoordinateRing) ⟶ BlockGlobalDerivedSolution :=
  limit.lift blockDerivedSolutionDiagramFace.actualDiagram
    blockGlobalRightDerivedPointCone

theorem blockGlobalLeftDerivedPoint_restriction (stage : Nat) :
    blockGlobalLeftDerivedPoint ≫
        limit.π blockDerivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) =
      generatedBlockLocalLeftDerivedPoint stage := by
  exact limit.lift_π blockGlobalLeftDerivedPointCone (Opposite.op stage)

theorem blockGlobalRightDerivedPoint_restriction (stage : Nat) :
    blockGlobalRightDerivedPoint ≫
        limit.π blockDerivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) =
      generatedBlockLocalRightDerivedPoint stage := by
  exact limit.lift_π blockGlobalRightDerivedPointCone (Opposite.op stage)

abbrev PairDerivedExtensionFunctor :=
  (ModuleCat.extendScalars
      blockCoordinateToPairZeroFiber).mapHomologicalComplex
    (ComplexShape.up ℤ)

noncomputable abbrev PairGlobalDerivedSolution :=
  PairDerivedExtensionFunctor.obj BlockGlobalDerivedSolution

noncomputable abbrev PairDerivedScalarSingleOne :=
  PairDerivedExtensionFunctor.obj
    (CochainMappingCoconeMappedBoundaryAtomOver.ScalarSingleOne
      (R := BlockCoordinateRing))

noncomputable def pairGlobalLeftDerivedPoint :
    PairDerivedScalarSingleOne ⟶ PairGlobalDerivedSolution :=
  PairDerivedExtensionFunctor.map blockGlobalLeftDerivedPoint

noncomputable def pairGlobalRightDerivedPoint :
    PairDerivedScalarSingleOne ⟶ PairGlobalDerivedSolution :=
  PairDerivedExtensionFunctor.map blockGlobalRightDerivedPoint

/-! The universal pair point lives in the corrected derived solution before
any complex point is selected. -/
noncomputable def pairUniversalDerivedPoint :
    PairDerivedScalarSingleOne ⟶ PairGlobalDerivedSolution :=
  universalLeftCoordinate installedOwner • pairGlobalLeftDerivedPoint +
    universalRightCoordinate installedOwner • pairGlobalRightDerivedPoint

noncomputable def pairReversedUniversalDerivedPoint :
    PairDerivedScalarSingleOne ⟶ PairGlobalDerivedSolution :=
  universalRightCoordinate installedOwner • pairGlobalLeftDerivedPoint +
    universalLeftCoordinate installedOwner • pairGlobalRightDerivedPoint

noncomputable def pairUniversalDerivedAntiInvariantPoint :
    PairDerivedScalarSingleOne ⟶ PairGlobalDerivedSolution :=
  pairUniversalDerivedPoint - pairReversedUniversalDerivedPoint

noncomputable abbrev PointGlobalDerivedSolution
    (point : DeterminantLinePoint) :=
  (PointExtensionFunctor point).obj PairGlobalDerivedSolution

noncomputable abbrev PointDerivedScalarSingleOne
    (point : DeterminantLinePoint) :=
  (PointExtensionFunctor point).obj PairDerivedScalarSingleOne

/-! Actual specialization of the same generated universal derived point. -/
noncomputable def determinantLineDerivedSolutionPoint
    (point : DeterminantLinePoint) :
    PointDerivedScalarSingleOne point ⟶
      PointGlobalDerivedSolution point :=
  (PointExtensionFunctor point).map pairUniversalDerivedPoint

noncomputable def determinantLineReversedDerivedSolutionPoint
    (point : DeterminantLinePoint) :
    PointDerivedScalarSingleOne point ⟶
      PointGlobalDerivedSolution point :=
  (PointExtensionFunctor point).map pairReversedUniversalDerivedPoint

noncomputable def mathlibZeroDerivedSolutionPoint
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    PointDerivedScalarSingleOne (mathlibZeroPoint coordinate zetaZero) ⟶
      PointGlobalDerivedSolution (mathlibZeroPoint coordinate zetaZero) :=
  determinantLineDerivedSolutionPoint
    (mathlibZeroPoint coordinate zetaZero)

/-! ## Same-occurrence q-rich point-owner splice

The analytic point is specialized only after the source-generated full-row
component has been built.  This is deliberately a map-level object: it keeps
the `WholeRole`/`FactorRow` coordinates in the transposed total instead of
projecting them to the old endpoint fibre.  The frozen arithmetic consumer is
the next type check; no endpoint equality or fixedness is introduced here.
-/

noncomputable abbrev PairQRichExtensionFunctor :=
  (ModuleCat.extendScalars
      blockCoordinateToPairZeroFiber).mapHomologicalComplex
    (ComplexShape.up ℤ)

noncomputable abbrev PointQRichExtensionFunctor
    (point : DeterminantLinePoint) :=
  PointExtensionFunctor point

noncomputable abbrev PointQRichFullRowTotal
    (point : DeterminantLinePoint) (stage : Nat) :=
  (PointQRichExtensionFunctor point).obj
    (PairQRichExtensionFunctor.obj
      (fullRowDerivedSquare stage).verticalTotal)

noncomputable abbrev PointQRichLineageSource
    (point : DeterminantLinePoint) :=
    (PointQRichExtensionFunctor point).obj
    (PairQRichExtensionFunctor.obj QRichLineageSingleOne)

noncomputable abbrev PairQRichFullRowTotal (stage : Nat) :=
  PairDerivedExtensionFunctor.obj (fullRowDerivedSquare stage).verticalTotal

noncomputable abbrev PairQRichLineageSource :=
  PairQRichExtensionFunctor.obj QRichLineageSingleOne

noncomputable def pairQRichLineageBasePoint
    (base : BlockDualBase) :
    PairDerivedScalarSingleOne ⟶ PairQRichLineageSource :=
  PairQRichExtensionFunctor.map (qRichLineageBasePoint base)

noncomputable def pairQRichLineageTransposedPoint (stage : Nat) :
    PairQRichLineageSource ⟶ PairQRichFullRowTotal stage :=
  PairQRichExtensionFunctor.map
    (qRichLineageFullRowTransposedPoint stage)

noncomputable def pairQRichLineageCoordinateComponent (stage : Nat) :
    PairDerivedScalarSingleOne ⟶ PairQRichFullRowTotal stage :=
  universalLeftCoordinate installedOwner •
      (pairQRichLineageBasePoint blockLeftEndpointBase ≫
        pairQRichLineageTransposedPoint stage) +
    universalRightCoordinate installedOwner •
      (pairQRichLineageBasePoint blockRightEndpointBase ≫
        pairQRichLineageTransposedPoint stage)

noncomputable def pointQRichLineageCoordinateComponent
    (point : DeterminantLinePoint) (stage : Nat) :
    PointDerivedScalarSingleOne point ⟶
      (PointExtensionFunctor point).obj (PairQRichFullRowTotal stage) :=
  (PointQRichExtensionFunctor point).map
    (pairQRichLineageCoordinateComponent stage)

noncomputable def mathlibZeroQRichCoordinateComponent
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0)
    (stage : Nat) :
    PointDerivedScalarSingleOne (mathlibZeroPoint coordinate zetaZero) ⟶
      (PointExtensionFunctor (mathlibZeroPoint coordinate zetaZero)).obj
        (PairQRichFullRowTotal stage) :=
  pointQRichLineageCoordinateComponent
    (mathlibZeroPoint coordinate zetaZero) stage

theorem mathlibZeroQRichCoordinateComponent_same_owner
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0)
    (stage : Nat) :
    mathlibZeroQRichCoordinateComponent coordinate zetaZero stage =
      (PointQRichExtensionFunctor
        (mathlibZeroPoint coordinate zetaZero)).map
        (pairQRichLineageCoordinateComponent stage) :=
  rfl

noncomputable def pointQRichFullRowTransposedPoint
    (point : DeterminantLinePoint) (stage : Nat) :
    PointQRichLineageSource point ⟶ PointQRichFullRowTotal point stage :=
  (PointQRichExtensionFunctor point).map
    (PairQRichExtensionFunctor.map
      (qRichLineageFullRowTransposedPoint stage))

noncomputable def pointQRichLineageRestriction
    (point : DeterminantLinePoint) (stage : Nat) :
    PointQRichLineageSource point ⟶ PointQRichLineageSource point :=
  (PointQRichExtensionFunctor point).map
    (PairQRichExtensionFunctor.map
      (qRichLineageSingleOneRestriction stage))

noncomputable def pointQRichFullRowVerticalTransition
    (point : DeterminantLinePoint) (stage : Nat) :
    PointQRichFullRowTotal point (stage + 1) ⟶
      PointQRichFullRowTotal point stage :=
  (PointQRichExtensionFunctor point).map
    (PairQRichExtensionFunctor.map
      (fullRowDerivedCube stage).verticalTotalTransition)

theorem pointQRichFullRowTransposedPoint_successor
    (point : DeterminantLinePoint) (stage : Nat) :
    pointQRichFullRowTransposedPoint point (stage + 1) ≫
        pointQRichFullRowVerticalTransition point stage =
      pointQRichLineageRestriction point stage ≫
        pointQRichFullRowTransposedPoint point stage := by
  change
    (PointQRichExtensionFunctor point).map
        (PairQRichExtensionFunctor.map
          (qRichLineageFullRowTransposedPoint (stage + 1))) ≫
      (PointQRichExtensionFunctor point).map
        (PairQRichExtensionFunctor.map
          ((fullRowDerivedCube stage).verticalTotalTransition)) =
    (PointQRichExtensionFunctor point).map
        (PairQRichExtensionFunctor.map
          (qRichLineageSingleOneRestriction stage)) ≫
      (PointQRichExtensionFunctor point).map
        (PairQRichExtensionFunctor.map
          (qRichLineageFullRowTransposedPoint stage))
  rw [← (PointQRichExtensionFunctor point).map_comp,
    ← (PointQRichExtensionFunctor point).map_comp,
    ← PairQRichExtensionFunctor.map_comp,
    ← PairQRichExtensionFunctor.map_comp,
    qRichLineageFullRowTransposedPoint_successor]

theorem pointQRichFullRowTransposedPoint_projects
    (point : DeterminantLinePoint) (stage : Nat) :
    pointQRichFullRowTransposedPoint point stage =
      (PointQRichExtensionFunctor point).map
        (PairQRichExtensionFunctor.map
          (qRichLineageFullRowTransposedPoint stage)) :=
  rfl

/-! ## Canonical projection back to the generated derived chain

The full-row total is not a parallel endpoint object.  Its existing inverse
transposition followed by the horizontal `fst` is the canonical map back to
the already generated corrected derived solution.  The next theorem records
that this projection is natural for the same successor cube; no coordinate
specialization or finite-generation premise is introduced.
-/

noncomputable def fullRowToDerivedSolution (stage : Nat) :
    (fullRowDerivedSquare stage).verticalTotal ⟶
      LocalDerivedSolution stage :=
  (fullRowDerivedSquare stage).generatedTotalIso.inv ≫
    CochainComplex.mappingCocone.fst (fullRowHorizontalMap stage)

noncomputable def qRichLineageDerivedSolutionPoint (stage : Nat) :
    QRichLineageSingleOne ⟶ LocalDerivedSolution stage :=
  qRichLineageFullRowTransposedPoint stage ≫
    fullRowToDerivedSolution stage

theorem qRichLineageDerivedSolutionPoint_eq (stage : Nat) :
    qRichLineageDerivedSolutionPoint stage =
      qRichDerivedLineagePoint stage := by
  simp [qRichLineageDerivedSolutionPoint, fullRowToDerivedSolution,
    qRichLineageFullRowTransposedPoint, Category.assoc,
    qRichLineageFullRowOuterPoint_fst]

@[reassoc (attr := simp)] theorem qRichLineageDerivedSolutionPoint_fst_zero
    (stage : Nat) :
    qRichLineageDerivedSolutionPoint stage ≫
        CochainComplex.mappingCocone.fst
          (CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber.localTotalInclusion
            stage) = 0 := by
  rw [qRichLineageDerivedSolutionPoint_eq,
    qRichDerivedLineagePoint_fst]

theorem fullRowToDerivedSolution_successor (stage : Nat) :
    fullRowToDerivedSolution (stage + 1) ≫
        localCorrectedEndpointRestriction stage =
      (fullRowDerivedCube stage).verticalTotalTransition ≫
        fullRowToDerivedSolution stage := by
  unfold fullRowToDerivedSolution
  rw [Category.assoc,
    ← QRich.fullRowUpperTransition_eq_localCorrectedEndpointRestriction stage]
  have fstSquare :=
    CochainMappingCoconeFunctoriality.mappingCoconeMap_fst
      (fullRowHorizontalMap (stage + 1))
      (fullRowHorizontalMap stage)
      (fullRowDerivedCube stage).upperTransition
      (fullRowDerivedCube stage).lowerTransition
      (fullRowDerivedCube stage).horizontalMapSquare
  have fstSquare' :
      (fullRowDerivedCube stage).horizontalTotalTransition ≫
          CochainComplex.mappingCocone.fst
            (fullRowHorizontalMap stage) =
        CochainComplex.mappingCocone.fst
            (fullRowHorizontalMap (stage + 1)) ≫
          (fullRowDerivedCube stage).upperTransition := by
    exact fstSquare
  rw [← fstSquare', ← Category.assoc,
    CochainMappingCoconeTotalFiberNaturality.HomotopyCommutativeCochainSquareMorphismAt.generatedTotalIso_inv_naturality]
  rfl

/-! The full-row owner also has a strict successor after projection to the
already generated local derived solution.  This is the first global-limit
splice: the q-rich source is still over `BlockCoordinateRing`, and no point
or finite-generation specialization has occurred. -/
theorem qRichLineageDerivedSolutionPoint_successor (stage : Nat) :
    qRichLineageSingleOneRestriction stage ≫
        qRichLineageDerivedSolutionPoint stage =
      qRichLineageDerivedSolutionPoint (stage + 1) ≫
        localCorrectedEndpointRestriction stage := by
  unfold qRichLineageDerivedSolutionPoint
  calc
    qRichLineageSingleOneRestriction stage ≫
          (qRichLineageFullRowTransposedPoint stage ≫
            fullRowToDerivedSolution stage) =
        (qRichLineageSingleOneRestriction stage ≫
          qRichLineageFullRowTransposedPoint stage) ≫
            fullRowToDerivedSolution stage :=
      (Category.assoc _ _ _).symm
    _ = (qRichLineageFullRowTransposedPoint (stage + 1) ≫
          (fullRowDerivedCube stage).verticalTotalTransition) ≫
            fullRowToDerivedSolution stage := by
      rw [qRichLineageFullRowTransposedPoint_successor]
    _ = qRichLineageFullRowTransposedPoint (stage + 1) ≫
          ((fullRowDerivedCube stage).verticalTotalTransition ≫
            fullRowToDerivedSolution stage) :=
      Category.assoc _ _ _
    _ = qRichLineageFullRowTransposedPoint (stage + 1) ≫
          (fullRowToDerivedSolution (stage + 1) ≫
            localCorrectedEndpointRestriction stage) := by
      rw [fullRowToDerivedSolution_successor]
    _ = (qRichLineageFullRowTransposedPoint (stage + 1) ≫
          fullRowToDerivedSolution (stage + 1)) ≫
            localCorrectedEndpointRestriction stage :=
      (Category.assoc _ _ _).symm

noncomputable abbrev qRichLineageDiagram :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat BlockCoordinateRing) ℤ :=
  Functor.ofOpSequence
    (X := fun _stage => QRichLineageSingleOne)
    qRichLineageSingleOneRestriction

/-! A constant-source cone would erase the actual q-rich transition.  The
stage-zero map is multiplication by `3`, so it is not the identity even on
the canonical left endpoint base.  This is a kernel-checked rejection of the
tempting unscaled cone, not a no-go for the source diagram above. -/
theorem qRichLineageSingleOneRestriction_zero_ne_id :
    qRichLineageSingleOneRestriction 0 ≠ 𝟙 QRichLineageSingleOne := by
  intro equality
  have degreeMap := congrArg (fun arrow => arrow.f 1) equality
  have linearMap := congrArg (fun arrow => arrow.hom) degreeMap
  have evaluated := congrArg (fun map => map blockLeftEndpointBase) linearMap
  change (blockQRichSuccessorScale 0 : BlockCoordinateRing) •
      blockLeftEndpointBase = blockLeftEndpointBase at evaluated
  have scaleZero : blockQRichSuccessorScale 0 = 3 := by
    unfold blockQRichSuccessorScale
    have historyEquality :
        StageHistory seedOccurrence.root 0 =
          CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory 0 := by
      rfl
    rw [historyEquality,
      CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory_cardinalShadow]
  rw [scaleZero] at evaluated
  have atZero := congrFun evaluated 0
  norm_num [blockLeftEndpointBase] at atZero
  exact (show (3 : BlockCoordinateRing) ≠ 1 by
    intro equality'
    have constants : MvPolynomial.C (σ := BlockVariable) (3 : ℤ) =
        MvPolynomial.C (σ := BlockVariable) (1 : ℤ) := by
      simpa using equality'
    have integers := (MvPolynomial.C_injective BlockVariable ℤ) constants
    norm_num at integers) atZero

/-! ## Typed point-owner strike

The q-rich source is not a constant cone already over `BlockCoordinateRing`.
Its stage-zero successor is the literal integer `3`; consequently any
putative constant source map compatible with that successor has zero
degree-one component.  This is a scoped kernel-checked rejection of the
unscaled point owner, not a rejection of the source-generated q-rich diagram
itself.
-/

theorem qRichLineageSingleOneRestriction_zero_eq_three_nsmul :
    qRichLineageSingleOneRestriction 0 = (3 : ℕ) • 𝟙 QRichLineageSingleOne := by
  apply HomologicalComplex.Hom.ext
  funext degree
  by_cases h : degree = 1
  · subst degree
    change ModuleCat.ofHom
        ((blockQRichSuccessorScale 0 : BlockCoordinateRing) •
          (LinearMap.id : BlockDualBase →ₗ[BlockCoordinateRing] BlockDualBase)) = _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f]
    change (blockQRichSuccessorScale 0 : BlockCoordinateRing) • x =
      (3 : ℕ) • x
    have scale : blockQRichSuccessorScale 0 = 3 := by
      unfold blockQRichSuccessorScale
      have historyEquality :
          StageHistory seedOccurrence.root 0 =
            CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory 0 := by
        rfl
      rw [historyEquality,
        CanonicalUnitArithmeticFactorizationOccurrence.runtimeWholeHistory_cardinalShadow]
    rw [scale]
    exact Nat.cast_smul_eq_nsmul BlockCoordinateRing 3 x
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1
      BlockDualBaseObject degree h).eq_of_src _ _

theorem qRichConstantSource_degreeOne_zero
    (sourceMap : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      QRichLineageSingleOne)
    (compat : sourceMap ≫ qRichLineageSingleOneRestriction 0 = sourceMap) :
    sourceMap.f 1 = 0 := by
  rw [qRichLineageSingleOneRestriction_zero_eq_three_nsmul] at compat
  have hcomp := congrArg (fun arrow => arrow.f 1) compat
  simp only [HomologicalComplex.comp_f] at hcomp
  rw [HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f] at hcomp
  rw [CategoryTheory.Preadditive.comp_nsmul, Category.comp_id] at hcomp
  have h2map : (2 : ℕ) • sourceMap.f 1 = 0 := by
    have hsub := sub_eq_zero.mpr hcomp
    have hrewrite : (3 : ℕ) • sourceMap.f 1 - sourceMap.f 1 =
        (2 : ℕ) • sourceMap.f 1 := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul]
      simp
    rw [hrewrite] at hsub
    exact hsub
  have h2mapScalar : (2 : BlockCoordinateRing) • sourceMap.f 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h2value := congrArg (fun arrow => arrow.hom x) h2map
    simpa only [two_smul] using h2value
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h2value := congrArg (fun arrow => arrow.hom x) h2mapScalar
  change (2 : BlockCoordinateRing) •
      ((sourceMap.f 1).hom x : BlockDualBase) = 0 at h2value
  have twoNe : (2 : BlockCoordinateRing) ≠ 0 := by
    change MvPolynomial.C (σ := BlockVariable) (2 : ℤ) ≠ 0
    rw [MvPolynomial.C_ne_zero]
    norm_num
  exact (IsRegular.smul_eq_zero_iff_right
    (M := BlockDualBase)
    (IsRegular.of_ne_zero twoNe)).mp h2value

noncomputable def generatedQRichLineageDerivedSolutionPoint (stage : Nat) :
    QRichLineageSingleOne ⟶
      blockDerivedSolutionDiagramFace.actualDiagram.obj
        (Opposite.op stage) :=
  qRichLineageDerivedSolutionPoint
      (blockDerivedSolutionProcess.stateAt stage) ≫
    eqToHom (blockDerivedSolutionDiagramFace.actualDiagram_obj stage).symm

theorem generatedQRichLineageDerivedSolutionPoint_successor (stage : Nat) :
    qRichLineageSingleOneRestriction stage ≫
        generatedQRichLineageDerivedSolutionPoint stage =
      generatedQRichLineageDerivedSolutionPoint (stage + 1) ≫
        blockDerivedSolutionDiagramFace.actualDiagram.map
          ((homOfLE (Nat.le_succ stage)).op) := by
  rw [blockDerivedSolutionDiagramFace.actualDiagram_succ]
  unfold generatedQRichLineageDerivedSolutionPoint
  simp only [RootGeneratedCofinalProcessDiagramAt.actualDiagram_obj,
    eqToHom_refl, Category.comp_id,
    RootGeneratedCofinalProcessDiagramAt.actualProcess,
    blockDerivedSolutionDiagramFace,
    blockDerivedSolutionProcessOccurrence_process,
    blockDerivedSolutionProcess_stateAt_succ]
  change qRichLineageSingleOneRestriction stage ≫
      qRichLineageDerivedSolutionPoint
        (blockDerivedSolutionProcess.stateAt stage) =
    qRichLineageDerivedSolutionPoint
        (Nat.succ (blockDerivedSolutionProcess.stateAt stage)) ≫
      localCorrectedEndpointRestriction
        (blockDerivedSolutionProcess.stateAt stage)
  rw [blockDerivedSolutionProcess_stateAt]
  exact qRichLineageDerivedSolutionPoint_successor stage

noncomputable def qRichLineageToDerivedDiagram :
    qRichLineageDiagram ⟶ blockDerivedSolutionDiagramFace.actualDiagram :=
  NatTrans.ofOpSequence generatedQRichLineageDerivedSolutionPoint
    (fun stage => by
      simpa only [qRichLineageDiagram,
        Functor.ofOpSequence_map_homOfLE_succ] using
        generatedQRichLineageDerivedSolutionPoint_successor stage)

noncomputable def globalQRichLineageDerivedSolutionPoint :
    limit qRichLineageDiagram ⟶ BlockGlobalDerivedSolution :=
  limMap qRichLineageToDerivedDiagram

theorem globalQRichLineageDerivedSolutionPoint_restriction (stage : Nat) :
    globalQRichLineageDerivedSolutionPoint ≫
        limit.π blockDerivedSolutionDiagramFace.actualDiagram
          (Opposite.op stage) =
      limit.π qRichLineageDiagram (Opposite.op stage) ≫
        generatedQRichLineageDerivedSolutionPoint stage := by
  exact limMap_π qRichLineageToDerivedDiagram (Opposite.op stage)

/-! The frozen local-process mouth consumes an additive FG element carrier.
The specialized full-row total is intentionally not silently coerced into
that mouth: this compile-time guard records the remaining typed arrow rather
than smuggling an FG premise or a parallel presentation. -/
example (_point : DeterminantLinePoint) (_stage : Nat) : True := by
  fail_if_success
    letI : AddGroup.FG
        ((PointQRichFullRowTotal _point _stage).X 1 : Type) := inferInstance
  trivial

theorem blockDerivedSolutionDiagramFace_projects :
    blockDerivedSolutionDiagramFace.root = seedOccurrence :=
  blockDerivedSolutionDiagramFace
    |>.preserves_root_process_and_generated_diagram |>.1

theorem preserves_exact_root_pair_zero_fibre_and_mathlib_point
    (coordinate : ℂ) (zetaZero : riemannZeta coordinate = 0) :
    blockDerivedSolutionDiagramFace.root = seedOccurrence ∧
      (mathlibZeroPoint coordinate zetaZero).pair =
        (coordinate, coordinateReversal coordinate) ∧
      mathlibZeroDerivedSolutionPoint coordinate zetaZero =
        determinantLineDerivedSolutionPoint
          (mathlibZeroPoint coordinate zetaZero) :=
  ⟨blockDerivedSolutionDiagramFace_projects, rfl, rfl⟩

end
end CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionPointSpecialization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
