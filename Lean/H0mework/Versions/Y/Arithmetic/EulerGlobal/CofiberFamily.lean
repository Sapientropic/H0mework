import H0mework.Realization.MappingCone.Functoriality
import H0mework.Versions.Y.Arithmetic.EulerGlobal.HistoryZeroFiberState
import H0mework.Realization.MappingCone.HomotopyDescent
import H0mework.Realization.MappingCone.ProjectionHomotopy
import H0mework.Realization.Arithmetic.DerivedAdicCofiber

/-!
# Family-level zero-fibre action cofiber

The generated global determinant zero-fibre ring supplies its universal
parameter `r`.  On the same whole-relation vertex family, the actual action
therefore supplies `1-rF`.  The frozen derived-cofiber kernel consumes that
map at the exact factorization occurrence.

This file exposes only the entire cofiber family, reversal, its tautological
target cocycle, and the global-to-local restriction maps.  It chooses no
point, asserts no nonzero or unit normalization, and contains no classical
coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticIntegralActionCofiberFamily

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolutionLocalLanding
open CanonicalUnitArithmeticFactorizationWholeHistoryIntegralZeroFiberState
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CategoryTheory
open CategoryTheory.Limits
open CochainMappingCoconeFunctoriality
open CofinalPolynomialSectionZeroFiber
open DerivedAdicCofiber
open MappingCoconeHomotopyDescent
open LivingLawMappingCoconeProjectionNullHomotopy
open scoped TensorProduct

noncomputable section

/-! ## Rooted global family -/

abbrev ScalarVertexObject : ModuleCat ℤ := ModuleCat.of ℤ ScalarVertex

noncomputable abbrev scalarVertexSingle :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj ScalarVertexObject

noncomputable def actionMap : scalarVertexSingle ⟶ scalarVertexSingle :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom universalEulerOperator)

noncomputable def reversalMap : scalarVertexSingle ⟶ scalarVertexSingle :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom extendedReversalZero)

theorem reversal_action_square :
    reversalMap ≫ actionMap = actionMap ≫ reversalMap := by
  unfold reversalMap actionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun universalEulerOperator_reversal_commutes value

def scalarVertexOccurrence : RootedAccountedUnfolding
    (DerivedAdicCofiber.IntegralCochainComplex ℤ) :=
  seedOccurrence.map fun _owner => scalarVertexSingle

def actionMapOccurrence : RootedAccountedUnfolding
    (scalarVertexOccurrence.root ⟶ scalarVertexOccurrence.root) :=
  seedOccurrence.map fun _owner => actionMap

def actionCofiberFace : RootGeneratedDerivedAdicCofiberAt
    seedOccurrence scalarVertexOccurrence scalarVertexOccurrence
      actionMapOccurrence :=
  RootGeneratedDerivedAdicCofiberAt.generate

noncomputable abbrev ActionCofiber :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  CochainComplex.mappingCocone actionMap

theorem actionCofiber_eq_frameworkCofiber :
    ActionCofiber = actionCofiberFace.cofiberComplex :=
  rfl

/-- Family-level tautological target cocycle.  This is not a selected point. -/
noncomputable def tautologicalInclusion :
    CochainComplex.HomComplex.Cocycle scalarVertexSingle ActionCofiber 1 :=
  CochainComplex.mappingCocone.inr actionMap

noncomputable def cofiberReversal : ActionCofiber ⟶ ActionCofiber :=
  mappingCoconeMap actionMap actionMap reversalMap reversalMap
    reversal_action_square

theorem actionCofiberFace_preserves_exact_occurrence_and_action :
    actionCofiberFace.root = seedOccurrence ∧
      actionCofiberFace.sourceComplex = scalarVertexSingle ∧
      actionCofiberFace.targetComplex = scalarVertexSingle ∧
      actionCofiberFace.actualTransition = actionMap := by
  exact actionCofiberFace.preserves_actual_transition

/-! ## Full whole-relation family -/

abbrev ScalarRelationObject : ModuleCat ℤ := ModuleCat.of ℤ ScalarRelation

noncomputable abbrev scalarRelationSingle :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj ScalarRelationObject

noncomputable def scalarDifferentialMap :
    scalarVertexSingle ⟶ scalarRelationSingle :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom extendedDifferential)

def relationEulerOperator : ScalarRelation →ₗ[ℤ] ScalarRelation :=
  LinearMap.id - extendedEulerOne

noncomputable def relationActionMap :
    scalarRelationSingle ⟶ scalarRelationSingle :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom relationEulerOperator)

noncomputable def scalarRelationReversalMap :
    scalarRelationSingle ⟶ scalarRelationSingle :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom extendedReversalOne)

theorem reversal_differential_square :
    reversalMap ≫ scalarDifferentialMap =
      scalarDifferentialMap ≫ scalarRelationReversalMap := by
  unfold reversalMap scalarDifferentialMap scalarRelationReversalMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun extendedDifferential_reversal_square value

theorem globalEulerReversalOne_commutes :
    globalReversalOne.comp globalEulerOne =
      globalEulerOne.comp globalReversalOne := by
  exact congrArg
    (fun action : RelationGlobalState ⟶ RelationGlobalState =>
      (action.f 1).hom)
    globalEuler_reversal_commutes

theorem extendedEuler_reversalOne_commutes :
    extendedReversalOne.comp extendedEulerOne =
      extendedEulerOne.comp extendedReversalOne := by
  rw [extendedReversalOne, extendedEulerOne,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact globalEulerReversalOne_commutes

theorem relationEulerOperator_reversal_commutes :
    relationEulerOperator.comp extendedReversalOne =
      extendedReversalOne.comp relationEulerOperator := by
  unfold relationEulerOperator
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id]
  apply congrArg (fun current => extendedReversalOne - current)
  exact extendedEuler_reversalOne_commutes.symm

theorem relationReversal_action_square :
    scalarRelationReversalMap ≫ relationActionMap =
      relationActionMap ≫ scalarRelationReversalMap := by
  unfold scalarRelationReversalMap relationActionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun relationEulerOperator_reversal_commutes value

theorem action_differential_linear_square :
    extendedDifferential.comp universalEulerOperator =
      relationEulerOperator.comp extendedDifferential := by
  unfold universalEulerOperator relationEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    extendedDifferential_euler_square]

theorem action_differential_square :
    actionMap ≫ scalarDifferentialMap =
      scalarDifferentialMap ≫ relationActionMap := by
  unfold actionMap scalarDifferentialMap relationActionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun action_differential_linear_square value

noncomputable abbrev ScalarWholeRelationComplex :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  CochainComplex.mappingCocone scalarDifferentialMap

noncomputable def wholeActionMap :
    ScalarWholeRelationComplex ⟶ ScalarWholeRelationComplex :=
  mappingCoconeMap scalarDifferentialMap scalarDifferentialMap
    actionMap relationActionMap action_differential_square

noncomputable def wholeReversalMap :
    ScalarWholeRelationComplex ⟶ ScalarWholeRelationComplex :=
  mappingCoconeMap scalarDifferentialMap scalarDifferentialMap
    reversalMap scalarRelationReversalMap reversal_differential_square

theorem wholeReversal_action_square :
    wholeReversalMap ≫ wholeActionMap =
      wholeActionMap ≫ wholeReversalMap := by
  unfold wholeReversalMap wholeActionMap
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact reversal_action_square
  · exact relationReversal_action_square

def scalarWholeRelationOccurrence : RootedAccountedUnfolding
    (DerivedAdicCofiber.IntegralCochainComplex ℤ) :=
  seedOccurrence.map fun _owner => ScalarWholeRelationComplex

def wholeActionMapOccurrence : RootedAccountedUnfolding
    (scalarWholeRelationOccurrence.root ⟶
      scalarWholeRelationOccurrence.root) :=
  seedOccurrence.map fun _owner => wholeActionMap

def wholeActionCofiberFace : RootGeneratedDerivedAdicCofiberAt
    seedOccurrence scalarWholeRelationOccurrence scalarWholeRelationOccurrence
      wholeActionMapOccurrence :=
  RootGeneratedDerivedAdicCofiberAt.generate

noncomputable abbrev WholeActionCofiber :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  CochainComplex.mappingCocone wholeActionMap

theorem wholeActionCofiber_eq_frameworkCofiber :
    WholeActionCofiber = wholeActionCofiberFace.cofiberComplex :=
  rfl

/-- The full family-level universal inclusion.  It contains all relation
degrees and still chooses no element. -/
noncomputable def wholeTautologicalInclusion :
    CochainComplex.HomComplex.Cocycle
      ScalarWholeRelationComplex WholeActionCofiber 1 :=
  CochainComplex.mappingCocone.inr wholeActionMap

noncomputable def wholeCofiberReversal :
    WholeActionCofiber ⟶ WholeActionCofiber :=
  mappingCoconeMap wholeActionMap wholeActionMap
    wholeReversalMap wholeReversalMap wholeReversal_action_square

theorem wholeTautologicalInclusion_reversal :
    wholeTautologicalInclusion.1.comp
        (CochainComplex.HomComplex.Cochain.ofHom
          wholeCofiberReversal) (add_zero 1) =
      (CochainComplex.HomComplex.Cochain.ofHom
        wholeReversalMap).comp wholeTautologicalInclusion.1
          (zero_add 1) := by
  exact mappingCoconeMap_inr wholeActionMap wholeReversalMap
    wholeReversalMap wholeReversal_action_square

theorem wholeActionCofiberFace_preserves_exact_occurrence_and_action :
    wholeActionCofiberFace.root = seedOccurrence ∧
      wholeActionCofiberFace.sourceComplex = ScalarWholeRelationComplex ∧
      wholeActionCofiberFace.targetComplex = ScalarWholeRelationComplex ∧
      wholeActionCofiberFace.actualTransition = wholeActionMap := by
  exact wholeActionCofiberFace.preserves_actual_transition

/-! ## Local restrictions of the same family -/

def localParameterMultiplication (stage : Nat) :
    LocalCoefficientRing stage →ₗ[ℤ] LocalCoefficientRing stage where
  toFun value :=
    AdjoinRoot.root
        (GlobalDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial * value
  map_add' := by intro left right; exact mul_add _ _ _
  map_smul' := by
    intro scalar value
    simp only [RingHom.id_apply]
    simpa [mul_comm] using mul_smul_comm scalar
      (AdjoinRoot.root
        (GlobalDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial) value

def localSuccessorArrow (stage : Nat) :
    (Opposite.op (stage + 1) : ℕᵒᵖ) ⟶ Opposite.op stage :=
  (homOfLE (Nat.le_succ stage)).op

def localCoefficientSuccessor (stage : Nat) :
    LocalCoefficientRing (stage + 1) →ₗ[ℤ] LocalCoefficientRing stage :=
  (GlobalZeroFiberDiagram.map (localSuccessorArrow stage)).hom
    |>.toAddMonoidHom.toIntLinearMap

theorem localCoefficientSuccessor_parameter_square (stage : Nat) :
    (localCoefficientSuccessor stage).comp
        (localParameterMultiplication (stage + 1)) =
      (localParameterMultiplication stage).comp
        (localCoefficientSuccessor stage) := by
  apply LinearMap.ext
  intro value
  change
    (zeroFiberMap
      (globalSectionFace.globalSectionDiagram.map
        (localSuccessorArrow stage)))
        (AdjoinRoot.root
            (GlobalDeterminantSectionDiagram.obj
              (Opposite.op (stage + 1))).polynomial * value) =
      AdjoinRoot.root
          (GlobalDeterminantSectionDiagram.obj
            (Opposite.op stage)).polynomial *
        (zeroFiberMap
          (globalSectionFace.globalSectionDiagram.map
            (localSuccessorArrow stage))) value
  rw [map_mul, zeroFiberMap_root]

def localScalarVertexSuccessor (stage : Nat) :
    LocalScalarVertex (stage + 1) →ₗ[ℤ] LocalScalarVertex stage :=
  TensorProduct.map (localCoefficientSuccessor stage)
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction
      seedOccurrence.root stage)

def localScalarRelationSuccessor (stage : Nat) :
    LocalScalarRelation (stage + 1) →ₗ[ℤ] LocalScalarRelation stage :=
  TensorProduct.map (localCoefficientSuccessor stage)
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction
      seedOccurrence.root stage)

theorem localScalarSuccessor_differential_square (stage : Nat) :
    (localExtendedDifferential stage).comp
        (localScalarVertexSuccessor stage) =
      (localScalarRelationSuccessor stage).comp
        (localExtendedDifferential (stage + 1)) := by
  unfold localExtendedDifferential localScalarVertexSuccessor
    localScalarRelationSuccessor
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact factorizationRestriction_differential_square
      seedOccurrence.root stage

def localExtendedEuler (stage : Nat) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarVertex stage :=
  TensorProduct.map (localParameterMultiplication stage)
    (vertexEulerAction seedOccurrence.root stage)

def localEulerOperator (stage : Nat) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarVertex stage :=
  LinearMap.id - localExtendedEuler stage

def localExtendedReversalZero (stage : Nat) :
    LocalScalarVertex stage →ₗ[ℤ] LocalScalarVertex stage :=
  TensorProduct.map LinearMap.id
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
      seedOccurrence.root stage)

theorem coefficientRestriction_parameter_square (stage : Nat) :
    (coefficientRestriction stage).comp parameterMultiplication =
      (localParameterMultiplication stage).comp
        (coefficientRestriction stage) := by
  apply LinearMap.ext
  intro value
  change
    (limit.π GlobalZeroFiberDiagram (Opposite.op stage)).hom
        (universalDeterminantParameter * value) =
      AdjoinRoot.root
          (GlobalDeterminantSectionDiagram.obj
            (Opposite.op stage)).polynomial *
        (show LocalCoefficientRing stage from
          (limit.π GlobalZeroFiberDiagram (Opposite.op stage)).hom value)
  rw [map_mul, universalParameter_restriction]

theorem vertexRestriction_euler_square (stage : Nat) :
    (vertexRestriction stage).comp globalEulerZero =
      (vertexEulerAction seedOccurrence.root stage).comp
        (vertexRestriction stage) := by
  have square := globalEulerAction_restriction (Opposite.op stage)
  exact congrArg (fun arrow => (arrow.f 0).hom) square

theorem vertexRestriction_reversal_square (stage : Nat) :
    (vertexRestriction stage).comp globalReversalZero =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
        seedOccurrence.root stage).comp (vertexRestriction stage) := by
  have square := globalReversal_restriction (Opposite.op stage)
  exact congrArg (fun arrow => (arrow.f 0).hom) square

theorem localTensorRestriction_euler_square (stage : Nat) :
    (localTensorRestriction stage).comp extendedEulerZero =
      (localExtendedEuler stage).comp (localTensorRestriction stage) := by
  rw [localTensorRestriction, extendedEulerZero, localExtendedEuler,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    coefficientRestriction_parameter_square,
    vertexRestriction_euler_square]

theorem localTensorRestriction_operator_square (stage : Nat) :
    (localTensorRestriction stage).comp universalEulerOperator =
      (localEulerOperator stage).comp (localTensorRestriction stage) := by
  unfold universalEulerOperator localEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    localTensorRestriction_euler_square]

theorem localTensorRestriction_reversal_square (stage : Nat) :
    (localTensorRestriction stage).comp extendedReversalZero =
      (localExtendedReversalZero stage).comp
        (localTensorRestriction stage) := by
  rw [localTensorRestriction, extendedReversalZero,
    localExtendedReversalZero,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact vertexRestriction_reversal_square stage

theorem localExtendedEuler_reversal_commutes (stage : Nat) :
    (localExtendedReversalZero stage).comp (localExtendedEuler stage) =
      (localExtendedEuler stage).comp
        (localExtendedReversalZero stage) := by
  rw [localExtendedReversalZero, localExtendedEuler,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact (vertexEuler_reversal_commutes seedOccurrence.root stage).symm

theorem localEulerOperator_reversal_commutes (stage : Nat) :
    (localEulerOperator stage).comp (localExtendedReversalZero stage) =
      (localExtendedReversalZero stage).comp
        (localEulerOperator stage) := by
  unfold localEulerOperator
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id]
  apply congrArg (fun current => localExtendedReversalZero stage - current)
  exact (localExtendedEuler_reversal_commutes stage).symm

abbrev LocalScalarVertexObject (stage : Nat) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LocalScalarVertex stage)

noncomputable abbrev localScalarVertexSingle (stage : Nat) :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    (LocalScalarVertexObject stage)

noncomputable def localActionMap (stage : Nat) :
    localScalarVertexSingle stage ⟶ localScalarVertexSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localEulerOperator stage))

noncomputable def localVertexReversalMap (stage : Nat) :
    localScalarVertexSingle stage ⟶ localScalarVertexSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localExtendedReversalZero stage))

noncomputable def globalToLocalMap (stage : Nat) :
    scalarVertexSingle ⟶ localScalarVertexSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localTensorRestriction stage))

theorem globalToLocal_action_square (stage : Nat) :
    globalToLocalMap stage ≫ localActionMap stage =
      actionMap ≫ globalToLocalMap stage := by
  unfold globalToLocalMap localActionMap actionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localTensorRestriction_operator_square stage).symm value

theorem globalToLocal_vertex_reversal_square (stage : Nat) :
    globalToLocalMap stage ≫ localVertexReversalMap stage =
      reversalMap ≫ globalToLocalMap stage := by
  unfold globalToLocalMap localVertexReversalMap reversalMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localTensorRestriction_reversal_square stage).symm value

noncomputable abbrev LocalActionCofiber (stage : Nat) :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  CochainComplex.mappingCocone (localActionMap stage)

/-- Actual restriction of the family-level zero-fibre cofiber. -/
noncomputable def cofiberRestriction (stage : Nat) :
    ActionCofiber ⟶ LocalActionCofiber stage :=
  mappingCoconeMap actionMap (localActionMap stage)
    (globalToLocalMap stage) (globalToLocalMap stage)
      (globalToLocal_action_square stage)

noncomputable def localTautologicalInclusion (stage : Nat) :
    CochainComplex.HomComplex.Cocycle
      (localScalarVertexSingle stage) (LocalActionCofiber stage) 1 :=
  CochainComplex.mappingCocone.inr (localActionMap stage)

theorem cofiberRestriction_fst (stage : Nat) :
    cofiberRestriction stage ≫
        CochainComplex.mappingCocone.fst (localActionMap stage) =
      CochainComplex.mappingCocone.fst actionMap ≫
        globalToLocalMap stage :=
  mappingCoconeMap_fst actionMap (localActionMap stage)
    (globalToLocalMap stage) (globalToLocalMap stage)
      (globalToLocal_action_square stage)

/-- Naturality of the tautological target direction under actual restriction. -/
theorem cofiberRestriction_snd (stage : Nat) :
    (CochainComplex.HomComplex.Cochain.ofHom
        (cofiberRestriction stage)).comp
          (CochainComplex.mappingCocone.snd (localActionMap stage))
            (zero_add (-1)) =
      (CochainComplex.mappingCocone.snd actionMap).comp
        (CochainComplex.HomComplex.Cochain.ofHom
          (globalToLocalMap stage)) (add_zero (-1)) :=
  mappingCoconeMap_snd actionMap (localActionMap stage)
    (globalToLocalMap stage) (globalToLocalMap stage)
      (globalToLocal_action_square stage)

/-- The universal target inclusion restricts as a family; no point is chosen. -/
theorem tautologicalInclusion_restriction (stage : Nat) :
    tautologicalInclusion.1.comp
        (CochainComplex.HomComplex.Cochain.ofHom
          (cofiberRestriction stage)) (add_zero 1) =
      (CochainComplex.HomComplex.Cochain.ofHom
        (globalToLocalMap stage)).comp
          (localTautologicalInclusion stage).1 (zero_add 1) := by
  exact mappingCoconeMap_inr_between actionMap (localActionMap stage)
    (globalToLocalMap stage) (globalToLocalMap stage)
      (globalToLocal_action_square stage)

/-! ## Full local whole-relation restrictions -/

abbrev LocalScalarRelationObject (stage : Nat) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LocalScalarRelation stage)

noncomputable abbrev localScalarRelationSingle (stage : Nat) :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    (LocalScalarRelationObject stage)

noncomputable def localScalarDifferentialMap (stage : Nat) :
    localScalarVertexSingle stage ⟶ localScalarRelationSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localExtendedDifferential stage))

def localRelationExtendedEuler (stage : Nat) :
    LocalScalarRelation stage →ₗ[ℤ] LocalScalarRelation stage :=
  TensorProduct.map (localParameterMultiplication stage)
    (relationEulerAction seedOccurrence.root stage)

def localExtendedReversalOne (stage : Nat) :
    LocalScalarRelation stage →ₗ[ℤ] LocalScalarRelation stage :=
  TensorProduct.map LinearMap.id
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
      seedOccurrence.root stage)

theorem localScalarSuccessor_euler_square (stage : Nat) :
    (localScalarVertexSuccessor stage).comp
        (localExtendedEuler (stage + 1)) =
      (localExtendedEuler stage).comp
        (localScalarVertexSuccessor stage) := by
  unfold localScalarVertexSuccessor localExtendedEuler
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp,
    localCoefficientSuccessor_parameter_square]
  apply congrArg₂ TensorProduct.map
  · rfl
  · exact
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction_euler_square
        seedOccurrence.root stage

theorem localScalarRelationSuccessor_euler_square (stage : Nat) :
    (localScalarRelationSuccessor stage).comp
        (localRelationExtendedEuler (stage + 1)) =
      (localRelationExtendedEuler stage).comp
        (localScalarRelationSuccessor stage) := by
  unfold localScalarRelationSuccessor localRelationExtendedEuler
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp,
    localCoefficientSuccessor_parameter_square]
  apply congrArg₂ TensorProduct.map
  · rfl
  · exact
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction_euler_square
        seedOccurrence.root stage

theorem localScalarSuccessor_operator_square (stage : Nat) :
    (localScalarVertexSuccessor stage).comp
        (localEulerOperator (stage + 1)) =
      (localEulerOperator stage).comp
        (localScalarVertexSuccessor stage) := by
  unfold localEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    localScalarSuccessor_euler_square]

theorem localScalarSuccessor_reversal_square (stage : Nat) :
    (localScalarVertexSuccessor stage).comp
        (localExtendedReversalZero (stage + 1)) =
      (localExtendedReversalZero stage).comp
        (localScalarVertexSuccessor stage) := by
  unfold localScalarVertexSuccessor localExtendedReversalZero
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction_reversal_square
        seedOccurrence.root stage

theorem localScalarRelationSuccessor_reversal_square (stage : Nat) :
    (localScalarRelationSuccessor stage).comp
        (localExtendedReversalOne (stage + 1)) =
      (localExtendedReversalOne stage).comp
        (localScalarRelationSuccessor stage) := by
  unfold localScalarRelationSuccessor localExtendedReversalOne
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact
      CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationRestriction_reversal_square
        seedOccurrence.root stage

def localRelationEulerOperator (stage : Nat) :
    LocalScalarRelation stage →ₗ[ℤ] LocalScalarRelation stage :=
  LinearMap.id - localRelationExtendedEuler stage

theorem localScalarRelationSuccessor_operator_square (stage : Nat) :
    (localScalarRelationSuccessor stage).comp
        (localRelationEulerOperator (stage + 1)) =
      (localRelationEulerOperator stage).comp
        (localScalarRelationSuccessor stage) := by
  unfold localRelationEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    localScalarRelationSuccessor_euler_square]

theorem localExtendedDifferential_euler_square (stage : Nat) :
    (localExtendedDifferential stage).comp (localExtendedEuler stage) =
      (localRelationExtendedEuler stage).comp
        (localExtendedDifferential stage) := by
  rw [localExtendedDifferential, localExtendedEuler,
    localRelationExtendedEuler,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro value
    rfl
  · exact factorizationDifferential_euler_square
      seedOccurrence.root stage

theorem localExtendedDifferential_reversal_square (stage : Nat) :
    (localExtendedDifferential stage).comp
        (localExtendedReversalZero stage) =
      (localExtendedReversalOne stage).comp
        (localExtendedDifferential stage) := by
  rw [localExtendedDifferential, localExtendedReversalZero,
    localExtendedReversalOne,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact factorizationDifferential_reversal_square
      seedOccurrence.root stage

theorem localRelationExtendedEuler_reversal_commutes (stage : Nat) :
    (localExtendedReversalOne stage).comp
        (localRelationExtendedEuler stage) =
      (localRelationExtendedEuler stage).comp
        (localExtendedReversalOne stage) := by
  rw [localExtendedReversalOne, localRelationExtendedEuler,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact (relationEuler_reversal_commutes seedOccurrence.root stage).symm

theorem localAction_differential_linear_square (stage : Nat) :
    (localExtendedDifferential stage).comp (localEulerOperator stage) =
      (localRelationEulerOperator stage).comp
        (localExtendedDifferential stage) := by
  unfold localEulerOperator localRelationEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    localExtendedDifferential_euler_square]

theorem localRelationEulerOperator_reversal_commutes (stage : Nat) :
    (localRelationEulerOperator stage).comp
        (localExtendedReversalOne stage) =
      (localExtendedReversalOne stage).comp
        (localRelationEulerOperator stage) := by
  unfold localRelationEulerOperator
  rw [LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id]
  apply congrArg (fun current => localExtendedReversalOne stage - current)
  exact (localRelationExtendedEuler_reversal_commutes stage).symm

noncomputable def localRelationActionMap (stage : Nat) :
    localScalarRelationSingle stage ⟶ localScalarRelationSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localRelationEulerOperator stage))

noncomputable def localRelationReversalMap (stage : Nat) :
    localScalarRelationSingle stage ⟶ localScalarRelationSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localExtendedReversalOne stage))

theorem localAction_differential_square (stage : Nat) :
    localActionMap stage ≫ localScalarDifferentialMap stage =
      localScalarDifferentialMap stage ≫ localRelationActionMap stage := by
  unfold localActionMap localScalarDifferentialMap localRelationActionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localAction_differential_linear_square stage) value

theorem localReversal_differential_square (stage : Nat) :
    localVertexReversalMap stage ≫ localScalarDifferentialMap stage =
      localScalarDifferentialMap stage ≫
        localRelationReversalMap stage := by
  unfold localVertexReversalMap localScalarDifferentialMap
    localRelationReversalMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localExtendedDifferential_reversal_square stage) value

theorem localVertexReversal_action_square (stage : Nat) :
    localVertexReversalMap stage ≫ localActionMap stage =
      localActionMap stage ≫ localVertexReversalMap stage := by
  unfold localVertexReversalMap localActionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localEulerOperator_reversal_commutes stage) value

theorem localRelationReversal_action_square (stage : Nat) :
    localRelationReversalMap stage ≫ localRelationActionMap stage =
      localRelationActionMap stage ≫ localRelationReversalMap stage := by
  unfold localRelationReversalMap localRelationActionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localRelationEulerOperator_reversal_commutes stage) value

noncomputable abbrev LocalScalarWholeRelationComplex (stage : Nat) :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  CochainComplex.mappingCocone (localScalarDifferentialMap stage)

noncomputable def localWholeActionMap (stage : Nat) :
    LocalScalarWholeRelationComplex stage ⟶
      LocalScalarWholeRelationComplex stage :=
  mappingCoconeMap (localScalarDifferentialMap stage)
    (localScalarDifferentialMap stage)
      (localActionMap stage) (localRelationActionMap stage)
        (localAction_differential_square stage)

noncomputable def localWholeReversalMap (stage : Nat) :
    LocalScalarWholeRelationComplex stage ⟶
      LocalScalarWholeRelationComplex stage :=
  mappingCoconeMap (localScalarDifferentialMap stage)
    (localScalarDifferentialMap stage)
      (localVertexReversalMap stage) (localRelationReversalMap stage)
        (localReversal_differential_square stage)

theorem localWholeReversal_action_square (stage : Nat) :
    localWholeReversalMap stage ≫ localWholeActionMap stage =
      localWholeActionMap stage ≫ localWholeReversalMap stage := by
  unfold localWholeReversalMap localWholeActionMap
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact localVertexReversal_action_square stage
  · exact localRelationReversal_action_square stage

/-! ### One actual source successor on the local family -/

noncomputable def localVertexSuccessorMap (stage : Nat) :
    localScalarVertexSingle (stage + 1) ⟶ localScalarVertexSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localScalarVertexSuccessor stage))

noncomputable def localRelationSuccessorMap (stage : Nat) :
    localScalarRelationSingle (stage + 1) ⟶
      localScalarRelationSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localScalarRelationSuccessor stage))

theorem localSuccessor_differential_square (stage : Nat) :
    localVertexSuccessorMap stage ≫ localScalarDifferentialMap stage =
      localScalarDifferentialMap (stage + 1) ≫
        localRelationSuccessorMap stage := by
  unfold localVertexSuccessorMap localScalarDifferentialMap
    localRelationSuccessorMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localScalarSuccessor_differential_square stage) value

theorem localSuccessor_action_square_zero (stage : Nat) :
    localActionMap (stage + 1) ≫ localVertexSuccessorMap stage =
      localVertexSuccessorMap stage ≫ localActionMap stage := by
  unfold localActionMap localVertexSuccessorMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localScalarSuccessor_operator_square stage) value

theorem localSuccessor_action_square_one (stage : Nat) :
    localRelationActionMap (stage + 1) ≫
        localRelationSuccessorMap stage =
      localRelationSuccessorMap stage ≫
        localRelationActionMap stage := by
  unfold localRelationActionMap localRelationSuccessorMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localScalarRelationSuccessor_operator_square stage) value

theorem localSuccessor_reversal_square_zero (stage : Nat) :
    localVertexReversalMap (stage + 1) ≫ localVertexSuccessorMap stage =
      localVertexSuccessorMap stage ≫ localVertexReversalMap stage := by
  unfold localVertexReversalMap localVertexSuccessorMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localScalarSuccessor_reversal_square stage) value

theorem localSuccessor_reversal_square_one (stage : Nat) :
    localRelationReversalMap (stage + 1) ≫
        localRelationSuccessorMap stage =
      localRelationSuccessorMap stage ≫
        localRelationReversalMap stage := by
  unfold localRelationReversalMap localRelationSuccessorMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localScalarRelationSuccessor_reversal_square stage) value

noncomputable def localWholeRelationSuccessorMap (stage : Nat) :
    LocalScalarWholeRelationComplex (stage + 1) ⟶
      LocalScalarWholeRelationComplex stage :=
  mappingCoconeMap (localScalarDifferentialMap (stage + 1))
    (localScalarDifferentialMap stage)
      (localVertexSuccessorMap stage) (localRelationSuccessorMap stage)
        (localSuccessor_differential_square stage)

theorem localWholeSuccessor_action_square (stage : Nat) :
    localWholeActionMap (stage + 1) ≫
        localWholeRelationSuccessorMap stage =
      localWholeRelationSuccessorMap stage ≫
        localWholeActionMap stage := by
  unfold localWholeActionMap localWholeRelationSuccessorMap
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact localSuccessor_action_square_zero stage
  · exact localSuccessor_action_square_one stage

theorem localWholeSuccessor_reversal_square (stage : Nat) :
    localWholeReversalMap (stage + 1) ≫
        localWholeRelationSuccessorMap stage =
      localWholeRelationSuccessorMap stage ≫
        localWholeReversalMap stage := by
  unfold localWholeReversalMap localWholeRelationSuccessorMap
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact localSuccessor_reversal_square_zero stage
  · exact localSuccessor_reversal_square_one stage

noncomputable def globalToLocalRelationMap (stage : Nat) :
    scalarRelationSingle ⟶ localScalarRelationSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localRelationTensorRestriction stage))

theorem globalToLocal_differential_square (stage : Nat) :
    globalToLocalMap stage ≫ localScalarDifferentialMap stage =
      scalarDifferentialMap ≫ globalToLocalRelationMap stage := by
  unfold globalToLocalMap localScalarDifferentialMap scalarDifferentialMap
    globalToLocalRelationMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localTensorRestriction_differential_square stage) value

noncomputable def globalToLocalWholeRelationMap (stage : Nat) :
    ScalarWholeRelationComplex ⟶ LocalScalarWholeRelationComplex stage :=
  mappingCoconeMap scalarDifferentialMap
    (localScalarDifferentialMap stage)
      (globalToLocalMap stage) (globalToLocalRelationMap stage)
        (globalToLocal_differential_square stage)

theorem relationRestriction_euler_square (stage : Nat) :
    (relationRestriction stage).comp globalEulerOne =
      (relationEulerAction seedOccurrence.root stage).comp
        (relationRestriction stage) := by
  have square := globalEulerAction_restriction (Opposite.op stage)
  exact congrArg (fun arrow => (arrow.f 1).hom) square

theorem relationRestriction_reversal_square (stage : Nat) :
    (relationRestriction stage).comp globalReversalOne =
      (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.relationReversal
        seedOccurrence.root stage).comp (relationRestriction stage) := by
  have square := globalReversal_restriction (Opposite.op stage)
  exact congrArg (fun arrow => (arrow.f 1).hom) square

theorem localRelationTensorRestriction_euler_square (stage : Nat) :
    (localRelationTensorRestriction stage).comp extendedEulerOne =
      (localRelationExtendedEuler stage).comp
        (localRelationTensorRestriction stage) := by
  rw [localRelationTensorRestriction, extendedEulerOne,
    localRelationExtendedEuler,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    coefficientRestriction_parameter_square,
    relationRestriction_euler_square]

theorem localRelationTensorRestriction_operator_square (stage : Nat) :
    (localRelationTensorRestriction stage).comp relationEulerOperator =
      (localRelationEulerOperator stage).comp
        (localRelationTensorRestriction stage) := by
  unfold relationEulerOperator localRelationEulerOperator
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    localRelationTensorRestriction_euler_square]

theorem localRelationTensorRestriction_reversal_square (stage : Nat) :
    (localRelationTensorRestriction stage).comp extendedReversalOne =
      (localExtendedReversalOne stage).comp
        (localRelationTensorRestriction stage) := by
  rw [localRelationTensorRestriction, extendedReversalOne,
    localExtendedReversalOne,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact relationRestriction_reversal_square stage

theorem globalToLocal_relation_action_square (stage : Nat) :
    globalToLocalRelationMap stage ≫ localRelationActionMap stage =
      relationActionMap ≫ globalToLocalRelationMap stage := by
  unfold globalToLocalRelationMap localRelationActionMap relationActionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localRelationTensorRestriction_operator_square stage).symm value

theorem globalToLocal_relation_reversal_square (stage : Nat) :
    globalToLocalRelationMap stage ≫ localRelationReversalMap stage =
      scalarRelationReversalMap ≫ globalToLocalRelationMap stage := by
  unfold globalToLocalRelationMap localRelationReversalMap
    scalarRelationReversalMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localRelationTensorRestriction_reversal_square stage).symm value

theorem globalToLocal_wholeAction_square (stage : Nat) :
    globalToLocalWholeRelationMap stage ≫ localWholeActionMap stage =
      wholeActionMap ≫ globalToLocalWholeRelationMap stage := by
  unfold globalToLocalWholeRelationMap localWholeActionMap wholeActionMap
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact globalToLocal_action_square stage
  · exact globalToLocal_relation_action_square stage

theorem globalToLocal_wholeReversal_square (stage : Nat) :
    globalToLocalWholeRelationMap stage ≫ localWholeReversalMap stage =
      wholeReversalMap ≫ globalToLocalWholeRelationMap stage := by
  unfold globalToLocalWholeRelationMap localWholeReversalMap wholeReversalMap
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr
  · exact globalToLocal_vertex_reversal_square stage
  · exact globalToLocal_relation_reversal_square stage

noncomputable abbrev LocalWholeActionCofiber (stage : Nat) :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  CochainComplex.mappingCocone (localWholeActionMap stage)

noncomputable def localWholeCofiberReversal (stage : Nat) :
    LocalWholeActionCofiber stage ⟶ LocalWholeActionCofiber stage :=
  mappingCoconeMap (localWholeActionMap stage)
    (localWholeActionMap stage)
      (localWholeReversalMap stage) (localWholeReversalMap stage)
        (localWholeReversal_action_square stage)

noncomputable def localWholeCofiberSuccessorMap (stage : Nat) :
    LocalWholeActionCofiber (stage + 1) ⟶ LocalWholeActionCofiber stage :=
  mappingCoconeMap (localWholeActionMap (stage + 1))
    (localWholeActionMap stage)
      (localWholeRelationSuccessorMap stage)
      (localWholeRelationSuccessorMap stage)
        (localWholeSuccessor_action_square stage).symm

theorem localWholeCofiberSuccessor_reversal_square (stage : Nat) :
    localWholeCofiberReversal (stage + 1) ≫
        localWholeCofiberSuccessorMap stage =
      localWholeCofiberSuccessorMap stage ≫
        localWholeCofiberReversal stage := by
  unfold localWholeCofiberReversal localWholeCofiberSuccessorMap
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr <;>
    exact localWholeSuccessor_reversal_square stage

noncomputable def wholeCofiberRestriction (stage : Nat) :
    WholeActionCofiber ⟶ LocalWholeActionCofiber stage :=
  mappingCoconeMap wholeActionMap (localWholeActionMap stage)
    (globalToLocalWholeRelationMap stage)
    (globalToLocalWholeRelationMap stage)
      (globalToLocal_wholeAction_square stage)

theorem wholeCofiberRestriction_reversal_square (stage : Nat) :
    wholeCofiberReversal ≫ wholeCofiberRestriction stage =
      wholeCofiberRestriction stage ≫ localWholeCofiberReversal stage := by
  unfold wholeCofiberReversal wholeCofiberRestriction
    localWholeCofiberReversal
  rw [← mappingCoconeMap_comp, ← mappingCoconeMap_comp]
  apply mappingCoconeMap_congr <;>
    exact (globalToLocal_wholeReversal_square stage).symm

noncomputable def localWholeTautologicalInclusion (stage : Nat) :
    CochainComplex.HomComplex.Cocycle
      (LocalScalarWholeRelationComplex stage)
      (LocalWholeActionCofiber stage) 1 :=
  CochainComplex.mappingCocone.inr (localWholeActionMap stage)

theorem localWholeTautologicalInclusion_reversal (stage : Nat) :
    (localWholeTautologicalInclusion stage).1.comp
        (CochainComplex.HomComplex.Cochain.ofHom
          (localWholeCofiberReversal stage)) (add_zero 1) =
      (CochainComplex.HomComplex.Cochain.ofHom
        (localWholeReversalMap stage)).comp
          (localWholeTautologicalInclusion stage).1 (zero_add 1) := by
  exact mappingCoconeMap_inr (localWholeActionMap stage)
    (localWholeReversalMap stage) (localWholeReversalMap stage)
      (localWholeReversal_action_square stage)

theorem localWholeTautologicalInclusion_successor (stage : Nat) :
    (localWholeTautologicalInclusion (stage + 1)).1.comp
        (CochainComplex.HomComplex.Cochain.ofHom
          (localWholeCofiberSuccessorMap stage)) (add_zero 1) =
      (CochainComplex.HomComplex.Cochain.ofHom
        (localWholeRelationSuccessorMap stage)).comp
          (localWholeTautologicalInclusion stage).1 (zero_add 1) := by
  exact mappingCoconeMap_inr_between
    (localWholeActionMap (stage + 1)) (localWholeActionMap stage)
      (localWholeRelationSuccessorMap stage)
      (localWholeRelationSuccessorMap stage)
        (localWholeSuccessor_action_square stage).symm

theorem wholeTautologicalInclusion_restriction (stage : Nat) :
    wholeTautologicalInclusion.1.comp
        (CochainComplex.HomComplex.Cochain.ofHom
          (wholeCofiberRestriction stage)) (add_zero 1) =
      (CochainComplex.HomComplex.Cochain.ofHom
        (globalToLocalWholeRelationMap stage)).comp
          (localWholeTautologicalInclusion stage).1 (zero_add 1) := by
  exact mappingCoconeMap_inr_between wholeActionMap
    (localWholeActionMap stage)
      (globalToLocalWholeRelationMap stage)
      (globalToLocalWholeRelationMap stage)
      (globalToLocal_wholeAction_square stage)

/-! ## Point-free actual factorization rows on the tautological family -/

abbrev LocalScalarInnerObject (stage : Nat) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LocalScalarInner stage)

noncomputable abbrev localScalarInnerSingle (stage : Nat) :
    DerivedAdicCofiber.IntegralCochainComplex ℤ :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    (LocalScalarInnerObject stage)

def localScalarInnerSuccessor (stage : Nat) :
    LocalScalarInner (stage + 1) →ₗ[ℤ] LocalScalarInner stage :=
  TensorProduct.map (localCoefficientSuccessor stage)
    (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
      seedOccurrence.root stage)

noncomputable def localScalarInnerSuccessorMap (stage : Nat) :
    localScalarInnerSingle (stage + 1) ⟶ localScalarInnerSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localScalarInnerSuccessor stage))

theorem wholeAntiInvariantProjection_successor_square (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
        seedOccurrence.root stage).comp
        (wholeAntiInvariantProjection (stage + 1)) =
      (wholeAntiInvariantProjection stage).comp
        (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction
          seedOccurrence.root stage) := by
  apply LinearMap.ext
  intro value
  exact (innerAntiInvariant_restriction seedOccurrence.root stage
    (value none)).symm

theorem localWholeAntiInvariantComponent_successor_square (stage : Nat) :
    (localScalarInnerSuccessor stage).comp
        (localWholeAntiInvariantComponent (stage + 1)) =
      (localWholeAntiInvariantComponent stage).comp
        (localScalarVertexSuccessor stage) := by
  unfold localScalarInnerSuccessor localWholeAntiInvariantComponent
    localScalarVertexSuccessor
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro coefficient
    rfl
  · exact wholeAntiInvariantProjection_successor_square stage

noncomputable def localWholeAntiInvariantSingleMap (stage : Nat) :
    localScalarVertexSingle stage ⟶ localScalarInnerSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localWholeAntiInvariantComponent stage))

theorem localWholeAntiInvariantSingleMap_successor_square (stage : Nat) :
    localVertexSuccessorMap stage ≫
        localWholeAntiInvariantSingleMap stage =
      localWholeAntiInvariantSingleMap (stage + 1) ≫
        localScalarInnerSuccessorMap stage := by
  unfold localVertexSuccessorMap localWholeAntiInvariantSingleMap
    localScalarInnerSuccessorMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact LinearMap.congr_fun
    (localWholeAntiInvariantComponent_successor_square stage).symm value

noncomputable def localQuotientAntiInvariantSingleMap (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    localScalarVertexSingle stage ⟶ localScalarInnerSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localQuotientAntiInvariantComponent stage row))

noncomputable def localRelationRowSingleMap (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    localScalarRelationSingle stage ⟶ localScalarInnerSingle stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (localRelationRow stage row))

def localRowPrimePower {stage : Nat}
    (row : FactorRow seedOccurrence.root stage) : ℤ :=
  ((rowPrime row : Nat) : ℤ) ^ rowExponent row

theorem localRelationRow_differential_linear
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    (localRelationRow stage row).comp (localExtendedDifferential stage) =
      localWholeAntiInvariantComponent stage -
        localRowPrimePower row •
          localQuotientAntiInvariantComponent stage row := by
  apply LinearMap.ext
  intro value
  exact localRelationRow_differential stage row value

theorem localRelationRow_single_factorization
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    localScalarDifferentialMap stage ≫
        localRelationRowSingleMap stage row =
      localWholeAntiInvariantSingleMap stage -
        localRowPrimePower row •
          localQuotientAntiInvariantSingleMap stage row := by
  unfold localScalarDifferentialMap localRelationRowSingleMap
    localWholeAntiInvariantSingleMap localQuotientAntiInvariantSingleMap
  rw [← Functor.map_comp]
  let single := CochainComplex.singleFunctor (ModuleCat ℤ) 0
  have underlying :
      ModuleCat.ofHom (localExtendedDifferential stage) ≫
          ModuleCat.ofHom (localRelationRow stage row) =
        ModuleCat.ofHom
          (localWholeAntiInvariantComponent stage -
            localRowPrimePower row •
              localQuotientAntiInvariantComponent stage row) := by
    apply ModuleCat.hom_ext
    exact localRelationRow_differential_linear stage row
  change single.map
      (ModuleCat.ofHom (localExtendedDifferential stage) ≫
        ModuleCat.ofHom (localRelationRow stage row)) = _
  rw [underlying]
  change single.map
      (ModuleCat.ofHom (localWholeAntiInvariantComponent stage) -
        localRowPrimePower row •
          ModuleCat.ofHom
            (localQuotientAntiInvariantComponent stage row)) = _
  rw [Functor.map_sub, Functor.map_zsmul]

noncomputable def localWholeAntiInvariantCoordinateMap (stage : Nat) :
    LocalScalarWholeRelationComplex stage ⟶ localScalarInnerSingle stage :=
  CochainComplex.mappingCocone.fst (localScalarDifferentialMap stage) ≫
    localWholeAntiInvariantSingleMap stage

theorem localWholeAntiInvariantCoordinateMap_successor_square (stage : Nat) :
    localWholeRelationSuccessorMap stage ≫
        localWholeAntiInvariantCoordinateMap stage =
      localWholeAntiInvariantCoordinateMap (stage + 1) ≫
        localScalarInnerSuccessorMap stage := by
  unfold localWholeAntiInvariantCoordinateMap
  unfold localWholeRelationSuccessorMap
  rw [← Category.assoc,
    mappingCoconeMap_fst (localScalarDifferentialMap (stage + 1))
      (localScalarDifferentialMap stage)
      (localVertexSuccessorMap stage) (localRelationSuccessorMap stage)
      (localSuccessor_differential_square stage)]
  rw [Category.assoc,
    localWholeAntiInvariantSingleMap_successor_square stage,
    ← Category.assoc]

noncomputable def localQuotientAntiInvariantCoordinateMap (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalScalarWholeRelationComplex stage ⟶ localScalarInnerSingle stage :=
  CochainComplex.mappingCocone.fst (localScalarDifferentialMap stage) ≫
    localQuotientAntiInvariantSingleMap stage row

theorem localCoordinateDifference_factorizes_through_actual_row
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    localWholeAntiInvariantCoordinateMap stage -
        localRowPrimePower row •
          localQuotientAntiInvariantCoordinateMap stage row =
      (CochainComplex.mappingCocone.fst
          (localScalarDifferentialMap stage) ≫
        localScalarDifferentialMap stage) ≫
          localRelationRowSingleMap stage row := by
  unfold localWholeAntiInvariantCoordinateMap
    localQuotientAntiInvariantCoordinateMap
  rw [Category.assoc, localRelationRow_single_factorization stage row]
  simp only [Preadditive.comp_sub, Preadditive.comp_zsmul]

/-- The actual factorization row supplies the homotopy; the mapping-cocone
universal property supplies its vanishing.  No point or division root occurs. -/
noncomputable def localFactorizationRowHomotopy
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    Homotopy
      (localWholeAntiInvariantCoordinateMap stage -
        localRowPrimePower row •
          localQuotientAntiInvariantCoordinateMap stage row)
      0 := by
  refine (Homotopy.ofEq
    (localCoordinateDifference_factorizes_through_actual_row stage row)).trans ?_
  simpa only [Category.assoc, Limits.zero_comp] using
    ((projectionNullHomotopy
      (localScalarDifferentialMap stage)).compRight
        (localRelationRowSingleMap stage row))

abbrev LocalCoordinateClass (stage : Nat) :=
  CochainComplex.HomComplex.CohomologyClass
    (LocalScalarWholeRelationComplex stage)
    (localScalarInnerSingle stage) 0

noncomputable def localWholeAntiInvariantClass (stage : Nat) :
    LocalCoordinateClass stage :=
  CochainComplex.HomComplex.CohomologyClass.mk
    (CochainComplex.HomComplex.Cocycle.ofHom
      (localWholeAntiInvariantCoordinateMap stage))

noncomputable def localQuotientAntiInvariantClass (stage : Nat)
    (row : FactorRow seedOccurrence.root stage) :
    LocalCoordinateClass stage :=
  CochainComplex.HomComplex.CohomologyClass.mk
    (CochainComplex.HomComplex.Cocycle.ofHom
      (localQuotientAntiInvariantCoordinateMap stage row))

/-- Actual factorization produces divisibility of the tautological
anti-invariant homotopy class before any quotient evaluator is invoked. -/
theorem localWholeAntiInvariantClass_landing
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    localWholeAntiInvariantClass stage =
      localRowPrimePower row •
        localQuotientAntiInvariantClass stage row := by
  apply sub_eq_zero.mp
  unfold localWholeAntiInvariantClass localQuotientAntiInvariantClass
  change
    CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.ofHom
            (localWholeAntiInvariantCoordinateMap stage)) -
        CochainComplex.HomComplex.CohomologyClass.mk
          (localRowPrimePower row •
            CochainComplex.HomComplex.Cocycle.ofHom
              (localQuotientAntiInvariantCoordinateMap stage row)) = 0
  rw [← CochainComplex.HomComplex.CohomologyClass.mk_sub]
  let difference :=
    localWholeAntiInvariantCoordinateMap stage -
      localRowPrimePower row •
        localQuotientAntiInvariantCoordinateMap stage row
  have cocycleDifference :
      CochainComplex.HomComplex.Cocycle.ofHom
            (localWholeAntiInvariantCoordinateMap stage) -
          localRowPrimePower row •
            CochainComplex.HomComplex.Cocycle.ofHom
              (localQuotientAntiInvariantCoordinateMap stage row) =
        CochainComplex.HomComplex.Cocycle.ofHom difference := by
    apply CochainComplex.HomComplex.Cocycle.ext
    ext sourceDegree : 1
    rfl
  rw [cocycleDifference]
  apply (CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff _).2
  refine ⟨-1, by omega,
    CochainComplex.HomComplex.Cochain.ofHomotopy
      (localFactorizationRowHomotopy stage row), ?_⟩
  change CochainComplex.HomComplex.δ (-1) 0
      (CochainComplex.HomComplex.Cochain.ofHomotopy
        (localFactorizationRowHomotopy stage row)) =
    CochainComplex.HomComplex.Cochain.ofHom difference
  simp only [difference,
    CochainComplex.HomComplex.δ_ofHomotopy,
    CochainComplex.HomComplex.Cochain.ofHom_zero, sub_zero]

theorem localWholeAntiInvariantClass_landing_nat
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    localWholeAntiInvariantClass stage =
      (rowPrime row : Nat) ^ rowExponent row •
        localQuotientAntiInvariantClass stage row := by
  simpa only [localRowPrimePower, ← Nat.cast_pow, natCast_zsmul] using
    localWholeAntiInvariantClass_landing stage row

theorem localWholeAntiInvariantClass_quotientZero
    (stage : Nat) (row : FactorRow seedOccurrence.root stage) :
    PrimePowerQuotientEvaluation.evaluator
        (LocalCoordinateClass stage)
        (localWholeAntiInvariantClass stage)
        (rowPrime row) (rowExponent row) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff
    (localWholeAntiInvariantClass stage)).2
  exact ⟨localQuotientAntiInvariantClass stage row,
    (localWholeAntiInvariantClass_landing_nat stage row).symm⟩

/-- Reading the local tautological inclusion through the canonical shifted
target projection returns the entire local whole-relation family. -/
theorem localWholeTautologicalInclusion_readback (stage : Nat) :
    (localWholeTautologicalInclusion stage).1.comp
        (CochainComplex.mappingCocone.snd
          (localWholeActionMap stage)) (add_neg_cancel (1 : ℤ)) =
      CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 (LocalScalarWholeRelationComplex stage)) := by
  ext sourceDegree : 1
  simp [localWholeTautologicalInclusion,
    CochainComplex.HomComplex.Cochain.comp_v]

@[reassoc] theorem wholeTautologicalInclusion_restriction_v (stage : Nat) :
    wholeTautologicalInclusion.1.v 0 1 (by omega) ≫
        (wholeCofiberRestriction stage).f 1 =
      (globalToLocalWholeRelationMap stage).f 0 ≫
        (localWholeTautologicalInclusion stage).1.v 0 1 (by omega) := by
  have equality := wholeTautologicalInclusion_restriction stage
  exact CochainComplex.HomComplex.Cochain.congr_v equality 0 1 (by omega)

@[reassoc] theorem localWholeTautologicalInclusion_readback_v (stage : Nat) :
    (localWholeTautologicalInclusion stage).1.v 0 1 (by omega) ≫
        (CochainComplex.mappingCocone.snd
          (localWholeActionMap stage)).v 1 0 (by omega) =
      𝟙 _ := by
  have equality := localWholeTautologicalInclusion_readback stage
  exact CochainComplex.HomComplex.Cochain.congr_v equality 0 0 (by omega)

@[reassoc] theorem globalToLocalWholeRelationMap_fst_zero (stage : Nat) :
    (globalToLocalWholeRelationMap stage).f 0 ≫
        (CochainComplex.mappingCocone.fst
          (localScalarDifferentialMap stage)).f 0 =
      (CochainComplex.mappingCocone.fst scalarDifferentialMap).f 0 ≫
        (globalToLocalMap stage).f 0 := by
  exact congrArg (fun arrow => arrow.f 0)
    (mappingCoconeMap_fst scalarDifferentialMap
      (localScalarDifferentialMap stage)
      (globalToLocalMap stage) (globalToLocalRelationMap stage)
      (globalToLocal_differential_square stage))

theorem preserves_family_tautological_restrictions :
    actionCofiberFace.root = seedOccurrence ∧
      actionCofiberFace.actualTransition = actionMap ∧
      (∀ stage, cofiberRestriction stage ≫
          CochainComplex.mappingCocone.fst (localActionMap stage) =
        CochainComplex.mappingCocone.fst actionMap ≫
          globalToLocalMap stage) ∧
      (∀ stage, tautologicalInclusion.1.comp
          (CochainComplex.HomComplex.Cochain.ofHom
            (cofiberRestriction stage)) (add_zero 1) =
        (CochainComplex.HomComplex.Cochain.ofHom
          (globalToLocalMap stage)).comp
            (localTautologicalInclusion stage).1 (zero_add 1)) := by
  exact ⟨actionCofiberFace_preserves_exact_occurrence_and_action.1,
    actionCofiberFace_preserves_exact_occurrence_and_action.2.2.2,
    cofiberRestriction_fst, tautologicalInclusion_restriction⟩

end
end CanonicalUnitArithmeticIntegralActionCofiberFamily
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
