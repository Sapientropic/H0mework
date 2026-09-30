import H0mework.Versions.Y.Arithmetic.EulerAnalytic.CoordinateSpecialization
import H0mework.Versions.Y.Arithmetic.EulerGlobal.HistoryRelationEmbedding
import H0mework.Versions.Y.Arithmetic.UnitArithmetic.CoordinateProjectionObstruction

/-!
# Actual endpoint section of the generated determinant coordinate family

The installed coordinate zero fibre supplies its universal coordinate `u`.
The actual whole-relation diagram independently supplies two persistent
degree-zero endpoint basis vectors.  They occupy the actual `none` role,
are preserved by runtime successor restriction, and are exchanged by the
source-generated global reversal.

Their universal coordinate combination specializes at a point `s` to
`s ⊗ e₀ + (1-conj s) ⊗ e₁`.  Both endpoint equations are generated
readbacks.  No zero, fixedness, endpoint law, division root, or functional
equation is accepted from a caller.

The actual differential is retained rather than required to vanish: it is
calculated as `(u-ιu) ⊗ boundary`.  This is the source-owned two-term datum
for the downstream mapping-cocone atom.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationFullEulerSolutionAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationGlobalAction
open CanonicalUnitArithmeticFactorizationFullEulerWholeRelationUniversalSolution
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateSpecialization
open CanonicalUnitArithmeticFactorizationWholeHistoryIntegralRelationEmbedding
open CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
open CategoryTheory
open CategoryTheory.Limits
open DerivedAdicCofiber
open scoped TensorProduct

noncomputable section

/-! ## Coordinate-family scalar extension -/

abbrev CoordinateCoefficientRing := CoordinateZeroFiberRing

abbrev CoordinateScalarVertex :=
  TensorProduct ℤ CoordinateCoefficientRing GlobalVertex

abbrev CoordinateScalarRelation :=
  TensorProduct ℤ CoordinateCoefficientRing GlobalRelation

def coordinateExtendedDifferential :
    CoordinateScalarVertex →ₗ[ℤ] CoordinateScalarRelation :=
  TensorProduct.map LinearMap.id globalDifferential

def coordinateExtendedReversalZero :
    CoordinateScalarVertex →ₗ[ℤ] CoordinateScalarVertex :=
  TensorProduct.map LinearMap.id globalReversalZero

def pointCoefficientMap (point : Point) :
    CoordinateCoefficientRing →ₗ[ℤ] ℂ :=
  point.specialization.toAddMonoidHom.toIntLinearMap

abbrev ComplexScalarVertex := TensorProduct ℤ ℂ GlobalVertex

def pointVertexSpecialization (point : Point) :
    CoordinateScalarVertex →ₗ[ℤ] ComplexScalarVertex :=
  TensorProduct.map (pointCoefficientMap point) LinearMap.id

/-! ## Runtime-generated endpoint basis -/

def localEndpointVertexMap (stage : Nat) :
    DualBase →ₗ[ℤ] WholeVertexModule seedOccurrence.root stage where
  toFun base role :=
    match role with
    | none => localInnerEmbedding seedOccurrence.root stage base
    | some _row => 0
  map_add' left right := by
    funext role
    cases role with
    | none => exact (localInnerEmbedding seedOccurrence.root stage).map_add left right
    | some row => simp
  map_smul' scalar value := by
    funext role
    cases role with
    | none => exact (localInnerEmbedding seedOccurrence.root stage).map_smul scalar value
    | some row => simp

theorem localEndpointVertexMap_successor (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction
      seedOccurrence.root stage).comp
        (localEndpointVertexMap (stage + 1)) =
      localEndpointVertexMap stage := by
  apply LinearMap.ext
  intro base
  funext role
  cases role with
  | none =>
      change
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierRestriction
            seedOccurrence.root stage
            (localInnerEmbedding seedOccurrence.root (stage + 1) base) =
          localInnerEmbedding seedOccurrence.root stage base
      exact carrierRestriction_localInnerEmbedding seedOccurrence.root stage base
  | some row =>
      simp [CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexRestriction,
        localEndpointVertexMap]

theorem localEndpointVertexMap_reversal (stage : Nat) :
    (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
        seedOccurrence.root stage).comp (localEndpointVertexMap stage) =
      (localEndpointVertexMap stage).comp dualBaseReversal := by
  apply LinearMap.ext
  intro base
  funext role
  cases role with
  | none =>
      change
        CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.carrierReversal
            seedOccurrence.root stage
            (localInnerEmbedding seedOccurrence.root stage base) =
          localInnerEmbedding seedOccurrence.root stage (dualBaseReversal base)
      exact localInnerEmbedding_reversal seedOccurrence.root stage base
  | some row =>
      simp [CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal,
        localEndpointVertexMap]

abbrev DualBaseObject : ModuleCat ℤ := ModuleCat.of ℤ DualBase

abbrev ArithmeticGlobalVertex :=
  ((limit (localRelationDiagram seedOccurrence.root)).X 0 : Type)

abbrev degreeZeroEvaluation : IntegralCochainComplex ℤ ⥤ ModuleCat ℤ :=
  HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℤ) 0

abbrev endpointDegreeZeroDiagram : ℕᵒᵖ ⥤ ModuleCat ℤ :=
  localRelationDiagram seedOccurrence.root ⋙ degreeZeroEvaluation

noncomputable def endpointDegreeZeroCone :
    Cone endpointDegreeZeroDiagram where
  pt := DualBaseObject
  π := NatTrans.ofOpSequence
    (fun stage => ModuleCat.ofHom (localEndpointVertexMap stage))
    (fun stage => by
      simp only [Functor.const_obj_map, endpointDegreeZeroDiagram,
        Functor.comp_map, HomologicalComplex.eval_map,
        localRelationDiagram, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact (localEndpointVertexMap_successor stage).symm)

noncomputable def endpointDegreeZeroLift :
    DualBaseObject ⟶ limit endpointDegreeZeroDiagram := by
  simpa only [endpointDegreeZeroCone] using
    (limit.lift endpointDegreeZeroDiagram endpointDegreeZeroCone)

noncomputable def degreeZeroLimitIso :
    (limit (localRelationDiagram seedOccurrence.root)).X 0 ≅
      limit endpointDegreeZeroDiagram :=
  preservesLimitIso degreeZeroEvaluation
    (localRelationDiagram seedOccurrence.root)

theorem degreeZeroLimitIso_inv_restriction (stage : Nat) :
    degreeZeroLimitIso.inv ≫
        (limit.π (localRelationDiagram seedOccurrence.root)
          (Opposite.op stage)).f 0 =
      limit.π endpointDegreeZeroDiagram (Opposite.op stage) := by
  exact preservesLimitIso_inv_π degreeZeroEvaluation
    (localRelationDiagram seedOccurrence.root) (Opposite.op stage)

theorem degreeZeroLimitIso_hom_projection (stage : ℕᵒᵖ) :
    degreeZeroLimitIso.hom ≫ limit.π endpointDegreeZeroDiagram stage =
      (limit.π (localRelationDiagram seedOccurrence.root) stage).f 0 := by
  exact preservesLimitIso_hom_π degreeZeroEvaluation
    (localRelationDiagram seedOccurrence.root) stage

noncomputable def globalEndpointVertexMapHom :
    DualBaseObject ⟶ (limit (localRelationDiagram seedOccurrence.root)).X 0 :=
  endpointDegreeZeroLift ≫ degreeZeroLimitIso.inv

def globalEndpointVertexMap : DualBase →ₗ[ℤ] ArithmeticGlobalVertex :=
  globalEndpointVertexMapHom.hom

theorem globalEndpointVertexMapHom_restriction (stage : Nat) :
    globalEndpointVertexMapHom ≫
        (limit.π (localRelationDiagram seedOccurrence.root)
          (Opposite.op stage)).f 0 =
      ModuleCat.ofHom (localEndpointVertexMap stage) := by
  rw [globalEndpointVertexMapHom, Category.assoc,
    degreeZeroLimitIso_inv_restriction]
  exact limit.lift_π endpointDegreeZeroCone (Opposite.op stage)

theorem globalEndpointVertexMap_restriction (stage : Nat) :
    ((limit.π (localRelationDiagram seedOccurrence.root)
      (Opposite.op stage)).f 0).hom.comp globalEndpointVertexMap =
      localEndpointVertexMap stage := by
  exact congrArg ModuleCat.Hom.hom
    (globalEndpointVertexMapHom_restriction stage)

def leftEndpointBase : DualBase
  | 0 => 1
  | 1 => 0

def rightEndpointBase : DualBase
  | 0 => 0
  | 1 => 1

@[simp] theorem dualBaseReversal_leftEndpointBase :
    dualBaseReversal leftEndpointBase = rightEndpointBase := by
  funext index
  fin_cases index <;> rfl

@[simp] theorem dualBaseReversal_rightEndpointBase :
    dualBaseReversal rightEndpointBase = leftEndpointBase := by
  funext index
  fin_cases index <;> rfl

def globalLeftEndpoint : ArithmeticGlobalVertex :=
  globalEndpointVertexMap leftEndpointBase

def globalRightEndpoint : ArithmeticGlobalVertex :=
  globalEndpointVertexMap rightEndpointBase

noncomputable def rawGlobalReversal :
    limit (localRelationDiagram seedOccurrence.root) ⟶
      limit (localRelationDiagram seedOccurrence.root) :=
  limMap (reversalNatTrans seedOccurrence.root)

def rawGlobalReversalZero : ArithmeticGlobalVertex →ₗ[ℤ]
    ArithmeticGlobalVertex :=
  (rawGlobalReversal.f 0).hom

theorem rawGlobalReversalZero_endpoint_map :
    rawGlobalReversalZero.comp globalEndpointVertexMap =
      globalEndpointVertexMap.comp dualBaseReversal := by
  have homEquality :
      globalEndpointVertexMapHom ≫ rawGlobalReversal.f 0 =
        ModuleCat.ofHom dualBaseReversal ≫ globalEndpointVertexMapHom := by
    apply (cancel_mono degreeZeroLimitIso.hom).1
    apply limit.hom_ext
    intro stage
    have reversalRestrictionZero :
        rawGlobalReversal.f 0 ≫
            (limit.π (localRelationDiagram seedOccurrence.root) stage).f 0 =
          (limit.π (localRelationDiagram seedOccurrence.root) stage).f 0 ≫
            ((reversalNatTrans seedOccurrence.root).app stage).f 0 := by
      exact congrArg (fun arrow => arrow.f 0)
        (limMap_π (reversalNatTrans seedOccurrence.root) stage)
    calc
      ((globalEndpointVertexMapHom ≫ rawGlobalReversal.f 0) ≫
          degreeZeroLimitIso.hom) ≫
            limit.π endpointDegreeZeroDiagram stage =
          globalEndpointVertexMapHom ≫
            (rawGlobalReversal.f 0 ≫
              (degreeZeroLimitIso.hom ≫
                limit.π endpointDegreeZeroDiagram stage)) := by
            simp only [Category.assoc]
      _ = globalEndpointVertexMapHom ≫
            (rawGlobalReversal.f 0 ≫
              (limit.π (localRelationDiagram seedOccurrence.root) stage).f 0) := by
            rw [degreeZeroLimitIso_hom_projection]
      _ = globalEndpointVertexMapHom ≫
            ((limit.π (localRelationDiagram seedOccurrence.root) stage).f 0 ≫
              ((reversalNatTrans seedOccurrence.root).app stage).f 0) := by
            rw [reversalRestrictionZero]
      _ = (globalEndpointVertexMapHom ≫
              (limit.π (localRelationDiagram seedOccurrence.root) stage).f 0) ≫
            ((reversalNatTrans seedOccurrence.root).app stage).f 0 := by
            simp only [Category.assoc]
      _ = ModuleCat.ofHom (localEndpointVertexMap stage.unop) ≫
            ((reversalNatTrans seedOccurrence.root).app stage).f 0 := by
            rw [globalEndpointVertexMapHom_restriction]
      _ = ModuleCat.ofHom dualBaseReversal ≫
            ModuleCat.ofHom (localEndpointVertexMap stage.unop) := by
            apply ModuleCat.hom_ext
            change
              (CanonicalUnitArithmeticFactorizationFullEulerWholeRelationComplexAction.vertexReversal
                  seedOccurrence.root stage.unop).comp
                    (localEndpointVertexMap stage.unop) =
                (localEndpointVertexMap stage.unop).comp dualBaseReversal
            exact localEndpointVertexMap_reversal stage.unop
      _ = ModuleCat.ofHom dualBaseReversal ≫
            (globalEndpointVertexMapHom ≫
              (limit.π (localRelationDiagram seedOccurrence.root) stage).f 0) := by
            rw [globalEndpointVertexMapHom_restriction]
      _ = ModuleCat.ofHom dualBaseReversal ≫
            (globalEndpointVertexMapHom ≫
              (degreeZeroLimitIso.hom ≫
                limit.π endpointDegreeZeroDiagram stage)) := by
            rw [degreeZeroLimitIso_hom_projection]
      _ = ((ModuleCat.ofHom dualBaseReversal ≫ globalEndpointVertexMapHom) ≫
              degreeZeroLimitIso.hom) ≫
            limit.π endpointDegreeZeroDiagram stage := by
            simp only [Category.assoc]
  change
    (rawGlobalReversal.f 0).hom.comp globalEndpointVertexMap =
      globalEndpointVertexMap.comp dualBaseReversal
  exact congrArg ModuleCat.Hom.hom homEquality

@[simp] theorem rawGlobalReversalZero_leftEndpoint :
    rawGlobalReversalZero globalLeftEndpoint = globalRightEndpoint := by
  change rawGlobalReversalZero (globalEndpointVertexMap leftEndpointBase) = _
  rw [← LinearMap.comp_apply, rawGlobalReversalZero_endpoint_map,
    LinearMap.comp_apply, dualBaseReversal_leftEndpointBase]
  rfl

@[simp] theorem rawGlobalReversalZero_rightEndpoint :
    rawGlobalReversalZero globalRightEndpoint = globalLeftEndpoint := by
  change rawGlobalReversalZero (globalEndpointVertexMap rightEndpointBase) = _
  rw [← LinearMap.comp_apply, rawGlobalReversalZero_endpoint_map,
    LinearMap.comp_apply, dualBaseReversal_rightEndpointBase]
  rfl

def actualGlobalLeftEndpoint : GlobalVertex := by
  change ArithmeticGlobalVertex
  exact globalLeftEndpoint

def actualGlobalRightEndpoint : GlobalVertex := by
  change ArithmeticGlobalVertex
  exact globalRightEndpoint

@[simp] theorem actualGlobalReversalZero_leftEndpoint :
    globalReversalZero actualGlobalLeftEndpoint = actualGlobalRightEndpoint := by
  change rawGlobalReversalZero globalLeftEndpoint = globalRightEndpoint
  exact rawGlobalReversalZero_leftEndpoint

@[simp] theorem actualGlobalReversalZero_rightEndpoint :
    globalReversalZero actualGlobalRightEndpoint = actualGlobalLeftEndpoint := by
  change rawGlobalReversalZero globalRightEndpoint = globalLeftEndpoint
  exact rawGlobalReversalZero_rightEndpoint

/-! ## Universal coordinate endpoint section -/

def reversedCoordinateFunction : CoordinateFunctionRing :=
  fun coordinate => coordinateReversal coordinate

def universalReversedCoordinate : CoordinateCoefficientRing :=
  Ideal.Quotient.mk coordinateZeroIdeal reversedCoordinateFunction

@[simp] theorem Point.specialization_universalReversedCoordinate
    (point : Point) :
    point.specialization universalReversedCoordinate =
      coordinateReversal point.coordinate :=
  rfl

def universalCoordinateEndpointSection : CoordinateScalarVertex :=
  universalCoordinate ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
    universalReversedCoordinate ⊗ₜ[ℤ] actualGlobalRightEndpoint

theorem coordinateExtendedReversalZero_universalEndpointSection :
    coordinateExtendedReversalZero universalCoordinateEndpointSection =
      universalCoordinate ⊗ₜ[ℤ] actualGlobalRightEndpoint +
        universalReversedCoordinate ⊗ₜ[ℤ] actualGlobalLeftEndpoint := by
  simp only [universalCoordinateEndpointSection, map_add,
    coordinateExtendedReversalZero, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [actualGlobalReversalZero_leftEndpoint,
    actualGlobalReversalZero_rightEndpoint]

theorem pointVertexSpecialization_universalEndpointSection (point : Point) :
    pointVertexSpecialization point universalCoordinateEndpointSection =
      point.coordinate ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
        coordinateReversal point.coordinate ⊗ₜ[ℤ] actualGlobalRightEndpoint := by
  simp [pointVertexSpecialization, universalCoordinateEndpointSection,
    pointCoefficientMap]

/-! ## Actual endpoint readback -/

def endpointPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

def endpointFactor : RuntimePrimePowerFactorAt endpointPrime 1 :=
  RuntimePrimePowerFactorAt.generate endpointPrime 1 (by omega)

abbrev endpointStage : Nat := endpointFactor.stage

def endpointStagePrime : StagePrime seedOccurrence.root endpointStage :=
  CanonicalUnitArithmeticFactorizationWholeHistorySolutionCofinalRigidity.stagePrimeIndex
    endpointFactor

def localEulerEndpointRead (dualIndex : Fin 2) :
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.Carrier
        seedOccurrence.root endpointStage →ₗ[ℤ] ℤ :=
  (LinearMap.proj (endpointStagePrime, dualIndex)).comp
    (CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead
      seedOccurrence.root endpointStage)

def localWholeEndpointRead (dualIndex : Fin 2) :
    WholeVertexModule seedOccurrence.root endpointStage →ₗ[ℤ] ℤ :=
  (localEulerEndpointRead dualIndex).comp (LinearMap.proj none)

def rawGlobalWholeEndpointRead (dualIndex : Fin 2) :
    ArithmeticGlobalVertex →ₗ[ℤ] ℤ :=
  (localWholeEndpointRead dualIndex).comp
    ((limit.π (localRelationDiagram seedOccurrence.root)
      (Opposite.op endpointStage)).f 0).hom

def actualGlobalWholeEndpointRead (dualIndex : Fin 2) :
    GlobalVertex →ₗ[ℤ] ℤ := by
  change ArithmeticGlobalVertex →ₗ[ℤ] ℤ
  exact rawGlobalWholeEndpointRead dualIndex

theorem rawGlobalWholeEndpointRead_endpointBase
    (dualIndex basisIndex : Fin 2) :
    rawGlobalWholeEndpointRead dualIndex
        (globalEndpointVertexMap
          (fun index => if index = basisIndex then 1 else 0)) =
      if dualIndex = basisIndex then 1 else 0 := by
  unfold rawGlobalWholeEndpointRead
  change localWholeEndpointRead dualIndex
      ((((limit.π (localRelationDiagram seedOccurrence.root)
        (Opposite.op endpointStage)).f 0).hom.comp
          globalEndpointVertexMap)
        (fun index => if index = basisIndex then 1 else 0)) = _
  rw [globalEndpointVertexMap_restriction]
  unfold localWholeEndpointRead
  rw [LinearMap.comp_apply]
  change
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead
      seedOccurrence.root endpointStage
      (localInnerEmbedding seedOccurrence.root endpointStage
        (fun index => if index = basisIndex then 1 else 0))
      (endpointStagePrime, dualIndex) = _
  unfold localInnerEmbedding
  rw [LinearMap.comp_apply,
    CanonicalUnitArithmeticFactorizationFullEulerSolutionAction.baseRead_solutionOfBase]
  rfl

@[simp] theorem actualGlobalWholeEndpointRead_left_zero :
    actualGlobalWholeEndpointRead 0 actualGlobalLeftEndpoint = 1 := by
  change rawGlobalWholeEndpointRead 0 globalLeftEndpoint = 1
  have baseEquality : leftEndpointBase =
      (fun index => if index = (0 : Fin 2) then 1 else 0) := by
    funext index
    fin_cases index <;> rfl
  rw [globalLeftEndpoint, baseEquality]
  exact rawGlobalWholeEndpointRead_endpointBase (0 : Fin 2) (0 : Fin 2)

@[simp] theorem actualGlobalWholeEndpointRead_left_one :
    actualGlobalWholeEndpointRead 1 actualGlobalLeftEndpoint = 0 := by
  change rawGlobalWholeEndpointRead 1 globalLeftEndpoint = 0
  have baseEquality : leftEndpointBase =
      (fun index => if index = (0 : Fin 2) then 1 else 0) := by
    funext index
    fin_cases index <;> rfl
  rw [globalLeftEndpoint, baseEquality]
  exact rawGlobalWholeEndpointRead_endpointBase (1 : Fin 2) (0 : Fin 2)

@[simp] theorem actualGlobalWholeEndpointRead_right_zero :
    actualGlobalWholeEndpointRead 0 actualGlobalRightEndpoint = 0 := by
  change rawGlobalWholeEndpointRead 0 globalRightEndpoint = 0
  have baseEquality : rightEndpointBase =
      (fun index => if index = (1 : Fin 2) then 1 else 0) := by
    funext index
    fin_cases index <;> rfl
  rw [globalRightEndpoint, baseEquality]
  exact rawGlobalWholeEndpointRead_endpointBase (0 : Fin 2) (1 : Fin 2)

@[simp] theorem actualGlobalWholeEndpointRead_right_one :
    actualGlobalWholeEndpointRead 1 actualGlobalRightEndpoint = 1 := by
  change rawGlobalWholeEndpointRead 1 globalRightEndpoint = 1
  have baseEquality : rightEndpointBase =
      (fun index => if index = (1 : Fin 2) then 1 else 0) := by
    funext index
    fin_cases index <;> rfl
  rw [globalRightEndpoint, baseEquality]
  exact rawGlobalWholeEndpointRead_endpointBase (1 : Fin 2) (1 : Fin 2)

def complexWholeEndpointRead (dualIndex : Fin 2) :
    ComplexScalarVertex →ₗ[ℤ] ℂ :=
  (TensorProduct.rid ℤ ℂ).toLinearMap.comp
    (TensorProduct.map LinearMap.id
      (actualGlobalWholeEndpointRead dualIndex))

@[simp] theorem complexWholeEndpointRead_tmul
    (dualIndex : Fin 2) (coefficient : ℂ) (vertex : GlobalVertex) :
    complexWholeEndpointRead dualIndex (coefficient ⊗ₜ[ℤ] vertex) =
      coefficient * actualGlobalWholeEndpointRead dualIndex vertex := by
  simp [complexWholeEndpointRead, mul_comm]

theorem pointSpecialization_leftEndpoint (point : Point) :
    complexWholeEndpointRead 0
        (pointVertexSpecialization point universalCoordinateEndpointSection) =
      point.coordinate := by
  rw [pointVertexSpecialization_universalEndpointSection, map_add]
  simp

theorem pointSpecialization_rightEndpoint (point : Point) :
    complexWholeEndpointRead 1
        (pointVertexSpecialization point universalCoordinateEndpointSection) =
      coordinateReversal point.coordinate := by
  rw [pointVertexSpecialization_universalEndpointSection, map_add]
  simp

/-! ## Calculated two-term boundary -/

def endpointAntiInvariantBase : DualBase :=
  leftEndpointBase - rightEndpointBase

def localEndpointBoundaryRelation (stage : Nat) :
    WholeRelationModule seedOccurrence.root stage :=
  fun _row =>
    localInnerEmbedding seedOccurrence.root stage endpointAntiInvariantBase

theorem factorizationDifferential_leftEndpoint (stage : Nat) :
    factorizationDifferential seedOccurrence.root stage
        (localEndpointVertexMap stage leftEndpointBase) =
      localEndpointBoundaryRelation stage := by
  funext row
  change
    innerAntiInvariant seedOccurrence.root stage
        (localInnerEmbedding seedOccurrence.root stage leftEndpointBase) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seedOccurrence.root stage 0 =
      localInnerEmbedding seedOccurrence.root stage endpointAntiInvariantBase
  rw [map_zero, smul_zero, sub_zero,
    innerAntiInvariant_localInnerEmbedding]
  congr 1
  funext index
  fin_cases index <;> rfl

theorem factorizationDifferential_rightEndpoint (stage : Nat) :
    factorizationDifferential seedOccurrence.root stage
        (localEndpointVertexMap stage rightEndpointBase) =
      -localEndpointBoundaryRelation stage := by
  funext row
  change
    innerAntiInvariant seedOccurrence.root stage
        (localInnerEmbedding seedOccurrence.root stage rightEndpointBase) -
      (((rowPrime row : Nat) : ℤ) ^ rowExponent row) •
        innerAntiInvariant seedOccurrence.root stage 0 =
      -localInnerEmbedding seedOccurrence.root stage endpointAntiInvariantBase
  rw [map_zero, smul_zero, sub_zero,
    innerAntiInvariant_localInnerEmbedding, ← map_neg]
  congr 1
  funext index
  fin_cases index <;> rfl

abbrev CoordinateLocalWholeVertex (stage : Nat) :=
  TensorProduct ℤ CoordinateCoefficientRing
    (WholeVertexModule seedOccurrence.root stage)

abbrev CoordinateLocalWholeRelation (stage : Nat) :=
  TensorProduct ℤ CoordinateCoefficientRing
    (WholeRelationModule seedOccurrence.root stage)

def localUniversalCoordinateEndpointSection (stage : Nat) :
    CoordinateLocalWholeVertex stage :=
  universalCoordinate ⊗ₜ[ℤ]
      localEndpointVertexMap stage leftEndpointBase +
    universalReversedCoordinate ⊗ₜ[ℤ]
      localEndpointVertexMap stage rightEndpointBase

def localCoordinateFactorizationDifferential (stage : Nat) :
    CoordinateLocalWholeVertex stage →ₗ[ℤ]
      CoordinateLocalWholeRelation stage :=
  TensorProduct.map LinearMap.id
    (factorizationDifferential seedOccurrence.root stage)

/-- The endpoint datum is a calculated two-term chain, not a zero premise. -/
theorem localCoordinateEndpoint_differential (stage : Nat) :
    localCoordinateFactorizationDifferential stage
        (localUniversalCoordinateEndpointSection stage) =
      (universalCoordinate - universalReversedCoordinate) ⊗ₜ[ℤ]
        localEndpointBoundaryRelation stage := by
  simp only [localCoordinateFactorizationDifferential,
    localUniversalCoordinateEndpointSection, map_add,
    TensorProduct.map_tmul, LinearMap.id_apply,
    factorizationDifferential_leftEndpoint,
    factorizationDifferential_rightEndpoint,
    TensorProduct.tmul_neg]
  rw [sub_eq_add_neg, TensorProduct.add_tmul, TensorProduct.neg_tmul]

end
end CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
