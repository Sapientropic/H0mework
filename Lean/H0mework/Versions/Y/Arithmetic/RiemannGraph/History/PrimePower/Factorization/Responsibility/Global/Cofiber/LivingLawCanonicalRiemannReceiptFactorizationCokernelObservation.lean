import H0mework.Realization.Coherent.Completion
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Observation.LivingLawCanonicalRiemannReceiptRoleSeparatedArithmeticObservation
import H0mework.Versions.Y.Arithmetic.BlockSpecialization.PairCofiberBoundaryRead

/-!
# Receipt exact envelope through the actual factorization action cofiber

The same full receipt table generates two sibling observations: the faithful
role-separated arithmetic endpoint face and a block endpoint face sent through
the existing factorization differential and relation-action cokernel.  Every
finite cokernel read is the restriction of the existing global endpoint class.

The cokernel face may have a legitimate representation kernel; it is not
promoted to a faithful detector.  No compatible family, differential-zero,
descent, separator, finite, or determinant premise is accepted.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofiber

open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockAnalyticEndpointBoundaryEigenAction
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryDeterminantSupport
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open SourceGeneratedIntegralCoherentCompletion
open Cofinal
open Observation
open CategoryTheory
open CategoryTheory.Limits
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence

noncomputable section

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram

abbrev ComplexBlockWholeVertex (stage : Nat) :=
  ComplexifiedCarrier (BlockWholeVertex seedOccurrence.root stage)

abbrev ComplexBlockWholeRelation (stage : Nat) :=
  ComplexifiedCarrier (BlockWholeRelation seedOccurrence.root stage)

abbrev ComplexLocalActionCokernel (stage : Nat) :=
  ComplexifiedCarrier (LocalRelationActionCokernel stage)

abbrev ComplexGlobalActionCokernel :=
  ComplexifiedCarrier GlobalRelationActionCokernel

def complexBlockFactorizationDifferential (stage : Nat) :
    ComplexBlockWholeVertex stage →ₗ[ℂ] ComplexBlockWholeRelation stage :=
  complexifiedLinearMap
    ((integralToComplexification
        (L := BlockWholeRelation seedOccurrence.root stage)).comp
      ((blockFactorizationDifferential seedOccurrence.root stage
        ).restrictScalars ℤ))

def complexLocalRelationActionCokernelProjection (stage : Nat) :
    ComplexBlockWholeRelation stage →ₗ[ℂ] ComplexLocalActionCokernel stage :=
  complexifiedLinearMap
    ((integralToComplexification (L := LocalRelationActionCokernel stage)).comp
      ((localRelationActionCokernelProjection stage).restrictScalars ℤ))

def pairLocalBlockEndpointVertex (stage : Nat) :
    QRich.ClozelJPair →ₗ[ℂ] ComplexBlockWholeVertex stage where
  toFun := fun value =>
    value.1 ⊗ₜ[ℤ]
        localBlockEndpointVertexMap stage blockLeftEndpointBase +
      value.2 ⊗ₜ[ℤ]
        localBlockEndpointVertexMap stage blockRightEndpointBase
  map_add' := by
    intro left right
    simp only [Prod.fst_add, Prod.snd_add, TensorProduct.add_tmul]
    abel
  map_smul' := by
    intro scalar value
    change (scalar * value.1) ⊗ₜ[ℤ] _ +
        (scalar * value.2) ⊗ₜ[ℤ] _ =
      scalar • (value.1 ⊗ₜ[ℤ] _ + value.2 ⊗ₜ[ℤ] _)
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp only [smul_eq_mul]

def pairLocalFactorizationCokernelRead (stage : Nat) :
    QRich.ClozelJPair →ₗ[ℂ] ComplexLocalActionCokernel stage :=
  (complexLocalRelationActionCokernelProjection stage).comp
    ((complexBlockFactorizationDifferential stage).comp
      (pairLocalBlockEndpointVertex stage))

theorem pairLocalFactorizationCokernelRead_eq
    (stage : Nat) (value : QRich.ClozelJPair) :
    pairLocalFactorizationCokernelRead stage value =
      (value.1 - value.2) ⊗ₜ[ℤ]
        localEndpointBoundaryCokernelClass stage := by
  simp [pairLocalFactorizationCokernelRead,
    pairLocalBlockEndpointVertex,
    complexBlockFactorizationDifferential,
    complexLocalRelationActionCokernelProjection,
    blockFactorizationDifferential_leftEndpoint,
    blockFactorizationDifferential_rightEndpoint,
    localEndpointBoundaryCokernelClass,
    sub_eq_add_neg, TensorProduct.add_tmul,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg,
    ← TensorProduct.tmul_eq_smul_one_tmul]

def complexGlobalCokernelRestriction (stage : Nat) :
    ComplexGlobalActionCokernel →ₗ[ℂ] ComplexLocalActionCokernel stage :=
  complexifiedLinearMap
    ((integralToComplexification (L := LocalRelationActionCokernel stage)).comp
      (((limit.π localRelationActionCokernelDiagram
        (Opposite.op stage)).hom).restrictScalars ℤ))

def pairDifference : QRich.ClozelJPair →ₗ[ℂ] ℂ where
  toFun := fun value => value.1 - value.2
  map_add' := by
    intro left right
    simp only [Prod.fst_add, Prod.snd_add]
    module
  map_smul' := by
    intro scalar value
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    module

def pairGlobalFactorizationCokernelClass :
    QRich.ClozelJPair →ₗ[ℂ] ComplexGlobalActionCokernel :=
  (LinearMap.toSpanSingleton ℂ ComplexGlobalActionCokernel
    (1 ⊗ₜ[ℤ] globalEndpointBoundaryCokernelClass)).comp pairDifference

theorem pairGlobalFactorizationCokernelClass_eq
    (value : QRich.ClozelJPair) :
    pairGlobalFactorizationCokernelClass value =
      (value.1 - value.2) ⊗ₜ[ℤ]
        globalEndpointBoundaryCokernelClass := by
  simp [pairGlobalFactorizationCokernelClass, pairDifference,
    LinearMap.toSpanSingleton_apply,
    ← TensorProduct.tmul_eq_smul_one_tmul]

theorem pairFactorizationCokernel_commutes
    (stage : Nat) (value : QRich.ClozelJPair) :
    complexGlobalCokernelRestriction stage
        (pairGlobalFactorizationCokernelClass value) =
      pairLocalFactorizationCokernelRead stage value := by
  rw [pairGlobalFactorizationCokernelClass_eq,
    pairLocalFactorizationCokernelRead_eq]
  rw [complexGlobalCokernelRestriction, complexifiedLinearMap_tmul]
  change (value.1 - value.2) •
      (1 ⊗ₜ[ℤ]
        (limit.π localRelationActionCokernelDiagram
          (Opposite.op stage)).hom globalEndpointBoundaryCokernelClass) = _
  rw [globalEndpointBoundaryCokernelClass_restriction]
  exact (TensorProduct.tmul_eq_smul_one_tmul
    (value.1 - value.2) (localEndpointBoundaryCokernelClass stage)).symm

abbrev RoleSeparatedGlobalCokernelObservation :=
  Nat → PrimeExponentPoleReceiptRole → ComplexGlobalActionCokernel

def tableFactorizationCokernelObservation : ReceiptTable →ₗ[ℂ]
    RoleSeparatedGlobalCokernelObservation where
  toFun := fun table cursor role =>
    pairGlobalFactorizationCokernelClass (table cursor role)
  map_add' := by
    intro left right
    funext cursor role
    exact pairGlobalFactorizationCokernelClass.map_add _ _
  map_smul' := by
    intro scalar table
    funext cursor role
    exact pairGlobalFactorizationCokernelClass.map_smul scalar _

def exactEnvelopeFactorizationCokernelObservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReceiptExactCarrier observation nontrivial →ₗ[ℂ]
      RoleSeparatedGlobalCokernelObservation :=
  tableFactorizationCokernelObservation.comp
    (envelopeToTable observation nontrivial)

theorem exactEnvelope_factorization_square
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : ReceiptExactCarrier observation nontrivial)
    (cursor stage : Nat) (role : PrimeExponentPoleReceiptRole) :
    complexGlobalCokernelRestriction stage
        (exactEnvelopeFactorizationCokernelObservation observation nontrivial
          value cursor role) =
      pairLocalFactorizationCokernelRead stage
        ((envelopeToTable observation nontrivial value) cursor role) := by
  exact pairFactorizationCokernel_commutes stage _

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofiber
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
