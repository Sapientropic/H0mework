import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Cofiber.LivingLawCanonicalRiemannReceiptFactorizationCokernelObservation
import H0mework.Versions.Y.Arithmetic.EulerLog.RootIncidence

/-!
# Source installation certificate for the receipt factorization cofiber

The actual zero-owned receipt point is read through the block differential at
every finite stage.  Its arithmetic and cokernel faces share the literal
factorization seed; their product remains faithful even when the cokernel face
has a representation kernel.  Role fusion is a downstream relation read.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofiber

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open Cofinal
open Observation
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog

noncomputable section

theorem zeroOwnedFactorizationCokernelObservation_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    exactEnvelopeFactorizationCokernelObservation observation nontrivial
        (zeroOwnedReceiptExactPoint observation nontrivial) cursor role =
      pairGlobalFactorizationCokernelClass
        (receiptRoleValue observation nontrivial cursor role) := by
  change pairGlobalFactorizationCokernelClass
      (envelopeToTable observation nontrivial
        (receiptEnvelopeSourceMap observation nontrivial
          (receiptCofinalFace observation nontrivial).root.root.2.table)
        cursor role) = _
  rw [show envelopeToTable observation nontrivial
      (receiptEnvelopeSourceMap observation nontrivial
        (receiptCofinalFace observation nontrivial).root.root.2.table) =
        (receiptCofinalFace observation nontrivial).root.root.2.table by
    exact LinearMap.congr_fun
      (envelopeToTable_source observation nontrivial) _]
  rw [receiptCofinalFace_root_table]

theorem zeroOwnedFactorizationCokernelObservation_localRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor stage : Nat) (role : PrimeExponentPoleReceiptRole) :
    complexGlobalCokernelRestriction stage
        (exactEnvelopeFactorizationCokernelObservation observation nontrivial
          (zeroOwnedReceiptExactPoint observation nontrivial) cursor role) =
      pairLocalFactorizationCokernelRead stage
        (receiptRoleValue observation nontrivial cursor role) := by
  rw [zeroOwnedFactorizationCokernelObservation_source]
  exact pairFactorizationCokernel_commutes stage _

def cokernelRoleFusionAt (cursor : Nat) :
    RoleSeparatedGlobalCokernelObservation →ₗ[ℂ]
      ComplexGlobalActionCokernel where
  toFun := fun value => value cursor .retained - value cursor .energy -
    value cursor .vertical
  map_add' := by
    intro left right
    simp only [Pi.add_apply]
    module
  map_smul' := by
    intro scalar value
    simp only [Pi.smul_apply, RingHom.id_apply]
    module

theorem zeroOwnedFactorizationCokernelObservation_fusion_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    cokernelRoleFusionAt cursor
        (exactEnvelopeFactorizationCokernelObservation observation nontrivial
          (zeroOwnedReceiptExactPoint observation nontrivial)) = 0 := by
  have relation :
      receiptRoleValue observation nontrivial cursor .retained =
        receiptRoleValue observation nontrivial cursor .energy +
          receiptRoleValue observation nontrivial cursor .vertical := by
    simpa only [receiptCofinalFace_root_table] using
      receiptCofinalFace_root_relation observation nontrivial cursor
  change exactEnvelopeFactorizationCokernelObservation observation nontrivial
          (zeroOwnedReceiptExactPoint observation nontrivial) cursor .retained -
        exactEnvelopeFactorizationCokernelObservation observation nontrivial
          (zeroOwnedReceiptExactPoint observation nontrivial) cursor .energy -
      exactEnvelopeFactorizationCokernelObservation observation nontrivial
        (zeroOwnedReceiptExactPoint observation nontrivial) cursor .vertical = 0
  rw [zeroOwnedFactorizationCokernelObservation_source,
    zeroOwnedFactorizationCokernelObservation_source,
    zeroOwnedFactorizationCokernelObservation_source]
  rw [relation, map_add]
  module

def exactEnvelopeArithmeticCokernelObservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReceiptExactCarrier observation nontrivial →ₗ[ℂ]
      RoleSeparatedGlobalObservation ×
        RoleSeparatedGlobalCokernelObservation :=
  (exactEnvelopeArithmeticObservation observation nontrivial).prod
    (exactEnvelopeFactorizationCokernelObservation observation nontrivial)

theorem exactEnvelopeArithmeticCokernelObservation_injective
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Function.Injective
      (exactEnvelopeArithmeticCokernelObservation observation nontrivial) := by
  intro left right equality
  apply exactEnvelopeArithmeticObservation_injective observation nontrivial
  exact congrArg Prod.fst equality

theorem receiptCofinalFace_projects_seed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((((((((receiptCofinalFace observation nontrivial).root.map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst = seedOccurrence := by
  rw [receiptCofinalFace_projects_allPrime]
  exact zeroOwnedAllPrimeWeilQuadraticOccurrence_projects_to_seed
    observation nontrivial

theorem receiptCofinalFace_globalEndpoint_same_seed
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((((((((receiptCofinalFace observation nontrivial).root.map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst =
      globalEndpointBoundaryCokernelOccurrence.map Prod.fst := by
  rw [receiptCofinalFace_projects_seed,
    globalEndpointBoundaryCokernelOccurrence_projects]

theorem receiptCofinalFace_globalEulerLog_same_factorizationOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((((((((receiptCofinalFace observation nontrivial).root.map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Sigma.fst).map
        Sigma.fst).map Sigma.fst).map Prod.fst =
      globalEulerLogOccurrence.map (fun payload => payload.1.1) := by
  rw [receiptCofinalFace_globalEndpoint_same_seed]
  exact
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlaceEulerLogIncidence.globalEulerLog_endpointBoundary_same_factorizationOccurrence.symm

structure ZeroOwnedReceiptFactorizationCokernelCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Type where
  joint_observation_injective : Function.Injective
    (exactEnvelopeArithmeticCokernelObservation observation nontrivial)
  source_readback : ∀ cursor role,
    type_of% (zeroOwnedFactorizationCokernelObservation_source
      observation nontrivial cursor role)
  local_factorization_square : ∀ cursor role stage,
    type_of% (zeroOwnedFactorizationCokernelObservation_localRead
      observation nontrivial cursor stage role)
  role_fusion_zero : ∀ cursor,
    type_of% (zeroOwnedFactorizationCokernelObservation_fusion_zero
      observation nontrivial cursor)
  shared_factorization_seed : type_of%
    (receiptCofinalFace_globalEndpoint_same_seed observation nontrivial)
  shared_eulerLog_occurrence : type_of%
    (receiptCofinalFace_globalEulerLog_same_factorizationOccurrence
      observation nontrivial)
  existing_pair_cofiber_read : ∀ stage,
    type_of%
      (CanonicalRiemannPairCofiberBoundaryRead.globalEndpointClass_pairCofiber_common_local_read
        stage)

def generateZeroOwnedReceiptFactorizationCokernelCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ZeroOwnedReceiptFactorizationCokernelCertificate observation nontrivial where
  joint_observation_injective :=
    exactEnvelopeArithmeticCokernelObservation_injective observation nontrivial
  source_readback := zeroOwnedFactorizationCokernelObservation_source
    observation nontrivial
  local_factorization_square :=
    fun cursor role stage =>
      zeroOwnedFactorizationCokernelObservation_localRead
        observation nontrivial cursor stage role
  role_fusion_zero := zeroOwnedFactorizationCokernelObservation_fusion_zero
    observation nontrivial
  shared_factorization_seed :=
    receiptCofinalFace_globalEndpoint_same_seed observation nontrivial
  shared_eulerLog_occurrence :=
    receiptCofinalFace_globalEulerLog_same_factorizationOccurrence
      observation nontrivial
  existing_pair_cofiber_read :=
    CanonicalRiemannPairCofiberBoundaryRead.globalEndpointClass_pairCofiber_common_local_read

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofiber
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
