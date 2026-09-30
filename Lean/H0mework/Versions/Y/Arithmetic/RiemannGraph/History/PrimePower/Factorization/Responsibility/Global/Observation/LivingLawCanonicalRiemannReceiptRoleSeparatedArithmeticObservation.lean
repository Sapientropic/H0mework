import H0mework.Versions.Y.Arithmetic.EulerAnalytic.CoordinateEndpointSection
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Perfectification.LivingLawCanonicalRiemannZeroOwnedReceiptExactEnvelope

/-!
# Role-separated arithmetic observation of the receipt exact envelope

Each retained/energy/vertical pair is sent to the existing two global
arithmetic endpoint sections, while the three roles remain separate.  The
map is faithful: the existing endpoint reads recover both complex
coordinates.  Only the downstream role-blind fusion forgets the roles, and
the actual zero-owned table lands in its explicit kernel.

Thus relation settlement no longer deletes the receipt state itself.  No
differential-zero, descent, separator, finite, or determinant premise is
accepted.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Observation

open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateEndpointSection
open Cofinal
open scoped TensorProduct

noncomputable section

def pairGlobalEndpointMap : QRich.ClozelJPair →ₗ[ℂ] ComplexScalarVertex where
  toFun := fun value =>
    value.1 ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
      value.2 ⊗ₜ[ℤ] actualGlobalRightEndpoint
  map_add' := by
    intro left right
    simp only [Prod.fst_add, Prod.snd_add, TensorProduct.add_tmul]
    abel
  map_smul' := by
    intro scalar value
    change (scalar * value.1) ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
        (scalar * value.2) ⊗ₜ[ℤ] actualGlobalRightEndpoint =
      scalar • (value.1 ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
        value.2 ⊗ₜ[ℤ] actualGlobalRightEndpoint)
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp only [smul_eq_mul]

@[simp] theorem pairGlobalEndpointMap_leftRead (value : QRich.ClozelJPair) :
    complexWholeEndpointRead 0 (pairGlobalEndpointMap value) = value.1 := by
  change complexWholeEndpointRead 0
      (value.1 ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
        value.2 ⊗ₜ[ℤ] actualGlobalRightEndpoint) = value.1
  rw [map_add, complexWholeEndpointRead_tmul,
    complexWholeEndpointRead_tmul,
    actualGlobalWholeEndpointRead_left_zero,
    actualGlobalWholeEndpointRead_right_zero]
  ring

@[simp] theorem pairGlobalEndpointMap_rightRead (value : QRich.ClozelJPair) :
    complexWholeEndpointRead 1 (pairGlobalEndpointMap value) = value.2 := by
  change complexWholeEndpointRead 1
      (value.1 ⊗ₜ[ℤ] actualGlobalLeftEndpoint +
        value.2 ⊗ₜ[ℤ] actualGlobalRightEndpoint) = value.2
  rw [map_add, complexWholeEndpointRead_tmul,
    complexWholeEndpointRead_tmul,
    actualGlobalWholeEndpointRead_left_one,
    actualGlobalWholeEndpointRead_right_one]
  ring

theorem pairGlobalEndpointMap_injective :
    Function.Injective pairGlobalEndpointMap := by
  intro left right equality
  apply Prod.ext
  · simpa using congrArg (complexWholeEndpointRead 0) equality
  · simpa using congrArg (complexWholeEndpointRead 1) equality

abbrev RoleSeparatedGlobalObservation :=
  Nat → PrimeExponentPoleReceiptRole → ComplexScalarVertex

def tableArithmeticObservation : ReceiptTable →ₗ[ℂ]
    RoleSeparatedGlobalObservation where
  toFun := fun table cursor role => pairGlobalEndpointMap (table cursor role)
  map_add' := by
    intro left right
    funext cursor role
    exact pairGlobalEndpointMap.map_add _ _
  map_smul' := by
    intro scalar table
    funext cursor role
    exact pairGlobalEndpointMap.map_smul scalar _

theorem tableArithmeticObservation_injective :
    Function.Injective tableArithmeticObservation := by
  intro left right equality
  funext cursor role
  apply pairGlobalEndpointMap_injective
  exact congrFun (congrFun equality cursor) role

def exactEnvelopeArithmeticObservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReceiptExactCarrier observation nontrivial →ₗ[ℂ]
      RoleSeparatedGlobalObservation :=
  tableArithmeticObservation.comp (envelopeToTable observation nontrivial)

theorem exactEnvelopeArithmeticObservation_injective
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Function.Injective
      (exactEnvelopeArithmeticObservation observation nontrivial) :=
  tableArithmeticObservation_injective.comp
    (envelopeToTable_bijective observation nontrivial).1

theorem exactEnvelopeArithmeticObservation_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (table : ReceiptTable) (cursor : Nat)
    (role : PrimeExponentPoleReceiptRole) :
    exactEnvelopeArithmeticObservation observation nontrivial
        (receiptEnvelopeSourceMap observation nontrivial table) cursor role =
      pairGlobalEndpointMap (table cursor role) := by
  change pairGlobalEndpointMap
      (envelopeToTable observation nontrivial
        (receiptEnvelopeSourceMap observation nontrivial table) cursor role) = _
  rw [show envelopeToTable observation nontrivial
      (receiptEnvelopeSourceMap observation nontrivial table) = table by
    exact LinearMap.congr_fun (envelopeToTable_source observation nontrivial) table]

/-- The old role-blind read is now an explicit downstream measurement. -/
def roleFusionAt (cursor : Nat) : RoleSeparatedGlobalObservation →ₗ[ℂ]
    ComplexScalarVertex where
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

theorem tableArithmeticObservation_fusion_zero
    (table : ReceiptTable) (cursor : Nat)
    (relation : table cursor .retained =
      table cursor .energy + table cursor .vertical) :
    roleFusionAt cursor (tableArithmeticObservation table) = 0 := by
  change pairGlobalEndpointMap (table cursor .retained) -
      pairGlobalEndpointMap (table cursor .energy) -
        pairGlobalEndpointMap (table cursor .vertical) = 0
  rw [relation, map_add]
  module

def zeroOwnedReceiptExactPoint
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReceiptExactCarrier observation nontrivial :=
  receiptEnvelopeSourceMap observation nontrivial
    (receiptCofinalFace observation nontrivial).root.root.2.table

theorem zeroOwnedArithmeticObservation_leftRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    complexWholeEndpointRead 0
        (exactEnvelopeArithmeticObservation observation nontrivial
          (zeroOwnedReceiptExactPoint observation nontrivial) cursor role) =
      (receiptRoleValue observation nontrivial cursor role).1 := by
  rw [zeroOwnedReceiptExactPoint,
    exactEnvelopeArithmeticObservation_source,
    pairGlobalEndpointMap_leftRead]
  exact congrArg Prod.fst
    (receiptCofinalFace_root_table observation nontrivial cursor role)

theorem zeroOwnedArithmeticObservation_rightRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) (role : PrimeExponentPoleReceiptRole) :
    complexWholeEndpointRead 1
        (exactEnvelopeArithmeticObservation observation nontrivial
          (zeroOwnedReceiptExactPoint observation nontrivial) cursor role) =
      (receiptRoleValue observation nontrivial cursor role).2 := by
  rw [zeroOwnedReceiptExactPoint,
    exactEnvelopeArithmeticObservation_source,
    pairGlobalEndpointMap_rightRead]
  exact congrArg Prod.snd
    (receiptCofinalFace_root_table observation nontrivial cursor role)

theorem zeroOwnedReceiptExactPoint_fusion_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) :
    roleFusionAt cursor
        (exactEnvelopeArithmeticObservation observation nontrivial
          (zeroOwnedReceiptExactPoint observation nontrivial)) = 0 := by
  rw [zeroOwnedReceiptExactPoint]
  have observationEq :
      exactEnvelopeArithmeticObservation observation nontrivial
          (receiptEnvelopeSourceMap observation nontrivial
            (receiptCofinalFace observation nontrivial).root.root.2.table) =
        tableArithmeticObservation
          (receiptCofinalFace observation nontrivial).root.root.2.table := by
    funext index role
    exact exactEnvelopeArithmeticObservation_source observation nontrivial
      _ index role
  rw [observationEq]
  exact tableArithmeticObservation_fusion_zero _ cursor
    (receiptCofinalFace_root_relation observation nontrivial cursor)

/-- Actual role-separated arithmetic state in the inverse fibre of the
role-blind measurement. -/
def zeroOwnedRoleSeparatedArithmeticRelationPoint
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (cursor : Nat) : LinearMap.ker (roleFusionAt cursor) :=
  ⟨exactEnvelopeArithmeticObservation observation nontrivial
      (zeroOwnedReceiptExactPoint observation nontrivial),
    zeroOwnedReceiptExactPoint_fusion_zero observation nontrivial cursor⟩

/-- Opaque installation certificate for the role-separated observation.
Bundling prevents downstream root elaboration from replaying the full
cofinal-envelope proof term. -/
structure ZeroOwnedRoleSeparatedArithmeticObservationCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Type where
  observation_injective : Function.Injective
    (exactEnvelopeArithmeticObservation observation nontrivial)
  observation_readback : ∀ cursor role,
    type_of% (zeroOwnedArithmeticObservation_leftRead
        observation nontrivial cursor role) ∧
      type_of% (zeroOwnedArithmeticObservation_rightRead
        observation nontrivial cursor role)
  role_separated_relation : ∀ cursor,
    type_of% (zeroOwnedReceiptExactPoint_fusion_zero
      observation nontrivial cursor)

def generateZeroOwnedRoleSeparatedArithmeticObservationCertificate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ZeroOwnedRoleSeparatedArithmeticObservationCertificate
      observation nontrivial where
  observation_injective := exactEnvelopeArithmeticObservation_injective
    observation nontrivial
  observation_readback := fun cursor role =>
    ⟨zeroOwnedArithmeticObservation_leftRead
        observation nontrivial cursor role,
      zeroOwnedArithmeticObservation_rightRead
        observation nontrivial cursor role⟩
  role_separated_relation := zeroOwnedReceiptExactPoint_fusion_zero
    observation nontrivial

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Observation
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
