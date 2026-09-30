import H0mework.Versions.X.Arithmetic.UnitArithmetic.EulerPrefix
import H0mework.Versions.X.Arithmetic.UnitArithmetic.DualReadouts

/-!
# Source-generated cofinal Euler limit

The finite UnitHistory prefixes form a cofinal enumeration of rational-prime
local factors.  At every arithmetic coefficient they eventually equal the
all-prime formal Euler product.  This makes the global formal zeta value a
unique cofinal readout of the common source rather than primitive root data.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCofinalEulerLimit

open ArithmeticGeneration
open CanonicalUnitArithmeticCofinalEulerPrefix
open CanonicalUnitArithmeticCommonCarrier
open CanonicalUnitArithmeticCommonDeterminantState
open CanonicalUnitArithmeticDualReadouts
open CanonicalUnitArithmeticPrimePowerIncidence
open GradedIntegralDeterminantLine
open Filter

noncomputable section

theorem primeAtStage_injective : Function.Injective primeAtStage := by
  intro left right samePrime
  apply Nat.nth_injective Nat.infinite_setOfPred_prime
  exact congrArg Subtype.val samePrime

def primePrefixFinset (bound : Nat) : Finset Nat.Primes :=
  (Finset.range bound).image primeAtStage

theorem primePrefixFinset_mono : Monotone primePrefixFinset := by
  intro left right bound prime primeMem
  rcases Finset.mem_image.mp primeMem with ⟨stage, stageMem, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨stage, Finset.mem_range.mpr
    ((Finset.mem_range.mp stageMem).trans_le bound), rfl⟩

theorem everyFinitePrimeSet_enters_prefix
    (primes : Finset Nat.Primes) :
    ∃ bound, primes ⊆ primePrefixFinset bound := by
  let bound := primes.sup stageOfPrime + 1
  refine ⟨bound, ?_⟩
  intro prime primeMem
  apply Finset.mem_image.mpr
  refine ⟨stageOfPrime prime, Finset.mem_range.mpr ?_,
    primeAtStage_stageOfPrime prime⟩
  exact Nat.lt_succ_of_le (Finset.le_sup primeMem)

theorem finiteEulerPrefix_eq_stageProduct (history : UnitHistory) :
    finiteEulerPrefix history =
      ∏ stage ∈ Finset.range history.cardinalShadow,
        sourceLocalFormalEulerFactor (primeAtStage stage) := by
  induction history with
  | empty =>
      change (1 : ArithmeticFunction ℤ) =
        ∏ stage ∈ Finset.range 0,
          sourceLocalFormalEulerFactor (primeAtStage stage)
      simp
  | next prior inductionHypothesis =>
      rw [finiteEulerPrefix_next, inductionHypothesis]
      change
        sourceLocalFormalEulerFactor
              (primeAtStage prior.cardinalShadow) *
            (∏ stage ∈ Finset.range prior.cardinalShadow,
              sourceLocalFormalEulerFactor (primeAtStage stage)) =
          ∏ stage ∈ Finset.range (Nat.succ prior.cardinalShadow),
            sourceLocalFormalEulerFactor (primeAtStage stage)
      rw [Finset.prod_range_succ]
      exact mul_comm _ _

theorem finiteEulerPrefix_eq_primeProduct (history : UnitHistory) :
    finiteEulerPrefix history =
      ∏ prime ∈ primePrefixFinset history.cardinalShadow,
        localFormalEulerFactor prime := by
  rw [finiteEulerPrefix_eq_stageProduct, primePrefixFinset,
    Finset.prod_image primeAtStage_injective.injOn]
  rfl

/-- At every coefficient, the source-generated finite prefixes eventually
stabilize to the formal all-prime Euler product. -/
theorem cofinalPrefix_eventually_eq_formalEulerCoefficients
    (source : CoordinateFreeRelationSource) (coefficient : Nat) :
    ∀ᶠ stage : Nat in atTop,
      cofinalPrefix source stage coefficient =
        formalEulerCoefficients coefficient := by
  have finiteProductsEventually :=
    formalEulerCoefficients_eventually_finite coefficient
  rw [Filter.eventually_atTop] at finiteProductsEventually
  obtain ⟨requiredPrimes, stable⟩ := finiteProductsEventually
  obtain ⟨bound, requiredSubset⟩ :=
    everyFinitePrimeSet_enters_prefix requiredPrimes
  apply Filter.eventually_atTop.2
  refine ⟨bound, ?_⟩
  intro stage stageLarge
  rw [cofinalPrefix, finiteEulerPrefix_eq_primeProduct,
    cofinalHistory_cardinalShadow]
  apply stable
  exact requiredSubset.trans <|
    primePrefixFinset_mono <|
      stageLarge.trans (Nat.le_add_left stage source.history.cardinalShadow)

/-- Exact cofinal-limit law over one coordinate-free source. -/
structure CofinalEulerLimitAt
    (source : CoordinateFreeRelationSource)
    (limit : ArithmeticFunction ℤ) : Prop where
  private mk ::
  pointwiseEventually : ∀ coefficient : Nat,
    ∀ᶠ stage : Nat in atTop,
      cofinalPrefix source stage coefficient = limit coefficient

theorem formalEulerCofinalLimit
    (source : CoordinateFreeRelationSource) :
    CofinalEulerLimitAt source formalEulerCoefficients :=
  ⟨cofinalPrefix_eventually_eq_formalEulerCoefficients source⟩

theorem cofinalEulerLimit_unique
    {source : CoordinateFreeRelationSource}
    {left right : ArithmeticFunction ℤ}
    (leftLimit : CofinalEulerLimitAt source left)
    (rightLimit : CofinalEulerLimitAt source right) :
    left = right := by
  ext coefficient
  have together := (leftLimit.pointwiseEventually coefficient).and
    (rightLimit.pointwiseEventually coefficient)
  rcases together.exists with ⟨stage, leftEq, rightEq⟩
  exact leftEq.symm.trans rightEq

/-- Generated package of the unique cofinal limit for one source point. -/
structure GeneratedCofinalEulerLimit : Type where
  private mk ::
  source : CoordinateFreeRelationSource
  limit : ArithmeticFunction ℤ
  generated : CofinalEulerLimitAt source limit

def GeneratedCofinalEulerLimit.generate
    (source : CoordinateFreeRelationSource) : GeneratedCofinalEulerLimit :=
  ⟨source, formalEulerCoefficients, formalEulerCofinalLimit source⟩

/-- The all-prime formal Euler object is now attached with its source-generated
cofinal law, not by a bare constant map. -/
def cofinalLimitOccurrence : RootedAccountedUnfolding
    ((DomainPoint × CoordinateFreeRelationSource) ×
      GeneratedCofinalEulerLimit) :=
  commonOccurrence.map fun point =>
    (point, GeneratedCofinalEulerLimit.generate point.2)

theorem cofinalLimitOccurrence_projects_to_commonOccurrence :
    cofinalLimitOccurrence.map Prod.fst = commonOccurrence := by
  rw [cofinalLimitOccurrence, RootedAccountedUnfolding.map_map]
  change commonOccurrence.map id = commonOccurrence
  exact RootedAccountedUnfolding.map_id _

def cofinalEulerOccurrence : RootedAccountedUnfolding
    (DomainPoint × ArithmeticFunction ℤ) :=
  cofinalLimitOccurrence.map fun point =>
    (point.1.1, point.2.limit)

theorem cofinalEulerOccurrence_projects_to_exact_unit_root :
    cofinalEulerOccurrence.map Prod.fst =
      CanonicalUnitArithmeticPrimePowerIncidence.rootOccurrence := by
  rw [cofinalEulerOccurrence, RootedAccountedUnfolding.map_map]
  change cofinalLimitOccurrence.map (fun point => point.1.1) = _
  rw [cofinalLimitOccurrence, RootedAccountedUnfolding.map_map]
  exact commonOccurrence_projects_to_exact_unit_root

@[simp] theorem cofinalEulerOccurrence_root_value :
    cofinalEulerOccurrence.root.2 = formalEulerCoefficients :=
  rfl

/-- Actual all-prime-to-local factorization is now a readout of the unique
source-generated cofinal occurrence. -/
theorem cofinalEulerPrimePowerFactorization
    (prime : Nat.Primes) (exponent : Nat) :
    EulerPrimePowerFactorizationAt
      CanonicalUnitArithmeticPrimePowerIncidence.rootOccurrence
      cofinalEulerOccurrence prime exponent where
  rootProjects := cofinalEulerOccurrence_projects_to_exact_unit_root
  factorizes := by
    rw [cofinalEulerOccurrence_root_value]
    exact formalEulerCoefficients_apply_primePower prime exponent
  unitNormalization := by
    rw [cofinalEulerOccurrence_root_value,
      formalEulerCoefficients_apply_primePower,
      localFormalEulerFactor_apply_primePower]
    exact isUnit_one

structure CofinalSelfDualArithmeticZetaDeterminantFibreAt
    (eulerOccurrence : RootedAccountedUnfolding
      (DomainPoint × ArithmeticFunction ℤ)) : Type where
  private mk ::

def cofinalSelfDualArithmeticZetaDeterminantFibre :
    CofinalSelfDualArithmeticZetaDeterminantFibreAt
      cofinalEulerOccurrence :=
  ⟨⟩

theorem cofinalSelfDualFibre_preserves_reversal :
    Function.Involutive CanonicalUnitArithmeticCommonCarrier.reversal :=
  CanonicalUnitArithmeticCommonCarrier.reversal_involutive

theorem cofinalSelfDualFibre_preserves_determinant_root :
    determinantState.determinantFace.root = commonOccurrence :=
  determinant_preserves_common_occurrence

theorem cofinalSelfDualFibre_has_generated_unit :
    Module.finrank ℤ IntegralLine = 1 ∧
      Nonempty (CanonicalIntegralUnitTorsor IntegralLine) :=
  ⟨determinantState.determinantFace.integralLine_finrank,
    ⟨unitTorsor⟩⟩

/-- Goldbach's additive fibre and the cofinal self-dual Euler fibre are sealed
as restrictions of the same named root authority. -/
structure CofinalCommonArithmeticReadoutStateAt
    (_additive : GoldbachAdditiveFibreAt 1)
    (_zeta : CofinalSelfDualArithmeticZetaDeterminantFibreAt
      cofinalEulerOccurrence) : Type where
  private mk ::

def cofinalCommonArithmeticReadoutState :
    CofinalCommonArithmeticReadoutStateAt goldbachAdditiveFibre
      cofinalSelfDualArithmeticZetaDeterminantFibre :=
  ⟨⟩

theorem cofinal_named_faces_share_occurrence_ledger_and_next :
    commonFacadeSeed.tick.generated.occurrence =
        commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          commonFacadeSeed.current.visit.current ∧
      HEq commonFacadeSeed.tick.generated.wholeLedgerWriteBack
        (commonFacadeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          commonFacadeSeed.current.visit.current) ∧
      commonFacadeSeed.tick.nextCurrent =
        commonFacade.process.stateAt
          (commonFacade.process.successor commonFacadeSeed.state) :=
  both_named_faces_share_occurrence_ledger_and_next

end
end CanonicalUnitArithmeticCofinalEulerLimit
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
