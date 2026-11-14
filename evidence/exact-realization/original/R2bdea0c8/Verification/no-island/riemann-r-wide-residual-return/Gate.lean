import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualReturnConsumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 620000
set_option linter.defProp false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CP809Independent

open BurnolPhysicalState Filter RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open SourceGeneratedFiniteGram RootGeneratedDebtActivationJointSource.OwnerFree WideResidualReturn
open scoped Topology InnerProductSpace

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner DivisionEffectPrice.wideNormed
open private closedStockNormed from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondStockCayleyGrowth
attribute [local instance] closedStockNormed

open private priceDelta from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualReturnNative
open private cotests from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "action" => advanceWide coord observation.mathlibZero
local notation "d" => sourceDamping coord
local notation "stock" => actualWide observation nontrivial half depth
local notation "bank" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "read" => sample observation nontrivial half depth
local notation "fit" => currentFit observation nontrivial half depth ordinal
local notation "observed" => observedGraph observation nontrivial half depth ordinal
local notation "diff" => difference observation nontrivial half depth ordinal
local notation "realized" => PriceStream.graph observation nontrivial half depth diff
local notation "err" => observedError observation nontrivial half depth ordinal
local notation "result" => paid observation nontrivial half depth ordinal
local notation "relations" => DenseDivisionPrice.relationStock observation half
local notation "prices" => PriceStream.prices observation nontrivial half depth

private theorem actual_birth_bank_order_and_paid_price_difference (n : Nat) :
    let evaluate := priceDelta observation nontrivial half depth n
    evaluate (bank ordinal,bank (ordinal+1)) = PrefixImage.sample (diff).val n ∧
    evaluate (bank (ordinal+1),bank ordinal) = -(PrefixImage.sample (diff).val n) := by
  let evaluate := priceDelta observation nontrivial half depth n
  have price : read n ((bank (ordinal+1)).1 - (bank ordinal).1) = PrefixImage.sample (diff).val n :=
    difference_source observation nontrivial half depth ordinal n
  constructor
  · exact price
  · change read n ((bank ordinal).1 - (bank (ordinal+1)).1) = _
    rw [← neg_sub, map_neg, price]

private theorem paid_graph_has_separate_observation_and_action_error (n m : Nat) :
    err n = ‖realized-observed n‖ ∧
    fit n m = Geom.finite action d m (observed n) ∧
    ‖fit n m-stock ordinal‖ ≤ Geom.noisyBudget d (linearBudget coord) m ‖realized‖ (err n) :=
  ⟨observed_error_eq observation nontrivial half depth ordinal n,
    finite_source observation nontrivial half depth ordinal n m,
    finite_graph_error observation nontrivial half depth ordinal n m⟩

private theorem source_effect_recovers_the_nonzero_original_graph :
    Geom.inverse action d realized = stock ordinal ∧ realized ≠ 0 := by
  have effect := difference_graph observation nontrivial half depth ordinal
  let inverse := DivisionEffectPrice.effectInverse observation half
  have solved : inverse ((action-1) (stock ordinal)) = stock ordinal :=
    congrArg (fun op : Wide →L[ℂ] Wide => op (stock ordinal))
      (DivisionEffectPrice.inverse_equations observation half).1
  have restored : Geom.inverse action d realized = stock ordinal :=
    (congrArg inverse effect).trans solved
  have live : stock ordinal ≠ 0 := by
    intro erased
    have seen := actual_observation observation nontrivial half depth ordinal
    rw [erased, map_zero] at seen
    exact WidePositionGap.actual_division_physical_ne_zero observation nontrivial half depth ordinal seen.symm
  exact ⟨restored, fun erased => live (by rw [← restored,erased,map_zero])⟩

private theorem actual_write_executes_native_R_and_full_relation (n m : Nat) :
    (result n m).2.2 = action (result n m).2.1 ∧
    relations (result n m).2.2 = advanceStock coord (relations (result n m).2.1) := by
  have paid := paid_source observation nontrivial half depth ordinal n m
  have wrote := (congrArg (fun value : Wide × Wide × Wide => value.2.2) paid).trans
    (congrArg (fun value : Wide × Wide × Wide => action value.2.1) paid).symm
  exact ⟨wrote, actual_next_relation observation nontrivial half depth ordinal n m⟩

private theorem diagonal_recovers_closed_graph_and_independent_next_K :
    Tendsto (fun n => (result n n).2.1) atTop (𝓝 (stock ordinal)) ∧
    Tendsto (fun n => (result n n).2.2) atTop (𝓝 (stock (ordinal+1))) ∧
    ∀ i, Tendsto (fun n => prices (result n n).2.2 i) atTop (𝓝 (prices (stock (ordinal+1)) i)) :=
  ⟨actual_graph_tendsto observation nontrivial half depth ordinal,
    actual_next_graph observation nontrivial half depth ordinal,
    actual_next_K observation nontrivial half depth ordinal⟩

private def paid_terminal_keeps_its_whole_next_and_original_macro (n m : Nat) :=
  let consumed := consume_actual_wide_return observation nontrivial half depth ordinal n m
  let paid := consumed.1
  let localWholeNext := paid.2.2.2.2.2
  let originalMacro := consumed.2.2.2.2.2.2
  And.intro paid.2.1 <| And.intro paid.2.2.1 <| And.intro paid.2.2.2.1 <|
    And.intro paid.2.2.2.2.1 <|
    And.intro localWholeNext.2.2.1 <| And.intro localWholeNext.2.2.2 <|
    And.intro originalMacro.2.2.2.2.2.2.2.1 <|
    And.intro originalMacro.2.2.2.2.2.2.2.2.1 originalMacro.2.2.2.2.2.2.2.2.2

private theorem zero_inverse_round_erases_both_graphs_and_misses_actual_stock (n : Nat) :
    (result n 0).2 = (0,0) ∧ (result n 0).2.1 ≠ stock ordinal := by
  have empty : fit n 0 = 0 := by
    rw [finite_source, Geom.finite_zero, zero_apply]
  have paid := paid_source observation nontrivial half depth ordinal n 0
  have erased : (result n 0).2 = (0,0) := by
    have two := congrArg (Prod.snd : Wide × (Wide × Wide) → Wide × Wide) paid
    exact two.trans (Prod.ext empty ((congrArg action empty).trans (map_zero _)))
  refine ⟨erased,?_⟩
  intro equal
  have stockZero : stock ordinal = 0 := equal.symm.trans (congrArg Prod.fst erased)
  have seen := actual_observation observation nontrivial half depth ordinal
  rw [stockZero,map_zero] at seen
  exact WidePositionGap.actual_division_physical_ne_zero observation nontrivial half depth ordinal seen.symm

end CP809Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

#eval IO.println "CP809_CONTROL + actual_birth_bank_order_and_paid_price_difference"
#eval IO.println "CP809_CONTROL + paid_graph_has_separate_observation_and_action_error"
#eval IO.println "CP809_CONTROL + source_effect_recovers_the_nonzero_original_graph"
#eval IO.println "CP809_CONTROL + actual_write_executes_native_R_and_full_relation"
#eval IO.println "CP809_CONTROL + diagonal_recovers_closed_graph_and_independent_next_K"
#eval IO.println "CP809_CONTROL + paid_terminal_keeps_its_whole_next_and_original_macro"
#eval IO.println "CP809_CONTROL - zero_inverse_round_erases_both_graphs_and_misses_actual_stock"
#eval IO.println "CP809_GATE_PASS positive=6 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
