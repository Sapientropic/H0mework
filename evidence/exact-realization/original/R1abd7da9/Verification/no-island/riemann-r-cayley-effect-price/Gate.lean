import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionEffectPrice
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace CayleyEffectInverseCertificate

open SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse

private theorem a_linear_cayley_power_budget_pays_a_two_sided_bounded_effect_inverse
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (action : A) {d budget : ℝ} (positive : 0 < d)
    (growth : ∀ n : Nat, ‖(cayley action d)^n‖ ≤ ((n : ℝ)+1)*budget) :
    inverse action d * (action-1) = 1 ∧ (action-1) * inverse action d = 1 ∧
    ‖inverse action d‖ ≤ inverseBudget d budget := by
  have both := inverse_effect action positive growth
  exact ⟨both.1,both.2,inverse_norm action positive growth⟩

#eval IO.println "CP621_CONTROL + a_linear_cayley_power_budget_pays_a_two_sided_bounded_effect_inverse"

end CayleyEffectInverseCertificate

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace DivisionEffectPriceCertificate

open BurnolPhysicalState SourceGeneratedFiniteGram
open scoped InnerProductSpace
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open private cotests price_read separates from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
open private whole_power growth from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionEffectPrice
open private relation_actual from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice
open private closedStockNormed from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondStockCayleyGrowth

attribute [local instance] OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot.wideInner closedStockNormed

local instance wideNormed : NormedSpace ℂ Wide := wideInner.toNormedSpace

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "native" => advanceWide c observation.mathlibZero
local notation "tests" => cotests observation nontrivial half depth
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "graph" => DivisionPriceStream.graph observation nontrivial half depth
local notation "capture" => DivisionPriceStream.capture observation nontrivial half depth
local notation "nextOf" => DivisionPriceStream.advance observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "relations" => DenseDivisionPrice.relationStock observation half
local notation "classAt" => Rel.sourceClass observation nontrivial half depth
local notation "inventoryAt" => relationInventory observation nontrivial half depth
local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "effectAt" => DivisionEffectPrice.effect observation nontrivial half depth
local notation "recoverAt" => DivisionEffectPrice.recover observation nontrivial half depth
local notation "inverseAt" => DivisionEffectPrice.effectInverse observation half

private theorem the_original_lifted_cayley_budget_controls_both_native_effect_inverses (n : Nat) (x : Wide) :
    type_of% (whole_power observation half n x) ∧ type_of% (growth observation half n) ∧
    type_of% (DivisionEffectPrice.inverse_equations observation half) ∧
    type_of% (DivisionEffectPrice.inverse_bound observation half) :=
  ⟨whole_power observation half n x,growth observation half n,
    DivisionEffectPrice.inverse_equations observation half,DivisionEffectPrice.inverse_bound observation half⟩

#eval IO.println "CP621_CONTROL + the_original_lifted_cayley_budget_controls_both_native_effect_inverses"

private theorem one_complete_effect_stream_reads_next_minus_current_and_inverts_both_ways (data : Data) (i : Nat) :
    graph (effectAt data) = native (graph data) - graph data ∧
    (effectAt data).val i = (nextOf data).val i - data.val i ∧
    recoverAt (effectAt data) = data ∧ effectAt (recoverAt data) = data :=
  ⟨DivisionPriceStream.graph_capture observation nontrivial half depth _,
    congrFun (DivisionEffectPrice.effect_prices observation nontrivial half depth data) i,
    DivisionEffectPrice.recover_effect observation nontrivial half depth data,
    DivisionEffectPrice.effect_recover observation nontrivial half depth data⟩

#eval IO.println "CP621_CONTROL + one_complete_effect_stream_reads_next_minus_current_and_inverts_both_ways"

private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
  type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

private theorem the_actual_effect_recovers_both_original_graphs_relations_and_whole (ordinal : Nat) :
    let current := capture (stock ordinal)
    let recovered := recoverAt (effectAt current)
    graph recovered = stock ordinal ∧ graph (nextOf recovered) = stock (ordinal+1) ∧
    relations (graph recovered) = inventoryAt ordinal (classAt ordinal) ∧
    relations (graph (nextOf recovered)) = inventoryAt (ordinal+1) (classAt (ordinal+1)) ∧
    LiteralWholeNext observation nontrivial half depth ordinal := by
  let current := capture (stock ordinal)
  let recovered := recoverAt (effectAt current)
  have roundTrip : recovered = current := DivisionEffectPrice.recover_effect observation nontrivial half depth current
  have original := DivisionPriceStream.actual_current_and_next observation nontrivial half depth ordinal
  have oldGraph : graph recovered = stock ordinal := (congrArg graph roundTrip).trans original.1
  have nextGraph : graph (nextOf recovered) = stock (ordinal+1) :=
    (congrArg (fun data => graph (nextOf data)) roundTrip).trans original.2.1
  exact ⟨oldGraph,nextGraph,
    (congrArg relations oldGraph).trans (relation_actual observation nontrivial half depth ordinal),
    (congrArg relations nextGraph).trans (relation_actual observation nontrivial half depth (ordinal+1)),
    literal_whole_next observation nontrivial half depth ordinal⟩

#eval IO.println "CP621_CONTROL + the_actual_effect_recovers_both_original_graphs_relations_and_whole"

private theorem an_actual_nonzero_graph_cannot_have_all_zero_effect_prices (ordinal : Nat) :
    ¬ ∀ i, (effectAt (capture (stock ordinal))).val i = 0 := by
  let actual := stock ordinal
  let current := capture actual
  let changed := effectAt current
  have actual_ne : actual ≠ 0 := by
    intro zero
    obtain ⟨test,nonzero⟩ := actual_single_slot_price_nonzero observation nontrivial half depth ordinal
    have silent := (actual_observation observation nontrivial half depth ordinal).symm.trans
      ((congrArg observe zero).trans (map_zero observe))
    exact nonzero ((congrArg (inner ℂ (burnolCompletedMellinRieszVector test.val : BurnolL2)) silent).trans
      (inner_zero_right _))
  intro silent
  have read : PrefixImage.read tests (graph changed) = changed.val :=
    (price_read observation nontrivial half depth (graph changed)).symm.trans
      (DivisionPriceStream.prices_graph observation nontrivial half depth changed)
  have noEffect : graph changed = 0 :=
    separates observation nontrivial half depth (graph changed) (fun i => (congrFun read i).trans (silent i))
  have decoded : graph (recoverAt changed) = inverseAt (graph changed) :=
    DivisionPriceStream.graph_capture observation nontrivial half depth _
  have roundTrip : graph (recoverAt changed) = actual :=
    (congrArg graph (DivisionEffectPrice.recover_effect observation nontrivial half depth current)).trans
      (DivisionPriceStream.graph_capture observation nontrivial half depth actual)
  exact actual_ne (roundTrip.symm.trans
    (decoded.trans ((congrArg (fun x => inverseAt x) noEffect).trans (map_zero inverseAt))))

#eval IO.println "CP621_CONTROL - an_actual_nonzero_graph_cannot_have_all_zero_effect_prices"
#eval IO.println "CP621_GATE_PASS positive=4 negative=1"

end DivisionEffectPriceCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
