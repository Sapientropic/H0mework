import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualReturnNative

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 155000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn

open BurnolPhysicalState Filter
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open SourceGeneratedFiniteGram
open SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse (finite_observed_error)
open scoped Topology InnerProductSpace

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner

attribute [local instance] DivisionEffectPrice.wideNormed

open private cotests price_read from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
open private cotests_separate from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "d" => sourceDamping c
local notation "native" => advanceWide c observation.mathlibZero
local notation "stock" => actualWide observation nontrivial half depth
local notation "fit" => currentFit observation nontrivial half depth ordinal
local notation "cov" => cotests observation nontrivial half depth
local notation "data" => difference observation nontrivial half depth ordinal
local notation "graph" => PriceStream.graph observation nontrivial half depth
local notation "price" => PriceStream.prices observation nontrivial half depth
local notation "result" => paid observation nontrivial half depth ordinal
local notation "relations" => DenseDivisionPrice.relationStock observation half

open private closedStockNormed from H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondStockCayleyGrowth
attribute [local instance] closedStockNormed

open private growth from H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionEffectPrice

private theorem graph_inverse :
    Geom.inverse native d (graph data) = stock ordinal := by
  let action : Wide →L[ℂ] Wide := native
  let point := stock ordinal
  let response := graph data
  have effect : response = (action-1) point :=
    difference_graph observation nontrivial half depth ordinal
  let recover := DivisionEffectPrice.effectInverse observation half
  have solved : recover ((action-1) point) = point :=
    congrArg (fun act : Wide →L[ℂ] Wide => act point)
      (DivisionEffectPrice.inverse_equations observation half).1
  exact (congrArg recover effect).trans solved

attribute [local irreducible] currentFit observedGraph observedError difference paid actualWide in
theorem finite_graph_error (n m : Nat) :
    ‖fit n m-stock ordinal‖ ≤ errorBudget observation nontrivial half depth ordinal n m := by
  let datum : Wide := graph data
  let projection : Wide := observedGraph observation nontrivial half depth ordinal n
  have resolved := graph_inverse observation nontrivial half depth ordinal
  have source := finite_source observation nontrivial half depth ordinal n m
  have read := observed_error_eq observation nontrivial half depth ordinal n
  have budget : errorBudget observation nontrivial half depth ordinal n m =
      Geom.noisyBudget d (linearBudget c) m ‖datum‖ (observedError observation nontrivial half depth ordinal n) := rfl
  exact @finite_observed_error Wide (inferInstanceAs (NormedAddCommGroup Wide)) DivisionEffectPrice.wideNormed
    (inferInstanceAs (CompleteSpace Wide)) native d (linearBudget c) (sourceDamping_pos c)
    (linearBudget_nonnegative c) (growth observation half) datum projection (stock ordinal) (fit n m) m
    (observedError observation nontrivial half depth ordinal n)
    (errorBudget observation nontrivial half depth ordinal n m) resolved source read budget

private theorem data_prefix_tendsto :
    Tendsto (observedGraph observation nontrivial half depth ordinal) atTop (𝓝 (graph data)) := by
  have exactPrice : PrefixImage.read cov (graph data) = (data).val :=
    PrefixImage.read_realized cov data
  let tests : Nat → Wide := cov
  let point : Wide := graph data
  have direct := @PrefixReadback.inverse_tendsto Wide (inferInstanceAs (NormedAddCommGroup Wide))
    wideInner (inferInstanceAs (CompleteSpace Wide)) tests
    (cotests_separate observation nontrivial half depth) point
  change Tendsto (PrefixImage.approximate tests (data).val) atTop (𝓝 point)
  exact (congrArg (fun stream : Nat → ℂ =>
    Tendsto (PrefixImage.approximate tests stream) atTop (𝓝 point)) exactPrice).mp direct

/-- Both finite cutoffs use the graph's observed energy and actual action budget. -/
theorem diagonal (n : Nat) :
    ‖(result n n).2.1-stock ordinal‖ ≤ errorBudget observation nontrivial half depth ordinal n n := by
  have paidRead : (result n n).2.1 = fit n n :=
    congrArg (fun value : Wide × Wide × Wide => value.2.1) (paid_source observation nontrivial half depth ordinal n n)
  exact (congrArg (fun value : Wide => ‖value-stock ordinal‖ ≤
    errorBudget observation nontrivial half depth ordinal n n) paidRead).mpr
    (finite_graph_error observation nontrivial half depth ordinal n n)

attribute [local irreducible] currentFit errorBudget observedError difference paid in
theorem actual_graph_tendsto :
    Tendsto (fun n => (result n n).2.1) atTop (𝓝 (stock ordinal)) := by
  let budget := Geom.inverseBudget d (linearBudget c)
  let whole := graph data
  let priceError := observedError observation nontrivial half depth ordinal
  have converges := data_prefix_tendsto observation nontrivial half depth ordinal
  have prices : Tendsto priceError atTop (𝓝 0) := by
    have moved := ((tendsto_const_nhds (x := whole)).sub converges).norm
    rw [sub_self, norm_zero] at moved
    exact moved.congr' (Eventually.of_forall fun n => (observed_error_eq observation nontrivial half depth ordinal n).symm)
  have left := prices.const_mul budget
  have right := ((Geom.linear_retention_tendsto (sourceDamping_pos c)).const_mul
    (linearBudget c)).mul_const (budget*‖whole‖)
  have total := left.add right
  simp only [mul_zero, zero_mul, zero_add] at total
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (diagonal observation nontrivial half depth ordinal) ?_
  exact total.congr' (Eventually.of_forall fun n => by
    simp only [errorBudget, Geom.noisyBudget, budget, whole, priceError, mul_assoc (linearBudget c)])

private theorem next_source (n m : Nat) :
    (result n m).2.2 = native (result n m).2.1 := by
  have executed := paid_source observation nontrivial half depth ordinal n m
  exact (congrArg (fun value : Wide × Wide × Wide => value.2.2) executed).trans
    (congrArg (fun value : Wide × Wide × Wide => native value.2.1) executed).symm

theorem actual_next_graph :
    Tendsto (fun n => (result n n).2.2) atTop (𝓝 (stock (ordinal+1))) := by
  have arrived := ((native).continuous.tendsto (stock ordinal)).comp
    (actual_graph_tendsto observation nontrivial half depth ordinal)
  have next : native (stock ordinal) = stock (ordinal+1) :=
    actual_wide_next observation nontrivial half depth ordinal
  have reindexed := (congrArg (fun x : Wide => Tendsto (fun n => native (result n n).2.1) atTop (𝓝 x)) next).mp arrived
  exact reindexed.congr' (Eventually.of_forall fun n => (next_source observation nontrivial half depth ordinal n n).symm)

theorem actual_next_K (i : Nat) :
    Tendsto (fun n => price (result n n).2.2 i) atTop
      (𝓝 (price (stock (ordinal+1)) i)) := by
  let meter : Wide →L[ℂ] ℂ := innerSL ℂ (cov i)
  have actual (x : Wide) : price x i = meter x :=
    congrFun (price_read observation nontrivial half depth x) i
  simp only [actual]
  exact (meter.continuous.tendsto _).comp (actual_next_graph observation nontrivial half depth ordinal)

theorem actual_next_relation :
    ∀ n m, relations (result n m).2.2 =
      advanceStock c (relations (result n m).2.1) := by
  intro n m
  exact (congrArg relations (next_source observation nontrivial half depth ordinal n m)).trans
    (DenseDivisionPrice.relation_advance observation nontrivial half (result n m).2.1).symm

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "consume_actual_wide_return"

theorem consume_actual_wide_return (n m : Nat) :
    type_of% (actual_paid_graph_return observation nontrivial half depth ordinal n m) ∧
    type_of% (finite_graph_error observation nontrivial half depth ordinal n m) ∧
    type_of% (actual_graph_tendsto observation nontrivial half depth ordinal) ∧
    type_of% (actual_next_graph observation nontrivial half depth ordinal) ∧
    type_of% (actual_next_relation observation nontrivial half depth ordinal) ∧
    (∀ i, type_of% (actual_next_K observation nontrivial half depth ordinal i)) ∧
    type_of% (DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth ordinal) :=
  ⟨actual_paid_graph_return observation nontrivial half depth ordinal n m,
    finite_graph_error observation nontrivial half depth ordinal n m,
    actual_graph_tendsto observation nontrivial half depth ordinal,
    actual_next_graph observation nontrivial half depth ordinal,
    actual_next_relation observation nontrivial half depth ordinal,
    fun i => actual_next_K observation nontrivial half depth ordinal i,
    DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth ordinal⟩

end WideResidualReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
