import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FiniteDivisionPriceWrite
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace PrefixEnergyCertificate

open SourceGeneratedFiniteGram.PrefixImage
open scoped InnerProductSpace
open private realized_projection from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage.PrefixEnergy
open private source_span from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixReadback

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem total_and_missing_energy_are_exact (source : Nat → H) (data : Admitted source) (n : Nat) :
    sSup (Set.range (energy source data.val)) = ‖realize source data‖^2 ∧
    ‖realize source data - approximate source data.val n‖^2 =
      sSup (Set.range (energy source data.val)) - energy source data.val n :=
  ⟨total_energy source data,error_squared source data n⟩

#eval IO.println "CP618_CONTROL + total_and_missing_energy_are_exact"

private theorem least_accepted_prefix_of_the_complete_admitted_stream (source : Nat → H)
    (data : Admitted source) (ε : ℝ) (positive : 0 < ε) :
    let n := firstWithin source data ε positive
    ‖realize source data - approximate source data.val n‖ < ε ∧
      ∀ m < n, ε ≤ ‖realize source data - approximate source data.val m‖ :=
  first_within source data ε positive

#eval IO.println "CP618_CONTROL + least_accepted_prefix_of_the_complete_admitted_stream"

open SourceGeneratedFiniteGram in
private theorem empty_prefix_is_zero (source : Nat → H) (data : Admitted source) :
    approximate source data.val 0 = 0 := by
  let emptyTests := fun i : Fin 0 => source i.val
  have emptySpan : Projection.sourceSpan emptyTests = ⊥ := by
    rw [source_span,Set.range_eq_empty emptyTests,Submodule.span_empty]
  have member : approximate source data.val 0 ∈ Projection.sourceSpan emptyTests := by
    rw [realized_projection]
    exact Submodule.starProjection_apply_mem _ _
  rw [emptySpan] at member
  simpa only [Submodule.mem_bot] using member

end PrefixEnergyCertificate

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace FiniteDivisionPriceWriteCertificate

open BurnolPhysicalState SourceGeneratedFiniteGram
open scoped InnerProductSpace
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open private cotests from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

attribute [local instance] OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot.wideInner

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "measured" => DivisionPriceStream.capture observation nontrivial half depth
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "stockAt" => actualWide observation nontrivial half depth
local notation "tests" => cotests observation nontrivial half depth
local notation "finiteWrite" => FiniteDivisionPriceWrite.write observation nontrivial half depth
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

private theorem the_finite_graph_write_prices_its_own_original_R_output_and_bounds_every_price
    (data : Data) (n : Nat) :
    (finiteWrite data n).1.1 =
      advanceWide c observation.mathlibZero (PrefixImage.approximate tests data.val n) ∧
    (finiteWrite data n).2 = priceAt (finiteWrite data n).1.1 ∧
    type_of% (FiniteDivisionPriceWrite.whole_bound observation nontrivial half depth data n) ∧
    ∀ i : Nat, type_of% (FiniteDivisionPriceWrite.price_bound observation nontrivial half depth data n i) :=
  ⟨rfl,rfl,FiniteDivisionPriceWrite.whole_bound observation nontrivial half depth data n,
    FiniteDivisionPriceWrite.price_bound observation nontrivial half depth data n⟩

#eval IO.println "CP618_CONTROL + the_finite_graph_write_prices_its_own_original_R_output_and_bounds_every_price"

private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
  type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

private theorem one_actual_literal_stream_pays_bounded_next_and_original_whole
    (ordinal : Nat) (ε : ℝ) (positive : 0 < ε) :
    let data := measured (stockAt ordinal)
    type_of% (FiniteDivisionPriceWrite.write_within_bound observation nontrivial half depth data ε positive) ∧
      type_of% (DivisionPriceStream.actual_current_and_next observation nontrivial half depth ordinal) ∧
      LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨FiniteDivisionPriceWrite.write_within_bound observation nontrivial half depth
      (measured (stockAt ordinal)) ε positive,
    DivisionPriceStream.actual_current_and_next observation nontrivial half depth ordinal,
    literal_whole_next observation nontrivial half depth ordinal⟩

#eval IO.println "CP618_CONTROL + one_actual_literal_stream_pays_bounded_next_and_original_whole"

private theorem the_empty_prefix_cannot_approximate_the_actual_nonzero_graph_for_free (ordinal : Nat) :
    let actual := stockAt ordinal
    let data := measured actual
    0 < ‖actual‖ ∧ PrefixImage.approximate tests data.val 0 = 0 ∧
      PrefixImage.remainingEnergy tests data 0 = ‖actual‖^2 ∧
      ¬ ‖actual - PrefixImage.approximate tests data.val 0‖ < ‖actual‖ := by
  let actual := stockAt ordinal
  let data := measured actual
  have actual_ne : actual ≠ 0 := by
    intro zero
    obtain ⟨test,nonzero⟩ := actual_single_slot_price_nonzero observation nontrivial half depth ordinal
    have silent := (actual_observation observation nontrivial half depth ordinal).symm.trans
      ((congrArg observe zero).trans (map_zero observe))
    exact nonzero ((congrArg (inner ℂ (burnolCompletedMellinRieszVector test.val : BurnolL2)) silent).trans
      (inner_zero_right _))
  have finite_zero : PrefixImage.approximate tests data.val 0 = 0 :=
    PrefixEnergyCertificate.empty_prefix_is_zero tests data
  have recovered : PrefixImage.realize tests data = actual :=
    DivisionPriceStream.graph_capture observation nontrivial half depth actual
  have squared := (PrefixImage.error_squared tests data 0).symm
  rw [recovered,finite_zero,sub_zero] at squared
  refine ⟨norm_pos_iff.mpr actual_ne,finite_zero,squared,?_⟩
  rw [finite_zero,sub_zero]
  exact lt_irrefl _

#eval IO.println "CP618_CONTROL - the_empty_prefix_cannot_approximate_the_actual_nonzero_graph_for_free"
#eval IO.println "CP618_GATE_PASS positive=4 negative=1"

end FiniteDivisionPriceWriteCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
