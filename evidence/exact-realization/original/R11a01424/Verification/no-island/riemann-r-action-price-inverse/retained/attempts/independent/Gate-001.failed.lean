import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.InverseDivisionPrice
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace ActionImageCertificate

open SourceGeneratedFiniteGram.PrefixImage
open scoped InnerProductSpace

variable {H F : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem true_adjoint_reads_the_same_prices_and_exposes_the_full_action_kernel
    (action : H →L[ℂ] F) (tests : Nat → F) (i : Nat)
    (separate : Function.Injective (read tests))
    (data : Admitted (ActionImage.pull action tests)) (value : H) :
    ActionImage.pull action tests i = action.adjoint (tests i) ∧
    (ActionImage.captureNext action tests value).val = read tests (action value) ∧
    read (ActionImage.pull action tests) value = read tests (action value) ∧
    (((∀ n, residual (ActionImage.pull action tests) data.val n = 0) ∧
      BddAbove (Set.range (energy (ActionImage.pull action tests) data.val))) ↔
      ∃ x : H, read tests (action x) = data.val) ∧
    (read tests (action value) = data.val ↔
      value - ActionImage.inverse action tests data ∈ LinearMap.ker action.toLinearMap) :=
  ⟨rfl,rfl,ActionImage.action_read action tests value,
    ActionImage.admitted_iff_action_image action tests data.val,
    ActionImage.complete_fibre action tests separate data value⟩

#eval IO.println "CP620_CONTROL + true_adjoint_reads_the_same_prices_and_exposes_the_full_action_kernel"

end ActionImageCertificate

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace InverseDivisionPriceCertificate

open BurnolPhysicalState SourceGeneratedFiniteGram
open scoped InnerProductSpace
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open private cotests price_read from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
open private coefficients native_injective tests_injective from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.InverseDivisionPrice

open private relation_actual from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice

attribute [local instance] OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot.wideInner

local instance wideNormed : NormedSpace ℂ Wide := wideInner.toNormedSpace

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "native" => advanceWide c observation.mathlibZero
local notation "tests" => cotests observation nontrivial half depth
local notation "pulled" => PrefixImage.ActionImage.pull (H := Wide) (F := Wide) native tests
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "graph" => DivisionPriceStream.graph observation nontrivial half depth
local notation "capture" => DivisionPriceStream.capture observation nontrivial half depth
local notation "nextOf" => DivisionPriceStream.advance observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "relations" => DenseDivisionPrice.relationStock observation half
local notation "classAt" => Rel.sourceClass observation nontrivial half depth
local notation "inventoryAt" => relationInventory observation nontrivial half depth
local notation "Incoming" => InverseDivisionPrice.Incoming observation nontrivial half depth
local notation "previous" => InverseDivisionPrice.predecessor observation nontrivial half depth
local notation "backTo" => InverseDivisionPrice.back observation nontrivial half depth
local notation "literal" => InverseDivisionPrice.literalNext observation nontrivial half depth
local notation "coefficient" => coefficients observation half

private theorem admissible_predecessor_data_use_the_original_R_action_and_literal_successor_prices
    (data : Nat → ℂ) (ordinal : Nat) :
    (((∀ n, PrefixImage.residual pulled data n = 0) ∧
      BddAbove (Set.range (PrefixImage.energy pulled data))) ↔
      ∃ x : Wide, priceAt (native x) = data) ∧
    (literal ordinal).val = priceAt (stock (ordinal+1)) :=
  ⟨InverseDivisionPrice.original_price_preimage observation nontrivial half depth data,rfl⟩

#eval IO.println "CP620_CONTROL + admissible_predecessor_data_use_the_original_R_action_and_literal_successor_prices"

private theorem the_same_inverse_recovers_the_old_graph_and_executes_the_original_coefficient_inverse
    (data : Incoming) (i : Nat) :
    Function.Injective native ∧
    graph (backTo data) = previous data ∧
    (nextOf (backTo data)).val = data.val ∧
    coefficient (previous data) i = inversePrefix c (coefficient (graph (nextOf (backTo data)))) i :=
  ⟨native_injective observation half,DivisionPriceStream.graph_capture observation nontrivial half depth (previous data),
    InverseDivisionPrice.exact_rewrite observation nontrivial half depth data,
    InverseDivisionPrice.predecessor_coefficients observation nontrivial half depth data i⟩

#eval IO.println "CP620_CONTROL + the_same_inverse_recovers_the_old_graph_and_executes_the_original_coefficient_inverse"

private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
  type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

private theorem literal_successor_prices_restore_both_original_graphs_relations_and_whole (ordinal : Nat) :
    let data := literal ordinal
    let old := backTo data
    let next := nextOf old
    graph old = stock ordinal ∧ relations (graph old) = inventoryAt ordinal (classAt ordinal) ∧
    graph next = stock (ordinal+1) ∧ relations (graph next) = inventoryAt (ordinal+1) (classAt (ordinal+1)) ∧
    LiteralWholeNext observation nontrivial half depth ordinal := by
  let data := literal ordinal
  let next := nextOf (backTo data)
  have paid := InverseDivisionPrice.actual_predecessor observation nontrivial half depth ordinal
  have nextGraph : graph next = stock (ordinal+1) :=
    (congrArg graph paid.2.2).trans (DivisionPriceStream.graph_capture observation nontrivial half depth _)
  have nextRelation := (congrArg relations nextGraph).trans (relation_actual observation nontrivial half depth (ordinal+1))
  exact ⟨paid.1,paid.2.1,nextGraph,nextRelation,literal_whole_next observation nontrivial half depth ordinal⟩

#eval IO.println "CP620_CONTROL + literal_successor_prices_restore_both_original_graphs_relations_and_whole"

private theorem the_zero_action_cannot_generate_the_actual_nonzero_current_prices (ordinal : Nat) :
    let data := priceAt (stock ordinal)
    let zeroAction : Wide →L[ℂ] Wide := 0
    ((∀ n, PrefixImage.residual tests data n = 0) ∧ BddAbove (Set.range (PrefixImage.energy tests data))) ∧
    ¬ ((∀ n, PrefixImage.residual (PrefixImage.ActionImage.pull zeroAction tests) data n = 0) ∧
      BddAbove (Set.range (PrefixImage.energy (PrefixImage.ActionImage.pull zeroAction tests) data))) := by
  let actual := stock ordinal
  let data := priceAt actual
  let zeroAction : Wide →L[ℂ] Wide := 0
  have actual_ne : actual ≠ 0 := by
    intro zero
    obtain ⟨test,nonzero⟩ := actual_single_slot_price_nonzero observation nontrivial half depth ordinal
    have silent := (actual_observation observation nontrivial half depth ordinal).symm.trans
      ((congrArg observe zero).trans (map_zero observe))
    exact nonzero ((congrArg (inner ℂ (burnolCompletedMellinRieszVector test.val : BurnolL2)) silent).trans
      (inner_zero_right _))
  refine ⟨(DivisionPriceStream.original_price_image observation nontrivial half depth data).mpr ⟨actual,rfl⟩,?_⟩
  intro admitted
  obtain ⟨x,read⟩ := (PrefixImage.ActionImage.admitted_iff_action_image zeroAction tests data).mp admitted
  have atZero : zeroAction x = 0 := rfl
  have sourceRead : PrefixImage.read tests actual = data := (price_read observation nontrivial half depth actual).symm
  have same : PrefixImage.read tests actual = PrefixImage.read tests 0 :=
    (sourceRead.trans read.symm).trans (congrArg (PrefixImage.read tests) atZero)
  exact actual_ne (tests_injective observation nontrivial half depth same)

#eval IO.println "CP620_CONTROL - the_zero_action_cannot_generate_the_actual_nonzero_current_prices"
#eval IO.println "CP620_GATE_PASS positive=4 negative=1"

end InverseDivisionPriceCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
