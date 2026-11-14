import SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage.ActionImage
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.InverseDivisionPrice

open BurnolPhysicalState HilbertInventory HilbertInventory.SecondConductorStock
open HilbertInventory.SecondConductorStock.SingleSlot
open scoped InnerProductSpace lp
open Set

open private actual_next_stock from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
open private cotests price_read separates from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
open private relation_actual from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner

namespace Image
export SourceGeneratedFiniteGram.PrefixImage (Admitted read residual energy)
export SourceGeneratedFiniteGram.PrefixImage.ActionImage
  (pull admitted_iff_action_image captureNext inverse forward_equation inverse_capture)
end Image

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "native" => advanceWide c observation.mathlibZero
local notation "tests" => cotests observation nontrivial half depth
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "graph" => DivisionPriceStream.graph observation nontrivial half depth
local notation "capture" => DivisionPriceStream.capture observation nontrivial half depth
local notation "nextOf" => DivisionPriceStream.advance observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "relations" => DenseDivisionPrice.relationStock observation half

private def position (x : Wide) : PositionField :=
  ⟨LogStock.field (base (toWhole x)),LogStock.field_mem (base (toWhole x))⟩

local notation "coefficient" => (fun x : Wide => (basis c).repr (position x))

private theorem coefficient_step (x : Wide) :
    nextCoefficients c (coefficient x) = coefficient (native x) :=
  actual_next_stock c (position x) (position (native x)) (LogStock.advance_field c (base (toWhole x)))

private theorem native_injective : Function.Injective native := by
  intro x y same
  let output := coefficient (native y)
  have xRead := (nextCoefficients_fibre c (coefficient x) output).1
    ((coefficient_step observation half x).trans (congrArg coefficient same))
  have yRead := (nextCoefficients_fibre c (coefficient y) output).1 (coefficient_step observation half y)
  have paid : coefficient x = coefficient y :=
    lp.ext (funext fun i => (xRead i).trans (yRead i).symm)
  have raw := congrArg (fun v : PositionField => (v : BurnolL2)) ((basis c).repr.injective paid)
  exact observe_injective (congrArg OriginalKCombPhysicalAction.physicalProjection raw)

private theorem tests_injective : Function.Injective (Image.read tests) := by
  intro x y same
  apply sub_eq_zero.mp
  apply separates observation nontrivial half depth
  intro i
  change inner ℂ (tests i) (x-y) = 0
  rw [inner_sub_right]
  exact sub_eq_zero.mpr (congrFun same i)

local notation "pulled" => Image.pull native tests
abbrev Incoming := Image.Admitted pulled
local notation "NextData" => Incoming observation nontrivial half depth

/-- The finite residual and energy here concern the original full predecessor graph. -/
theorem original_price_preimage (data : Nat → ℂ) :
    ((∀ n, Image.residual pulled data n = 0) ∧ BddAbove (range (Image.energy pulled data))) ↔
      ∃ value : Wide, priceAt (native value) = data := by
  refine (Image.admitted_iff_action_image native tests data).trans ?_
  constructor
  · rintro ⟨x,read⟩
    exact ⟨x,(price_read observation nontrivial half depth (native x)).trans read⟩
  · rintro ⟨x,read⟩
    exact ⟨x,(price_read observation nontrivial half depth (native x)).symm.trans read⟩

/-- Decode the old graph from the next prices by running the inverse of the pulled tests. -/
def predecessor (data : NextData) : Wide := Image.inverse native tests data

local notation "previous" => predecessor observation nontrivial half depth

def back (data : NextData) : Data := capture (previous data)

local notation "backTo" => back observation nontrivial half depth

theorem exact_rewrite (data : NextData) : (nextOf (backTo data)).val = data.val := by
  change priceAt (native (graph (capture (previous data)))) = data.val
  rw [DivisionPriceStream.graph_capture,price_read]
  exact Image.forward_equation native tests data

theorem predecessor_coefficients (data : NextData) (i : Nat) :
    coefficient (previous data) i =
      inversePrefix c (coefficient (graph (nextOf (backTo data)))) i := by
  have old := DivisionPriceStream.graph_capture observation nontrivial half depth (previous data)
  have next : graph (nextOf (backTo data)) = native (previous data) :=
    (congrArg Prod.fst (DivisionPriceStream.exact_write observation nontrivial half depth
      (backTo data))).trans (congrArg native old)
  rw [next]
  exact (nextCoefficients_fibre c _ _).mp (coefficient_step observation half (previous data)) i

/-- The actual data come from the literal successor itself. Its original receipt pays the inverse's admission. -/
def literalNext (ordinal : Nat) : NextData :=
  ⟨priceAt (stock (ordinal+1)),by
    rw [← actual_wide_next observation nontrivial half depth ordinal,price_read]
    exact (Image.captureNext native tests (stock ordinal)).property⟩

local notation "literal" => literalNext observation nontrivial half depth
local notation "classAt" => Rel.sourceClass observation nontrivial half depth
local notation "inventoryAt" => relationInventory observation nontrivial half depth

/-- The inverse of the original next prices restores the original predecessor, both relations and its actual write. -/
theorem actual_predecessor (ordinal : Nat) :
    let data := literal ordinal
    graph (backTo data) = stock ordinal ∧
      relations (graph (backTo data)) = inventoryAt ordinal (classAt ordinal) ∧
      nextOf (backTo data) = capture (stock (ordinal+1)) := by
  let data := literal ordinal
  have actual := actual_wide_next observation nontrivial half depth ordinal
  have measured : data = Image.captureNext native tests (stock ordinal) :=
    Subtype.ext ((congrArg priceAt actual.symm).trans (price_read observation nontrivial half depth _))
  have previousGraph : previous data = stock ordinal :=
    (congrArg previous measured).trans
      (Image.inverse_capture native tests (native_injective observation half)
        (tests_injective observation nontrivial half depth) (stock ordinal))
  have old : graph (backTo data) = stock ordinal :=
    (DivisionPriceStream.graph_capture observation nontrivial half depth _).trans previousGraph
  exact ⟨old,(congrArg relations old).trans (relation_actual observation nontrivial half depth ordinal),
    Subtype.ext (exact_rewrite observation nontrivial half depth data)⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.InverseDivisionPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
