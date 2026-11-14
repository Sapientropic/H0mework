import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.DivisionPriceStream

open BurnolPhysicalState HilbertInventory HilbertInventory.SecondConductorStock.SingleSlot
open scoped InnerProductSpace Topology
open Filter Set

open private physicalRead cotests_separate relation_actual from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner

namespace Image
export SourceGeneratedFiniteGram.PrefixImage (read residual energy Admitted)
end Image

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "denseHeight" => DenseDivisionPrice.height observation nontrivial half depth
local notation "addressAt" => DenseDivisionPrice.address observation nontrivial half depth

private def cotests (i : Nat) : Wide := covector (addressAt i)

local notation "tests" => cotests observation nontrivial half depth

/-- Read the actual original K line on the full position projection of this graph. -/
def prices (value : Wide) (i : Nat) : ℂ :=
  PhysicalPriceCountable.price (denseHeight i) (physicalRead value)

local notation "priceAt" => prices observation nontrivial half depth

private theorem price_read (value : Wide) : priceAt value = Image.read tests value := by
  funext i
  exact (PhysicalPriceCountable.price_is_original_K (denseHeight i) (physicalRead value)).trans
    (covector_read (addressAt i) value).symm

private theorem separates (value : Wide) (silent : ∀ i, Image.read tests value i = 0) : value = 0 :=
  cotests_separate observation nontrivial half depth value silent

abbrev Stream := Image.Admitted tests

local notation "Data" => Stream observation nontrivial half depth

/-- Admission is tested by actual finite residuals and bounded generated graph energy. -/
theorem original_price_image (data : Nat → ℂ) :
    ((∀ n, Image.residual tests data n = 0) ∧ BddAbove (range (Image.energy tests data))) ↔
      ∃ x : Wide, priceAt x = data := by
  refine (SourceGeneratedFiniteGram.PrefixImage.admitted_iff_image tests data).trans ?_
  constructor
  · rintro ⟨x,same⟩
    exact ⟨x,(price_read observation nontrivial half depth x).trans same⟩
  · rintro ⟨x,same⟩
    exact ⟨x,(price_read observation nontrivial half depth x).symm.trans same⟩

def capture (value : Wide) : Data :=
  ⟨priceAt value,by
    rw [price_read]
    exact (SourceGeneratedFiniteGram.PrefixImage.capture tests value).property⟩

local notation "recorded" => capture observation nontrivial half depth

/-- Only the admitted K stream enters the finite inverse and its limit. -/
def graph (data : Data) : Wide := SourceGeneratedFiniteGram.PrefixImage.realize tests data

local notation "decoded" => graph observation nontrivial half depth

theorem graph_capture (value : Wide) : decoded (recorded value) = value := by
  have same : recorded value =
      SourceGeneratedFiniteGram.PrefixImage.capture tests value :=
    Subtype.ext (price_read observation nontrivial half depth value)
  exact (congrArg decoded same).trans
    (SourceGeneratedFiniteGram.PrefixImage.realize_captured tests (separates observation nontrivial half depth) value)

theorem prices_graph (data : Data) : priceAt (decoded data) = data.val :=
  (price_read observation nontrivial half depth (decoded data)).trans
    (SourceGeneratedFiniteGram.PrefixImage.read_realized tests data)

/-- The input prices reconstruct the graph, execute its original R action and emit the next K stream. -/
def advance (data : Data) : Data := recorded (advanceWide c observation.mathlibZero (decoded data))

local notation "nextOf" => advance observation nontrivial half depth
local notation "relations" => DenseDivisionPrice.relationStock observation half

theorem exact_write (data : Data) :
    (decoded (nextOf data),relations (decoded (nextOf data))) =
      (advanceWide c observation.mathlibZero (decoded data),advanceStock c (relations (decoded data))) := by
  have action : decoded (nextOf data) = advanceWide c observation.mathlibZero (decoded data) :=
    graph_capture observation nontrivial half depth _
  exact Prod.ext action ((congrArg relations action).trans
    (DenseDivisionPrice.relation_advance observation nontrivial half (decoded data)).symm)

local notation "graphAt" => actualWide observation nontrivial half depth
local notation "classAt" => Rel.sourceClass observation nontrivial half depth
local notation "stockAt" => relationInventory observation nontrivial half depth

/-- The original cofinal graph and its original relation occurrence read back from the emitted price streams. -/
theorem actual_current_and_next (ordinal : Nat) :
    let current := recorded (graphAt ordinal)
    let next := nextOf current
    decoded current = graphAt ordinal ∧ decoded next = graphAt (ordinal+1) ∧
      next = recorded (graphAt (ordinal+1)) ∧
      relations (decoded current) = stockAt ordinal (classAt ordinal) ∧
      advanceStock c (relations (decoded current)) = stockAt (ordinal+1) (classAt (ordinal+1)) := by
  let current := recorded (graphAt ordinal)
  have old : decoded current = graphAt ordinal :=
    graph_capture observation nontrivial half depth _
  have actual : advanceWide c observation.mathlibZero (decoded current) = graphAt (ordinal+1) :=
    (congrArg (advanceWide c observation.mathlibZero) old).trans
      (actual_wide_next observation nontrivial half depth ordinal)
  have nextGraph : decoded (nextOf current) = graphAt (ordinal+1) :=
    (congrArg Prod.fst (exact_write observation nontrivial half depth current)).trans actual
  have beforeStock : relations (decoded current) = stockAt ordinal (classAt ordinal) :=
    (congrArg relations old).trans (relation_actual observation nontrivial half depth ordinal)
  have nextStock : advanceStock c (relations (decoded current)) = stockAt (ordinal+1) (classAt (ordinal+1)) :=
    (congrArg Prod.snd (exact_write observation nontrivial half depth current)).symm.trans
      ((congrArg relations nextGraph).trans (relation_actual observation nontrivial half depth (ordinal+1)))
  exact ⟨old,nextGraph,congrArg recorded actual,beforeStock,nextStock⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.DivisionPriceStream
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
