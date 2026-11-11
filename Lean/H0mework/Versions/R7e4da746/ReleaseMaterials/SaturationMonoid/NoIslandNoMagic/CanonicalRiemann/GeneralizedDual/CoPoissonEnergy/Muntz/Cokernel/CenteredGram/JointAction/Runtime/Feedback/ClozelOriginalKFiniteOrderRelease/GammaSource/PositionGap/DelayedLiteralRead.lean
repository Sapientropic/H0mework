import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedWordSeparation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState Finset HilbertInventory.SecondConductorStock.SingleSlot
open scoped BigOperators InnerProductSpace

open private raw_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback

namespace PriceGram
export SourceGeneratedFiniteGram (Coordinates)
export SourceGeneratedFiniteGram.Projection (synthesis coefficients predictable_readback predictable_source)
end PriceGram

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "seed" => (burnolPaCombApproximation 0:BurnolL2)
local notation "FK" => fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)
local notation "R" => burnolDirectRightResolventCLM c
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "price" => FixedFourierKFeedback.price observation nontrivial half depth

/-- The scalar columns use the same fixed K price at consecutive literal Division rows. -/
def literalPriceColumn (start : Nat) (indices : Finset Nat) (width : Nat)
    (j : indices) : PriceGram.Coordinates (Fin width) :=
  WithLp.toLp 2 fun n => price (start+j.val+n.val)

private theorem literal_columns_independent (start : Nat) :
    LinearIndependent ℂ (fun j : Nat => fun n : Nat => price (start+j+n)) := by
  have source : (fun j : Nat => fun n : Nat => price (start+j+n)) =
      (fun j : Nat => fun n : Nat => inner ℂ FK ((R^(m+(start+2)+n+j)) seed)) := by
    funext j n
    rw [← FixedFourierKFeedback.actual_whole_price observation nontrivial half depth, raw_power]
    rw [show m+(start+j+n+2)=m+(start+2)+n+j by omega]
  rw [source]
  exact actual_power_price_columns_independent observation nontrivial half _

private theorem exists_literal_price_window (start : Nat) (indices : Finset Nat) :
    ∃ width, (PriceGram.synthesis (literalPriceColumn observation nontrivial half depth start indices width)).ker = ⊥ := by
  classical
  let col := literalPriceColumn observation nontrivial half depth start indices
  let unseen (width : Nat) := (PriceGram.synthesis (col width)).ker
  have descending : Antitone unseen := by
    intro a b ordered coefficients noRead
    change PriceGram.synthesis (col b) coefficients = 0 at noRead
    change PriceGram.synthesis (col a) coefficients = 0
    ext n
    have read := congrArg (fun w : PriceGram.Coordinates (Fin b) => w ⟨n.val,n.isLt.trans_le ordered⟩) noRead
    simpa only [col, literalPriceColumn, PriceGram.synthesis, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, WithLp.ofLp_toLp,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using read
  have rankAttained : ∃ r : Nat, ∃ width, Module.finrank ℂ (unseen width) = r := ⟨_,0,rfl⟩
  obtain ⟨width, least⟩ := Nat.find_spec rankAttained
  have stable (later : Nat) (after : width ≤ later) : unseen width = unseen later := by
    have below := descending after
    by_contra different
    have strict := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne below (Ne.symm different))
    have minimal := Nat.find_min' rankAttained ⟨later,rfl⟩
    exact (not_lt_of_ge minimal) (strict.trans_le least.le)
  refine ⟨width,eq_bot_iff.mpr ?_⟩
  intro a noRead
  have all : ∑ j : indices, a j • (fun n : Nat => price (start+j.val+n)) = 0 := by
    funext n
    let later := max width (n+1)
    have carried : a ∈ unseen later := stable later (le_max_left _ _) ▸ noRead
    change PriceGram.synthesis (col later) a = 0 at carried
    have seen := congrArg (fun w : PriceGram.Coordinates (Fin later) =>
      w ⟨n,(Nat.lt_succ_self n).trans_le (le_max_right _ _)⟩) carried
    simp only [col, literalPriceColumn, PriceGram.synthesis, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at seen ⊢
    exact seen
  have independent := (literal_columns_independent observation nontrivial half depth start).comp
    (Subtype.val : indices → Nat) Subtype.val_injective
  have vanished := (Fintype.linearIndependent_iff.mp independent) (fun j => a j) all
  change a = 0
  ext j
  exact vanished j

/-- The source chooses its shortest complete fixed-price prefix among literal future rows. -/
def literalPriceHorizon (start : Nat) (indices : Finset Nat) : Nat := by
  classical
  exact Nat.find (exists_literal_price_window observation nontrivial half depth start indices)

private theorem literal_price_horizon_kernel (start : Nat) (indices : Finset Nat) :
    (PriceGram.synthesis (literalPriceColumn observation nontrivial half depth start indices
      (literalPriceHorizon observation nontrivial half depth start indices))).ker = ⊥ := by
  classical
  exact Nat.find_spec (exists_literal_price_window observation nontrivial half depth start indices)

def readPriceWindow (width : Nat) (field : BurnolL2) : PriceGram.Coordinates (Fin width) :=
  WithLp.toLp 2 fun n => inner ℂ FK ((R^n.val) field)

private theorem actual_price_window_write (start : Nat) (indices : Finset Nat) (width : Nat)
    (a : PriceGram.Coordinates indices) :
    readPriceWindow observation half width (∑ j : indices, a j • raw (start+j.val)) =
      PriceGram.synthesis (literalPriceColumn observation nontrivial half depth start indices width) a := by
  ext n
  simp only [readPriceWindow, literalPriceColumn, PriceGram.synthesis, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp, Finset.sum_apply, Pi.smul_apply]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, smul_eq_mul]
  apply sum_congr rfl
  intro j _
  rw [← FixedFourierKFeedback.actual_whole_price observation nontrivial half depth,
    raw_power, raw_power, ← mul_apply_eq_comp, ← pow_add]
  rw [show n.val+(m+(start+j.val+2))=m+(start+j.val+n.val+2) by omega]

local notation "horizon" => literalPriceHorizon observation nontrivial half depth
local notation "columns" => literalPriceColumn observation nontrivial half depth

/-- Read only the finite fixed-price window and reconstitute the original complete graph stock. -/
def graphFromPriceWindow (start : Nat) (indices : Finset Nat)
    (values : PriceGram.Coordinates (Fin (horizon start indices))) : Wide :=
  let recovered := PriceGram.coefficients (columns start indices (horizon start indices)) values
  ∑ j : indices, recovered j • stock (start+j.val)

/-- The native R reads recover both the complete original graph and its actual next graph. -/
theorem actual_literal_price_graph_recovery (start : Nat) (indices : Finset Nat) (a : PriceGram.Coordinates indices) :
    let values := readPriceWindow observation half (horizon start indices)
      (∑ j : indices, a j • raw (start+j.val))
    let recovered := graphFromPriceWindow observation nontrivial half depth start indices values
    recovered = (∑ j : indices, a j • stock (start+j.val)) ∧
      advanceWide c observation.mathlibZero recovered = (∑ j : indices, a j • stock (start+j.val+1)) := by
  dsimp only
  rw [actual_price_window_write observation nontrivial half depth]
  let col := columns start indices (horizon start indices)
  have injective := LinearMap.ker_eq_bot.mp
    (literal_price_horizon_kernel observation nontrivial half depth start indices)
  have coefficients : PriceGram.coefficients col (PriceGram.synthesis col a) = a := by
    apply injective
    have read := PriceGram.predictable_readback col (PriceGram.synthesis col a)
    rw [PriceGram.predictable_source, Submodule.starProjection_eq_self_iff.mpr
      (show PriceGram.synthesis col a ∈ (PriceGram.synthesis col).range from ⟨a,rfl⟩)] at read
    exact read
  unfold graphFromPriceWindow
  change (∑ j : indices, PriceGram.coefficients col (PriceGram.synthesis col a) j • stock (start+j.val)) =
      (∑ j : indices, a j • stock (start+j.val)) ∧ _
  rw [coefficients]
  refine ⟨rfl, ?_⟩
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_smul, actual_wide_next]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
