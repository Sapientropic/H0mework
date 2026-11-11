import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativePrice

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState Finset
open HilbertInventory (modelInventory advanceStock)
open HilbertInventory.SecondConductorStock.SingleSlot
open scoped BigOperators InnerProductSpace

open private toRange from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private rebuildBirth from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.BornPriceWriteback

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => burnolDirectRightResolventCLM c
local notation "raw" => Native.raw observation nontrivial half depth
local notation "paid" => paidPriceRecord observation nontrivial half depth

/-- Each column is read from the original material receipts of its own source actor. -/
def paidMixtureRecord (start count samples : Nat) (a : Record.Values count) (b : ℂ) :
    Record.Values samples :=
  (∑ j : Fin count, a j • paid start samples (start+j.val)) + b • paid start samples (start+count)

theorem actual_paid_mixture_record (start count samples : Nat) (a : Record.Values count) (b : ℂ) :
    paidMixtureRecord observation nontrivial half depth start count samples a b =
      recordedPrices observation nontrivial half depth start samples
        ((∑ j : Fin count, a j • raw (start+j.val)) + b • raw (start+count)) := by
  ext row
  simp only [paidMixtureRecord, actual_paid_price_record, recordedPrices, Record.sample,
    WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sum, WithLp.ofLp_toLp,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, nativePriceAt,
    map_add, map_smul, map_sum, inner_add_right, inner_sum, inner_smul_right]

/-- The old rooted samples and the one new rooted sample drive the same exact birth decoder. -/
theorem actual_paid_birth_decode (start count : Nat) (a : Record.Values count) (b : ℂ) :
    decodeRecordedPrices observation nontrivial half depth start count
      (paidMixtureRecord observation nontrivial half depth start count count a b)
      ((paidMixtureRecord observation nontrivial half depth start count (count+1) a b) (Fin.last count)) = (a,b) := by
  rw [actual_paid_mixture_record, actual_paid_mixture_record]
  exact actual_recorded_price_birth observation nontrivial half depth start count a b

theorem actual_paid_price_writeback (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ) :
    let previous := paidMixtureRecord observation nontrivial half depth start (ordinal+1) (ordinal+1) a b
    let latest := (paidMixtureRecord observation nontrivial half depth start (ordinal+1) (ordinal+2) a b)
      (Fin.last (ordinal+1))
    let decoded := decodeRecordedPrices observation nontrivial half depth start (ordinal+1) previous latest
    let rebuilt := rebuildBirth observation nontrivial half depth start ordinal (toRange ordinal decoded.1,decoded.2)
    let next := rebuildBirth observation nontrivial half depth (start+1) ordinal (toRange ordinal a,b)
    (advanceWide c observation.mathlibZero rebuilt.1,
      advanceStock c (modelInventory observation nontrivial half rebuilt.2)) =
      (next.1, modelInventory observation nontrivial half next.2) := by
  have action : R (raw (start+ordinal)) = raw (start+(ordinal+1)) := by
    rw [← Nat.add_assoc, OriginalKCombFirstFullSourceDynamics.raw_successor,
      OriginalKCombCofinalRAction.original_R_direct]
    rfl
  have same := actual_sparse_price_writeback observation nontrivial half depth start ordinal a b
  dsimp only at same ⊢
  rw [action] at same
  rw [actual_paid_mixture_record, actual_paid_mixture_record]
  exact same

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
