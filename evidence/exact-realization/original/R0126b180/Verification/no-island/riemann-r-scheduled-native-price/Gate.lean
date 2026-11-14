import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledPriceMatrix
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace ScheduledNativePriceCertificate

open BurnolPhysicalState
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory (actual_relation_stock_next)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)

open private predecessor predecessor_next materialReceipt materialWhole material_whole_is_target paidAt from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativePrice

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "raw" => Native.raw observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "receiptAt" => scheduledMaterial observation nontrivial half depth
local notation "beforeAt" => predecessor observation nontrivial half depth

set_option cleanup.letToHave false in
private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
    type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

private theorem actual_receipt_original_whole_next (start count actor : Nat) (i : Fin count) :
    let before := beforeAt start count actor i
    receiptAt start count actor i = materialReceipt observation nontrivial half depth before ∧
      before+1 = actor+(schedule start count).val i ∧
      materialWhole observation nontrivial half depth before (paidAt observation nontrivial half depth before) =
        Native.calculatedTargetRaw observation nontrivial half depth before ∧
      LiteralWholeNext observation nontrivial half depth before :=
  ⟨rfl, predecessor_next observation nontrivial half depth start count actor i,
    material_whole_is_target observation nontrivial half depth _,
    literal_whole_next observation nontrivial half depth _⟩

#eval IO.println "CP591_CONTROL + actual_receipt_original_whole_next"

private theorem actual_preserved_receipt_and_paid_prices (start count actor : Nat) (i : Fin count) :
    receiptAt start (count+1) actor i.castSucc = receiptAt start count actor i ∧
      paidPriceSample observation nontrivial half depth start count actor i =
        recordedPrices observation nontrivial half depth start count (raw actor) i ∧
      paidPriceRecord observation nontrivial half depth start count actor =
        recordedPrices observation nontrivial half depth start count (raw actor) :=
  ⟨actual_scheduled_material_prior observation nontrivial half depth start count actor i,
    actual_paid_price_sample observation nontrivial half depth start count actor i,
    actual_paid_price_record observation nontrivial half depth start count actor⟩

#eval IO.println "CP591_CONTROL + actual_preserved_receipt_and_paid_prices"

set_option cleanup.letToHave false in
private theorem actual_matrix_and_birth_decoder (start count samples : Nat) (a : Record.Values count) (b : ℂ) :
    type_of% (actual_paid_mixture_record observation nontrivial half depth start count samples a b) ∧
      type_of% (actual_paid_birth_decode observation nontrivial half depth start count a b) :=
  ⟨actual_paid_mixture_record observation nontrivial half depth start count samples a b,
    actual_paid_birth_decode observation nontrivial half depth start count a b⟩

#eval IO.println "CP591_CONTROL + actual_matrix_and_birth_decoder"

set_option cleanup.letToHave false in
private theorem actual_dual_stock_writeback_and_next (start ordinal : Nat) (a : Record.Values (ordinal+1)) (b : ℂ) :
    type_of% (actual_paid_price_writeback observation nontrivial half depth start ordinal a b) ∧
      LiteralWholeNext observation nontrivial half depth (start+ordinal) :=
  ⟨actual_paid_price_writeback observation nontrivial half depth start ordinal a b,
    literal_whole_next observation nontrivial half depth (start+ordinal)⟩

#eval IO.println "CP591_CONTROL + actual_dual_stock_writeback_and_next"

private theorem actual_new_receipt_not_retained (start count actor : Nat) (i : Fin count) :
    receiptAt start (count+1) actor (Fin.last count) ≠ receiptAt start count actor i := by
  intro same
  have sameBefore : beforeAt start (count+1) actor (Fin.last count) = beforeAt start count actor i :=
    congrArg Sigma.fst same
  have sameTime : actor+(schedule start (count+1)).val (Fin.last count) =
      actor+(schedule start count).val i :=
    (predecessor_next observation nontrivial half depth start (count+1) actor (Fin.last count)).symm.trans
      ((congrArg (fun n : Nat => n+1) sameBefore).trans
        (predecessor_next observation nontrivial half depth start count actor i))
  exact (ne_of_gt (actual_price_record_fresh observation nontrivial half depth start count i))
    (Nat.add_left_cancel sameTime)

#eval IO.println "CP591_CONTROL - actual_new_receipt_not_retained"
#eval IO.println "CP591_GATE_PASS positive=4 negative=1"

end ScheduledNativePriceCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
