import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace CofinalSparseRecordCertificate

open BurnolPhysicalState Finset
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory (actual_relation_stock_next)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open scoped BigOperators

namespace S
export SourceGeneratedFiniteGram.CofinalRecord
  (Values sample columns replay withBirth birthResidual exists_birth_pivot decodeInsert decode_insert_exact
    pivotTime pivot_nonzero schedule schedule_prior schedule_last schedule_fresh)
export SourceGeneratedFiniteGram.Projection (coefficients synthesis)
end S

open private old_solver_synthesis from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalInsertion
open private replay_as_synthesis from SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
open private sourcePrices from
  SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord

run_cmd IO.eprintln "CP590_CONTROL + a_cofinal_pivot_recovers_each_coefficient_with_the_original_old_solver"
theorem a_cofinal_pivot_recovers_each_coefficient_with_the_original_old_solver
    {n : Nat} (src : Nat → Nat → ℂ) (rows : Fin n → Nat) (cutoff : Nat)
    (separates : LinearIndependent ℂ (fun j : Nat => fun t : Nat => src j (cutoff+t)))
    (faithful : Function.Injective (S.synthesis (S.columns src rows))) (a : S.Values n) (b : ℂ) :
    S.coefficients (S.columns src rows) (S.sample rows (S.replay src a)) = a ∧
    ∃ k : Nat, S.birthResidual src rows (cutoff+k) ≠ 0 ∧
      S.decodeInsert src rows (cutoff+k) (S.sample rows (S.withBirth src a b))
        (S.withBirth src a b (cutoff+k)) = (a,b) ∧
      S.decodeInsert src rows (cutoff+k) (S.sample rows (S.withBirth src a 0))
        (S.withBirth src a 0 (cutoff+k)) = (a,0) := by
  have old : S.coefficients (S.columns src rows) (S.sample rows (S.replay src a)) = a :=
    (congrArg (S.coefficients (S.columns src rows)) (replay_as_synthesis src rows a)).symm.trans
      (old_solver_synthesis src rows faithful a)
  obtain ⟨k,live⟩ := S.exists_birth_pivot src rows cutoff separates
  exact ⟨old,k,live,S.decode_insert_exact src rows faithful (cutoff+k) live a b,
    S.decode_insert_exact src rows faithful (cutoff+k) live a 0⟩

run_cmd IO.eprintln "CP590_CONTROL + the_empty_schedule_extends_by_one_strictly_later_original_address"
set_option cleanup.letToHave false in
theorem the_empty_schedule_extends_by_one_strictly_later_original_address
    (src : Nat → Nat → ℂ)
    (separates : ∀ cutoff : Nat, LinearIndependent ℂ (fun j : Nat => fun t : Nat => src j (cutoff+t)))
    (count : Nat) :
    let prior := (S.schedule src separates count).val;
    let grown := (S.schedule src separates (count+1)).val;
    let latest := grown (Fin.last count);
    (S.schedule src separates 0).val = (Fin.elim0 : Fin 0 → Nat) ∧
    (∀ i : Fin count, grown i.castSucc = prior i) ∧
    grown = Fin.snoc prior latest ∧
    (∀ i : Fin count, prior i < latest) ∧
    S.birthResidual src prior latest ≠ 0 ∧
    Function.Injective (S.synthesis (S.columns src grown)) := by
  refine ⟨rfl,S.schedule_prior src separates count,?_,S.schedule_fresh src separates count,?_,
    (S.schedule src separates (count+1)).property⟩
  · rw [S.schedule_last]
    rfl
  · rw [S.schedule_last]
    exact S.pivot_nonzero src separates (S.schedule src separates count).val

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "sch" => priceSchedule observation nontrivial half depth
local notation "recorded" => recordedPrices observation nontrivial half depth
local notation "native" => nativePriceAt observation half
local notation "decode" => decodeRecordedPrices observation nontrivial half depth
local notation "srcPrice" => sourcePrices observation nontrivial half depth

private def actualField (start count : Nat) (a : S.Values count) (b : ℂ) : BurnolL2 :=
  (∑ j : Fin count, a j • raw (start+j.val)) + b • raw (start+count)

run_cmd IO.eprintln "CP590_CONTROL + the_same_actual_field_retains_each_old_price_and_appends_one_new_read"
set_option cleanup.letToHave false in
theorem the_same_actual_field_retains_each_old_price_and_appends_one_new_read
    (start count : Nat) (a : S.Values count) (b : ℂ) :
    let field := actualField observation nontrivial half depth start count a b;
    let time := (sch start (count+1)).val (Fin.last count);
    (∀ i : Fin count, recorded start (count+1) field i.castSucc = recorded start count field i) ∧
    (∀ i : Fin count, (sch start count).val i < time) ∧
    recorded start (count+1) field (Fin.last count) = native field time ∧
    decode start count (recorded start count field) (native field time) = (a,b) :=
  ⟨actual_price_record_prior observation nontrivial half depth start count _,
    actual_price_record_fresh observation nontrivial half depth start count,rfl,
    actual_recorded_price_birth observation nontrivial half depth start count a b⟩

set_option cleanup.letToHave false in
private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
  type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

set_option cleanup.letToHave false in
private theorem literal_whole_next (ordinal : Nat) : LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

run_cmd IO.eprintln "CP590_CONTROL + the_sparse_record_writes_original_Gamma2_and_relation_successors"
set_option cleanup.letToHave false in
theorem the_sparse_record_writes_original_Gamma2_and_relation_successors
    (start ordinal : Nat) (a : S.Values (ordinal+1)) (b : ℂ) :
    type_of% (actual_sparse_price_writeback observation nontrivial half depth start ordinal a b) ∧
    LiteralWholeNext observation nontrivial half depth (start+ordinal) :=
  ⟨actual_sparse_price_writeback observation nontrivial half depth start ordinal a b,
    literal_whole_next observation nontrivial half depth (start+ordinal)⟩

private def oldPrediction (start count : Nat) (previous : S.Values count) : ℂ :=
  let prior := (sch start count).val
  let time := (sch start (count+1)).val (Fin.last count)
  S.replay (srcPrice start) (S.coefficients (S.columns (srcPrice start) prior) previous) time

run_cmd IO.eprintln "CP590_CONTROL - the_old_prediction_cannot_supply_the_latest_read_for_a_nonzero_birth"
set_option cleanup.letToHave false in
theorem the_old_prediction_cannot_supply_the_latest_read_for_a_nonzero_birth
    (start count : Nat) (a : S.Values count) (b : ℂ) (live : b ≠ 0) :
    let field := actualField observation nontrivial half depth start count a b;
    let prior := recorded start count field;
    let time := (sch start (count+1)).val (Fin.last count);
    native field time ≠ oldPrediction observation nontrivial half depth start count prior := by
  let field := actualField observation nontrivial half depth start count a b
  let prior := recorded start count field
  let time := (sch start (count+1)).val (Fin.last count)
  change native field time ≠ oldPrediction observation nontrivial half depth start count prior
  intro same
  have born := congrArg Prod.snd (actual_recorded_price_birth observation nontrivial half depth start count a b)
  change (native field time - oldPrediction observation nontrivial half depth start count prior) /
    S.birthResidual (srcPrice start) (sch start count).val time = b at born
  rw [same,sub_self,zero_div] at born
  exact live born.symm

run_cmd IO.eprintln "CP590_GATE_PASS positive=4 negative=1"

end CofinalSparseRecordCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
