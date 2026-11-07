import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Slices
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers.Material

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Slices.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Execution
open Exit.Grant.Cohort Exit.Grant.Cohort.Consumers
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)

noncomputable section

local notation "C" => Evolving.Epoch.Current (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit)
local notation "Request" => Option (Compile.RawInput Bool Bool Bool Unit Unit)
local notation "Script" => List Request

private def funding := paidPrefix lifeSource both
private def word := funding ++ both.exit

private theorem original_whole_word : compile lifeSource 0 both = word := by
  unfold compile chargedPrefix word funding
  simp [originalResponses]

private def fundingCut : Slice word.length :=
  ⟨0, funding.length, by simp [word]⟩

private def serviceCut : Slice word.length :=
  ⟨funding.length, both.exit.length, by simp [word]⟩

private def locate : Selection Request Bool := fun word service =>
  if within : funding.length ≤ word.length then
    if service then some ⟨funding.length, word.length - funding.length, by omega⟩
    else some ⟨0, funding.length, by simpa only [Nat.zero_add] using within⟩
  else none

private theorem located_funding : locate word false = some fundingCut := by
  simp [locate, fundingCut, word]

private theorem located_service : locate word true = some serviceCut := by
  simp [locate, serviceCut, word]

private def incoming (current : C) (word : Script) : ℚ :=
  (Exit.Redemption.sourceLaw current).totalCredit (inventory current word) false false

private def Issue : Bool → C → Script → Type
  | false, current, word => PLift (incoming current word < 1)
  | true, current, word => Clock.Window.Shortage current task word

private def inquiry : LocalInquiry C Request Issue
  | false, current, word => if short : incoming current word < 1 then some ⟨short⟩ else none
  | true, current, word => Clock.Window.inspect current task word

private def read : Bool → C → Script → EReal
  | false, current, word => ((incoming current word : ℝ) : EReal)
  | true, current, word => ((((endAt current word).raw.clock : ℚ) : ℝ) : EReal)

private theorem original_funding_clears :
    inquiry false (fundingCut.current lifeSource word) (fundingCut.body word) = none := by
  have body : fundingCut.body word = funding := by simp [Slice.body, fundingCut, word]
  have root : fundingCut.current lifeSource word = lifeSource := rfl
  have paid : incoming lifeSource funding = 1 :=
    original_population_grants_keep_gross_inflow_and_real_net_capacity_separate.1
  have within : ¬ incoming (fundingCut.current lifeSource word) (fundingCut.body word) < 1 := by
    rw [root, body, paid]
    exact lt_irrefl _
  simp only [inquiry, dif_neg within]

private theorem original_service_clears :
    inquiry true (serviceCut.current lifeSource word) (serviceCut.body word) = none := by
  have start : serviceCut.current lifeSource word = afterSecond := by
    unfold Slice.current Slice.before serviceCut word
    simp only [List.take_left]
    have original := both_original_members_receive_actual_payments_at_one_root.2
    simpa [exitStart, chargedPrefix, originalResponses, funding] using original
  have body : serviceCut.body word = both.exit := by simp [Slice.body, serviceCut, word]
  change Clock.Window.inspect (serviceCut.current lifeSource word) task (serviceCut.body word) = none
  have clears := (Clock.Window.passes_iff_every_original_service_commits_in_time _ _ _).mpr
    both_original_exit_services_commit_in_the_installed_window
  have same := congrArg (fun cut : C × Script => Clock.Window.inspect cut.1 task cut.2 = none)
    (congrArg₂ Prod.mk start body)
  exact same.mpr clears

theorem one_original_word_settles_funding_and_service_at_their_actual_cuts :
    readAt lifeSource locate id read word ∈ System.values lifeSource id (Slices.inspect lifeSource locate inquiry)
      (readAt lifeSource locate id read) ∧
      Recorded lifeSource word := by
  have actual : Settled lifeSource word := original_whole_word ▸ the_original_population_word_is_settled
  refine ⟨(the_simultaneous_domain_uses_only_slices_of_one_actual_whole_ledger _ _ _ _ _ _).mpr
    ⟨word, actual, ?_, rfl⟩, actual.toRecorded⟩
  intro key
  cases key
  · exact ⟨fundingCut, located_funding, original_funding_clears, record _ _,
      fundingCut.read_at_the_end_of_a_slice_uses_the_literal_original_successor lifeSource word⟩
  · exact ⟨serviceCut, located_service, original_service_clears, record _ _,
      serviceCut.read_at_the_end_of_a_slice_uses_the_literal_original_successor lifeSource word⟩

theorem omitting_the_funding_segment_keeps_the_original_named_obstruction :
    Recorded lifeSource [] ∧
      ∃ failure, Slices.inspect lifeSource locate inquiry false [] = some failure := by
  have missing : locate [] false = none := by
    have nonzero : 0 < funding.length := by decide +kernel
    simp [locate, not_le_of_gt nonzero]
  refine ⟨record _ _, ?_⟩
  unfold Slices.inspect
  split
  · rename_i found
    exact ⟨.absent found, rfl⟩
  · rename_i slice found
    rw [missing] at found
    cases found

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Slices.Consumers
