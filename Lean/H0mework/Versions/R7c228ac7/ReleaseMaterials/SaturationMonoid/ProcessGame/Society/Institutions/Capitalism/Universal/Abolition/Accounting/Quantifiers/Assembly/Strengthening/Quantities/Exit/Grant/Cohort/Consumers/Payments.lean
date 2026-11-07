import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Contract
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Completed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Reader

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers

open Source.Program Abolition.Root.Registered PublicFunction.Repayment
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (lifeWord source_ready source_review source_input_is_the_original_registered_input source_parameters
    the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers (position proposal pay_from_the_existing_source)
open Redemption (sourceLaw sourceOrigin)

noncomputable section

def otherPosition : Position Bool Unit := ⟨(), false, true⟩
def both : Plan Bool Bool Bool Unit Unit :=
  ⟨[], [(position, 1), (otherPosition, 2)], Execution.primitiveScript lifeWord⟩

def afterFirst := Execution.endAt lifeSource (paidWord lifeSource (position, 1))
def afterSecond := Execution.endAt afterFirst (paidWord afterFirst (otherPosition, 2))

theorem originalFirst : PaidAt lifeSource position 1 :=
  pay_from_the_existing_source 1 (by norm_num) (by norm_num)

private theorem the_second_grant_passes_at_the_real_successor :
    Qualified (sourceLaw afterFirst) (sourceOrigin afterFirst) afterFirst.raw otherPosition 2 := by
  have actual := originalFirst.actual.raw_is_the_complete_original_execution 0
  change afterFirst.raw =
    (sourceLaw lifeSource).step ((sourceLaw lifeSource).step lifeSource.raw (issue (sourceLaw lifeSource) position 1))
      (Redemption.request (sourceLaw lifeSource) position 1) at actual
  have indices := Execution.the_actual_script_keeps_the_original_reader_indices lifeSource
    (paidWord lifeSource (position, 1))
  change afterFirst.native.input = lifeSource.native.input ∧
    afterFirst.native.depth = lifeSource.native.depth ∧ afterFirst.native.count = lifeSource.native.count at indices
  unfold sourceLaw sourceOrigin
  rw [indices.1, indices.2.1, indices.2.2, source_parameters.1, source_parameters.2.1, actual]
  unfold sourceLaw
  rw [source_input_is_the_original_registered_input, the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

theorem originalSecond : PaidAt afterFirst otherPosition 2 :=
  paid_grant_is_the_literal_original_issue_and_redemption _ _ _ originalFirst.ready originalFirst.available
    the_second_grant_passes_at_the_real_successor

theorem both_original_members_receive_actual_payments_at_one_root :
    FundedBatch (fundingStart lifeSource both) both.tenders ∧
      exitStart lifeSource 0 both = afterSecond := by
  constructor
  · exact .extend source_ready source_review (by norm_num) originalFirst
      (.extend originalFirst.ready originalFirst.available (by norm_num) originalSecond (.empty _))
  · change Execution.endAt lifeSource
      (paidWord lifeSource (position, 1) ++ paidWord afterFirst (otherPosition, 2)) = _
    exact Execution.endAt_append _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers
