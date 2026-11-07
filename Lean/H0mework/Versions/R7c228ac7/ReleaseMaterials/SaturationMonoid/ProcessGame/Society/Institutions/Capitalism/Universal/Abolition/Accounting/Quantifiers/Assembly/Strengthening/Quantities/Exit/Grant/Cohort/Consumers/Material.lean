import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Material
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers.Population

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers

open Source.Program Abolition.Root.Registered
open Innovation.Contribution.Pricing.Consumers.Actual (source_input_is_the_original_registered_input)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers (position)
open Redemption (sourceLaw)

noncomputable section

private theorem one_law_for_both_actual_grants : sourceLaw afterFirst = sourceLaw lifeSource := by
  unfold sourceLaw
  rw [first_read_is_the_original_input]

private theorem original_unit_is_paid_at_rate_one :
    (sourceLaw lifeSource).settlementUnit () = false ∧ (sourceLaw lifeSource).settlementRate () = 1 := by
  unfold sourceLaw
  rw [source_input_is_the_original_registered_input]
  decide

private theorem the_original_grants_have_gross_one_and_outflow_two :
    grossReceived lifeSource both (false, false) = 1 ∧ fundingOutflow lifeSource both (false, false) = 2 := by
  let first := word (sourceLaw lifeSource) position 1
  let second := word (sourceLaw afterFirst) otherPosition 2
  have paidWords : allTenders lifeSource both =
      Execution.primitiveScript first ++ Execution.primitiveScript second := rfl
  have firstPaid := Execution.primitive_inventory originalFirst.actual 0
  have secondPaid := Execution.primitive_inventory originalSecond.actual 0
  change Execution.inventory lifeSource (Execution.primitiveScript first) =
    ((sourceLaw lifeSource).execute lifeSource.raw 0 first).items.map (fun item => { item with index := 0 }) at firstPaid
  change Execution.inventory afterFirst (Execution.primitiveScript second) =
    ((sourceLaw afterFirst).execute afterFirst.raw 0 second).items.map (fun item => { item with index := 0 }) at secondPaid
  have issuedSecond := originalSecond.qualified.1
  have settledSecond := originalSecond.qualified.2.2.1
  change (sourceLaw afterFirst).Valid afterFirst.raw (issue (sourceLaw afterFirst) otherPosition 2) at issuedSecond
  change (sourceLaw afterFirst).Valid ((sourceLaw afterFirst).step afterFirst.raw
    (issue (sourceLaw afterFirst) otherPosition 2)) (Redemption.request (sourceLaw afterFirst) otherPosition 2)
    at settledSecond
  rw [one_law_for_both_actual_grants] at issuedSecond settledSecond
  have issuedFirst := originalFirst.qualified.1
  have settledFirst := originalFirst.qualified.2.2.1
  change (sourceLaw lifeSource).Valid lifeSource.raw (issue (sourceLaw lifeSource) position 1) at issuedFirst
  change (sourceLaw lifeSource).Valid ((sourceLaw lifeSource).step lifeSource.raw
    (issue (sourceLaw lifeSource) position 1)) (Redemption.request (sourceLaw lifeSource) position 1) at settledFirst
  have items : Execution.inventory lifeSource (allTenders lifeSource both) =
      Execution.inventory lifeSource (Execution.primitiveScript first) ++
        Execution.inventory afterFirst (Execution.primitiveScript second) := by
    rw [paidWords, Execution.inventory_append]
    rfl
  change (sourceLaw lifeSource).totalCredit (Execution.inventory lifeSource (allTenders lifeSource both)) false false = 1 ∧
    (sourceLaw lifeSource).totalDebit (Execution.inventory lifeSource (allTenders lifeSource both)) false false = 2
  rw [items, firstPaid, secondPaid]
  dsimp only [first, second]
  simp only [word, RawLaw.execute, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, one_law_for_both_actual_grants, RawLaw.totalCredit, RawLaw.totalDebit, List.sum_cons,
    List.sum_nil, RawLaw.actualCredit, RawLaw.actualDebit, if_pos issuedFirst, if_pos settledFirst,
    if_pos issuedSecond, if_pos settledSecond]
  simp [RawLaw.credit, RawLaw.debit, issue, Redemption.request, position, otherPosition, locate, flowAt, amount,
    original_unit_is_paid_at_rate_one.1, original_unit_is_paid_at_rate_one.2]

theorem original_population_grants_keep_gross_inflow_and_real_net_capacity_separate :
    grossReceived lifeSource both (false, false) = 1 ∧
      fundingOutflow lifeSource both (false, false) = 2 ∧
      (exitStart lifeSource 0 both).raw.stock false false = lifeSource.raw.stock false false - 1 ∧
      (type_of% (the_full_original_population_really_enters_the_joint_exit_domain)) := by
  obtain ⟨incoming, outgoing⟩ := the_original_grants_have_gross_one_and_outflow_two
  have actual := the_entire_population_shares_one_post_charge_material_balance lifeSource both 0 (false, false)
  rw [incoming, outgoing] at actual
  have noCapture : captureNet lifeSource both 0 (false, false) = 0 := by
    simp [captureNet, actualCharges, Execution.originalResponses, Capture.netTaken,
      Execution.inventory, RawLaw.totalDebit, RawLaw.totalCredit]
  rw [noCapture] at actual
  change (exitStart lifeSource 0 both).raw.stock false false = lifeSource.raw.stock false false + 1 - 2 - 0 at actual
  exact ⟨incoming, outgoing, by linarith only [actual],
    the_full_original_population_really_enters_the_joint_exit_domain⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Consumers
