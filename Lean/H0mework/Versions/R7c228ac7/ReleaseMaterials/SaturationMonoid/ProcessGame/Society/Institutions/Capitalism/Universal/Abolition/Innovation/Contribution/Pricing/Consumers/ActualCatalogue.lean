import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualHistory

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers
noncomputable section

private theorem gross_routing_keeps_each_prior_request (front : RawEvent Bool Bool Bool Unit Unit)
    (keys : List (Bool × Bool × Bool)) (item : R) (original : item ∈ front) :
    item ∈ Joint.Planning.Menu.grossFrom Original.seed Original.grossClaim Original.shared front keys := by
  induction keys generalizing front with
  | nil => exact original
  | cons key rest ih =>
      dsimp only [Joint.Planning.Menu.grossFrom]
      apply ih
      split_ifs <;> first | exact List.mem_append_left _ original | exact original

private theorem productive_routing_keeps_each_prior_request (front : RawEvent Bool Bool Bool Unit Unit)
    (keys : List (Bool × Bool)) (item : R) (original : item ∈ front) :
    item ∈ Joint.Planning.Menu.productiveFrom Original.seed Original.grossClaim Original.shared true front keys := by
  induction keys generalizing front with
  | nil => exact original
  | cons key rest ih =>
      dsimp only [Joint.Planning.Menu.productiveFrom]
      apply ih
      split
      · exact List.mem_append_left _ original
      · exact original

theorem each_life_request_is_in_the_original_executed_programme (person : Bool) :
    life person ∈ Original.defaultWord := by
  have needs : life person ∈ Joint.Planning.Menu.needsWord Original.seed Original.grossClaim Original.shared := by
    unfold Joint.Planning.Menu.needsWord
    rw [Original.live_roster,Original.the_live_interpreter_is_the_same_public_physical_law]
    cases person <;> decide +kernel
  unfold Joint.Consumers.Compact.defaultWord Joint.Planning.Menu.plantPlan
  apply List.mem_append_left
  unfold Joint.Planning.Menu.materialPlan
  split
  · exact needs
  · apply productive_routing_keeps_each_prior_request
    apply gross_routing_keeps_each_prior_request
    exact List.mem_append_right _ needs

theorem each_life_request_is_in_the_actual_original_source_alphabet (person : Bool) :
    life person ∈ Material.Migration.sourceAlphabet (Root.sourceInput source) source.raw := by
  unfold Material.Migration.sourceAlphabet Root.sourceInput
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatten.mpr
  refine ⟨Original.defaultWord,?_,each_life_request_is_in_the_original_executed_programme person⟩
  unfold Abolition.Functions.Revision.Adaptive.consumedProposals
  apply List.mem_flatMap.mpr
  refine ⟨.execute Original.defaultWord,the_original_paid_programme_is_still_in_the_actual_quote_history,?_⟩
  simp [Abolition.Functions.Revision.Adaptive.proposalWords,Abolition.Functions.Revision.PublicPlan.proposedWords]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual
