import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Exit

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open PublicFunction.Mandate
open Quantities.Execution (endAt)

noncomputable section

def nominate : Req := request scope cutRaw false (.propose true)

def proposal : Reparation.Actual.Input Bool Bool Port Tech Unit := some (.primitive nominate)

private def nomination : Item := ⟨0, cut.raw, nominate⟩

private theorem nominate_lawful : active.Valid cut.raw nominate := by
  rw [cut_raw]
  decide +kernel

private theorem exact_grant_item : originalItems (seed := cut) opened.history proposal = [nomination] := by
  have originalLaw : (Physical.Public.interpreter cut.native.input).Valid cut.raw nominate := by
    rw [cut_input]
    exact PublicFunction.valid_physical active cut.raw nominate nominate_lawful
  have body := the_original_root_executes_the_generated_request cut nominate cut_ready cut_review rfl originalLaw
  change Optimality.Programme.Epoch.materialItems (queued cut nominate) ++ [] = _
  rw [List.append_nil]
  unfold Optimality.Programme.Epoch.materialItems
  rw [if_neg ((queued_is_ready_iff cut nominate).mpr cut_ready)]
  exact body.2.1

private theorem grant_at (site : Fin (originalItems (seed := cut) opened.history proposal).length) :
    (originalItems (seed := cut) opened.history proposal)[site] = nomination := by
  have listed : (originalItems (seed := cut) opened.history proposal)[site] ∈
      originalItems (seed := cut) opened.history proposal := List.getElem_mem _
  have same := congrArg (fun rows : List Item =>
    (originalItems (seed := cut) opened.history proposal)[site] ∈ rows) exact_grant_item
  exact List.mem_singleton.mp (same.mp listed)

private def firstGrant : Fin (originalItems (seed := cut) opened.history proposal).length :=
  ⟨0, by rw [exact_grant_item]; decide⟩

private theorem creates_grant : Grants nomination.request := by decide +kernel

private theorem original_nominee : true ∈ opened.roster :=
  List.mem_append_left _ (every_original_member_is_a_bearer cut id [] true (standing true))

private theorem no_material_question_for_the_nominee : questions cut nomination = [(false, .signature)] := by
  unfold questions materialQuestions financialQuestions
  change (false, (Exposure.signature : Exposure Bool Bool Unit)) ::
    (((Physical.Public.interpreter cut.native.input).actualDebit cut.raw nominate).filterMap _) ++ [] = _
  rw [cut_input, cut_raw]
  rfl

theorem refusing_nominee_still_passes_the_original_material_gate :
    Admitted opened.roster (withhold yes true) opened.history proposal := by
  constructor
  · intro item listed
    change item ∈ originalItems (seed := cut) opened.history proposal at listed
    rw [exact_grant_item] at listed
    have exactItem := List.mem_singleton.mp listed
    subst item
    change cut.native.input.law.Valid cut.raw nominate
    rw [cut_input]
    exact nominate_lawful
  · intro position question asked _
    change question ∈ questions cut (originalItems (seed := cut) opened.history proposal)[position] at asked
    rw [grant_at position, no_material_question_for_the_nominee] at asked
    have same := List.mem_singleton.mp asked
    subst question
    rfl

theorem the_same_original_grant_accepts_yes_and_refuses_the_nominees_no :
    grantRule opened.roster yes opened.history proposal firstGrant ∧
      ¬ grantRule opened.roster (withhold yes true) opened.history proposal firstGrant := by
  constructor
  · constructor
    · change ForcePeace.Renewal.IndependentNomination
        (originalItems (seed := cut) opened.history proposal)[firstGrant].request
      rw [grant_at]
      decide +kernel
    · intro _ _ _
      rfl
  · intro admitted
    have denied := any_withholding_original_bearer_vetoes_a_grant
      opened.roster yes opened.history proposal firstGrant true original_nominee admitted
    rw [grant_at] at denied
    exact denied creates_grant

theorem the_installed_root_cannot_emit_the_refused_grant
    (offer : Word → Word) :
    proposal ∉ (opened.decide (withhold yes true) offer proposal).emitted ∧
      Quantities.Recorded cut (opened.write (withhold yes true) offer proposal).history ∧
      MandateExit.ReadyAt cut [] (opened.write (withhold yes true) offer proposal).history
        (id : Bool → Bool) base scope noControl := by
  let decision := opened.decide (withhold yes true) offer proposal
  let reached := opened.write (withhold yes true) offer proposal
  refine ⟨?_, Quantities.record _ _, reached.continues⟩
  intro chosen
  exact the_same_original_grant_accepts_yes_and_refuses_the_nominees_no.2
    ((decision.every_emitted_input_is_lawful proposal chosen).2 firstGrant)

def coalition
    (rival : Nat → Word → Reparation.Actual.Input Bool Bool Port Tech Unit)
    (offer : Nat → Word → Word → Word) : Scheduler Bool Bool Port Tech Unit :=
  ⟨fun _ _ => .rival, fun _ _ => none, rival, offer⟩

theorem the_same_installed_bearer_keeps_release_against_every_adaptive_coalition
    (rival : Nat → Word → Reparation.Actual.Input Bool Bool Port Tech Unit)
    (offer : Nat → Word → Word → Word) (tick : Nat) :
    let reached := (coalition rival offer).guarded yes true opened tick
    Civil.Mandate.Released (endAt cut reached.history).raw ∧
      Quantities.Recorded cut reached.history ∧
      MandateExit.ReadyAt cut [] reached.history (id : Bool → Bool) base scope noControl := by
  have released : Civil.Mandate.Released (endAt cut opened.history).raw := by
    change Civil.Mandate.Released cut.raw
    rw [cut_raw]
    unfold Civil.Mandate.Released
    decide +kernel
  let reached := (coalition rival offer).guarded yes true opened tick
  exact ⟨(coalition rival offer).no_coalition_restores_the_original_authority_at_any_rival_prefix
    yes true opened installed released (every_original_member_is_a_bearer cut id [] true (standing true))
    tick (fun _ _ => rfl), Quantities.record _ _, reached.continues⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed
