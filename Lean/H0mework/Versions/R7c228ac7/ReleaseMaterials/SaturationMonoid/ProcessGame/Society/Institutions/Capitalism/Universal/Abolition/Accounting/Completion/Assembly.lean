import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Installation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Legacy
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (sourceDepth sourceCount : Nat)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)

local notation "original" => Financial.Installation.Runtime.frames input sourceDepth sourceCount
local notation "native" => Financial.Installation.Runtime.Frame.native
  (Financial.Installation.Runtime.frames input sourceDepth sourceCount)
local notation "visit" => Financial.Installation.Runtime.Frame.temporal input
  (Financial.Installation.Runtime.frames input sourceDepth sourceCount)

variable (origin : Root.Source.OriginAt input
    (Financial.Installation.Runtime.frames input sourceDepth sourceCount).native
    ((Financial.Installation.Runtime.frames input sourceDepth sourceCount).temporal input) claim)
  (word : RawEvent Party Good Port Technology Instrument)

local instance : Finite (native).root.toAuthoritativeRoot.source.projectionLaw.Projection :=
  (original).projectionFinite

/-- The observed context is read from tick 2's very root, including its installed
input face. No fresh liability or physical state is introduced at this seam. -/
def currentFamily := Root.Reentry.ofSource claim input
  (Root.Action.Installation.native input native visit claim word) visit word 1

theorem current_family_is_the_actual_observed_row :
    Root.Reentry.Frame.state claim (currentFamily input sourceDepth sourceCount claim word) =
      Root.Source.observed input native visit claim word :=
  Root.Reentry.ofSource_observed claim input
    (Root.Action.Installation.native input native visit claim word) visit word

include origin in
/-- All clauses refer to the same generated registered source and its actual
observed successor. Every later input is consumed before its next context is
returned; the finite contribution account is the original source's account. -/
theorem the_registered_root_carries_its_complete_account_into_each_actual_next_input :
    Root.Action.Runtime.SameSourceAccountingAt input native visit claim origin word (original).authority ∧
    ((Epoch.Finance.Legacy.generated input 0 0 ((original).cursor input).account).current.slots.map
      (fun slot => (Epoch.Finance.slotClaim input 0 0 slot).origin input 0 0)).Nodup ∧
    Contribution.OriginalClaimBounded input 0 0
      (Epoch.Finance.Legacy.generated input 0 0 ((original).cursor input).account).current ∧
    Root.Reentry.Frame.state claim (currentFamily input sourceDepth sourceCount claim word) =
      Root.Source.observed input native visit claim word ∧
    ∀ nextWord : RawEvent Party Good Port Technology Instrument,
      let frame := currentFamily input sourceDepth sourceCount claim word
      let next := Root.Reentry.Installation.successor claim frame nextWord
      (RootInquiryProcessNode.answered (Root.Reentry.Installation.presentation claim frame nextWord) PUnit.unit).erase =
        (⟨DebtActivationWorld.ExtendedNetwork (native).N (Responsibility.Family.activationLaw claim),
          ⟨next.V,next.root.toAuthoritativeRoot,next.visit⟩⟩ : AnyAuthoritativeRootCurrent) ∧
      Root.Reentry.Frame.state claim next = Responsibility.Family.State.advance claim
        (Root.Source.observed input native visit claim word) (Root.Source.actualLaw input) nextWord ∧
      (∀ key,(Root.Reentry.Frame.state claim next).remaining key ≤
        (Root.Source.observed input native visit claim word).remaining key) ∧
      (Root.Reentry.Frame.state claim next).raw.claims =
        (Root.Source.observed input native visit claim word).raw.claims := by
  refine ⟨Root.Action.Runtime.the_original_source_installs_and_consumes_its_complete_accounting
    input native visit claim origin word (original).authority,
    Contribution.Source.the_actual_translated_registered_account_has_one_slot_per_original_source
      input 0 0 sourceDepth sourceCount,
    Contribution.every_generated_claim_is_bounded_by_its_own_original_quantity input 0 0 _,
    current_family_is_the_actual_observed_row input sourceDepth sourceCount claim word,?_⟩
  intro nextWord
  let frame := currentFamily input sourceDepth sourceCount claim word
  have update := Root.Reentry.Installation.successor_reads_the_actual_updated_row claim frame nextWord
  rw [current_family_is_the_actual_observed_row] at update
  refine ⟨Root.Reentry.Installation.actual_process_resumption_is_the_same_native_next claim frame nextWord,update,?_,?_⟩
  · intro key
    rw [update]
    exact Responsibility.Family.State.actual_advance_never_refills_any_original_cell claim _ _ _ key
  · rw [update]
    exact Responsibility.Family.State.actual_advance_retains_every_original_financial_claim claim _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Completion
