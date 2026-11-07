import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Inputs
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

abbrev PhysicalState := Actual.Current (Party := Party) (Good := Good) (Port := Bool)
  (Technology := Nat) (Instrument := Unit)

theorem an_explicit_physical_step_reads_its_original_raw
    (first second : PhysicalState) (same : first.raw = second.raw)
    (raw : InputAt) (explicit : raw ≠ .advance) :
    (Physical.Public.compile input first raw).next.raw = (Physical.Public.compile input second raw).next.raw := by
  rcases first with ⟨before,phase,remaining⟩
  rcases second with ⟨after,otherPhase,otherRemaining⟩
  dsimp only at same
  cases same
  cases raw with
  | advance => exact (explicit rfl).elim
  | primitive request =>
      unfold Physical.Public.compile
      dsimp only [Physical.Public.wordAt]
      cases Material.inspectList (fun item : ExecutionItem Party Good Bool Nat Unit =>
        (Physical.Public.interpreter input).Valid item.before item.request)
        ((Physical.Public.interpreter input).rawItems before [request.resign request.signer]) <;> rfl
  | execute word =>
      unfold Physical.Public.compile
      dsimp only [Physical.Public.wordAt]
      cases Material.inspectList (fun item : ExecutionItem Party Good Bool Nat Unit =>
        (Physical.Public.interpreter input).Valid item.before item.request)
        ((Physical.Public.interpreter input).rawItems before (word.map (fun request => request.resign request.signer))) <;> rfl
  | code submission => rfl
  | migrate pair => rfl
  | stopReview => rfl
  | review code => rfl

theorem an_explicit_prefix_reads_only_its_original_raw
    (first second : PhysicalState) (same : first.raw = second.raw) (past : List InputAt)
    (explicit : ∀ raw ∈ past, raw ≠ .advance) :
    (past.foldl (fun state raw => (Physical.Public.compile input state raw).next) first).raw =
      (past.foldl (fun state raw => (Physical.Public.compile input state raw).next) second).raw := by
  induction past generalizing first second with
  | nil => exact same
  | cons raw past later =>
      exact later _ _ (an_explicit_physical_step_reads_its_original_raw first second same raw
        (explicit raw List.mem_cons_self))
        (fun candidate present => explicit candidate (List.mem_cons_of_mem _ present))

def trialRawAfterRead (before : Raw) (nature : RequestAt) : Raw :=
  ((readInputs nature).foldl (fun state raw => (Physical.Public.compile input state raw).next)
    (⟨before,.seeking,[]⟩ : PhysicalState)).raw

local instance (origin current : Raw) (members : List Party)
    (word : RawEvent Party Good Bool Nat Unit) :
    Decidable (Review.Guarded.Checks (Macro.Public.Scope.checkInput input) origin current members word) := by
  unfold Review.Guarded.Checks
  infer_instance

theorem the_actual_trial_read_inputs_have_no_automatic_advance (nature : RequestAt) :
    ∀ raw ∈ readInputs nature, raw ≠ .advance := by
  intro raw present
  simp only [readInputs, beforeReadInputs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at present
  rcases present with ((baseline | ⟨request, _, same⟩) | discovery | probe) | fee
  all_goals subst raw; intro impossible; cases impossible

theorem the_original_public_prefix_has_the_checked_real_raw
    (before : PhysicalState) (nature : RequestAt) :
    ((readInputs nature).foldl (fun state raw => (Physical.Public.compile input state raw).next) before).raw =
      trialRawAfterRead before.raw nature :=
  an_explicit_prefix_reads_only_its_original_raw before ⟨before.raw,.seeking,[]⟩ rfl _
    (the_actual_trial_read_inputs_have_no_automatic_advance nature)

def trialRawAfterRiskLiability (before : Raw) (nature liability : RequestAt) : Raw :=
  (Physical.Public.compile input
    ⟨trialRawAfterRead before nature,.seeking,[]⟩ (.primitive liability)).next.raw

set_option maxHeartbeats 2400000 in
theorem both_source_liabilities_leave_every_trial_branch_able_to_pay_common_work :
    firstRawVariants.all (fun before => ([0,1,2] : List Nat).all (fun version =>
      [Control.Scenario.successLiability,Control.Scenario.failureLiability].all (fun liability => decide
        (Review.Guarded.Checks (Macro.Public.Scope.checkInput input) Control.Scenario.seed
          (trialRawAfterRiskLiability before (Control.Scenario.discovery version) liability) [0,1,2]
          (Functions.Revision.PublicPlan.executable Control.Scenario.commonWork))))) = true := by
  decide +kernel

theorem the_original_paid_trial_and_native_liability_cover_the_whole_current_scope
    (before : Raw) (original : before ∈ firstRawVariants) (version : Nat)
    (tested : version ∈ ([0,1,2] : List Nat)) (liability : RequestAt)
    (native : liability ∈ [Control.Scenario.successLiability,Control.Scenario.failureLiability])
    (members : List Party) :
    Review.Guarded.Checks (Macro.Public.Scope.checkInput input) Control.Scenario.seed
      (trialRawAfterRiskLiability before (Control.Scenario.discovery version) liability) members
      (Functions.Revision.PublicPlan.executable Control.Scenario.commonWork) := by
  have checked := (List.all_eq_true.mp ((List.all_eq_true.mp
    ((List.all_eq_true.mp both_source_liabilities_leave_every_trial_branch_able_to_pay_common_work)
      before original)) version tested)) liability native
  apply the_original_checks_cover_any_member_subset _ _ _ [0,1,2] members
  · intro person _
    have present : ∀ person : Party, person ∈ ([0,1,2] : List Party) := by decide +kernel
    exact present person
  · exact of_decide_eq_true checked

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
