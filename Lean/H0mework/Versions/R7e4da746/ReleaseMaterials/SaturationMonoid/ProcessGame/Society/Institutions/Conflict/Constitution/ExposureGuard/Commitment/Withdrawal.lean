import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Publication
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Release

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate
open Quantities.Execution (drain endAt endAt_append nativePayments next remainingNative)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
  {base : RawLaw Party Good Port Technology Instrument}
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)

local notation "opening" => endAt seed prior.history
local notation "word" => afterBacklog opening [ForcePeace.withdrawalInput scope opening actor]

/-- The original signed revocation occupies the first material visit
after the native work. The same dispatcher writes its fee and release. -/
theorem the_reserved_withdrawal_consumes_its_original_release_receipt
    (rival : Scheduler Party Good Port M Instrument) (person : Party)
    (installed : Emergency.Installed seed base scope) (review : ReviewAvailable opening)
    (valid : (law base scope).Valid (opening).raw (ForcePeace.withdrawal scope opening actor))
    (approved : Certified prior answers word) :
    let reached := visitAt prior answers word rival person approved (word).length
    let current := endAt seed reached.history
    Civil.Mandate.Released current.raw ∧ current.raw.clock = (opening).raw.clock ∧
      ∀ good, current.raw.stock actor good + flowAt (locate actor scope.revisionCost) actor good = (opening).raw.stock actor good := by
  let drained := endAt opening (drain opening)
  have length : (drain opening).length ≤ remainingNative opening := by
    simp only [drain, nativePayments, List.length_replicate, le_rfl]
  have original := ForcePeace.all_native_interleavings_spend_the_same_backlog_without_material_effects
    opening (drain opening) length
  have ready := (Quantities.Execution.the_first_exhausted_native_cut_is_the_original_paid_drain opening).1
  have available : ReviewAvailable drained := by
    unfold ReviewAvailable
    rw [show drained.control = (opening).control from original.2.2.1]
    exact review
  have licensed : (law base scope).Valid drained.raw (ForcePeace.withdrawal scope opening actor) := by
    rw [show drained.raw = (opening).raw from original.2.1]
    exact valid
  have atDrain : Emergency.Installed drained base scope := (installed.along prior.history).along _
  have receipt := ForcePeace.release_at_the_original_material_visit actor atDrain ready available licensed
  have reached : (visitAt prior answers word rival person approved (word).length).history = prior.history ++ word :=
    (a_commitment_completes_at_exactly_its_literal_dispatch_count prior answers word rival person approved _).mpr le_rfl
  dsimp only
  rw [reached, endAt_append, afterBacklog, endAt_append]
  exact ⟨receipt.released, receipt.clock.trans (congrArg (·.clock) original.2.1),
    fun good => (receipt.paid good).trans (congrArg (fun raw => raw.stock actor good) original.2.1)⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
