import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation.Installed
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Quantities

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]
  {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  {ordered : List TaskId} {task : TaskId → PublicTaskSpec Party Good}
  {reserved : Finset (Due.Service.Ordinal source past)}
  {held : Finset (Due.Service.Need ordered.toFinset task)} {budget : Party × Good → ℚ}
  (old : PaidPrefix source past ordered task reserved held budget)

local notation "AtCut" => Execution.endAt source past
local notation "Word" => renewalSuffix AtCut
local notation "Query" => installedQuery AtCut

variable (newReserved : Finset (Due.Service.Ordinal (Execution.endAt source past)
  (renewalSuffix (Execution.endAt source past))))

inductive RenewalResult
  | paid (installed : InstalledPaid AtCut) (extension : Extension old Word newReserved)
  | otherRoute (selected : selectedRenewal (Query).choice = false)
  | refusedBody (physical : (Query).physicalResult.isAccepted = false)
  | unpaid (issue : Refusal old Word newReserved)

/-- Only the renewal chosen and physically paid by the old root is
eligible to extend this handoff. The root's other dispositions remain
readable on the very same query. -/
def tryRenew : RenewalResult old newReserved :=
  if selected : selectedRenewal (Query).choice then
    if accepted : (Query).physicalResult.isAccepted then
      match extend old Word newReserved with
      | .inl extension => .paid ⟨selected, accepted⟩ extension
      | .inr issue => .unpaid issue
    else .refusedBody (Bool.eq_false_iff.mpr accepted)
  else .otherRoute (Bool.eq_false_iff.mpr selected)

theorem tryRenew_pays_iff :
    (∃ installed extension, tryRenew old newReserved = .paid installed extension) ↔
      InstalledPaid AtCut ∧ ∃ extension, extend old Word newReserved = .inl extension := by
  constructor
  · rintro ⟨installed, extension, seen⟩
    exact ⟨installed, extension, by
      unfold tryRenew at seen
      rw [dif_pos installed.selected, dif_pos installed.physical] at seen
      cases result : extend old Word newReserved with
      | inl later =>
        rw [result] at seen
        cases seen
        rfl
      | inr reason =>
        rw [result] at seen
        cases seen⟩
  · rintro ⟨installed, extension, seen⟩
    exact ⟨installed, extension, by
      unfold tryRenew
      rw [dif_pos installed.selected, dif_pos installed.physical, seen]⟩

theorem the_renewal_retains_its_installed_phase_and_whole_ledger
    (installed : InstalledPaid AtCut) (extension : Extension old Word newReserved) :
    (Execution.endAt source (past ++ Word)).control.phase = (AtCut).control.phase ∧
      Recorded source (past ++ Word) ∧ Evolving.Epoch.Current.ClosedAt (Execution.endAt source (past ++ Word)) := by
  refine ⟨?_, extension.combined.settlement.toRecorded, extension.combined.settlement.toRecorded.next⟩
  rw [Execution.endAt_append]
  exact installed.keeps_the_phase_after_the_actual_drain AtCut old.settlement.finished

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Continuation
