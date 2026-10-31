import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Source.ProgrammeControl
open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority
open Institutions.Capitalism.Universal.Root

theorem step_preserves_open (current : Current) (request : RequestAt)
    (opened : current.technology.1 = true) : (law.step current request).technology.1 = true := by
  unfold RawLaw.step
  split
  next accepted =>
    have policy := accepted.1.2
    cases operation : request.operation <;> simp only [RawLaw.paidStep, operation]
    all_goals try exact opened
    rename_i operator target
    have checked : operator = request.signer ∧ request.consents = [] ∧ target.1 = true ∧
        (current.technology.2 = true → target.2 = true) := by
      simpa only [RawLaw.operationAllowed, law, RawPolicy.eval, operation, decide_eq_true_eq] using policy
    exact checked.2.2.1
  next => exact opened

theorem execution_preserves_open (current : Current) (word : RawEvent Party Good Port Technology Unit)
    (opened : current.technology.1 = true) (index : Nat) :
    (law.execute current index word).final.technology.1 = true ∧
      ∀ item ∈ (law.execute current index word).items, item.before.technology.1 = true := by
  induction word generalizing current index with
  | nil => exact ⟨opened, by simp [RawLaw.execute]⟩
  | cons request tail ih =>
      obtain ⟨final, items⟩ := ih (law.step current request) (step_preserves_open current request opened) (index + 1)
      refine ⟨final, ?_⟩
      intro item inside
      simp only [RawLaw.execute, List.mem_cons] at inside
      rcases inside with rfl | inside
      · exact opened
      · exact items item inside

theorem next_preserves_open (current : Current) (word : RawEvent Party Good Port Technology Unit)
    (opened : current.technology.1 = true) : (law.next current word).technology.1 = true :=
  (execution_preserves_open current word opened 0).1

theorem no_private_phase (current : Current) (opened : current.technology.1 = true)
    (port : Port) (recipient : Party) : ¬ PrivatePhase law current port recipient := by
  intro phase
  have denied := phase.2
  cases port <;> simp [law, opened] at denied

theorem no_capital_kernel (current : Current) (word : RawEvent Party Good Port Technology Unit)
    (opened : current.technology.1 = true) : ¬ Nonempty (Kernel.CapitalRelationKernel law current word) := by
  rintro ⟨capital⟩
  have phase := (capital.original_control_and_reproduced_phase law current word).2.2.2
  exact no_private_phase _ (next_preserves_open current word opened) _ _ phase

theorem every_later_actual_current_is_open (later : Nat) :
    (source.currentAt (3 + later)).technology.1 = true := by
  induction later with
  | zero => rw [raw_current_frame]; decide +kernel
  | succ later ih =>
      rw [raw_current_frame]
      change (law.next (source.frameAt (3 + later)).raw _).technology.1 = true
      apply next_preserves_open
      rwa [← raw_current_frame]

theorem actual_root_capital_family_is_empty (later : Nat)
    (item : RootFace.Item source.input (ProgrammeHistory.visitAt source.input (3 + later))) :
    Structural.familyAtVisit source.input (ProgrammeHistory.visitAt source.input (3 + later)) item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  have itemOpen : item.val.before.technology.1 = true :=
    (execution_preserves_open (source.currentAt (3 + later))
      (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input (3 + later)).current)
      (every_later_actual_current_is_open later) 0).2 item.val item.property
  rcases Structural.family_has_original_source_provenance source.input _ item port member with
    title | surplus | history
  · obtain ⟨capital, _found, _same, phase⟩ := title
    exact no_private_phase _ itemOpen _ _ phase
  · obtain ⟨capital, _found, _same, phase⟩ := surplus
    exact no_private_phase _ itemOpen _ _ phase
  · obtain ⟨capital, _found, _same, _valid, _required, actor, _affected, phase⟩ := history
    exact no_private_phase _ itemOpen _ _ phase

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
