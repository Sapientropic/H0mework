import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Initial

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
private theorem step_control (before : Actual.State (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (raw : Compile.RawInput Party Good Port Technology Instrument) :
    (Physical.Public.compile input before raw).next.phase = before.phase ∧
      (Physical.Public.compile input before raw).next.remaining = before.remaining := by
  cases Physical.Public.compile input before raw <;> exact ⟨rfl,rfl⟩

omit [DecidableEq Port] in
private theorem fold_control (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (before : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    (past.foldl (fun current raw => (Physical.Public.compile input current raw).next) before).phase = before.phase ∧
      (past.foldl (fun current raw => (Physical.Public.compile input current raw).next) before).remaining = before.remaining := by
  induction past generalizing before with
  | nil => exact ⟨rfl,rfl⟩
  | cons raw rest induction =>
      have later := induction ((Physical.Public.compile input before raw).next)
      have first := step_control input before raw
      exact ⟨later.1.trans first.1,later.2.trans first.2⟩

theorem original_control_is_read_without_replaying_the_material_body
    (depth count prefixLimit renewalLimit : Nat)
    (oldPast past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast past).phase =
        (Physical.stateAt input depth count prefixLimit renewalLimit oldPast).phase ∧
      (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast past).remaining =
        (Physical.stateAt input depth count prefixLimit renewalLimit oldPast).remaining :=
  fold_control input past _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source
