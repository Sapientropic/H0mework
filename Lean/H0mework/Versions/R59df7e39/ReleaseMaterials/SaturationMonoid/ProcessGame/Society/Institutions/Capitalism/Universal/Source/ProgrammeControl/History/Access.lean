import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

structure Access where
  access : Entry input endpoint
  need : Entry input endpoint
  mode : Kernel.AccessMode
  accessHolder : Party
  recipient : Party
  port : Port
  accessGood : Good
  needGood : Good
  delivery : List (RouteLeg input endpoint)

namespace Access
variable (access : Access input endpoint)

def controller := input.law.controller (access.access.raw input).before.technology access.port

def NeedPaid : Prop := match (access.need.raw input).request.operation with
  | .use bearer goods kind => bearer = access.recipient ∧
      (kind = .necessity ∨ kind = .maintenance) ∧
      input.law.Valid (access.need.raw input).before (access.need.raw input).request ∧
      0 < amount Good goods access.needGood
  | _ => False

instance : Decidable (access.NeedPaid input endpoint) := by
  unfold NeedPaid
  cases (access.need.raw input).request.operation <;> infer_instance

def Accessed : Prop := match access.mode with
  | .acquired =>
      0 < flowAt (input.law.actualCredit (access.access.raw input).before (access.access.raw input).request)
        access.accessHolder access.accessGood ∧
      Follows input endpoint (access.accessHolder, access.accessGood) (access.access.position input + 1)
        access.delivery (access.recipient, access.needGood) (access.need.position input)
  | .used => access.access.position input = access.need.position input ∧
      access.accessHolder = access.recipient ∧ access.accessGood = access.needGood ∧ access.delivery = [] ∧
      0 < flowAt (input.law.actualDebit (access.access.raw input).before (access.access.raw input).request)
        access.recipient access.needGood

instance : Decidable (access.Accessed input endpoint) := by unfold Accessed; cases access.mode <;> infer_instance

def Checks : Prop :=
  input.law.Valid (access.access.raw input).before (access.access.raw input).request ∧
  access.port ∈ input.law.requiredPorts (access.access.raw input).before (access.access.raw input).request ∧
  PrivatePhase input.law (access.access.raw input).before access.port access.recipient ∧
  access.NeedPaid input endpoint ∧ access.Accessed input endpoint ∧
  privateControl input endpoint (target input endpoint) access.port

instance : Decidable (access.Checks input endpoint) := by unfold Checks; infer_instance

omit [DecidableEq Port] in
theorem source_need_uses_original_clock (checks : access.Checks input endpoint) :
    ∃ goods kind,
      (access.need.raw input).request.operation = .use access.recipient goods kind ∧
      ((kind = .necessity ∧ goods = input.law.necessities (access.need.raw input).before access.recipient) ∨
       (kind = .maintenance ∧ goods = input.law.mandatoryMaintenance (access.need.raw input).before access.recipient)) ∧
      0 < amount Good goods access.needGood := by
  have paid := checks.2.2.2.1
  unfold NeedPaid at paid
  cases operation : (access.need.raw input).request.operation with
  | use bearer goods kind =>
      simp only [operation] at paid
      rcases paid with ⟨rfl, necessary | maintenance, accepted, positive⟩
      · subst kind
        have source := accepted.2.2.1
        simp only [RawLaw.ClaimGuard, operation] at source
        exact ⟨goods, .necessity, rfl, Or.inl ⟨rfl, source⟩, positive⟩
      · subst kind
        have source := accepted.2.2.1
        simp only [RawLaw.ClaimGuard, operation] at source
        exact ⟨goods, .maintenance, rfl, Or.inr ⟨rfl, source⟩, positive⟩
  | _ => simp only [operation] at paid

end Access

#print axioms Access.source_need_uses_original_clock

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
