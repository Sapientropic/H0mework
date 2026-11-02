import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)

inductive PrimitiveVerdict : Type
  | accepted (legal : input.law.Valid current.raw request)
  | refused (failure : ¬ input.law.Valid current.raw request)

def inspectPrimitive : PrimitiveVerdict input current request :=
  if legal : input.law.Valid current.raw request then .accepted legal else .refused legal

structure PrimitiveAt where
  private mk ::
  rawRequest : Request Party Good Port Technology Instrument
  source_exact : rawRequest = request
  verdict : PrimitiveVerdict input current rawRequest
  verdict_exact : HEq verdict (inspectPrimitive input current request)

def primitive : PrimitiveAt input current request := ⟨request, rfl, inspectPrimitive input current request, HEq.rfl⟩

def primitiveNext : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨input.law.step current.raw request, .seeking, current.remaining⟩

theorem primitive_keeps_the_original_request_and_pending_code :
    (primitive input current request).rawRequest = request ∧
      (primitiveNext input current request).remaining = current.remaining ∧
      (primitiveNext input current request).raw.clock = current.raw.clock ∧
      (primitiveNext input current request).raw.round = current.raw.round := by
  refine ⟨rfl, rfl, ?_⟩
  unfold primitiveNext RawLaw.step
  split <;> exact ⟨rfl, rfl⟩

theorem primitive_refusal_preserves_physical_current (failure : ¬ input.law.Valid current.raw request) :
    (primitiveNext input current request).raw = current.raw := by
  simp only [primitiveNext, RawLaw.step, if_neg failure]

theorem primitive_nonfinancial_keeps_claims (safe : Settlement.NonFinancialRequest request) :
    (primitiveNext input current request).raw.claims = current.raw.claims :=
  safe.step_claims input.law current.raw request

theorem primitive_financial_effect_is_the_original_request
    (instrument : Instrument) (debtor creditor : Party) :
    (primitiveNext input current request).raw.claims instrument debtor creditor =
      current.raw.claims instrument debtor creditor + input.law.actualClaimDelta current.raw request instrument debtor creditor :=
  input.law.step_financial_balance current.raw request instrument debtor creditor

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual
