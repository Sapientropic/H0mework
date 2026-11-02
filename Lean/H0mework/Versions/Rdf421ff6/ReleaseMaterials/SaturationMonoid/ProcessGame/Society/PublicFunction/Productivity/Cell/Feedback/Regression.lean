import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Effects

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback

def withoutWaste : Current :=
  { (source.frameAt 13).raw with stock := fun actor good =>
      if actor = 0 ∧ good = .waste then 0 else (source.frameAt 13).raw.stock actor good }

theorem regeneration_needs_the_actual_waste :
    (respond withoutWaste).kind = .repair ∧
    (law.next withoutWaste (respond withoutWaste).word).stock 6 .spare = 1 ∧
    (law.next withoutWaste (respond withoutWaste).word).stock 7 .seed = 0 := by
  decide +kernel

def legalButUnsafe : Current :=
  { (source.frameAt 16).raw with stock := fun actor good =>
      if actor = 7 ∧ good = .feed then 8
      else if actor = 7 ∧ good = .labor then 2
      else (source.frameAt 16).raw.stock actor good }

theorem raw_legality_does_not_override_the_living_floor :
    (attemptCopy legalButUnsafe 7 8).isPaid = true ∧
    (law.next legalButUnsafe (copy 7 8)).stock 7 .spare = 0 ∧
    (respond legalButUnsafe).kind = .repair ∧
    (respond legalButUnsafe).word.length = 0 ∧
    (law.next legalButUnsafe (respond legalButUnsafe).word).stock 7 .spare = 1 := by
  decide +kernel

def outstandingProbe : Current :=
  { (source.frameAt 13).raw with claims := fun _ debtor creditor =>
      if debtor = 6 ∧ creditor = 2 then 11 else 0 }

theorem repair_preserves_a_nonzero_original_claim :
    (respond outstandingProbe).kind = .repair ∧
    (law.next outstandingProbe (respond outstandingProbe).word).claims () 6 2 = 11 ∧
    (law.next outstandingProbe (respond outstandingProbe).word).claims = outstandingProbe.claims := by
  have keep := response_keeps_all_financial_positions outstandingProbe (by decide +kernel)
  refine ⟨by decide +kernel, ?_, keep⟩
  rw [keep]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback
