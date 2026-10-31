import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Clock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

def depth (current : AnyAuthoritativeRootCurrent) : Nat := match current.current.visit.history with
  | .finite history => ProductiveFiniteRootHistoryAt.causalDepth history
  | .postCofinal _ => 0

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

theorem answer_presentation_depth (n : Nat) : depth (answerPresentation seed claim n).erase = n + 1 := by
  change ProductiveFiniteRootHistoryAt.causalDepth (visitAt seed claim n).history = n + 1
  induction n with
  | zero => rfl
  | succ n earlier => exact congrArg Nat.succ earlier

theorem answer_presentation_erase_injective : Function.Injective (fun n => (answerPresentation seed claim n).erase) := by
  intro first second same
  have depths := congrArg depth same
  rw [answer_presentation_depth,answer_presentation_depth] at depths
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
