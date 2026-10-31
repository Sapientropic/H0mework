import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Reentry.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

private def readBound {α β : Sort _} (value : α) (bound : β) (same : HEq value bound) : β :=
  cast (type_eq_of_heq same) value

private theorem readBound_eq {α β : Sort _} (value : α) (bound : β) (same : HEq value bound) :
    readBound value bound same = bound := by
  cases same
  rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)

/-- Both execution law and member inventory are read through the already
installed context face, whose payload is fixed by this same original root. -/
def readContext : RawLaw Party Good Port Technology Instrument × List Party :=
  readBound frame.contextFace.rootRead (frame.actualLaw,frame.members) frame.context_heq

theorem readContext_eq : readContext claim frame = (frame.actualLaw,frame.members) :=
  readBound_eq _ _ frame.context_heq

def readLaw : RawLaw Party Good Port Technology Instrument := (readContext claim frame).1

def readMembers : List Party := (readContext claim frame).2

theorem readLaw_eq : readLaw claim frame = frame.actualLaw :=
  congrArg Prod.fst (readContext_eq claim frame)

theorem readMembers_eq : readMembers claim frame = frame.members :=
  congrArg Prod.snd (readContext_eq claim frame)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root
