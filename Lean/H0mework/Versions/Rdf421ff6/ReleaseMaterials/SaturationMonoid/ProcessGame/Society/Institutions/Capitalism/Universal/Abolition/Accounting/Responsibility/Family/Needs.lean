import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family

open Source.Program
open Innovation
open Exit.Necessity

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Root supplies its actual generated member inventory. Failure retains the
original bearer and the source's exact current necessity or maintenance bundle. -/
inductive NeedDisposition (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (members : List Party) : Type
  | paid (complete : AllNeedsPaid law before members word)
  | necessity (actor : Party) (original : actor ∈ members)
      (unpaid : ¬ BundlePaid law before word actor (law.necessities before actor) .necessity)
  | maintenance (actor : Party) (original : actor ∈ members)
      (unpaid : ¬ BundlePaid law before word actor (law.mandatoryMaintenance before actor) .maintenance)

def inspectNeeds (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) :
    (members : List Party) → NeedDisposition law before word members
  | [] => .paid (by simp [AllNeedsPaid])
  | actor :: rest =>
    if necessary : BundlePaid law before word actor (law.necessities before actor) .necessity then
      if maintained : BundlePaid law before word actor (law.mandatoryMaintenance before actor) .maintenance then
        match inspectNeeds law before word rest with
        | .paid later => .paid (by
            intro next member
            rcases List.mem_cons.mp member with same | old
            · exact same ▸ ⟨necessary,maintained⟩
            · exact later next old)
        | .necessity next member unpaid => .necessity next (List.mem_cons_of_mem actor member) unpaid
        | .maintenance next member unpaid => .maintenance next (List.mem_cons_of_mem actor member) unpaid
      else .maintenance actor List.mem_cons_self maintained
    else .necessity actor List.mem_cons_self necessary

/-- A proposal rejected at source ingress is never treated as an executed
payment word. Valid prefixes of admitted words remain actual events. -/
def Attempt.actualWord
    {law : RawLaw Party Good Port Technology Instrument} {before : RawCurrent Party Good Technology Instrument}
    {cohort : List Party} {victims : List (Party × Good)} {word : RawEvent Party Good Port Technology Instrument} :
    Attempt law before cohort victims word → RawEvent Party Good Port Technology Instrument
  | .accepted .. | .rejected .. => word
  | .foreign .. => []

variable {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

def inspectActualNeeds (claim : Claim source past nature response) (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (members : List Party) :
    NeedDisposition actualLaw state.raw (State.attempt claim state actualLaw word).actualWord members :=
  inspectNeeds actualLaw state.raw (State.attempt claim state actualLaw word).actualWord members

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family
