import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family

open Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Claim source past nature response)

inductive PaymentStatus (state : State claim) (keys : List (Party × Good)) : Type
  | paid (complete : ∀ key ∈ keys, state.remaining key = 0)
  | unpaid (key : Party × Good) (member : key ∈ keys) (positive : 0 < state.remaining key)

/-- Finite inspection generates the precise residual bearer and good, including
partially paid cells; it does not choose an unobserved future success. -/
def inspectPayment (state : State claim) : (keys : List (Party × Good)) → PaymentStatus claim state keys
  | [] => .paid (by simp)
  | key :: rest =>
    if zero : state.remaining key = 0 then
      match inspectPayment state rest with
      | .paid later => .paid (by
          intro next member
          rcases List.mem_cons.mp member with same | old
          · exact same ▸ zero
          · exact later next old)
      | .unpaid next member positive => .unpaid next (List.mem_cons_of_mem key member) positive
    else .unpaid key List.mem_cons_self (lt_of_le_of_ne (state.nonnegative key) (Ne.symm zero))

inductive MaterialVerdict (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Type
  | paid (complete : State.isPaid claim (State.advance claim state actualLaw word))
  | blocked (issue : ObstructionAt claim state)

def adjudicate (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : MaterialVerdict claim state actualLaw word :=
  match inspectPayment claim (State.advance claim state actualLaw word) (positiveScope source past nature response) with
  | .paid complete => .paid complete
  | .unpaid key member positive => .blocked ⟨actualLaw,word,key,member,positive⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family
