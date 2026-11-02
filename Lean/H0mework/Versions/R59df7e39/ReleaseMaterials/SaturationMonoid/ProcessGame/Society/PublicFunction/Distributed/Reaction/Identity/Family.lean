import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Finance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

abbrev Program := { policy : code.Policy // policy ∈ code.policies }
abbrev OriginalHistory := { history : History (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) // history ∈ code.histories }

def machine (program : Program code) (history : OriginalHistory code) (table : Table code) :
    Machine Party Good Port Technology Instrument :=
  ⟨code, program.val, program.property, history.val, history.property, respond code table, .original, [], none, []⟩

structure Profile (Party Good Port Technology Instrument : Type) where
  debts : List (DebtImage Party Good Port Technology Instrument)
  firstServices : List (Option Nat)
  deriving DecidableEq

def firstService (source : Machine Party Good Port Technology Instrument) (depth : Nat) (index : Native.Slot source) : Option Nat :=
  match (Native.historyAt source index depth).shape with
  | .live .. => none
  | .terminal first .. => some first

def profile (program : Program code) (history : OriginalHistory code) (table : Table code) :
    Profile Party Good Port Technology Instrument :=
  let source := machine code program history table
  ⟨financeImage code source.input (Native.generate source history.val.length).finance,
    (List.finRange source.code.task.slots.length).map (firstService source (history.val.length + 1))⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity
