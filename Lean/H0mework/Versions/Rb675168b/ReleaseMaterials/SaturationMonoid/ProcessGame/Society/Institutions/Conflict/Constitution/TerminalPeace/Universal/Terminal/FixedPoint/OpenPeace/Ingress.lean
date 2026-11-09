import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

variable {Party Good Port Technology Instrument : Type}

/-- The proposed authority is data. Only the native due queue can write
production or grant authority. -/
structure Proposal (Party Good Port Technology Instrument : Type) where
  wire : Wire Party Good Port Technology Instrument
  programme : ProgrammeSource.Input Party Good Port Technology Instrument

abbrev OpenOrders (Party Good Port Technology Instrument : Type) :=
  ℚ → ReviewBid Party Good Port Technology Instrument →
    ProgrammeSource.Input Party Good Port Technology Instrument → Party → Bool

inductive Input (Party Good Port Technology Instrument : Type)
  | native (due : NoFreeProbe.Due Party Good Port Technology Instrument)
  | proposal (attempt : Proposal Party Good Port Technology Instrument)

namespace Input

def due : Input Party Good Port Technology Instrument → NoFreeProbe.Due Party Good Port Technology Instrument
  | .native slot => slot
  | .proposal attempt => ⟨none, [attempt.wire]⟩

def orders (original : PaymentOrders Party Good Port Technology Instrument)
    (openOrders : OpenOrders Party Good Port Technology Instrument) :
    Input Party Good Port Technology Instrument → PaymentOrders Party Good Port Technology Instrument
  | .native _ => original
  | .proposal attempt => fun clock bid actor => original clock bid actor &&
    openOrders clock bid attempt.programme actor

/-- An uninstalled programme has no private eligibility or execution
entry. Its actual paid reply uses the original fixed refusal. -/
def replies (original : Replies Party Good Port Technology Instrument) :
    Input Party Good Port Technology Instrument → Replies Party Good Port Technology Instrument
  | .native _ => original
  | .proposal _ => { original with review := fun _ _ _ _ => false }

end Input

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
