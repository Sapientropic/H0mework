import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Decision.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

structure ReviewCursor where
  code : ReviewSource.Control.Code Party Good Port Technology Instrument
  remaining : List (RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument)
  feePaid : Bool
  halted : Bool
  renewalDue : Option (RawEvent Party Good Port Technology Instrument)

def ReviewCursor.initial (code : ReviewSource.Control.Code Party Good Port Technology Instrument)
    (prefixLimit renewalLimit : Nat) :
    ReviewCursor (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨code,code.candidates prefixLimit renewalLimit,false,false,none⟩

def ReviewCursor.recourse (cursor : ReviewCursor (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Bool :=
  cursor.halted || (cursor.remaining.isEmpty && cursor.renewalDue.isNone)

/-- These are the original programme-state coordinates. Raw stocks, claims,
technology and clocks are read from the live native frame, not stored here. -/
structure Control where
  phase : Actual.Phase Party Good Port Technology Instrument
  remaining : RawEvent Party Good Port Technology Instrument
  review : Option (ReviewCursor (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

variable (control : Control (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def Control.atRaw (raw : RawCurrent Party Good Technology Instrument) :
    Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨raw,control.phase,control.remaining⟩

def Control.fromState (state : Actual.State (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :
    Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨state.phase,state.remaining,none⟩

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (members : List Party)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def boundary : Prop :=
  match Decision.compile input origin members depth count prefixLimit renewalLimit current with
  | .blocked _ | .action (.renewal ..) => True
  | .action (.migration ..) | .action (.repair ..) => False

instance : Decidable (boundary input origin members depth count prefixLimit renewalLimit current) := by
  unfold boundary
  split <;> infer_instance

attribute [local simp] boundary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
