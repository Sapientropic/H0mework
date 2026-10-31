import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.LawfulPrefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Universal.Source.Program Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- This exact factory scope contains the original programme and its native
finite financial admissions. A generic old world is not accepted here. -/
structure Window where
  input : ProgrammeSource.Input Party Good Port Technology Instrument
  depth : Nat
  count : Nat

namespace Window
variable (window : Window (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def frame := Financial.Installation.Runtime.frames window.input window.depth window.count
def cursor := window.frame.cursor window.input
def visit := Financial.Installation.Cursor.lastExecutedVisit window.input window.cursor
def before := ProgrammeSource.rawCurrent window.input window.visit.current
def word := ProgrammeSource.rawEvent window.input window.visit.current
def account := window.cursor.account
def legs := Source.legs window.input.law window.before window.word

def Leg := Source.Leg window.input.law window.before window.word

def nativeSlots := window.account.current.slots
def pending := Financial.Installation.Cursor.pending window.input window.cursor
def Accounted : Prop := window.pending = []

instance : Decidable window.Accounted := by
  unfold Accounted
  cases window.pending <;> infer_instance

theorem every_current_slot_is_the_original_native_account : window.nativeSlots = window.cursor.account.current.slots := rfl

end Window
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source
