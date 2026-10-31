import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure.Coordinates
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Position
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Drain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Only rewrite the source's proven coordinates. The frame, current,
authority, actual account and past are the original values. -/
def readyPosition (shape : NativeShape source)
    (ready : ¬ Public.Inquiry.HasWork source.frame source.actual.actual) :
    Clearing.Position source.input source.depth source.count source.reader := by
  cases source with
  | mk input depth count prefixBound renewalBound pastTrace start frame reader visit actual paid authority rows =>
    rcases shape with ⟨prefixZero,renewalZero,pastEmpty⟩
    change prefixBound = 0 at prefixZero
    change renewalBound = 0 at renewalZero
    change pastTrace = [] at pastEmpty
    subst prefixBound
    subst renewalBound
    subst pastTrace
    exact ⟨start,frame,visit,actual,paid,authority,rows,ready⟩

theorem ready_position_is_the_same_actual_native_current (shape : NativeShape source)
    (ready : ¬ Public.Inquiry.HasWork source.frame source.actual.actual) :
    (readyPosition source shape ready).native = source := by
  cases source with
  | mk input depth count prefixBound renewalBound pastTrace start frame reader visit actual paid authority rows =>
    rcases shape with ⟨prefixZero,renewalZero,pastEmpty⟩
    change prefixBound = 0 at prefixZero
    change renewalBound = 0 at renewalZero
    change pastTrace = [] at pastEmpty
    subst prefixBound
    subst renewalBound
    subst pastTrace
    rfl

def drainedPosition (shape : NativeShape source) :
    Clearing.Position source.drained.input source.drained.depth source.drained.count source.drained.reader :=
  readyPosition source.drained (native_shape_survives_every_actual_descendant source shape source.drain.1)
    source.drained_has_no_pending_source_work.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure
