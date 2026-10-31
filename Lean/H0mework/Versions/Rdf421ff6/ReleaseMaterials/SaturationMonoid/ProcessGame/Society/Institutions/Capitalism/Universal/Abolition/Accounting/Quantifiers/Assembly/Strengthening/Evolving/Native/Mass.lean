import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Validity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Drain.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

namespace NativeCurrent




def mass : Nat := Public.Accounting.mass current.input current.depth current.count current.prefixLimit
  current.renewalLimit current.oldPast current.start current.actual.actual

def HasWork : Prop := Public.Inquiry.HasWork current.frame current.actual.actual

instance : Decidable (HasWork current) := inferInstanceAs (Decidable (Public.Inquiry.HasWork _ _))

theorem work_iff_positive_mass : HasWork current ↔ 0 < mass current :=
  Public.Accounting.Drain.actual_work_iff_positive_source_mass current.frame current.actual.actual

theorem advance_spends_one_actual_source_position (work : HasWork current) :
    mass (advance current) + 1 = mass current := by
  change Public.Inquiry.HasWork current.frame current.actual.actual at work
  unfold advance selected
  rw [dif_pos work]
  split
  · rename_i registered _
    exact Public.Accounting.the_original_admission_spends_exactly_its_actual_head current.input
      current.depth current.count current.prefixLimit current.renewalLimit current.oldPast current.start registered
  · exact Public.Accounting.Drain.every_actual_internal_restriction_spends_one_position
      current.frame current.actual.actual work

theorem advance_strictly_consumes_internal_work (work : HasWork current) :
    mass (advance current) < mass current := by
  have spent := advance_spends_one_actual_source_position current work
  omega

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
