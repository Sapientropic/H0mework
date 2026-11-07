import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Next
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.ReaderPast

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)

theorem next_reader_length : (next current complete).native.actual.readerCursor.past.length =
    current.native.actual.readerCursor.past.length + 1 := by
  calc
    _ = (current.native.oldPast ++ (next current complete).native.actual.snapshot.past).length :=
      congrArg List.length (Source.reader_past (next current complete).native.actual)
    _ = (current.native.oldPast ++ (current.native.actual.snapshot.past ++ [_])).length :=
      congrArg (fun past => (current.native.oldPast ++ past).length) (next_snapshot_keeps_the_one_actual_effective_input current complete)
    _ = (current.native.oldPast ++ current.native.actual.snapshot.past).length + 1 := by
      simp only [List.length_append,List.length_singleton];omega
    _ = _ := congrArg (fun past => past.length + 1) (Source.reader_past current.native.actual).symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition
