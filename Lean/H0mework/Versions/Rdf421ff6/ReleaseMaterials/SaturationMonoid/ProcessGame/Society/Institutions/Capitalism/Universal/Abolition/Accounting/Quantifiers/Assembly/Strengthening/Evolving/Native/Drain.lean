import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Mass
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Drain.Finite
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History.Actual

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

private theorem path_eq_history (tick : Nat) :
    FiniteDrain.path advance current tick = History.currentAt current tick := by
  induction tick with
  | zero => rfl
  | succ tick ih => exact congrArg advance ih

/-- The least stop is chosen inside the original source mass. The abstract
Nat descent proof never unfolds the dependent rooted-current structure. -/
def drain (current : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :
    {tick : Nat // tick ≤ mass current ∧ ¬ HasWork (History.currentAt current tick)} := by
  let answer := FiniteDrain.generated advance mass HasWork
    advance_spends_one_actual_source_position
    (fun source empty active => Nat.ne_of_gt ((work_iff_positive_mass source).mp active) empty) current
  exact ⟨answer.1,answer.2.1,by rw [← path_eq_history current answer.1]; exact answer.2.2⟩

def drained := History.currentAt current (drain current).1

theorem drained_has_no_pending_source_work :
    (drain current).1 ≤ mass current ∧ ¬ HasWork (drained current) := (drain current).2

theorem drained_is_a_literal_actual_descendant :
    drained current = History.currentAt current (drain current).1 := rfl

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
