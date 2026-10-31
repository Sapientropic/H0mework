import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Installed

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

private theorem nativeNext_paid :
    (Public.Accounting.nativeNext current.input current.depth current.count current.prefixLimit
      current.renewalLimit current.oldPast current.start current.actual.actual).bodyPaid = true := by
  unfold Public.Accounting.nativeNext
  rw [dif_pos current.bodyPaid]
  split
  · exact current.bodyPaid
  · exact (Public.Accounting.Current.after_item_reads_the_source_generated_native_account _ current.bodyPaid _).2.2

/-- A non-birth native head advances the original account; the public body is
not rerun. Branch admission is established by the query compiler separately. -/
def ordinary : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  input := current.input
  depth := current.depth
  count := current.count
  prefixLimit := current.prefixLimit
  renewalLimit := current.renewalLimit
  oldPast := current.oldPast
  start := current.start
  frame := current.frame
  reader := current.reader
  visit := Public.Accounting.Born.Action.nextVisit (full current) current.visit
  actual := ⟨Public.Accounting.nativeNext current.input current.depth current.count current.prefixLimit
    current.renewalLimit current.oldPast current.start current.actual.actual,
    current.frame.cursor_next current.visit.current current.actual.actual current.actual.aligned⟩
  bodyPaid := nativeNext_paid current
  authority := Public.Accounting.Born.Action.nextAuthorityForInstalledEntry (full current) current.visit current.authority
  rows := nextPaidRows (full current).root current.visit ((full current).successor current.visit.current) current.rows

theorem ordinary_keeps_both_original_claims :
    (ordinary current).rows.productive.claim = current.rows.productive.claim ∧
      (ordinary current).rows.gross.claim = current.rows.gross.claim :=
  nextPaidRows_preserves_both_original_claims _ _ _ _

theorem ordinary_is_the_actual_root_successor :
    (ordinary current).erase =
      ⟨(full current).N,⟨(full current).V,(full current).root.toAuthoritativeRoot,
        current.visit.next ((full current).successor current.visit.current).next_eq⟩⟩ := rfl

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
