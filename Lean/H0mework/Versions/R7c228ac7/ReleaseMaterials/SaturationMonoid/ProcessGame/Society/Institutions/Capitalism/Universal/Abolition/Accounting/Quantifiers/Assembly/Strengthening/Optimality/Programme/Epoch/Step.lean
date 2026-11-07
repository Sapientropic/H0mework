import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

private theorem paidPhysical (native : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :
    Evolving.Epoch.Source.originalState native =
      Physical.Public.stateAt native.input native.depth native.count native.prefixLimit native.renewalLimit
        native.oldPast (Physical.next native.start).past := by
  unfold Evolving.Epoch.Source.originalState Public.Inquiry.ActualAt.snapshot
  rw [native.bodyPaid]
  rfl

private theorem ordinaryPhysical :
    Evolving.Epoch.Source.originalState current.ordinary.native = Evolving.Epoch.Source.originalState current.native := by
  rw [paidPhysical,paidPhysical]
  rfl

private theorem bornPhysical
    (registered : Public.Accounting.Registration current.native.input current.native.depth current.native.count
      current.native.prefixLimit current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual) :
    Evolving.Epoch.Source.originalState (current.birth registered).native = Evolving.Epoch.Source.originalState current.native := by
  rw [paidPhysical,paidPhysical]
  rfl

private theorem writtenPhysical
    (ready : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual) :
    Evolving.Epoch.Source.originalState (Evolving.Epoch.Transition.next current ready).native = current.physicalResult.next := by
  exact Evolving.Epoch.Transition.the_material_target_is_the_same_actual_public_result current

theorem the_effective_step_is_the_literal_actual_physical_successor :
    run current.native.input (Evolving.Epoch.Source.originalState current.native) (effective current) =
      Evolving.Epoch.Source.originalState current.advance.native := by
  by_cases work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual
  · rw [effective,if_pos work]
    unfold Evolving.Epoch.Current.advance
    rw [dif_pos work]
    split
    · exact (bornPhysical current _).symm
    · exact (ordinaryPhysical current).symm
  · rw [effective,if_neg work,run,run,current.advance_eq_epoch work,writtenPhysical]
    rfl

theorem the_effective_step_has_exactly_the_reported_material_inventory :
    items current.native.input (Evolving.Epoch.Source.originalState current.native) (effective current) = materialItems current := by
  by_cases work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual
  · simp only [effective,materialItems,if_pos work,items]
  · simp only [effective,materialItems,if_neg work,items,List.append_nil]
    rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
