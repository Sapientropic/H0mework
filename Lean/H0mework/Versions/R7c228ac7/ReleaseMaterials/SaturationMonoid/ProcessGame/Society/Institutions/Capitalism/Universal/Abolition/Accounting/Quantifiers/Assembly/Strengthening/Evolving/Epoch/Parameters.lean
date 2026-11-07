import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

theorem Current.advance_parameters :
    current.advance.native.input = current.native.input ∧
      current.advance.native.depth = current.native.depth ∧ current.advance.native.count = current.native.count ∧
      current.advance.native.prefixLimit = current.native.prefixLimit ∧ current.advance.native.renewalLimit = current.native.renewalLimit ∧
      current.advance.native.oldPast = current.native.oldPast ∧ HEq current.advance.native.reader current.native.reader := by
  let P := fun next : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) =>
    next.native.input = current.native.input ∧ next.native.depth = current.native.depth ∧
      next.native.count = current.native.count ∧ next.native.prefixLimit = current.native.prefixLimit ∧
      next.native.renewalLimit = current.native.renewalLimit ∧ next.native.oldPast = current.native.oldPast ∧
      HEq next.native.reader current.native.reader
  change P current.advance
  by_cases work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual
  · cases selected : Public.Accounting.registration? current.native.input current.native.depth current.native.count
        current.native.prefixLimit current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual with
    | some registered =>
        have same : current.advance = current.birth registered := by
          unfold Current.advance
          rw [dif_pos work,selected]
        exact (congrArg P same).mpr ⟨rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩
    | none =>
        have same : current.advance = current.ordinary := by
          unfold Current.advance
          rw [dif_pos work,selected]
        exact (congrArg P same).mpr ⟨rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩
  · exact (congrArg P (current.advance_eq_epoch work)).mpr ⟨rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩

theorem History.parameters (n : Nat) :
    (History.currentAt current n).native.input = current.native.input ∧
      (History.currentAt current n).native.depth = current.native.depth ∧
      (History.currentAt current n).native.count = current.native.count ∧
      (History.currentAt current n).native.prefixLimit = current.native.prefixLimit ∧
      (History.currentAt current n).native.renewalLimit = current.native.renewalLimit ∧
      (History.currentAt current n).native.oldPast = current.native.oldPast ∧
      HEq (History.currentAt current n).native.reader current.native.reader := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩
  | succ n prior =>
      have step := (History.currentAt current n).advance_parameters
      exact ⟨step.1.trans prior.1,step.2.1.trans prior.2.1,step.2.2.1.trans prior.2.2.1,
        step.2.2.2.1.trans prior.2.2.2.1,step.2.2.2.2.1.trans prior.2.2.2.2.1,
        step.2.2.2.2.2.1.trans prior.2.2.2.2.2.1,step.2.2.2.2.2.2.trans prior.2.2.2.2.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
