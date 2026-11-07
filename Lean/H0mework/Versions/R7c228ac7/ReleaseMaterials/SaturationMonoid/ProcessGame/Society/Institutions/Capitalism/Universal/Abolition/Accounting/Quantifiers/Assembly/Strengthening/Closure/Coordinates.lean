import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.History.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure

open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def NativeShape : Prop := source.prefixLimit = 0 ∧ source.renewalLimit = 0 ∧ source.oldPast = []

theorem every_actual_step_keeps_the_original_source_coordinates :
    source.advance.prefixLimit = source.prefixLimit ∧
      source.advance.renewalLimit = source.renewalLimit ∧ source.advance.oldPast = source.oldPast := by
  unfold Evolving.NativeCurrent.advance Evolving.NativeCurrent.selected
  split
  · split <;> exact ⟨rfl,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl⟩

theorem all_actual_descendants_keep_the_original_source_coordinates (n : Nat) :
    (Evolving.History.currentAt source n).prefixLimit = source.prefixLimit ∧
      (Evolving.History.currentAt source n).renewalLimit = source.renewalLimit ∧
      (Evolving.History.currentAt source n).oldPast = source.oldPast := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n previous =>
    have step := every_actual_step_keeps_the_original_source_coordinates (Evolving.History.currentAt source n)
    exact ⟨step.1.trans previous.1,step.2.1.trans previous.2.1,step.2.2.trans previous.2.2⟩

theorem native_shape_survives_every_actual_descendant (shape : NativeShape source) (n : Nat) :
    NativeShape (Evolving.History.currentAt source n) := by
  have same := all_actual_descendants_keep_the_original_source_coordinates source n
  exact ⟨same.1.trans shape.1,same.2.1.trans shape.2.1,same.2.2.trans shape.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure
