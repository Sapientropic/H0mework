import H0mework.Physics.Actual.WeakHistory
import H0mework.Physics.Actual.WeakCluster
import H0mework.Physics.Actual.HistoryOnShell

/-! Candidate membership retains the images of every weak occurrence of
the original history. The canonical value is read from its first native write. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Weak

open Filter StageNineHolonomicField
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFriedrichsAllOrderWeakLimitOccurrence

noncomputable section

abbrev Occurrence := CountableHilbertWeakLimitOccurrence sequence

def Candidate := {payload : Payload // ∃ occurrence : Occurrence, occurrence.limit = payload}

def ofOccurrence (occurrence : Occurrence) : Candidate :=
  ⟨occurrence.limit, occurrence, rfl⟩

def density : Candidate → Payload := Subtype.val

theorem density_injective : Function.Injective density := Subtype.val_injective

theorem sequence_eventually_firstWrite (coordinate : ℕ) :
    ∀ᶠ index in atTop, sequence index coordinate = sequence 7 coordinate := by
  filter_upwards [History.configuration_eventually_firstWrite] with index same
  have smoothSame :
      (⟨History.configuration index, History.configuration_smooth index⟩ :
        {configuration : StageNineHolonomicConfiguration // configuration.Smooth}) =
      ⟨History.configuration 7, History.configuration_smooth 7⟩ := Subtype.ext same
  exact congrArg (fun configuration :
      {configuration : StageNineHolonomicConfiguration // configuration.Smooth} ↦
    Fields.compactCoordinates configuration.1 configuration.2 coordinate) smoothSame

def canonical : Candidate :=
  ⟨sequence 7, WeakCluster.occurrenceOfEventuallyConstant sequence_eventually_firstWrite, rfl⟩

@[simp] theorem canonical_density : density canonical = sequence 7 := rfl

end
end SaturationMonoid.PhysicsCore.Stage9CU.Weak
