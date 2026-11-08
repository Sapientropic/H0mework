import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Run
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Shared

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

/-- The legacy full-bundle contract still consumes its own original
matching. The service solver spends only its complement. -/
structure WholeChoice (source : C) (script : Script) (atomic : Finset TaskId) (task : TaskId → Task) where
  matching : Finset ((Σ id, Fin (task id).slots.length) × Ordinal source script)
  original : matching ∈ (Clock.Window.Shared.geometry source atomic task script).matchings
  full : matching.card = (Clock.Window.Shared.geometry source atomic task script).leftCarrier.card

def WholeChoice.reserved {source : C} {script : Script} {atomic : Finset TaskId} {task : TaskId → Task}
    (choice : WholeChoice source script atomic task) : Finset (Ordinal source script) :=
  choice.matching.image Prod.snd

theorem WholeChoice.has_its_own_atomic_settlement {source : C} {script : Script} {atomic : Finset TaskId}
    {task : TaskId → Task} (choice : WholeChoice source script atomic task) :
    Clock.Window.Shared.Assigned source atomic task script :=
  ⟨choice.matching, choice.original, choice.full⟩

theorem a_whole_original_payment_excludes_its_ordinal_from_every_fragment
    {source : C} {script : Script} {atomic fragments : Finset TaskId} {task : TaskId → Task}
    (choice : WholeChoice source script atomic task)
    (receipt : (network source script fragments task choice.reserved).Certificate)
    (edge : (Σ id, Fin (task id).slots.length) × Ordinal source script) (paid : edge ∈ choice.matching)
    (line : Need fragments task) (good : { good // good ∈ goods fragments task }) :
    (edge.2 ∈ choice.reserved) ∧
      receipt.allocation line (edge.2, good) = 0 ∧ Recorded source script := by
  have booked : edge.2 ∈ choice.reserved :=
    Finset.mem_image.mpr ⟨edge, paid, rfl⟩
  exact ⟨booked, reserved_original_uses_cannot_be_spent_on_fragments receipt line (edge.2, good) booked,
    record source script⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
