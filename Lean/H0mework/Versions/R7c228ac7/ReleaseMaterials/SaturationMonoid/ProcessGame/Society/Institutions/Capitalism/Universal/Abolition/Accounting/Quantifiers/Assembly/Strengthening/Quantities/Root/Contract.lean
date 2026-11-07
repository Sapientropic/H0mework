import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Profile
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Coverage

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

structure SourceQuantityEnvelopeAt (source : C) : Prop where
  originalDisposition : ∀ script : Script, Recorded source script ∧
    (Settled source script ∨ Nonempty (Obstruction source script))
  exactBounds : ∀ read : Script → EReal,
    IsGLB (Bounds.values source read) (Bounds.lower source read) ∧
    IsLUB (Bounds.values source read) (Bounds.upper source read) ∧
    Bounds.Minimum source read ∧ Bounds.Maximum source read
  jointProfile : ∀ profile,
    profile ∈ Bounds.values source (costProfile source) ↔
      ∃ script, Settled source script ∧ costProfile source script = profile
  jointIdeal :
    (∃ script, Settled source script ∧ costProfile source script = Bounds.ideal source (costProfile source)) ∨
    (∀ script, Settled source script → ∃ address,
      Bounds.ideal source (costProfile source) address < costProfile source script address)
  compare : ∀ left right, Settled source left → Settled source right →
    (∀ address, costProfile source left address ≤ costProfile source right address) ∨
    (∀ address, costProfile source right address ≤ costProfile source left address) ∨
    Nonempty (Bounds.Tradeoff source (costProfile source) left right)

/-- The exact price, time or amount readout can vary. Feasibility, material
incidence and the old claim maps always come from the same source fold. -/
theorem the_original_root_generates_its_feasible_domain_and_tight_bounds (source : C) :
    SourceQuantityEnvelopeAt source where
  originalDisposition := fun script => ⟨record source script, by
    cases decideAt source script with
    | feasible paid => exact .inl (settle source script paid)
    | blocked issue => exact .inr ⟨issue⟩⟩
  exactBounds := fun read => ⟨Bounds.lower_is_tight source read, Bounds.upper_is_tight source read,
    Bounds.resolve_minimum source read, Bounds.resolve_maximum source read⟩
  jointProfile := Bounds.observed_iff_settled source (costProfile source)
  jointIdeal := Bounds.the_joint_ideal_is_paid_or_every_completion_has_an_exact_gap source (costProfile source)
  compare := Bounds.compare_paid source (costProfile source)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities
