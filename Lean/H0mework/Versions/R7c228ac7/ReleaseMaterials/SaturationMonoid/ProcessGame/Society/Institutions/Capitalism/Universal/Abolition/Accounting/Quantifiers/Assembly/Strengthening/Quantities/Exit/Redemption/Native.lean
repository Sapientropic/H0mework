import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Coverage

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

abbrev sourceLaw (source : C) := Physical.Public.interpreter source.native.input

abbrev sourceOrigin (source : C) :=
  Actual.origin source.native.input source.native.depth source.native.count

def script (source : C) (position : Position Party Instrument) (quantity : ℚ) :=
  Execution.primitiveScript [request (sourceLaw source) position quantity]

structure PaidAt (source : C) (position : Position Party Instrument) (quantity : ℚ) : Prop where
  safe : Safe (sourceLaw source) (sourceOrigin source) source.raw position quantity
  exactTrace : Trace source [request (sourceLaw source) position quantity]
    (Execution.endAt source (script source position quantity))
  readback : (Execution.endAt source (script source position quantity)).raw =
    (sourceLaw source).step source.raw (request (sourceLaw source) position quantity)
  ready : Ready (Execution.endAt source (script source position quantity))
  complete : Recorded source (script source position quantity)

theorem the_open_interpreter_admits_the_original_personal_gate
    (source : C) (position : Position Party Instrument) (quantity : ℚ) :
    Authorized (sourceLaw source) source.raw position quantity :=
  ⟨rfl, fun _ _ => rfl⟩

/-- Every amount in the corridor uses the same original primitive and
native head. Its target is the literal successor of that execution. -/
theorem the_original_root_pays_every_admitted_safe_redemption
    (source : C) (position : Position Party Instrument) (quantity : ℚ)
    (ready : Ready source) (review : ReviewAvailable source)
    (safe : Safe (sourceLaw source) (sourceOrigin source) source.raw position quantity) :
    PaidAt source position quantity := by
  let redeem := request (sourceLaw source) position quantity
  have actual := two_actual_root_steps_pay_and_consume_the_generated_primitive
    source redeem ready review rfl safe.2.1
  exact ⟨safe, .cons source redeem [] _ ready review rfl safe.2.1 (.nil _),
    actual.2, actual.1, record source (script source position quantity)⟩

theorem actual_personal_redemption_domain_is_exact
    (source : C) (position : Position Party Instrument) (quantity : ℚ)
    (ready : Ready source) (review : ReviewAvailable source) :
    PaidAt source position quantity ↔ position.debtor ≠ position.creditor ∧
      0 < rate (sourceLaw source) position ∧ Within (sourceLaw source) (sourceOrigin source) source.raw position quantity := by
  constructor
  · intro paid
    obtain ⟨different, positive, within, _⟩ :=
      (safe_iff_original_authority_and_tight_material_interval _ _ _ _ _).mp paid.safe
    exact ⟨different, positive, within⟩
  · rintro ⟨different, positive, within⟩
    exact the_original_root_pays_every_admitted_safe_redemption source position quantity ready review
      ((safe_iff_original_authority_and_tight_material_interval _ _ _ _ _).mpr
        ⟨different, positive, within, the_open_interpreter_admits_the_original_personal_gate source position quantity⟩)

theorem the_original_root_attains_both_redemption_endpoints
    (source : C) (position : Position Party Instrument)
    (ready : Ready source) (review : ReviewAvailable source)
    (distinct : position.debtor ≠ position.creditor)
    (positive : 0 < rate (sourceLaw source) position)
    (capacity : lower (sourceLaw source) (sourceOrigin source) source.raw position ≤ upper (sourceLaw source) (sourceOrigin source) source.raw position) :
    PaidAt source position (lower (sourceLaw source) (sourceOrigin source) source.raw position) ∧
    PaidAt source position (upper (sourceLaw source) (sourceOrigin source) source.raw position) ∧
    ∀ quantity, PaidAt source position quantity → Within (sourceLaw source) (sourceOrigin source) source.raw position quantity := by
  have domain := fun quantity => actual_personal_redemption_domain_is_exact source position quantity ready review
  exact ⟨(domain _).mpr ⟨distinct, positive, le_rfl, capacity⟩,
    (domain _).mpr ⟨distinct, positive, capacity, le_rfl⟩,
    fun quantity actual => ((domain quantity).mp actual).2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption
