import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem primitiveScript_append (first second : Word) :
    primitiveScript (first ++ second) = primitiveScript first ++ primitiveScript second := by
  induction first with
  | nil => rfl
  | cons request tail ih => simp only [List.cons_append, primitiveScript, ih]

theorem append_primitive_traces {source middle target : C} {first second : Word}
    (front : Trace source first middle) (back : Trace middle second target) :
    Trace source (first ++ second) target := by
  induction front with
  | nil => exact back
  | cons source request tail middle ready review noConsents valid later ih =>
    exact .cons source request (tail ++ second) target ready review noConsents valid (ih back)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
