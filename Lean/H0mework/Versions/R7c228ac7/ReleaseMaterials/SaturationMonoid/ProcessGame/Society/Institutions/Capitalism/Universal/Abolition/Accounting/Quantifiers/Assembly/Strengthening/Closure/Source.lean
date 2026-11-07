import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure.Run
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution Evolution.Ingress.Joint Evolution.Ingress.Joint.Material

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Quantifiers.Joint.Planning.Enough seed claim (Material.shared seed claim))
  (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

def current (n : Nat) := Evolving.History.currentAt (Evolving.Source.initial seed claim enough reader) n

theorem source_shape (n : Nat) : NativeShape (current seed claim enough reader n) :=
  native_shape_survives_every_actual_descendant (Evolving.Source.initial seed claim enough reader) ⟨rfl,rfl,rfl⟩ n

/-- The public quantifier ranges over every actual descendant, including
births. Neither a ready endpoint nor representation equations are input. -/
theorem every_actual_descendant_clears_its_whole_native_ledger_in_a_source_finite_bound
    (n : Nat)
    (resources : Resources (current seed claim enough reader n) (source_shape seed claim enough reader n)) :
    CompleteAt (current seed claim enough reader n) (source_shape seed claim enough reader n) resources :=
  the_original_source_drains_clears_and_resumes_in_its_own_finite_budget _ _ resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure.Source
