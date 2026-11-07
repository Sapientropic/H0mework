import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.State
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Transport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

attribute [local irreducible] Current.advance Planning.selected

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def baseEvolution (actual : FinancialCurrent seed) := Public.Accounting.wholeEvolution
  seed.input seed.depth seed.count 0 0 [] (cursor seed claim) (Background.family seed) actual

def baseOwner (actual : FinancialCurrent seed) :=
  Public.Accounting.owner seed.input seed.depth seed.count (Background.family seed) actual

theorem baseKeys (actual : FinancialCurrent seed) : Financial.Installation.KeepsKeys (baseEvolution seed claim actual) :=
  Public.Accounting.every_actual_step_keeps_all_original_responsibility_keys
    seed.input seed.depth seed.count 0 0 [] (cursor seed claim) (Background.family seed) actual

def withKeys (actual : FinancialCurrent seed) :
    { write : LedgerWriteEvolutionAt (Admission.N seed claim) ⟨support seed claim actual⟩
      ⟨support seed claim (next seed claim actual)⟩ // Financial.Installation.KeepsKeys write } := by
  by_cases paid : actual.bodyPaid = true
  · cases found : Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (cursor seed claim) actual with
    | none =>
        have stationary : next seed claim actual = actual := by
          simp only [next,Public.Accounting.next,dif_pos paid,found]
        rw [stationary]
        -- An exhausted original cursor carries the whole ledger without a transfer receipt.
        exact ⟨LedgerWriteEvolutionAt.identity _,⟨fun _ => rfl,fun _ => rfl⟩⟩
    | some item =>
        change { write : LedgerWriteEvolutionAt (Admission.N seed claim)
            ⟨Material.support seed claim _ (sharedAt seed claim actual)⟩
            ⟨Material.support seed claim _ (sharedAt seed claim (next seed claim actual))⟩ //
              Financial.Installation.KeepsKeys write }
        rw [native_bookkeeping_keeps_the_already_executed_material_state seed claim actual paid]
        exact ⟨Material.identityTransport seed claim (baseEvolution seed claim actual) (baseOwner seed actual)
          (sharedAt seed claim actual),Material.identityTransport_keeps_keys seed claim _ _ _ (baseKeys seed claim actual)⟩
  · have source := Public.Accounting.the_unexecuted_body_is_the_original_initial_state actual paid
    subst actual
    exact ⟨Material.wholeTransport seed claim (baseEvolution seed claim (initial seed)) (baseOwner seed (initial seed))
      (Material.shared seed claim) (Material.word seed claim),
      Material.the_whole_transport_retains_all_original_keys seed claim _ _ _ _ (baseKeys seed claim (initial seed))⟩

def evolution (actual : FinancialCurrent seed) : LedgerWriteEvolutionAt (Admission.N seed claim)
    ⟨support seed claim actual⟩ ⟨support seed claim (next seed claim actual)⟩ :=
  (withKeys seed claim actual).val

theorem every_original_key_survives_the_joint_actual_write (actual : FinancialCurrent seed) :
    Financial.Installation.KeepsKeys (evolution seed claim actual) := (withKeys seed claim actual).property

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
