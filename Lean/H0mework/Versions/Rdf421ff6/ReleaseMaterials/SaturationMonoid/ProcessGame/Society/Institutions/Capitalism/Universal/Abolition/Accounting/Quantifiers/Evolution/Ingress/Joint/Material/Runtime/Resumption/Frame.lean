import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Transport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))

local notation "F" => Runtime.flow seed claim

/-- This is the already executed joint root. Only its paid-body coordinates
expose native continuation; the old paid material rows remain history. -/
def nativeFrame : Public.NativeFrame seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) where
  N := Admission.N seed claim
  anchor := Background.nativeAccount seed
  family := family seed claim enough
  V := Runtime.V seed claim
  root := Runtime.Inquiry.root seed claim
  occurrence_eq_emitted := Abolition.Accounting.Root.Compiler.occurrence_eq_emitted F
  cursor := stageCursor seed
  support_exact := the_source_support_at_a_paid_cursor_is_the_same_lifted_whole_account seed claim enough
  successor := Abolition.Accounting.Root.Compiler.successor F
  cursor_next := by
    intro current actual aligned
    obtain ⟨paid,same⟩ := a_present_native_cursor_is_the_same_paid_current seed current actual aligned
    subst actual
    calc
      _ = stageCursor seed (Runtime.next seed claim current) :=
        congrArg (stageCursor seed) (Abolition.Accounting.Root.Compiler.successor_current F current)
      _ = some (Runtime.next seed claim current) := by
        simp [stageCursor,a_native_successor_keeps_the_existing_paid_body seed claim current paid]
      _ = _ := congrArg some (the_actual_root_next_is_the_original_native_next_without_new_admission seed claim current)
  successor_destination := by
    intro current actual aligned
    obtain ⟨paid,same⟩ := a_present_native_cursor_is_the_same_paid_current seed current actual aligned
    subst actual
    exact (Abolition.Accounting.Root.Compiler.successor_destination F current).trans
      (the_actual_paid_destination_is_the_literal_native_financial_destination seed claim enough current paid)
  entries_finite := Runtime.entries_finite seed claim
  successor_keys := every_actual_root_successor_keeps_all_original_responsibility_keys seed claim

theorem this_native_frame_is_the_same_actual_joint_root :
    (nativeFrame seed claim enough).root = Runtime.Inquiry.root seed claim ∧
      (nativeFrame seed claim enough).V = Runtime.V seed claim := ⟨rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption
