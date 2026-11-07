import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Check
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Census

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : PublicFunction.OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

def standing := Epoch.Interface.Actors.Census.parties source.input depth count prefixLimit renewalLimit current

theorem every_original_member_is_still_standing (person : Party)
    (original : person ∈ Actual.members source.input depth count) :
    person ∈ standing source depth count prefixLimit renewalLimit current :=
  List.mem_dedup.mpr (List.mem_append_left _ original)

theorem standing_has_exact_original_M0_provenance (person : Party) :
    person ∈ standing source depth count prefixLimit renewalLimit current ↔
      (Epoch.Interface.Actors.prelude source.input depth count (.actual prefixLimit renewalLimit current) person).isSome = true :=
  Epoch.Interface.Actors.Census.membership_is_exactly_the_original_prelude source.input depth count prefixLimit renewalLimit current person

variable (pair : Material.Migration.CodePair Party Good Port Technology Instrument)

/-- This is the proposed code's responsibility footprint, not a claim that
its parties already possess standing in the actual prefix. -/
def footprint :=
  (Source.ProgrammeFace.parties source.seed.law
      ((state source depth count prefixLimit renewalLimit current).raw, pair.1) ++
    Source.ProgrammeFace.parties source.seed.law
      (source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw pair.1, pair.2)).dedup

/-- A selected pair must also pay the prospective responsibilities of its
own code. This union does not insert candidates into the actual census. -/
def scope := (standing source depth count prefixLimit renewalLimit current ++
  footprint source depth count prefixLimit renewalLimit current pair).dedup

theorem current_standing_is_in_scope (person : Party)
    (present : person ∈ standing source depth count prefixLimit renewalLimit current) :
    person ∈ scope source depth count prefixLimit renewalLimit current pair :=
  List.mem_dedup.mpr (List.mem_append_left _ present)

theorem every_original_member_is_in_scope (person : Party)
    (original : person ∈ Actual.members source.input depth count) :
    person ∈ scope source depth count prefixLimit renewalLimit current pair :=
  current_standing_is_in_scope source depth count prefixLimit renewalLimit current pair person
    (every_original_member_is_still_standing source depth count prefixLimit renewalLimit current person original)

theorem each_tail_signer_has_an_original_code_incidence
    (item : ExecutionItem Party Good Port Technology Instrument)
    (original : item ∈ source.seed.law.rawItems
      (source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw pair.1) pair.2) :
    item.request.signer ∈ footprint source depth count prefixLimit renewalLimit current pair :=
  List.mem_dedup.mpr (List.mem_append_right _
    (List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨item, original, List.mem_cons_self⟩)))

theorem incoming_is_not_part_of_current_standing
    (raw : Compile.RawInput Party Good Port Technology Instrument) :
    standing source depth count prefixLimit renewalLimit (Physical.receive current raw) =
      standing source depth count prefixLimit renewalLimit current := rfl

#print axioms every_original_member_is_still_standing
#print axioms standing_has_exact_original_M0_provenance
#print axioms each_tail_signer_has_an_original_code_incidence

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census
