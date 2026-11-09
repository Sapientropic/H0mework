import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Cycle

set_option autoImplicit false
set_option maxRecDepth 8192

open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (C levy returnAt)
open Quantities.Execution (endAt)
open Reparation.Actual

noncomputable section

abbrev Origin := Occurrence Original.seed Original.community
abbrev Row := Origin × Balance
abbrev ExternalState (past : Original.Word) := State Original.seed Original.community past
abbrev before (past : Original.Word) := endAt Original.seed past

private theorem only_material_item {source : C} {input : Input Bool Bool Bool Unit Unit}
    {item : Original.Item} (literal : Boundary.Actual.items source input = [item])
    (site : Fin (Boundary.Actual.items source input).length) :
    (Boundary.Actual.items source input)[site] = item :=
  List.mem_singleton.mp ((congrArg (fun rows => (Boundary.Actual.items source input)[site] ∈ rows)
    literal).mp (List.getElem_mem _))

private def levyPosition {source : C} (actual : CycleAt source) :
    Fin (Boundary.Actual.items source Original.attack).length :=
  ⟨0, by rw [original_levy_items actual]; exact Nat.zero_lt_one⟩

private theorem measured_loss {source : C} (actual : CycleAt source) :
    Reparation.loss (Boundary.Actual.materialLaw source) Original.community
      ⟨0, source.raw, levy⟩ (false, true, false) = 6 := by
  unfold Boundary.Actual.materialLaw
  rw [actual.sameSource, actual.physical]
  decide +kernel

def levyDamage {source : C} (actual : CycleAt source) :
    Boundary.Actual.DamageAt source Original.attack Original.community :=
  ⟨(levyPosition actual, (false, true, false)), by
    change 0 < Reparation.loss (Boundary.Actual.materialLaw source) Original.community
      (Boundary.Actual.items source Original.attack)[levyPosition actual] (false, true, false)
    rw [only_material_item (original_levy_items actual), measured_loss actual]
    norm_num⟩

def levyOccurrence (past : Original.Word) (actual : CycleAt (before past)) : Origin :=
  ⟨past, Original.attack, levyDamage actual⟩

theorem the_new_levy_has_its_exact_position (past : Original.Word) (actual : CycleAt (before past)) :
    (levyOccurrence past actual).address = (past.length, 0, (false, true, false)) :=
  rfl

theorem the_new_levy_writes_six (past : Original.Word) (actual : CycleAt (before past)) :
    (levyOccurrence past actual).quantity = 6 := by
  change Reparation.loss (Boundary.Actual.materialLaw (before past)) Original.community
    (Boundary.Actual.items (before past) Original.attack)[levyPosition actual] (false, true, false) = 6
  rw [only_material_item (original_levy_items actual), measured_loss actual]

private theorem each_levy_damage_is_this_original_loss {source : C} (actual : CycleAt source)
    (damage : Boundary.Actual.DamageAt source Original.attack Original.community) :
    damage = levyDamage actual := by
  have literal : damage.item = ⟨0, source.raw, levy⟩ :=
    only_material_item (original_levy_items actual) damage.position
  have paid := damage.actual_foreign_debit.2.1
  have key := original_key damage
  rw [literal] at paid
  unfold keysAt at key
  rw [literal, RawLaw.actualDebit, if_pos paid] at key
  change damage.key ∈ [(false, true, false)] at key
  have width : (Boundary.Actual.items source Original.attack).length = 1 :=
    congrArg List.length (original_levy_items actual)
  have index := lt_of_lt_of_eq damage.position.isLt width
  have equal : damage.position = (levyDamage actual).position := by
    apply Fin.ext
    change damage.position.val = 0
    omega
  exact Subtype.ext (Prod.ext equal (List.mem_singleton.mp key))

theorem the_levy_opens_exactly_its_original_loss (past : Original.Word) (actual : CycleAt (before past)) :
    openings Original.seed Original.community past Original.attack = [levyOccurrence past actual] := by
  let loss := levyDamage actual
  have listed := Boundary.Actual.every_actual_debit_is_assessed loss
  have distinct := Boundary.Actual.each_damage_address_occurs_once (before past) Original.attack Original.community
  have only : Boundary.Actual.damages (before past) Original.attack Original.community = [loss] := by
    cases exactLosses : Boundary.Actual.damages (before past) Original.attack Original.community with
    | nil => exact (List.not_mem_nil (exactLosses ▸ listed)).elim
    | cons first remaining =>
      have same := each_levy_damage_is_this_original_loss actual first
      have empty : remaining = [] := List.eq_nil_iff_forall_not_mem.mpr fun other inside =>
        (List.nodup_cons.mp (exactLosses ▸ distinct)).1
          ((each_levy_damage_is_this_original_loss actual other).trans same.symm ▸ inside)
      rw [same, empty]
  unfold openings
  rw [only]
  rfl

theorem the_payers_material_return_opens_no_reverse_loss {source : C} (actual : CycleAt source) :
    Boundary.Actual.damages (middle source) returned Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have literal : damage.item = ⟨0, (middle source).raw, returnAt 6⟩ :=
    only_material_item (original_return_items actual) damage.position
  have paid := damage.actual_foreign_debit.2.1
  have key := original_key damage
  rw [literal] at paid
  unfold keysAt at key
  rw [literal, RawLaw.actualDebit, if_pos paid] at key
  change damage.key ∈ [(true, true, false)] at key
  have foreign := damage.actual_foreign_debit.1.1
  rw [List.mem_singleton.mp key] at foreign
  exact foreign rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
