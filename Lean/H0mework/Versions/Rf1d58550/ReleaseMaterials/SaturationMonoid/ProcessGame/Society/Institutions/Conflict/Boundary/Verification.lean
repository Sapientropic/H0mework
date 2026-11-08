import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Defence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ

theorem inspectExit_is_exact (baseline current : C) (residents : List Party) (word : Word) :
    (∃ exit, inspectExit baseline current residents word = .preserved exit) ↔
      ExitFloorAt baseline current residents word := by
  constructor
  · rintro ⟨exit, _⟩
    exact exit
  · intro verified
    unfold inspectExit
    cases observed : Root.inspect current word with
    | rejected issue =>
        have paid := (Root.inspect_accepts_iff current word).mpr verified.paid
        rw [observed] at paid
        cases paid
    | paid paid =>
        cases roles : Material.inspectList (Quantities.Exit.Grant.Independent current []) (actualItems current word) with
        | failure item original failed => exact (failed (verified.independent item original)).elim
        | clear independent =>
            cases quantities : Material.inspectList
                (fun cell : Cell => cell.2.2.2 ≤ deliveredAt current word cell)
                (floorCells baseline residents) with
            | failure cell original failed => exact (failed (verified.floor cell original)).elim
            | clear floor => exact ⟨verified, rfl⟩

variable {source : Root.Cut Party Good Port Technology Instrument}
  {attackWord : RawEvent Party Good Port Technology Instrument} {community : Party → Community}

theorem inspectDefence_is_exact (attack : AggressionAt source attackWord community)
    (response continuation : Word) :
    (∃ defence, inspectDefence attack response continuation = .permitted defence) ↔
      DefenceAt attack response continuation := by
  constructor
  · rintro ⟨defence, _⟩
    exact defence
  · intro verified
    unfold inspectDefence
    rw [dif_pos verified.victimStanding, dif_pos verified.active]
    cases observed : Root.inspect attack.after response with
    | rejected issue =>
        have paid := (Root.inspect_accepts_iff attack.after response).mpr verified.responsePaid
        rw [observed] at paid
        cases paid
    | paid paid =>
        dsimp only
        rw [dif_neg verified.closed]
        cases owners : Material.inspectList (GuardAt attack) (responseItems attack response) with
        | failure item original failed => exact (failed (verified.localOwners item original)).elim
        | clear original =>
            dsimp only
            split
            · rename_i capture rest observedCapture
              exact (verified.noOverreach ⟨capture⟩).elim
            · obtain ⟨exit, selected⟩ :=
                (inspectExit_is_exact source (Root.terminal attack.after response) attack.residents continuation).mpr
                  verified.independentExit
              rw [selected]
              exact ⟨verified, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
