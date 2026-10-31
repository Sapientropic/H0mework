import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.NeedFloor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Retiming

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

open Source.Program Exit.AutonomousProduction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (timing : input.law.TimeIndependent)

include timing

omit [DecidableEq Port] in
theorem actualAndIndependent_retime
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    ActualAndIndependent input (current.retime clock round) word ↔
      ActualAndIndependent input current word := by
  have trace := executed_items_retime input.law timing current clock round 0 word
  change input.law.rawItems (current.retime clock round) word =
    (input.law.rawItems current word).map (retimed clock round) at trace
  simp only [ActualAndIndependent, trace, List.forall_mem_map, retimed,
    input.law.valid_retime timing]
  rfl

omit [DecidableEq Port] in
theorem bundlePaid_retime
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (word : RawEvent Party Good Port Technology Instrument) (person : Party)
    (goods : Bundle Good) (purpose : Use) :
    Exit.Necessity.BundlePaid input.law (current.retime clock round) word person goods purpose ↔
      Exit.Necessity.BundlePaid input.law current word person goods purpose := by
  have trace := executed_items_retime input.law timing current clock round 0 word
  change input.law.rawItems (current.retime clock round) word =
    (input.law.rawItems current word).map (retimed clock round) at trace
  constructor
  · rintro (empty | ⟨item, present, valid, matched⟩)
    · exact Or.inl empty
    · rw [trace] at present
      obtain ⟨original, source, rfl⟩ := List.mem_map.mp present
      exact Or.inr ⟨original, source, (input.law.valid_retime timing _ _ _ _).mp valid, matched⟩
  · rintro (empty | ⟨item, present, valid, matched⟩)
    · exact Or.inl empty
    · refine Or.inr ⟨retimed clock round item, ?_,
        (input.law.valid_retime timing _ _ _ _).mpr valid, matched⟩
      rw [trace]
      exact List.mem_map.mpr ⟨item, present, rfl⟩

omit [DecidableEq Port] in
theorem needsPaid_retime
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    Exit.Necessity.AllNeedsPaid input.law (current.retime clock round) members word ↔
      Exit.Necessity.AllNeedsPaid input.law current members word := by
  simp only [Exit.Necessity.AllNeedsPaid, timing.necessities, timing.maintenance,
    bundlePaid_retime input timing]

omit [DecidableEq Port] in
theorem actualUse_retime
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (word : RawEvent Party Good Port Technology Instrument) (person : Party)
    (purpose : Use) (good : Good) :
    actualUse input (current.retime clock round) word person purpose good =
      actualUse input current word person purpose good := by
  have trace := executed_items_retime input.law timing current clock round 0 word
  change input.law.rawItems (current.retime clock round) word =
    (input.law.rawItems current word).map (retimed clock round) at trace
  simp only [actualUse, trace, List.map_map]
  congr 2
  funext item
  simp only [Function.comp_apply, retimed, RawLaw.actualDebit, input.law.valid_retime timing]
  rfl

omit [DecidableEq Port] in
theorem originalNeedFloor_retime
    (origin current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    OriginalNeedFloor input origin (current.retime clock round) members word ↔
      OriginalNeedFloor input origin current members word := by
  simp only [OriginalNeedFloor, actualUse_retime input timing]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation
