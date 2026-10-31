import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Checks
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Retiming

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument) (timing : law.TimeIndependent)

def retimed (clock : ℚ) (round : Nat) (item : ExecutionItem Party Good Port Technology Instrument) :=
  { item with before := item.before.retime clock round }

include timing

theorem executed_items_retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round index : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    (law.execute (current.retime clock round) index word).items =
      ((law.execute current index word).items).map (retimed clock round) := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simp only [RawLaw.execute, law.step_retime timing, ih, List.map_cons, retimed]

omit [DecidableEq Instrument] in
theorem at_retime (item : ExecutionItem Party Good Port Technology Instrument) (clock : ℚ) (round : Nat) :
    At law (retimed clock round item) ↔ At law item := by
  simp only [At, retimed, law.valid_retime timing]
  rfl

private theorem bundlePaid_retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (party : Party) (goods : Bundle Good) (purpose : Use) :
    Necessity.BundlePaid law (current.retime clock round) word party goods purpose ↔
      Necessity.BundlePaid law current word party goods purpose := by
  have trace := executed_items_retime law timing current clock round 0 word
  change law.rawItems (current.retime clock round) word =
    (law.rawItems current word).map (retimed clock round) at trace
  constructor
  · rintro (empty | ⟨item, member, valid, matched⟩)
    · exact Or.inl empty
    · rw [trace] at member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact Or.inr ⟨original, sourceMember, (law.valid_retime timing _ _ _ _).mp valid, matched⟩
  · rintro (empty | ⟨item, member, valid, matched⟩)
    · exact Or.inl empty
    · refine Or.inr ⟨retimed clock round item, ?_,
        (law.valid_retime timing _ _ _ _).mpr valid, matched⟩
      rw [trace]
      exact List.mem_map.mpr ⟨item, member, rfl⟩

theorem checks_retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round : Nat) (group : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    Checks law (current.retime clock round) group word ↔ Checks law current group word := by
  have trace := executed_items_retime law timing current clock round 0 word
  change law.rawItems (current.retime clock round) word =
    (law.rawItems current word).map (retimed clock round) at trace
  simp only [Checks, trace, List.forall_mem_map, at_retime law timing,
    Necessity.AllNeedsPaid, timing.necessities, timing.maintenance,
    bundlePaid_retime law timing]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction
