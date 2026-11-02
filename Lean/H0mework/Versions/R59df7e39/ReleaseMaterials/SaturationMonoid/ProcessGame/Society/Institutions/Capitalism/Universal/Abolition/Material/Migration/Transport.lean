import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Shared
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration

open Source.Program Source.ProgrammeControl Exit.AutonomousProduction Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Instrument] in
private theorem affected_retime (timing : input.law.TimeIndependent)
    (item : ExecutionItem Party Good Port Technology Instrument) (clock : ℚ) (round : Nat) :
    History.affectedSubjects input (retimed clock round item) = History.affectedSubjects input item := by
  simp only [History.affectedSubjects, retimed, RawLaw.actualCredit, input.law.valid_retime timing]
  rfl

theorem subjects_retime (timing : input.law.TimeIndependent)
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    subjects input (current.retime clock round) word = subjects input current word := by
  have trace := executed_items_retime input.law timing current clock round 0 word
  change input.law.rawItems (current.retime clock round) word =
    (input.law.rawItems current word).map (retimed clock round) at trace
  simp only [subjects, trace, List.flatMap_map, affected_retime input timing]

theorem finiteShared_retime (timing : input.law.TimeIndependent)
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    FiniteShared input (current.retime clock round) word ↔ FiniteShared input current word := by
  have trace := executed_items_retime input.law timing current clock round 0 word
  change input.law.rawItems (current.retime clock round) word =
    (input.law.rawItems current word).map (retimed clock round) at trace
  simp only [FiniteShared, trace, subjects_retime input timing, List.forall_mem_map, retimed]
  rfl

omit [DecidableEq Instrument] in
private theorem affected_addReserve (policy : input.law.ReserveInsensitive)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (accepted : input.law.Valid item.before item.request) :
    History.affectedSubjects input (reserved reserve item) = History.affectedSubjects input item := by
  have enlarged := input.law.valid_addReserve policy item.before reserve nonnegative item.request accepted
  have flow : input.law.actualCredit (item.before.addReserve reserve) item.request =
      input.law.actualCredit item.before item.request := by
    rw [RawLaw.actualCredit, if_pos enlarged, RawLaw.actualCredit, if_pos accepted]
    rfl
  simp only [History.affectedSubjects, reserved]
  rw [flow]

theorem finiteShared_addReserve (policy : input.law.ReserveInsensitive)
    (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (word : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ input.law.rawItems current word, input.law.Valid item.before item.request)
    (shared : FiniteShared input current word) : FiniteShared input (current.addReserve reserve) word := by
  have trace := executed_items_addReserve input policy current reserve nonnegative 0 word accepted
  change input.law.rawItems (current.addReserve reserve) word =
    (input.law.rawItems current word).map (reserved reserve) at trace
  have persons : subjects input (current.addReserve reserve) word = subjects input current word := by
    simp only [subjects, trace, List.flatMap_map]
    apply List.flatMap_congr
    intro item present
    exact affected_addReserve input policy item reserve nonnegative (accepted item present)
  intro item present port required person member
  rw [trace] at present
  obtain ⟨original, source, rfl⟩ := List.mem_map.mp present
  rw [persons] at member
  exact shared original source port required person member

theorem autonomous_addReserve (policy : input.law.ReserveInsensitive)
    (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ reserve person good)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument)
    (paid : Exit.AutonomousProduction.Checks input.law current members word) :
    Exit.AutonomousProduction.Checks input.law (current.addReserve reserve) members word := by
  have accepted := fun item present => (paid.1 item present).1.2.2.1
  have trace := executed_items_addReserve input policy current reserve nonnegative 0 word accepted
  change input.law.rawItems (current.addReserve reserve) word =
    (input.law.rawItems current word).map (reserved reserve) at trace
  refine ⟨?_, ?_⟩
  · intro item present
    rw [trace] at present
    obtain ⟨original, source, rfl⟩ := List.mem_map.mp present
    obtain ⟨self, signer⟩ := paid.1 original source
    exact ⟨⟨self.1, self.2.1, input.law.valid_addReserve policy _ reserve nonnegative _ self.2.2.1,
      self.2.2.2⟩, signer⟩
  · intro person member
    rw [policy.necessities, policy.maintenance]
    exact ⟨bundlePaid_addReserve input policy current reserve nonnegative word accepted person _ _ (paid.2 person member).1,
      bundlePaid_addReserve input policy current reserve nonnegative word accepted person _ _ (paid.2 person member).2⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration
