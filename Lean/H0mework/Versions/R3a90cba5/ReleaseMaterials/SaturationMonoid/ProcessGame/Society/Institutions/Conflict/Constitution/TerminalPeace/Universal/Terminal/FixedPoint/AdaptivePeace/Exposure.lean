import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace

open Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (community : Party → Community) (law : RawLaw Party Good Port Technology Instrument)
  (raw : RawCurrent Party Good Technology Instrument) (bid : ReviewBid Party Good Port Technology Instrument)

local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Key" => Party × Good

private def itemDemands (item : Item) (key : Key) : Prop :=
  community key.1 ≠ community item.request.signer ∧
    key.1 ∉ item.request.consents ∧
    flowAt (law.credit item.before item.request) key.1 key.2 <
      flowAt (law.debit item.before item.request) key.1 key.2

private instance [DecidableEq Community] (item : Item) (key : Key) :
    Decidable (itemDemands community law item key) := by
  unfold itemDemands
  infer_instance

/-- The demanded exposure uses the original instruction's signer even
when the filer is someone else or the instruction is refused. -/
def demandsAt (key : Key) : Prop :=
  ∃ item ∈ law.rawItems raw bid.attempted, itemDemands community law item key

private def declaredCells (item : Item) : List Key :=
  (law.debit item.before item.request).map Prod.fst ++ (law.credit item.before item.request).map Prod.fst

omit [DecidableEq Instrument] in
private theorem demand_in_declaredCells {item : Item} {key : Key}
    (demand : itemDemands community law item key) :
    key ∈ declaredCells law item := by
  by_contra absent
  have noDebit : flowAt (law.debit item.before item.request) key.1 key.2 = 0 := by
    apply amount_zero_of_absent
    intro lot listed same
    exact absent (List.mem_append_left _ (List.mem_map.mpr ⟨lot, listed, same⟩))
  have noCredit : flowAt (law.credit item.before item.request) key.1 key.2 = 0 := by
    apply amount_zero_of_absent
    intro lot listed same
    exact absent (List.mem_append_right _ (List.mem_map.mpr ⟨lot, listed, same⟩))
  have net := demand.2.2
  rw [noDebit, noCredit] at net
  exact (lt_irrefl 0) net

variable [DecidableEq Community]

/-- Scan both declared flows of each original instruction. An alias can
change the proposal but cannot change the key for the same exposed cell. -/
def demanded : Finset Key :=
  ((law.rawItems raw bid.attempted).flatMap fun item =>
    (declaredCells law item).filter fun key => decide (itemDemands community law item key)).toFinset

theorem mem_demanded_iff (key : Key) :
    key ∈ demanded community law raw bid ↔ demandsAt community law raw bid key := by
  simp only [demanded, List.mem_toFinset, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, demandsAt]
  constructor
  · rintro ⟨item, listed, _, demand⟩
    exact ⟨item, listed, demand⟩
  · rintro ⟨item, listed, demand⟩
    exact ⟨item, listed, demand_in_declaredCells community law demand, demand⟩

theorem demanded_nonempty_iff :
    (demanded community law raw bid).Nonempty ↔
      ∃ item ∈ law.rawItems raw bid.attempted, ∃ victim good,
        community victim ≠ community item.request.signer ∧ victim ∉ item.request.consents ∧
          flowAt (law.credit item.before item.request) victim good <
            flowAt (law.debit item.before item.request) victim good := by
  constructor
  · rintro ⟨key, listed⟩
    obtain ⟨item, original, demand⟩ := (mem_demanded_iff community law raw bid key).mp listed
    exact ⟨item, original, key.1, key.2, demand⟩
  · rintro ⟨item, original, victim, good, foreign, unconsented, net⟩
    exact ⟨(victim, good), (mem_demanded_iff community law raw bid (victim, good)).mpr
      ⟨item, original, foreign, unconsented, net⟩⟩

theorem existing_aggression_is_included
    (aggression : DemandsAggression (community := community) law raw bid) :
    (demanded community law raw bid).Nonempty := by
  obtain ⟨item, original, signer, victim, good, foreign, unconsented, net⟩ := aggression
  apply (demanded_nonempty_iff community law raw bid).mpr
  exact ⟨item, original, victim, good, signer.symm ▸ foreign, unconsented, net⟩

theorem demanded_nonempty_iff_of_same_signer
    (sameSigner : ∀ item ∈ law.rawItems raw bid.attempted, item.request.signer = bid.payer) :
    (demanded community law raw bid).Nonempty ↔ DemandsAggression (community := community) law raw bid := by
  refine ⟨?_, existing_aggression_is_included community law raw bid⟩
  intro nonempty
  obtain ⟨item, original, victim, good, foreign, unconsented, net⟩ :=
    (demanded_nonempty_iff community law raw bid).mp nonempty
  have signer := sameSigner item original
  exact ⟨item, original, signer, victim, good, signer ▸ foreign, unconsented, net⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace
