import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.ReplayRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

structure Snapshot (Technology : Type) where
  stock : List (List ℚ)
  claims : List (List (List ℚ))
  technology : Technology
  clock : ℚ
  round : Nat
  deriving DecidableEq

def snapshot (current : RawCurrent Party Good Technology Instrument) : Snapshot Technology :=
  ⟨code.parties.map (fun party => code.goods.map (current.stock party)),
    code.instruments.map (fun instrument => code.parties.map (fun debtor => code.parties.map (current.claims instrument debtor))),
    current.technology, current.clock, current.round⟩

private theorem map_read {α β : Type} (keys : List α) (first second : α → β)
    (same : keys.map first = keys.map second) (key : α) (inside : key ∈ keys) : first key = second key := by
  induction keys with
  | nil => cases inside
  | cons head tail ih =>
      obtain ⟨atHead, atTail⟩ := List.cons.inj same
      rcases List.mem_cons.mp inside with rfl | later
      · exact atHead
      · exact ih atTail later

omit [DecidableEq Port] [DecidableEq Technology] in
theorem snapshot_injective : Function.Injective (snapshot code) := by
  intro first second same
  apply RawCurrent.ext
  · funext party good
    exact map_read code.goods _ _
      (map_read code.parties _ _ (congrArg Snapshot.stock same) party (code.parties_cover party)) good (code.goods_cover good)
  · funext instrument debtor creditor
    exact map_read code.parties _ _
      (map_read code.parties _ _
        (map_read code.instruments _ _ (congrArg Snapshot.claims same) instrument (code.instruments_cover instrument))
        debtor (code.parties_cover debtor)) creditor (code.parties_cover creditor)
  · exact congrArg Snapshot.technology same
  · exact congrArg Snapshot.clock same
  · exact congrArg Snapshot.round same

inductive VisitImage (Technology : Type) where
  | bootstrap
  | running (current : Snapshot Technology) (past : List (Snapshot Technology))
  deriving DecidableEq

def visitImage : ProgrammeSource.Current (RawCurrent Party Good Technology Instrument) → VisitImage Technology
  | .bootstrap => .bootstrap
  | .running current past => .running (snapshot code current) (past.map (snapshot code))

omit [DecidableEq Port] [DecidableEq Technology] in
theorem visitImage_injective : Function.Injective (visitImage code) := by
  intro first second same
  cases first <;> cases second
  · rfl
  · cases same
  · cases same
  · obtain ⟨current, past⟩ := VisitImage.running.inj same
    congr
    · exact snapshot_injective code current
    · exact List.map_injective_iff.mpr (snapshot_injective code) past

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity
