import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Copy

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback

open Institutions.Capitalism.Universal.Source.Program

instance (current : Current) (parent child : Party) : Decidable (CopyResources current parent child) :=
  decidable_of_iff
    (current.technology = (true, true) ∧ parent ≠ child ∧ child ≠ 3 ∧
      2 ≤ current.stock parent .seed ∧ 8 ≤ current.stock parent .feed ∧
      1 ≤ current.stock parent .energy ∧ 2 ≤ current.stock parent .labor ∧
      2 ≤ current.stock parent .life ∧ 2 ≤ current.stock parent .spare ∧
      ∀ good, 0 ≤ current.stock child good)
    ⟨fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
      r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.1,
      r.2.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.2⟩,
      fun r => ⟨r.technology, r.distinct, r.ordinary, r.seed, r.feed, r.energy,
        r.labor, r.life, r.spare, r.child_stock⟩⟩

def parent (current : Current) : Party :=
  ((List.range (current.round + 6)).filter (fun actor => decide (0 < current.stock actor .seed))).getLast?.getD 0

def child (current : Current) : Party := max 6 (parent current + 1)

def budget : Bundle Good :=
  [(.seed, 2), (.feed, 8), (.energy, 1), (.labor, 2), (.life, 2), (.spare, 2)]

def reserve (supplier : Party) (good : Good) : ℚ :=
  if supplier = 3 then 0 else if good = .seed ∨ good = .life ∨ good = .spare then 1 else 0

def gatherGood (current : Current) (recipient : Party) (good : Good) (required : ℚ) :
    List Party → RawEvent Party Good Port Technology Unit
  | [] => []
  | supplier :: rest =>
      let quantity := min (max 0 (required - current.stock recipient good))
        (max 0 (current.stock supplier good - reserve supplier good))
      if supplier ≠ recipient ∧ 0 < quantity then
        let request := transfer supplier supplier recipient [(good, quantity)]
        request :: gatherGood (law.step current request) recipient good required rest
      else gatherGood current recipient good required rest

def gather (current : Current) (recipient : Party) : Bundle Good → RawEvent Party Good Port Technology Unit
  | [] => []
  | (good, required) :: rest =>
      let first := gatherGood current recipient good required [0, 3]
      first ++ gather (law.execute current 0 first).final recipient rest

def failedPrefix (current : Current) (parent child : Party) : RawEvent Party Good Port Technology Unit :=
  match attemptCopy current parent child with
  | .paid _ => []
  | .blocked failed _ _ => (copy parent child).take (failed.index + 1)

def recycle (current : Current) (recipient : Party) : RawEvent Party Good Port Technology Unit :=
  if current.stock recipient .spare < 2 ∧ 1 ≤ current.stock 0 .waste then
    [transfer 0 0 3 [(.waste, 1)], production 3, transfer 3 3 recipient [(.spare, 1)]]
  else []

def repairWord (current : Current) (parent child : Party) : RawEvent Party Good Port Technology Unit :=
  let first := failedPrefix current parent child
  let supplies := gather (law.execute current 0 first).final parent budget
  let regeneration := recycle (law.execute current 0 (first ++ supplies)).final parent
  first ++ supplies ++ regeneration

inductive Outcome (current : Current)
  | formation (original : Response current)
  | copied (resources : CopyResources current (parent current) (child current))
  | repair (missing : ¬ CopyResources current (parent current) (child current))

def respond (current : Current) : Outcome current :=
  if current.round ≤ 10 then .formation (Cell.respond current)
  else if resources : CopyResources current (parent current) (child current) then .copied resources
  else .repair resources

def Outcome.word {current : Current} : Outcome current → RawEvent Party Good Port Technology Unit
  | .formation original => original.word
  | .copied _ => copy (parent current) (child current)
  | .repair _ => repairWord current (parent current) (child current)

inductive Kind where
  | formation | copied | repair
  deriving DecidableEq, Repr

def Outcome.kind {current : Current} : Outcome current → Kind
  | .formation _ => .formation
  | .copied _ => .copied
  | .repair _ => .repair

structure Deficit (current : Current) (actor : Party) where
  good : Good
  required : ℚ
  declared : (good, required) ∈ budget
  short : current.stock actor good < required

def deficits (current : Current) (actor : Party) : List (Deficit current actor) :=
  budget.attach.flatMap fun item =>
    if short : current.stock actor item.val.1 < item.val.2 then
      [⟨item.val.1, item.val.2, item.property, short⟩]
    else []

def Outcome.remaining {current : Current} (outcome : Outcome current) :
    List (Deficit (law.next current outcome.word) (parent current)) :=
  deficits (law.next current outcome.word) (parent current)

theorem paid_word (current : Current)
    (resources : CopyResources current (parent current) (child current)) (started : 10 < current.round) :
    (respond current).word = copy (parent current) (child current) := by
  simp only [respond, if_neg (by omega : ¬ current.round ≤ 10), dif_pos resources, Outcome.word]

theorem repair_word (current : Current)
    (missing : ¬ CopyResources current (parent current) (child current)) (started : 10 < current.round) :
    (respond current).word = repairWord current (parent current) (child current) := by
  simp only [respond, if_neg (by omega : ¬ current.round ≤ 10), dif_neg missing, Outcome.word]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback
