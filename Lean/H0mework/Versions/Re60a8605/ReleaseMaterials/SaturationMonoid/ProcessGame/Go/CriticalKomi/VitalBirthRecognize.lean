import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth

theorem plan_area_le_possible {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) :
    (VitalChambers.points plan.detected.geometry).card ≤
      CoalitionBirth.possibleArea board colour := by
  let occupied := RegionAction.stones board colour
  let old := occupied ∪ occupied.biUnion adjacentPoints
  have oldOwn {stone : Point n}
      (value : Board.set board plan.point (some colour) stone = some colour)
      (different : stone ≠ plan.point) : stone ∈ occupied := by
    rw [Board.set_other _ _ different] at value
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, value⟩
  have included : VitalChambers.points plan.detected.geometry ⊆
      old ∪ insert plan.point (adjacentPoints plan.point) := by
    intro point member
    rcases Finset.mem_union.mp member with stone | eye
    · by_cases same : point = plan.point
      · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl same))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (oldOwn (plan.detected.holds.1 point stone) same))
    · obtain ⟨_, ⟨stone, adjacent⟩, boundary⟩ :=
        VitalChambers.eye_data plan.detected.holds eye
      have reversed := mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
        (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))
      by_cases same : stone = plan.point
      · subst stone
        exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr reversed))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨stone, oldOwn (boundary stone adjacent) same, reversed⟩))
  have unionBound := (Finset.card_le_card included).trans (Finset.card_union_le _ _)
  have inserted := Finset.card_insert_le plan.point (adjacentPoints plan.point)
  have addition : 1 + (adjacentPoints plan.point).card ≤
      (Finset.univ : Finset (Point n)).sup (fun point => 1 + (adjacentPoints point).card) :=
    Finset.le_sup (f := fun point : Point n => 1 + (adjacentPoints point).card)
      (Finset.mem_univ plan.point)
  have whole := Finset.card_le_card
    (Finset.subset_univ (VitalChambers.points plan.detected.geometry))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at whole
  change _ ≤ min (n * n) (old.card + _)
  exact Nat.le_min.mpr ⟨whole, by omega⟩

theorem plan_accepted_possible {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (threshold : Int)
    (accepted : acceptsMargin colour threshold
      (VitalChambers.bound plan.detected.geometry colour) = true) :
    acceptsMargin colour threshold (CoalitionBirth.possibleBound board colour) = true := by
  have area := plan_area_le_possible plan
  cases colour with
  | positive =>
      have bound : threshold ≤ 2 * ((VitalChambers.points plan.detected.geometry).card : Int) -
          ((n * n : Nat) : Int) := of_decide_eq_true accepted
      apply decide_eq_true
      change threshold ≤ 2 * (CoalitionBirth.possibleArea board .positive : Int) -
        ((n * n : Nat) : Int)
      omega
  | negative =>
      have bound : ((n * n : Nat) : Int) -
          2 * ((VitalChambers.points plan.detected.geometry).card : Int) ≤ threshold :=
        of_decide_eq_true accepted
      apply decide_eq_true
      change ((n * n : Nat) : Int) -
        2 * (CoalitionBirth.possibleArea board .negative : Int) ≤ threshold
      omega

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthRecognize

structure SavedCandidate {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) extends VitalBirth.Candidate frame colour threshold seen where
  saved : VitalBirth.SavedCore plan

/-- The source may generate different room families for different completion
points. Retain the first saved candidate and stop when a distinct one is paid. -/
def scanMiai? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (playing : frame.visible.status = .playing) (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) :
    List (Point n) → Option (SavedCandidate frame colour threshold seen) →
      Option (Certificate colour threshold frame)
  | [], _ => none
  | point :: rest, first =>
      match VitalBirth.candidate? frame colour threshold seen point with
      | none => scanMiai? frame colour threshold seen tracked playing opponent passes rest first
      | some candidate =>
          if saved : VitalBirth.SavedCore candidate.plan then
            match first with
            | none => scanMiai? frame colour threshold seen tracked playing opponent passes rest
                (some ⟨candidate, saved⟩)
            | some retained =>
                if distinct : retained.plan.point ≠ candidate.plan.point then
                  some (VitalBirth.miaiCertificate seen tracked retained.plan candidate.plan distinct
                    retained.saved saved retained.virgin candidate.virgin playing opponent passes
                    threshold retained.accepted candidate.accepted)
                else scanMiai? frame colour threshold seen tracked playing opponent passes rest first
          else scanMiai? frame colour threshold seen tracked playing opponent passes rest first

def recognize? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int) :
    Option (Certificate colour threshold frame) :=
  if playing : frame.visible.status = .playing then
    if acceptsMargin colour threshold (CoalitionBirth.possibleBound frame.visible.board colour) then
      let seen := CoalitionBirth.retained frame colour
      have tracked := CoalitionBirth.retained_tracked frame colour
      if owned : frame.visible.toMove = colour then
        (allPoints n).findSome? (fun point =>
          (VitalBirth.candidate? frame colour threshold seen point).map (fun candidate =>
            VitalBirth.ownCertificate seen tracked candidate.plan candidate.virgin playing owned
              threshold candidate.accepted))
      else
        have opponent : frame.visible.toMove = colour.other := by
          cases colour <;> cases turn : frame.visible.toMove <;> simp_all [Polarity.other]
        if passes : frame.visible.consecutivePasses = 0 then
          scanMiai? frame colour threshold seen tracked playing opponent passes (allPoints n) none
        else none
    else none
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthRecognize
