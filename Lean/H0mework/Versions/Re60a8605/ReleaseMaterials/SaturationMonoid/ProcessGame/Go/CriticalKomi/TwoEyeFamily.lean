import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeRecognize

/-!
All source-recognized groups of one colour share one surviving area carrier.
Its finite union counts overlapping cores and eyes once.  Pointwise native
preservation makes the whole family a forcing invariant and generates one
executable policy with the resulting whole-play area bound.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeFamily

abbrev Family (n : Nat) := List (TwoEye.Geometry n)

def groupPoints {n : Nat} (geometry : TwoEye.Geometry n) : Finset (Point n) :=
  geometry.core ∪ {geometry.eye₁, geometry.eye₂}

def points {n : Nat} : Family n → Finset (Point n)
  | [] => ∅
  | geometry :: remaining => groupPoints geometry ∪ points remaining

def Holds {n : Nat} (family : Family n) (colour : Polarity) (board : Board n) : Prop :=
  ∀ geometry ∈ family, TwoEye.Holds geometry colour board

instance {n : Nat} (family : Family n) (colour : Polarity) (board : Board n) :
    Decidable (Holds family colour board) :=
  inferInstanceAs (Decidable (∀ geometry ∈ family, TwoEye.Holds geometry colour board))

theorem groupPoints_subset_area {n : Nat} {geometry : TwoEye.Geometry n}
    {colour : Polarity} {board : Board n} (inside : TwoEye.Holds geometry colour board) :
    groupPoints geometry ⊆ TwoEye.Score.areaPoints board colour := by
  intro point member
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_union.mp member with coreMember | eyeMember
  · exact Or.inl (TwoEye.core_colour inside coreMember)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at eyeMember
    rcases eyeMember with rfl | rfl
    · exact Or.inr (TwoEye.Score.eye₁_owner inside)
    · exact Or.inr (TwoEye.Score.eye₂_owner inside)

theorem points_subset_area {n : Nat} (family : Family n) {colour : Polarity}
    {board : Board n} (inside : Holds family colour board) :
    points family ⊆ TwoEye.Score.areaPoints board colour := by
  induction family with
  | nil => exact Finset.empty_subset _
  | cons geometry remaining ih =>
      apply Finset.union_subset
      · exact groupPoints_subset_area (inside geometry List.mem_cons_self)
      · exact ih (fun next member => inside next (List.mem_cons_of_mem geometry member))

/-- No pairwise disjointness is required: scoring consumes the deduplicated union. -/
theorem area_lower {n : Nat} (family : Family n) {colour : Polarity}
    {board : Board n} (inside : Holds family colour board) :
    (points family).card ≤ areaScore board colour :=
  Finset.card_le_card (points_subset_area family inside)

theorem points_duplicate {n : Nat} (geometry : TwoEye.Geometry n) (remaining : Family n) :
    points (geometry :: geometry :: remaining) = points (geometry :: remaining) := by
  simp only [points, ← Finset.union_assoc, Finset.union_self]

def bound {n : Nat} (family : Family n) : Polarity → Int
  | .positive => 2 * ((points family).card : Int) - ((n * n : Nat) : Int)
  | .negative => ((n * n : Nat) : Int) - 2 * ((points family).card : Int)

@[simp] theorem empty_positive_bound (n : Nat) :
    bound ([] : Family n) .positive = -((n * n : Nat) : Int) := by
  simp only [bound, points, Finset.card_empty, Nat.cast_zero, mul_zero, zero_sub]

@[simp] theorem empty_negative_bound (n : Nat) :
    bound ([] : Family n) .negative = ((n * n : Nat) : Int) := by
  simp only [bound, points, Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero]

theorem score_accepted {n : Nat} (family : Family n) (colour : Polarity) (board : Board n)
    (inside : Holds family colour board) :
    acceptsMargin colour (bound family colour) (areaMargin board) = true := by
  cases colour with
  | positive =>
      exact decide_eq_true
        (TwoEye.Score.black_margin_bound board (points family).card (area_lower family inside))
  | negative =>
      exact decide_eq_true
        (TwoEye.Score.white_margin_bound board (points family).card (area_lower family inside))

theorem opponent_legalStep_preserves {n : Nat} {family : Family n} {colour : Polarity}
    {frame target : Frame n} {move : Move n}
    (inside : Holds family colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other) (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    Holds family colour target.visible.board := by
  intro geometry member
  exact TwoEye.opponent_legalStep_preserves (inside geometry member) opponent scoring step

def invariant {n : Nat} (family : Family n) (colour : Polarity) (frame : Frame n) : Bool :=
  (frame.visible.status == .playing || frame.visible.status == .terminal .twoPasses) &&
    decide (Holds family colour frame.visible.board)

theorem invariant_iff {n : Nat} (family : Family n) (colour : Polarity) (frame : Frame n) :
    invariant family colour frame = true ↔ ScoringStatus frame ∧ Holds family colour frame.visible.board := by
  simp [invariant, ScoringStatus]

theorem closed {n : Nat} (family : Family n) (colour : Polarity) :
    ClosedUnderNativeForcing colour (bound family colour) (invariant family colour) := by
  intro frame recognized
  obtain ⟨scoring, inside⟩ := (invariant_iff family colour frame).mp recognized
  cases status : frame.visible.status with
  | terminal reason =>
      have scored : reason = .twoPasses := by
        rcases scoring with playing | scored
        · rw [status] at playing
          contradiction
        · rw [status] at scored
          exact Status.terminal.inj scored
      subst reason
      simpa only [forcingRead, status, terminalGood, beq_self_eq_true, Bool.true_and] using
        score_accepted family colour frame.visible.board inside
  | playing =>
      simp only [forcingRead, status]
      by_cases owned : frame.visible.toMove = colour
      · apply (preimage_own colour frame (invariant family colour) owned).mpr
        let reply := passReply frame status
        refine ⟨reply.move, reply.target, reply.step, reply.notResign, ?_⟩
        apply (invariant_iff family colour reply.target).mpr
        exact ⟨nonresigning_step_scoringStatus reply.notResign reply.step, inside⟩
      · apply (preimage_opponent colour frame (invariant family colour) owned).mpr
        intro move target step permitted
        have opponent : frame.visible.toMove = colour.other := by
          cases colour <;> cases toMove : frame.visible.toMove <;> simp_all
        exact (invariant_iff family colour target).mpr
          ⟨nonresigning_step_scoringStatus permitted step,
            opponent_legalStep_preserves inside opponent permitted step⟩

def closure {n : Nat} (family : Family n) (colour : Polarity) :=
  compileSurvival colour (bound family colour) (invariant family colour) (closed family colour)

def policy {n : Nat} (family : Family n) (colour : Polarity) : ExecutablePolicy n :=
  (closure family colour).policy

theorem against_every_policy {n : Nat} (family : Family n) (colour : Polarity) (frame : Frame n)
    (inside : Holds family colour frame.visible.board) (scoring : ScoringStatus frame)
    (opponent : ExecutablePolicy n) :
    acceptsMargin colour (bound family colour)
      (areaMargin (executePolicies (versus colour (policy family colour) opponent)
        frame scoring).replay.final.visible.board) = true :=
  (closure family colour).against_every_policy
    ((invariant_iff family colour frame).mpr ⟨scoring, inside⟩) scoring opponent

structure Detected {n : Nat} (board : Board n) (colour : Polarity) where
  family : Family n
  holds : Holds family colour board

def Detected.prepend {n : Nat} {board : Board n} {colour : Polarity}
    (head : TwoEye.Detected board colour) (tail : Detected board colour) : Detected board colour where
  family := head.geometry :: tail.family
  holds := by
    intro geometry member
    rcases List.mem_cons.mp member with same | remaining
    · subst geometry
      exact head.holds
    · exact tail.holds geometry remaining

/-- Original group membership avoids repeated recognition work.  Every retained
geometry and its law still come from the board's own recognizer. -/
def scan {n : Nat} (board : Board n) (colour : Polarity) :
    List (Point n) → Finset (Point n) → Detected board colour
  | [], _ => ⟨[], by intro geometry member; cases member⟩
  | seed :: remaining, visited =>
      if seed ∈ visited then scan board colour remaining visited
      else if board seed = some colour then
        let tail := scan board colour remaining (visited ∪ groupAt board seed)
        match TwoEye.recognizeSeed? board colour seed with
        | none => tail
        | some detected => tail.prepend detected
      else scan board colour remaining visited

def recognize {n : Nat} (board : Board n) (colour : Polarity) : Detected board colour :=
  scan board colour (allPoints n) ∅

def Detected.bound {n : Nat} {board : Board n} {colour : Polarity}
    (detected : Detected board colour) : Int :=
  TwoEyeFamily.bound detected.family colour

def Detected.policy {n : Nat} {board : Board n} {colour : Polarity}
    (detected : Detected board colour) : ExecutablePolicy n :=
  TwoEyeFamily.policy detected.family colour

theorem Detected.guarantee {n : Nat} (frame : Frame n) (colour : Polarity)
    (detected : Detected frame.visible.board colour) (scoring : ScoringStatus frame)
    (opponent : ExecutablePolicy n) :
    acceptsMargin colour detected.bound
      (areaMargin (executePolicies (versus colour detected.policy opponent)
        frame scoring).replay.final.visible.board) = true :=
  against_every_policy detected.family colour frame detected.holds scoring opponent

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeFamily
