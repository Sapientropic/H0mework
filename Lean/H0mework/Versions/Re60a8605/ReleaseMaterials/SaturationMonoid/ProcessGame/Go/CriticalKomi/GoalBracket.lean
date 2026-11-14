import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.SourceLeaf

/-!
The fixed original 19×19 initial frame generates a certified score bracket from
finite board area and legal pass policies.  Each source answer replaces exactly
one bound and its unilateral executable policy.  Equality alone permits the
existing exact-margin consumer to read the two guarantees at one integer.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.GoalBracket

structure Bracket where
  lower : Int
  upper : Int
  white : ExecutablePolicy 19
  black : ExecutablePolicy 19
  white_guarantee : ∀ opponent : ExecutablePolicy 19,
    areaMargin (initialPlay 19 (versus .negative white opponent)).replay.final.visible.board ≤ upper
  black_guarantee : ∀ opponent : ExecutablePolicy 19,
    lower ≤ areaMargin (initialPlay 19 (versus .positive black opponent)).replay.final.visible.board

/-- The opposing views select the same policies on the same actual native play. -/
theorem versus_same_profile (white black : ExecutablePolicy 19) :
    versus .negative white black = versus .positive black white := by
  funext colour
  cases colour <;> simp only [versus, reduceCtorEq, if_false, if_true]

namespace Bracket

theorem lower_le_upper (bracket : Bracket) : bracket.lower ≤ bracket.upper := by
  have upper := bracket.white_guarantee bracket.black
  have lower := bracket.black_guarantee bracket.white
  rw [← versus_same_profile bracket.white bracket.black] at lower
  exact Int.le_trans lower upper

end Bracket

def initial : Bracket where
  lower := -361
  upper := 361
  white := passPolicy 19
  black := passPolicy 19
  white_guarantee opponent := by
    have bound := TwoEye.Score.white_margin_bound
      (initialPlay 19 (versus .negative (passPolicy 19) opponent)).replay.final.visible.board
      0 (Nat.zero_le _)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at bound
    exact bound
  black_guarantee opponent := by
    have bound := TwoEye.Score.black_margin_bound
      (initialPlay 19 (versus .positive (passPolicy 19) opponent)).replay.final.visible.board
      0 (Nat.zero_le _)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_sub] at bound
    exact bound

/-- A delivered unilateral guarantee contains runnable strategy data for this
exact original initial frame. Mathematical existence alone cannot fill it. -/
structure InitialBound where
  colour : Polarity
  value : Int
  policy : ExecutablePolicy 19
  guarantee : ∀ opponent : ExecutablePolicy 19,
    acceptsMargin colour value
      (areaMargin (initialPlay 19 (versus colour policy opponent)).replay.final.visible.board) = true

namespace InitialBound

def ofCertificate {colour : Polarity} {value : Int}
    (certificate : Certificate colour value (Frame.initial 19)) : InitialBound where
  colour := colour
  value := value
  policy := certificate.policy
  guarantee opponent := certificate.guarantee (.inl rfl) opponent

def ofAnswer {threshold : Int} (answer : Answer threshold (Frame.initial 19)) : InitialBound :=
  match answer with
  | .white certificate => ofCertificate certificate
  | .black certificate => ofCertificate certificate

def Improves (bound : InitialBound) (bracket : Bracket) : Prop :=
  match bound.colour with
  | .positive => bracket.lower < bound.value
  | .negative => bound.value < bracket.upper

instance (bound : InitialBound) (bracket : Bracket) : Decidable (bound.Improves bracket) := by
  unfold Improves
  cases bound.colour <;> infer_instance

end InitialBound

namespace Bracket

/-- Receive any already generated original unilateral strategy. The other side
is preserved, and a weaker receipt keeps the previously paid strategy data. -/
def absorb (bracket : Bracket) (bound : InitialBound) : Bracket :=
  match colour : bound.colour with
  | .positive =>
      if bracket.lower < bound.value then {
        lower := bound.value
        upper := bracket.upper
        white := bracket.white
        black := bound.policy
        white_guarantee := bracket.white_guarantee
        black_guarantee opponent := by
          have paid := bound.guarantee opponent
          rw [colour] at paid
          simpa only [acceptsMargin, decide_eq_true_eq] using paid
      } else bracket
  | .negative =>
      if bound.value < bracket.upper then {
        lower := bracket.lower
        upper := bound.value
        white := bound.policy
        black := bracket.black
        white_guarantee opponent := by
          have paid := bound.guarantee opponent
          rw [colour] at paid
          simpa only [acceptsMargin, decide_eq_true_eq] using paid
        black_guarantee := bracket.black_guarantee
      } else bracket

theorem absorb_of_not_improves (bracket : Bracket) (bound : InitialBound)
    (stable : ¬ bound.Improves bracket) : bracket.absorb bound = bracket := by
  rcases bound with ⟨colour, value, policy, guarantee⟩
  cases colour <;> simp_all [absorb, InitialBound.Improves]

theorem absorb_bounds (bracket : Bracket) (bound : InitialBound) :
    bracket.lower ≤ (bracket.absorb bound).lower ∧
      (bracket.absorb bound).upper ≤ bracket.upper := by
  unfold absorb
  split <;> split <;> simp_all <;> omega

def cut (bracket : Bracket) : Int := (bracket.lower + bracket.upper) / 2

theorem cut_bounds (bracket : Bracket) (nontrivial : bracket.lower < bracket.upper) :
    bracket.lower ≤ bracket.cut ∧ bracket.cut < bracket.upper := by
  unfold cut
  omega

def gap (bracket : Bracket) : Nat := (bracket.upper - bracket.lower).toNat

def update (bracket : Bracket) (answer : Answer bracket.cut (Frame.initial 19)) : Bracket :=
  match answer with
  | .white certificate => {
      lower := bracket.lower
      upper := bracket.cut
      white := certificate.policy
      black := bracket.black
      white_guarantee := fun opponent => by
        simpa only [initialPlay, acceptsMargin, decide_eq_true_eq] using
          certificate.guarantee (Or.inl rfl) opponent
      black_guarantee := bracket.black_guarantee
    }
  | .black certificate => {
      lower := bracket.cut + 1
      upper := bracket.upper
      white := bracket.white
      black := certificate.policy
      white_guarantee := bracket.white_guarantee
      black_guarantee := fun opponent => by
        simpa only [initialPlay, acceptsMargin, decide_eq_true_eq] using
          certificate.guarantee (Or.inl rfl) opponent
    }

theorem update_width_lt (bracket : Bracket)
    (answer : Answer bracket.cut (Frame.initial 19))
    (nontrivial : bracket.lower < bracket.upper) :
    (update bracket answer).upper - (update bracket answer).lower <
      bracket.upper - bracket.lower := by
  have bounds := cut_bounds bracket nontrivial
  cases answer with
  | white certificate =>
      change bracket.cut - bracket.lower < bracket.upper - bracket.lower
      omega
  | black certificate =>
      change bracket.upper - (bracket.cut + 1) < bracket.upper - bracket.lower
      omega

theorem update_gap_lt (bracket : Bracket)
    (answer : Answer bracket.cut (Frame.initial 19))
    (unsettled : bracket.lower ≠ bracket.upper) :
    (update bracket answer).gap < bracket.gap := by
  have ordered := lower_le_upper bracket
  have nextOrdered := lower_le_upper (update bracket answer)
  have progress := update_width_lt bracket answer (by omega)
  unfold gap
  omega

def finish (bracket : Bracket) (settled : bracket.lower = bracket.upper) : ExactInitialMargin where
  value := bracket.lower
  white := bracket.white
  black := bracket.black
  white_guarantee opponent := by
    rw [settled]
    exact bracket.white_guarantee opponent
  black_guarantee := bracket.black_guarantee

end Bracket

export Bracket (lower_le_upper cut cut_bounds gap update update_width_lt update_gap_lt finish)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.GoalBracket
