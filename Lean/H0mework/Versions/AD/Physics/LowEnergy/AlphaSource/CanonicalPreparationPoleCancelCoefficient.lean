import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationPoleSourceDivision

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPoleCancellation
open PreparationVacuumDAGCoefficient PreparationVacuumClockSymbol PreparationVacuumEngineBudget
open scoped BigOperators

def lowerExponent (e : PoleExponent) (i : Fin 3) : PoleExponent := Function.update e i (e i-1)

theorem lowerExponent_le (e : PoleExponent) (i j : Fin 3) : lowerExponent e i j≤e j := by
  by_cases same : j=i
  · subst j;simp [lowerExponent]
  · simp [lowerExponent,same]

theorem lowerExponent_factor (e : PoleExponent) (i : Fin 3) (positive : 0<e i)
    (x : SourcePhase) : sourceDenominator e x=poleFunction i x*sourceDenominator (lowerExponent e i) x := by
  have split : e=Pi.single i 1+lowerExponent e i := by
    funext j
    by_cases same : j=i
    · subst j;simp [lowerExponent];omega
    · simp [lowerExponent,same]
  calc
    sourceDenominator e x=sourceDenominator (Pi.single i 1+lowerExponent e i) x := congrArg (fun e=>sourceDenominator e x) split
    _=sourceDenominator (Pi.single i 1) x*sourceDenominator (lowerExponent e i) x := sourceDenominator_add _ _ x
    _=poleFunction i x*sourceDenominator (lowerExponent e i) x := by
      simp [sourceDenominator,Pi.single_apply]

def cancelStep (i : Fin 3) (c : NormalizedCoefficient) : NormalizedCoefficient :=
  if c.numerator=0 then ⟨0,0⟩ else
  if c.poles i=0 then c else
  if poleRemainder i c.numerator=0 then ⟨poleQuotient i c.numerator,lowerExponent c.poles i⟩ else c

theorem cancelStep_source (i : Fin 3) (c : NormalizedCoefficient) (x : SourcePhase) (hx : x∈poleDomain) :
    coefficientValue (cancelStep i c) x=coefficientValue c x := by
  unfold cancelStep
  split_ifs with numzero expzero remainder
  · simp [coefficientValue,numzero]
  · rfl
  · have identity:=congrArg (evalAt x) (poleDivision_identity i c.numerator)
    simp only [map_mul,remainder,add_zero,polePolynomial_source] at identity
    have exponent : 0<c.poles i:=Nat.pos_of_ne_zero expzero
    change evalAt x (poleQuotient i c.numerator)/sourceDenominator (lowerExponent c.poles i) x=
      evalAt x c.numerator/sourceDenominator c.poles x
    rw [identity,lowerExponent_factor c.poles i exponent x]
    field_simp [poleFunction_nonzero x hx i,sourceDenominator_nonzero (lowerExponent c.poles i) x hx]
  · rfl

theorem cancelStep_poles_le (i : Fin 3) (c : NormalizedCoefficient) (j : Fin 3) :
    (cancelStep i c).poles j≤c.poles j := by
  unfold cancelStep
  split_ifs
  · exact Nat.zero_le _
  · exact le_refl _
  · exact lowerExponent_le _ _ _
  · exact le_refl _

def cancelAt (i : Fin 3) (fuel : ℕ) (c : NormalizedCoefficient) : NormalizedCoefficient :=
  Nat.rec c (fun _ current=>cancelStep i current) fuel

theorem cancelAt_source (i : Fin 3) (fuel : ℕ) (c : NormalizedCoefficient)
    (x : SourcePhase) (hx : x∈poleDomain) : coefficientValue (cancelAt i fuel c) x=coefficientValue c x := by
  induction fuel with
  | zero=>rfl
  | succ n ih=>exact (cancelStep_source i (cancelAt i n c) x hx).trans ih

theorem cancelAt_poles_le (i : Fin 3) (fuel : ℕ) (c : NormalizedCoefficient) (j : Fin 3) :
    (cancelAt i fuel c).poles j≤c.poles j := by
  induction fuel with
  | zero=>exact le_refl _
  | succ n ih=>exact (cancelStep_poles_le i (cancelAt i n c) j).trans ih

def cancelCoefficient (c : NormalizedCoefficient) : NormalizedCoefficient :=
  cancelAt 2 (c.poles 2) (cancelAt 1 (c.poles 1) (cancelAt 0 (c.poles 0) c))

theorem cancelCoefficient_source (c : NormalizedCoefficient) (x : SourcePhase) (hx : x∈poleDomain) :
    coefficientValue (cancelCoefficient c) x=coefficientValue c x := by
  exact (cancelAt_source 2 _ _ x hx).trans ((cancelAt_source 1 _ _ x hx).trans (cancelAt_source 0 _ _ x hx))

theorem cancelCoefficient_poles_le (c : NormalizedCoefficient) (j : Fin 3) :
    (cancelCoefficient c).poles j≤c.poles j :=
  (cancelAt_poles_le 2 _ _ j).trans ((cancelAt_poles_le 1 _ _ j).trans (cancelAt_poles_le 0 _ _ j))

def CancelledAt (i : Fin 3) (c : NormalizedCoefficient) : Prop :=
  c.poles i=0 ∨ ¬ polePolynomial i∣c.numerator

theorem cancelStep_preserves_reduced (j i : Fin 3) (c : NormalizedCoefficient)
    (reduced : CancelledAt i c) : CancelledAt i (cancelStep j c) := by
  rcases reduced with exponent|nondiv
  · left
    have lower:=cancelStep_poles_le j c i
    rw [exponent] at lower
    exact Nat.eq_zero_of_le_zero lower
  · unfold cancelStep
    split_ifs with numzero expzero remainder
    · left;rfl
    · exact Or.inr nondiv
    · right
      intro divides
      apply nondiv
      have identity:=poleDivision_identity j c.numerator
      rw [remainder,add_zero] at identity
      rw [identity]
      exact dvd_mul_of_dvd_left divides _
    · exact Or.inr nondiv

theorem cancelAt_preserves_reduced (j i : Fin 3) (fuel : ℕ) (c : NormalizedCoefficient)
    (reduced : CancelledAt i c) : CancelledAt i (cancelAt j fuel c) := by
  induction fuel with
  | zero=>exact reduced
  | succ n ih=>exact cancelStep_preserves_reduced j i (cancelAt j n c) ih

theorem cancelStep_decreases (i : Fin 3) (c : NormalizedCoefficient)
    (pending : ¬ CancelledAt i c) : (cancelStep i c).poles i+1≤c.poles i := by
  have positive : 0<c.poles i := Nat.pos_of_ne_zero (fun zero=>pending (Or.inl zero))
  have divisible : polePolynomial i∣c.numerator := Classical.not_not.mp (fun no=>pending (Or.inr no))
  have remainder:= (poleRemainder_zero_iff i c.numerator).mpr divisible
  unfold cancelStep
  split_ifs with numzero expzero
  · change 1≤c.poles i
    omega
  · exact (positive.ne' expzero).elim
  · simp [lowerExponent];omega

theorem cancelAt_progress (i : Fin 3) (fuel : ℕ) (c : NormalizedCoefficient) :
    CancelledAt i (cancelAt i fuel c) ∨ (cancelAt i fuel c).poles i+fuel≤c.poles i := by
  induction fuel with
  | zero=>right;simp [cancelAt]
  | succ n ih=>
    rcases ih with reduced|count
    · left;exact cancelStep_preserves_reduced i i _ reduced
    · by_cases reduced : CancelledAt i (cancelAt i n c)
      · left;exact cancelStep_preserves_reduced i i _ reduced
      · right
        have smaller:=cancelStep_decreases i (cancelAt i n c) reduced
        change (cancelStep i (cancelAt i n c)).poles i+(n+1)≤_
        omega

theorem cancelAt_complete (i : Fin 3) (fuel : ℕ) (c : NormalizedCoefficient)
    (paid : c.poles i≤fuel) : CancelledAt i (cancelAt i fuel c) := by
  rcases cancelAt_progress i fuel c with done|count
  · exact done
  · left;omega

theorem cancelCoefficient_reduced (c : NormalizedCoefficient) (i : Fin 3) :
    CancelledAt i (cancelCoefficient c) := by
  fin_cases i
  · exact cancelAt_preserves_reduced 2 0 _ _
      (cancelAt_preserves_reduced 1 0 _ _ (cancelAt_complete 0 _ c (le_refl _)))
  · apply cancelAt_preserves_reduced 2 1
    exact cancelAt_complete 1 _ _ (cancelAt_poles_le 0 _ c 1)
  · exact cancelAt_complete 2 _ _
      ((cancelAt_poles_le 1 _ _ 2).trans (cancelAt_poles_le 0 _ c 2))

end LowEnergy.PreparationVacuumPoleCancellation
