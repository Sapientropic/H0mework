import H0mework.Physics.MotherLaws.StreamScalar
import H0mework.Physics.MotherLaws.FiniteEvaluation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws

open MotherFamilyOccurrence MotherCoordinateCompletion StageEightDiscreteFormation RationalSourceFormation
open Stage9C.Revision

noncomputable section

def inputPrefix (count : ℕ) (input : Stream) : Fin count → ℝ := fun i => input i.val

def pad (count : ℕ) (output : Fin count → ℝ) : Stream :=
  fun i => if bound : i < count then output ⟨i, bound⟩ else 0

theorem prefix_continuous (count : ℕ) : Continuous (inputPrefix count) :=
  continuous_pi fun i => continuous_apply i.val

theorem pad_continuous (count : ℕ) : Continuous (pad count) := by
  apply continuous_pi
  intro i
  by_cases bound : i < count
  · simpa only [pad, dif_pos bound] using continuous_apply (⟨i, bound⟩ : Fin count)
  · simp only [pad, dif_neg bound]
    exact continuous_const

def liftFinite (n m : ℕ) (law : C((Fin n → ℝ), (Fin m → ℝ))) : C(Stream, Stream) :=
  ⟨fun input => pad m (law (inputPrefix n input)),
    (pad_continuous m).comp (law.continuous.comp (prefix_continuous n))⟩

theorem liftFinite_apply (n m : ℕ) (law : C((Fin n → ℝ), (Fin m → ℝ)))
    (input : Stream) (output : Fin m) :
    liftFinite n m law input output.val = law (inputPrefix n input) output := by
  simp [liftFinite, pad]

theorem terms_at_code (n m : ℕ) (visit : MotherVisit) (code : ℕ)
    (same : codeOf visit = code) :
    MotherFiniteLaws.terms n m visit = List.ofFn (fun slot : Fin code.unpair.1 =>
      MotherFiniteLaws.termAt n m (pastVisit visit (unpack code.unpair.1 code.unpair.2 slot))) := by
  cases same
  unfold MotherFiniteLaws.terms
  change (List.ofFn (fun slot : Fin (codeOf visit).unpair.1 => MotherProgrammes.entryAt
    (pastVisit visit (unpack (codeOf visit).unpair.1 (codeOf visit).unpair.2 slot)))).map _ = _
  rw [List.map_ofFn]
  rfl

theorem terms_same_code (n m : ℕ) (first last : MotherVisit)
    (same : codeOf first = codeOf last) :
    MotherFiniteLaws.terms n m first = MotherFiniteLaws.terms n m last := by
  rw [terms_at_code n m first (codeOf last) same, terms_at_code n m last (codeOf last) rfl]
  apply congrArg List.ofFn
  funext slot
  apply MotherFiniteLaws.term_same_code
  have bound : unpack (codeOf last).unpair.1 (codeOf last).unpair.2 slot ≤ codeOf last :=
    (unpack_le _ _ slot).trans (Nat.unpair_right_le _)
  have boundFirst : unpack (codeOf last).unpair.1 (codeOf last).unpair.2 slot ≤ codeOf first := by
    rw [same]
    exact bound
  rw [past_code _ _ boundFirst, past_code _ _ bound]

theorem finiteLaw_same_code (n m : ℕ) (first last : MotherVisit)
    (same : codeOf first = codeOf last) :
    MotherFiniteLaws.finiteLaw n m first = MotherFiniteLaws.finiteLaw n m last := by
  ext input output
  change MotherFiniteLaws.eval n m first input output = MotherFiniteLaws.eval n m last input output
  unfold MotherFiniteLaws.eval
  rw [terms_same_code n m first last same]

def inputCount (visit : MotherVisit) : ℕ := (codeOf visit).unpair.1
def outputCount (visit : MotherVisit) : ℕ := (codeOf visit).unpair.2.unpair.1
def lawCode (visit : MotherVisit) : ℕ := (codeOf visit).unpair.2.unpair.2
def lawPrefix (visit : MotherVisit) : MotherVisit := pastVisit visit (lawCode visit)

theorem lawCode_le (visit : MotherVisit) : lawCode visit ≤ codeOf visit :=
  (Nat.unpair_right_le _).trans (Nat.unpair_right_le _)

theorem lawPrefix_code (visit : MotherVisit) : codeOf (lawPrefix visit) = lawCode visit :=
  past_code _ _ (lawCode_le visit)

/-- Dimensions, polynomial shape and coefficients are all read from one current mother's past. -/
def finiteNativeLaw (visit : MotherVisit) : C(Stream, Stream) :=
  liftFinite (inputCount visit) (outputCount visit)
    (MotherFiniteLaws.finiteLaw (inputCount visit) (outputCount visit) (lawPrefix visit))

theorem entry_origins (visit : MotherVisit) (entry : MotherProgrammes.Entry)
    (member : entry ∈ MotherProgrammes.programmeAt (lawPrefix visit)) :
    temporalDepth entry.discreteVisit.history ≤ temporalDepth visit.history ∧
      temporalDepth entry.coordinateVisit.history ≤ temporalDepth visit.history ∧
      ∀ slot : Fin (outputCount visit),
        temporalDepth (sample (outputCount visit) entry.coordinateVisit slot).history ≤
          temporalDepth visit.history := by
  have original := MotherFiniteLaws.entry_origins (outputCount visit) (lawPrefix visit) entry member
  have parent : temporalDepth (lawPrefix visit).history ≤ temporalDepth visit.history :=
    past_depth_le visit (lawCode visit)
  exact ⟨original.1.trans parent, original.2.1.trans parent,
    fun slot => (original.2.2 slot).trans parent⟩

theorem every_finite_law (n m : ℕ) (visit : MotherVisit) :
    ∃ code, finiteNativeLaw (SpinPair.visit (10 + code)) =
      liftFinite n m (MotherFiniteLaws.finiteLaw n m visit) := by
  let code := Nat.pair n (Nat.pair m (codeOf visit))
  let source := SpinPair.visit (10 + code)
  have inputs : inputCount source = n := by simp [inputCount, source, code, code_at]
  have outputs : outputCount source = m := by simp [outputCount, source, code, code_at]
  have programme : lawCode source = codeOf visit := by simp [lawCode, source, code, code_at]
  refine ⟨code, ?_⟩
  change liftFinite (inputCount source) (outputCount source)
    (MotherFiniteLaws.finiteLaw (inputCount source) (outputCount source) (lawPrefix source)) = _
  rw [inputs, outputs, finiteLaw_same_code n m (lawPrefix source) visit
    ((lawPrefix_code source).trans programme)]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws
