import H0mework.Fock.InverseDistribution.BirthSource
import H0mework.Fock.InverseDistribution.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionBirth

noncomputable section

def recovered (bound : Nat) (entries : Fin (bound + 1) → Option (Nat × ℚ) × ℚ) : Nat →₀ ℚ :=
  ∑ actor, SourceNativeInverseDistribution.inverseEntry (entries actor).1

def residual (bound : Nat) (entries : Fin (bound + 1) → Option (Nat × ℚ) × ℚ) : Nat →₀ ℚ :=
  SourceConditionalNativeKeys.word bound (fun actor => (entries actor).2)

private theorem inverse_scale (scale : ℚ) (entry : Option (Nat × ℚ) × ℚ) :
    SourceNativeInverseDistribution.inverseEntry (scaleEntry scale entry).1 =
      scale • SourceNativeInverseDistribution.inverseEntry entry.1 := by
  cases entry with
  | mk inverse remainder =>
    cases inverse with
    | none => simp only [scaleEntry, Option.map_none, SourceNativeInverseDistribution.inverseEntry, smul_zero]
    | some pair => simp only [scaleEntry, Option.map_some, SourceNativeInverseDistribution.inverseEntry,
        Finsupp.smul_single, smul_eq_mul]

private theorem inverse_zero (program : Nat × Nat) (target : Nat) :
    SourceNativeInverseDistribution.inverseEntry (SourceNativeInverseDistribution.splitEntry program target 0).1 = 0 := by
  cases computed : SourceNativeProgramInverse.decode program target <;>
    simp only [SourceNativeInverseDistribution.splitEntry, computed, SourceNativeInverseDistribution.inverseEntry,
      Finsupp.single_zero]

theorem recovered_advance {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat)
    (counts : Key → Nat) (previous : Key → Fin (bound + 1) → Option (Nat × ℚ) × ℚ) (key : Key) :
    recovered (bound + 1) (advance read bound program counts previous key) =
      if key = read (bound + 1) then
        ((counts key : ℚ) / (counts key + 1 : Nat)) • recovered bound (previous key) +
          SourceNativeInverseDistribution.inverseEntry
            (SourceNativeInverseDistribution.splitEntry program (bound + 2) ((counts key + 1 : Nat) : ℚ)⁻¹).1
      else recovered bound (previous key) := by
  by_cases selected : key = read (bound + 1)
  · simp only [recovered, advance, if_pos selected]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, inverse_scale, Finset.smul_sum]
  · simp only [recovered, advance, if_neg selected, Fin.sum_univ_castSucc,
      Fin.lastCases_castSucc, Fin.lastCases_last, inverse_zero, add_zero]

theorem residual_advance {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat)
    (counts : Key → Nat) (previous : Key → Fin (bound + 1) → Option (Nat × ℚ) × ℚ) (key : Key) :
    residual (bound + 1) (advance read bound program counts previous key) =
      if key = read (bound + 1) then
        ((counts key : ℚ) / (counts key + 1 : Nat)) • residual bound (previous key) +
          (SourceNativeInverseDistribution.splitEntry program (bound + 2) ((counts key + 1 : Nat) : ℚ)⁻¹).2 •
            SourceConditionalRationalStream.bornWord bound
      else residual bound (previous key) := by
  by_cases selected : key = read (bound + 1)
  · simp only [residual, advance, if_pos selected]
    have row : (fun actor : Fin (bound + 2) => (Fin.lastCases
        (SourceNativeInverseDistribution.splitEntry program (bound + 2) ((counts key + 1 : Nat) : ℚ)⁻¹)
        (fun earlier => scaleEntry ((counts key : ℚ) / (counts key + 1 : Nat)) (previous key earlier)) actor : Option (Nat × ℚ) × ℚ).2) =
        Fin.lastCases (SourceNativeInverseDistribution.splitEntry program (bound + 2) ((counts key + 1 : Nat) : ℚ)⁻¹).2
          (fun earlier => ((counts key : ℚ) / (counts key + 1 : Nat)) * (previous key earlier).2) := by
      funext actor
      refine Fin.lastCases ?_ (fun earlier => ?_) actor
      · simp only [Fin.lastCases_last]
      · simp only [Fin.lastCases_castSucc, scaleEntry]
    rw [row, SourceConditionalNativeKeys.word_append]
    congr 1
    exact (SourceConditionalNativeKeys.word bound).map_smul _ _
  · simp only [residual, advance, if_neg selected]
    have zero : (SourceNativeInverseDistribution.splitEntry program (bound + 2) 0).2 = 0 := by
      cases computed : SourceNativeProgramInverse.decode program (bound + 2) <;>
        simp only [SourceNativeInverseDistribution.splitEntry, computed]
    have row : (fun actor : Fin (bound + 2) => (Fin.lastCases (SourceNativeInverseDistribution.splitEntry program (bound + 2) 0)
        (previous key) actor : Option (Nat × ℚ) × ℚ).2) = Fin.lastCases 0 (fun earlier => (previous key earlier).2) := by
      funext actor
      refine Fin.lastCases ?_ (fun earlier => ?_) actor
      · simpa only [Fin.lastCases_last] using zero
      · simp only [Fin.lastCases_castSucc]
    rw [row, SourceConditionalNativeKeys.word_retained]

theorem recovered_next {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat) (key : Key) :
    recovered (bound + 1) (advance read bound program
      (fun key => (SourceConditionalNativeObservers.generate read bound key).1)
      (fun key => SourceNativeInverseDistribution.split bound program (SourceConditionalNativeObservers.generate read bound key).2) key) =
      SourceNativeInverseDistribution.recovered (bound + 1) program
        (SourceConditionalNativeObservers.generate read (bound + 1) key).2 := by
  rw [generated_next]
  rfl

theorem residual_next {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat) (key : Key) :
    residual (bound + 1) (advance read bound program
      (fun key => (SourceConditionalNativeObservers.generate read bound key).1)
      (fun key => SourceNativeInverseDistribution.split bound program (SourceConditionalNativeObservers.generate read bound key).2) key) =
      SourceNativeInverseDistribution.residual (bound + 1) program
        (SourceConditionalNativeObservers.generate read (bound + 1) key).2 := by
  rw [generated_next]
  rfl

end
end SourceInverseDistributionBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
