import H0mework.Physics.MotherProgrammesFormationRational.Consumer
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion

open Stage9C.Revision MotherFamilyOccurrence StageEightDiscreteFormation
open RationalSourceFormation

noncomputable section

def sample (count : ℕ) (visit : MotherVisit) (slot : Fin count) : MotherVisit :=
  pastVisit visit (unpack count (codeOf visit) slot)

theorem sample_code (count : ℕ) (visit : MotherVisit) (slot : Fin count) :
    codeOf (sample count visit slot) = unpack count (codeOf visit) slot :=
  past_code visit _ (unpack_le _ _ _)

theorem sample_is_past (count : ℕ) (visit : MotherVisit) (slot : Fin count) :
    temporalDepth (sample count visit slot).history ≤ temporalDepth visit.history :=
  past_depth_le visit _

def rationalAt (count : ℕ) (visit : MotherVisit) : Fin count → ℚ :=
  fun slot => rationalTrace (sourceAtVisit (sample count visit slot))

theorem actual_trace (count : ℕ) (visit : MotherVisit) (slot : Fin count) :
    (rationalAt count visit slot : ℝ) = sourceTrace (sourceAtVisit (sample count visit slot)) :=
  rational_trace_cast _

theorem packed_trace {count : ℕ} (codes : Fin count → ℕ) (slot : Fin count) :
    (rationalAt count (SpinPair.visit (10 + pack codes)) slot : ℝ) =
      traceAtVisit (SpinPair.visit (10 + codes slot)) := by
  rw [actual_trace]
  unfold traceAtVisit sourceAtVisit
  rw [sample_code, code_at, unpack_pack, code_at]

theorem every_rational_vector (count : ℕ) (values : Fin count → ℚ) :
    ∃ code, rationalAt count (SpinPair.visit (10 + code)) = values := by
  have each : ∀ slot : Fin count, ∃ code,
      traceAtVisit (SpinPair.visit (10 + code)) = (values slot : ℝ) :=
    fun slot => every_rational_generated (values slot)
  choose codes generated using each
  refine ⟨pack codes, ?_⟩
  funext slot
  apply Rat.cast_injective (α := ℝ)
  exact (packed_trace codes slot).trans (generated slot)

/-- Values of the fixed mother's finite histories, with the induced rational metric. -/
def RationalCarrier (count : ℕ) := Set.range (rationalAt count)

def fromVisit (count : ℕ) (visit : MotherVisit) : RationalCarrier count :=
  ⟨rationalAt count visit, visit, rfl⟩

def fromRational (count : ℕ) (values : Fin count → ℚ) : RationalCarrier count :=
  ⟨values, by
    obtain ⟨code, generated⟩ := every_rational_vector count values
    exact ⟨SpinPair.visit (10 + code), generated⟩⟩

instance (count : ℕ) : MetricSpace (RationalCarrier count) :=
  inferInstanceAs (MetricSpace (Set.range (rationalAt count)))

def realEmbedding (count : ℕ) (value : RationalCarrier count) : Fin count → ℝ :=
  fun slot => value.1 slot

theorem embedding_isometry (count : ℕ) : Isometry (realEmbedding count) := by
  have cast : Isometry (fun value : ℚ => (value : ℝ)) := Isometry.of_dist_eq (fun _ _ => rfl)
  have vectors := cast.postcomp_pi (α := Fin count)
  exact Isometry.of_dist_eq (fun first last => vectors.dist_eq first.1 last.1)

theorem embedding_dense (count : ℕ) : DenseRange (realEmbedding count) := by
  have rationalDense : DenseRange (fun values : Fin count → ℚ => fun slot => (values slot : ℝ)) :=
    DenseRange.piMap (fun _ : Fin count => Rat.denseRange_cast)
  intro real
  apply closure_mono (s := Set.range (fun values : Fin count → ℚ => fun slot => (values slot : ℝ))) _ (rationalDense real)
  rintro _ ⟨values, rfl⟩
  exact ⟨fromRational count values, rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion
