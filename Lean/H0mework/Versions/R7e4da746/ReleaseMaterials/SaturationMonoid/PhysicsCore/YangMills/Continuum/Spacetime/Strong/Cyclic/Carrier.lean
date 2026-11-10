import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Strong.Field
import Mathlib.Topology.Algebra.Module.Basic

/-! Actual smeared field words generate their own complete cyclic carrier and bounded field restrictions. -/

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace LinearPMap

namespace SaturationMonoid.PhysicsCore.YangMills.Spacetime.StrongFields.Cyclic
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))
  (strong : ∀ v, Continuous (Quantum.Generator.orbit U v))
  {L : Type*} (A : L → H →L[ℂ] H) (Ω : H)

abbrev Label (L : Type*) := L × Terminal.Test

def raw (l : Label L) : H →L[ℂ] H := field U strong (A l.1) l.2

def word (w : List (Label L)) : H := (w.map (raw U strong A)).prod Ω

theorem word_cons (l : Label L) (w : List (Label L)) :
    word U strong A Ω (l :: w) = raw U strong A l (word U strong A Ω w) := rfl

def algebraic : Submodule ℂ H := Submodule.span ℂ (Set.range (word U strong A Ω))
def carrier : Submodule ℂ H := (algebraic U strong A Ω).topologicalClosure
abbrev Space := ↥(carrier U strong A Ω)
local notation "V" => Space U strong A Ω
local notation "C" => carrier U strong A Ω

instance completeSpace : CompleteSpace V :=
  inferInstanceAs (CompleteSpace (algebraic U strong A Ω).topologicalClosure)

def inclusion : V →ₗᵢ[ℂ] H := (C).subtypeₗᵢ

theorem word_mem (w : List (Label L)) : word U strong A Ω w ∈ C :=
  (algebraic U strong A Ω).le_topologicalClosure (Submodule.subset_span ⟨w, rfl⟩)

def vector (w : List (Label L)) : V := ⟨word U strong A Ω w, word_mem U strong A Ω w⟩
def vacuum : V := vector U strong A Ω []

private theorem field_stable (l : Label L) : ∀ v ∈ C, raw U strong A l v ∈ C := by
  have original : algebraic U strong A Ω ≤ (C).comap (raw U strong A l).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    change raw U strong A l (word U strong A Ω w) ∈ C
    rw [← word_cons]
    exact word_mem U strong A Ω (l :: w)
  exact (algebraic U strong A Ω).topologicalClosure_minimal original
    ((algebraic U strong A Ω).isClosed_topologicalClosure.preimage (raw U strong A l).continuous)

def action (l : Label L) : V →L[ℂ] V :=
  ((raw U strong A l).domRestrict C).codRestrict C (fun v => field_stable U strong A Ω l v.val v.property)

theorem inclusion_action (l : Label L) (v : V) :
    inclusion U strong A Ω (action U strong A Ω l v) = raw U strong A l (inclusion U strong A Ω v) := rfl


theorem tempered (l : L) (v : V) : Continuous (fun f : Terminal.Test => action U strong A Ω (l,f) v) := by
  apply continuous_induced_rng.mpr
  exact (ContinuousLinearMap.apply ℂ H v.val).continuous.comp (field U strong (A l)).continuous

theorem action_word (l : Label L) (w : List (Label L)) :
    action U strong A Ω l (vector U strong A Ω w) = vector U strong A Ω (l :: w) := by
  apply Subtype.ext
  rfl

theorem vector_dense : Dense ((Submodule.span ℂ (Set.range (vector U strong A Ω))) : Set V) := by
  have image : (Submodule.span ℂ (Set.range (vector U strong A Ω))).map (C).subtype = algebraic U strong A Ω := by
    rw [Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  intro x
  rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  change x.val ∈ closure (Subtype.val '' (Submodule.span ℂ (Set.range (vector U strong A Ω)) : Set V))
  change x.val ∈ closure (((Submodule.span ℂ (Set.range (vector U strong A Ω))).map (C).subtype : Submodule ℂ H) : Set H)
  rw [image]
  exact x.property

theorem all_words (w : List (Label L)) :
    (w.map (action U strong A Ω)).prod (vacuum U strong A Ω) = vector U strong A Ω w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [ih, action_word]

theorem cyclic : Dense ((Submodule.span ℂ (Set.range
    (fun w : List (Label L) => (w.map (action U strong A Ω)).prod (vacuum U strong A Ω)))) : Set V) := by
  simpa only [all_words] using vector_dense U strong A Ω

end
end SaturationMonoid.PhysicsCore.YangMills.Spacetime.StrongFields.Cyclic
