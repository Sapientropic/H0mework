import H0mework.Physics.MotherProgrammesFormationCoordinates.Completion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamFormation

open MotherCoordinateCompletion MotherFamilyOccurrence
open Filter Topology UniformSpace

noncomputable section

def pad (count : ℕ) (value : Fin count → ℚ) : ℕ → ℝ :=
  fun slot => if bound : slot < count then (value ⟨slot, bound⟩ : ℝ) else 0

/-- Only existing finite rational observations of the fixed mother occur here. -/
def finiteNative (input : ℕ × MotherVisit) : ℕ → ℝ :=
  pad input.1 (rationalAt input.1 input.2)

def Raw := Set.range finiteNative

instance : UniformSpace Raw :=
  inferInstanceAs (UniformSpace (Set.range finiteNative))

instance : T2Space Raw :=
  inferInstanceAs (T2Space (Set.range finiteNative))

def readRaw : Raw → ℕ → ℝ := Subtype.val

theorem pad_mem_range (count : ℕ) (value : Fin count → ℚ) :
    pad count value ∈ Set.range finiteNative := by
  obtain ⟨code, generated⟩ := every_rational_vector count value
  refine ⟨(count, Stage9C.Revision.SpinPair.visit (10 + code)), ?_⟩
  unfold finiteNative
  rw [generated]

theorem pads_converge (value : ℕ → ℚ) :
    Tendsto (fun count => pad count (fun slot => value slot)) atTop
      (𝓝 (fun slot => (value slot : ℝ))) := by
  apply tendsto_pi_nhds.2
  intro slot
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop slot] with count bound
  simp [pad, bound]

theorem native_dense : DenseRange finiteNative := by
  have rationalContained :
      Set.range (fun value : ℕ → ℚ => fun slot => (value slot : ℝ)) ⊆
        closure (Set.range finiteNative) := by
    rintro _ ⟨value, rfl⟩
    exact isClosed_closure.mem_of_tendsto (pads_converge value)
      (Eventually.of_forall fun count => subset_closure (pad_mem_range count _))
  have rationalDense : DenseRange (fun value : ℕ → ℚ => fun slot => (value slot : ℝ)) :=
    DenseRange.piMap (fun _ : ℕ => Rat.denseRange_cast)
  intro value
  exact (closure_minimal rationalContained isClosed_closure) (rationalDense value)

theorem readRaw_inducing : IsUniformInducing readRaw :=
  isUniformEmbedding_subtype_val.isUniformInducing

abbrev Carrier := Completion Raw

def read : Carrier → ℕ → ℝ := Completion.extension readRaw

theorem read_coe (value : Raw) : read (value : Carrier) = value.1 :=
  Completion.extension_coe readRaw_inducing.uniformContinuous value

theorem read_inducing : IsUniformInducing read :=
  Completion.isUniformInducing_extension readRaw_inducing

theorem read_surjective : Function.Surjective read := by
  have contained : Set.range finiteNative ⊆ Set.range read := by
    rintro _ ⟨input, rfl⟩
    exact ⟨((⟨finiteNative input, input, rfl⟩ : Raw) : Carrier), read_coe _⟩
  intro value
  exact (closure_minimal contained read_inducing.isComplete_range.isClosed)
    (native_dense value)

/-- One completed source value carries the entire sequence simultaneously. -/
theorem simultaneous_formation (value : ℕ → ℝ) :
    ∃! material : Carrier, ∀ count : ℕ, ∀ slot : Fin count,
      read material slot = value slot := by
  obtain ⟨material, formed⟩ := read_surjective value
  refine ⟨material, fun _ slot => congrFun formed slot, ?_⟩
  intro other agrees
  apply read_inducing.isInducing.injective
  funext slot
  exact (agrees (slot + 1) ⟨slot, Nat.lt_succ_self slot⟩).trans
    (congrFun formed slot).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamFormation
