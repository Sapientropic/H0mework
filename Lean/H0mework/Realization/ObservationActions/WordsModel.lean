import H0mework.Realization.ObservationActions.WordsKernel

/-! The existing autonomous Model consumes the source-computed word inventory and every actual letter. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords

noncomputable section
universe r u
variable {R : Type r} [CommRing R]
variable {I C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (actions : I → C →ₗ[R] C) (read : C →ₗ[R] B) (primary : I)

abbrev Model := SourceGeneratedActionObservationHistory.Model (actions primary) (inventory actions read)

abbrev projection : C →ₗ[R] Model actions read primary :=
  SourceGeneratedActionObservationHistory.projection (actions primary) (inventory actions read)

private theorem retained (letter : I) :
    LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap (actions primary) (inventory actions read)) ≤
      (LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap (actions primary) (inventory actions read))).comap
        (actions letter) := by
  rw [original_kernel]
  exact kernel_invariant actions read letter

def advance (letter : I) : Model actions read primary →ₗ[R] Model actions read primary :=
  (LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap (actions primary) (inventory actions read))).mapQ
    (LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap (actions primary) (inventory actions read)))
    (actions letter) (retained actions read primary letter)

theorem advance_source (letter : I) (value : C) :
    advance actions read primary letter (projection actions read primary value) =
      projection actions read primary (actions letter value) := rfl

theorem primary_is_original : advance actions read primary primary =
    SourceGeneratedActionObservationHistory.modelAction (actions primary) (inventory actions read) := by
  apply LinearMap.ext
  intro value
  refine Submodule.Quotient.induction_on _ value fun source => ?_
  exact (SourceGeneratedActionObservationHistory.modelAction_source (actions primary) (inventory actions read) source).symm

def readout (word : List I) : Model actions read primary →ₗ[R] B :=
  (LinearMap.proj word).comp
    (SourceGeneratedActionObservationHistory.modelReadout (actions primary) (inventory actions read))

theorem readout_source (word : List I) (value : C) :
    readout actions read primary word (projection actions read primary value) = read (run actions word value) := rfl

theorem letter_readout (letter : I) (word : List I) (value : Model actions read primary) :
    readout actions read primary word (advance actions read primary letter value) =
      readout actions read primary (letter :: word) value := by
  refine Submodule.Quotient.induction_on _ value fun source => ?_
  rfl

theorem projection_fibre (left right : C) :
    projection actions read primary left = projection actions read primary right ↔
      ∀ word : List I, read (run actions word left) = read (run actions word right) := by
  calc
    _ ↔ projection actions read primary (left - right) = 0 := by rw [map_sub, sub_eq_zero]
    _ ↔ left - right ∈ LinearMap.ker
        (SourceGeneratedActionObservationHistory.sourceMap (actions primary) (inventory actions read)) :=
      SourceGeneratedScalarDifferentialResidual.canonicalResidual_eq_zero_iff _ _
    _ ↔ left - right ∈ LinearMap.ker (inventory actions read) := by rw [original_kernel]
    _ ↔ inventory actions read left = inventory actions read right := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    _ ↔ _ := funext_iff

theorem run_source (word : List I) (value : C) :
    run (advance actions read primary) word (projection actions read primary value) =
      projection actions read primary (run actions word value) := by
  induction word generalizing value with
  | nil => rfl
  | cons letter rest previous =>
      change run (advance actions read primary) rest
        (advance actions read primary letter (projection actions read primary value)) = _
      rw [advance_source, previous]
      rfl

def originalRestriction : Model actions read primary →ₗ[R]
    SourceGeneratedActionObservationHistory.Model (actions primary) read :=
  Submodule.factor (by
    rw [original_kernel]
    exact SourceGeneratedActionObservationHistory.invariant_submodule_le_kernel (actions primary) read _
      (kernel_invisible actions read) (kernel_invariant actions read primary))

theorem originalRestriction_source (value : C) :
    originalRestriction actions read primary (projection actions read primary value) =
      SourceGeneratedActionObservationHistory.projection (actions primary) read value := rfl

theorem originalRestriction_primary (value : Model actions read primary) :
    originalRestriction actions read primary (advance actions read primary primary value) =
      SourceGeneratedActionObservationHistory.modelAction (actions primary) read
        (originalRestriction actions read primary value) := by
  refine Submodule.Quotient.induction_on _ value fun source => ?_
  change originalRestriction actions read primary
    (advance actions read primary primary (projection actions read primary source)) =
      SourceGeneratedActionObservationHistory.modelAction (actions primary) read
        (originalRestriction actions read primary (projection actions read primary source))
  rw [advance_source, originalRestriction_source, originalRestriction_source]
  exact (SourceGeneratedActionObservationHistory.modelAction_source (actions primary) read source).symm

end
end SourceGeneratedActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
