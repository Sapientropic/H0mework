import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace

/-!
# Fourier action on the Burnol constant-gap face

The `L²` Fourier transform squares to reflection and therefore preserves the
two-sided constant-gap face.  Its restriction is a bijective linear isometry
and preserves the exact Hilbert energy.  This supplies a genuine
source-independent physical action carrier; nontrivial zero-evaluator landing
remains a separate producer responsibility.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open FourierTransform MeasureTheory
open scoped ENNReal

noncomputable section

/-- On `L²(ℝ)`, inverse Fourier is Fourier followed by reflection. -/
theorem fourierL2_symm_eq_reflect_fourierL2 (value : BurnolL2) :
    fourierL2.symm value = reflectL2 (fourierL2 value) := by
  apply DenseRange.induction_on (p := fun target : BurnolL2 ↦
    fourierL2.symm target = reflectL2 (fourierL2 target))
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top) value
  · apply isClosed_eq
    · exact fourierL2.symm.continuous
    · exact reflectL2.continuous.comp fourierL2.continuous
  intro test
  change FourierTransform.fourierInv (test.toLp 2) =
    reflectL2 (FourierTransform.fourier (test.toLp 2))
  rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  have fourierNeg := negMeasurePreserving.quasiMeasurePreserving.ae
    ((FourierTransform.fourier test).coeFn_toLp 2 (volume : Measure ℝ))
  filter_upwards [
    (FourierTransform.fourierInv test).coeFn_toLp 2 (volume : Measure ℝ),
    Lp.coeFn_compMeasurePreserving
      ((FourierTransform.fourier test).toLp 2 (volume : Measure ℝ))
      negMeasurePreserving, fourierNeg]
    with x left reflection fourierAt
  have inverseAt : (FourierTransform.fourierInv test) x =
      (FourierTransform.fourier test) (-x) := by
    rw [SchwartzMap.fourierInv_apply_eq]
    rfl
  calc
    ((FourierTransform.fourierInv test).toLp 2 (volume : Measure ℝ)) x =
        (FourierTransform.fourierInv test) x := left
    _ = (FourierTransform.fourier test) (-x) := inverseAt
    _ = ((FourierTransform.fourier test).toLp 2
          (volume : Measure ℝ)) (-x) := fourierAt.symm
    _ = reflectL2
        ((FourierTransform.fourier test).toLp 2
          (volume : Measure ℝ)) x := reflection.symm

theorem fourierL2_fourierL2 (value : BurnolL2) :
    fourierL2 (fourierL2 value) = reflectL2 value := by
  have identity := fourierL2_symm_eq_reflect_fourierL2 (fourierL2 value)
  calc
    fourierL2 (fourierL2 value) =
        reflectL2 (reflectL2 (fourierL2 (fourierL2 value))) :=
      (reflectL2_reflectL2 _).symm
    _ = reflectL2 (fourierL2.symm (fourierL2 value)) :=
      congrArg reflectL2 identity.symm
    _ = reflectL2 value :=
      congrArg reflectL2 (fourierL2.symm_apply_apply value)

/-- Fourier exchanges the two defining local conditions. -/
theorem fourierL2_mem_burnolFace {radius : ℝ} {value : BurnolL2}
    (membership : value ∈ burnolFace radius) :
    fourierL2 value ∈ burnolFace radius := by
  rw [mem_burnolFace_iff] at membership ⊢
  refine ⟨membership.2, ?_⟩
  rw [fourierL2_fourierL2]
  exact locallyConstantFace_reflectL2 membership.1

theorem fourierL2_fourth (value : BurnolL2) :
    fourierL2 (fourierL2 (fourierL2 (fourierL2 value))) = value := by
  calc
    fourierL2 (fourierL2 (fourierL2 (fourierL2 value))) =
        reflectL2 (fourierL2 (fourierL2 value)) := fourierL2_fourierL2 _
    _ = reflectL2 (reflectL2 value) :=
      congrArg reflectL2 (fourierL2_fourierL2 value)
    _ = value := reflectL2_reflectL2 value

theorem fourierL2_mem_burnolFace_iff {radius : ℝ} {value : BurnolL2} :
    fourierL2 value ∈ burnolFace radius ↔ value ∈ burnolFace radius := by
  constructor
  · intro first
    have second := fourierL2_mem_burnolFace first
    have third := fourierL2_mem_burnolFace second
    have fourth := fourierL2_mem_burnolFace third
    rwa [fourierL2_fourth] at fourth
  · exact fourierL2_mem_burnolFace

/-- Bosonic/even physicality constraint.  The full-line Fourier carrier is
reduced to the reflection-fixed sector corresponding to the cosine face. -/
def evenL2ClosedFace : ClosedSubmodule ℂ BurnolL2 :=
  { toSubmodule :=
      (reflectL2.toContinuousLinearMap -
        ContinuousLinearMap.id ℂ BurnolL2).ker
    isClosed' :=
      (reflectL2.toContinuousLinearMap -
        ContinuousLinearMap.id ℂ BurnolL2).isClosed_ker }

theorem mem_evenL2ClosedFace_iff {value : BurnolL2} :
    value ∈ evenL2ClosedFace ↔ reflectL2 value = value := by
  change (reflectL2.toContinuousLinearMap -
    ContinuousLinearMap.id ℂ BurnolL2) value = 0 ↔ _
  change reflectL2 value - value = 0 ↔ _
  constructor
  · exact sub_eq_zero.mp
  · exact sub_eq_zero.mpr

/-- Exact even Burnol face: constant position/cosine coordinates plus the
definitionally imposed reflection-fixed constraint. -/
def evenBurnolClosedFace (radius : ℝ) : ClosedSubmodule ℂ BurnolL2 :=
  burnolClosedFace radius ⊓ evenL2ClosedFace

theorem fourierL2_mem_evenL2ClosedFace {value : BurnolL2}
    (membership : value ∈ evenL2ClosedFace) :
    fourierL2 value ∈ evenL2ClosedFace := by
  rw [mem_evenL2ClosedFace_iff] at membership ⊢
  rw [← fourierL2_fourierL2 (fourierL2 value),
    fourierL2_fourierL2 value, membership]

theorem fourierL2_mem_evenBurnolClosedFace {radius : ℝ} {value : BurnolL2}
    (membership : value ∈ evenBurnolClosedFace radius) :
    fourierL2 value ∈ evenBurnolClosedFace radius := by
  exact ⟨fourierL2_mem_burnolFace membership.1,
    fourierL2_mem_evenL2ClosedFace membership.2⟩

/-- Fourier restricted to the physical face. -/
def faceFourier (radius : ℝ) :
    burnolFace radius →ₗᵢ[ℂ] burnolFace radius where
  toLinearMap :=
    { toFun := fun value ↦
        ⟨fourierL2 value, fourierL2_mem_burnolFace value.property⟩
      map_add' := by
        intro left right
        apply Subtype.ext
        exact fourierL2.map_add left right
      map_smul' := by
        intro coefficient value
        apply Subtype.ext
        exact fourierL2.map_smul coefficient value }
  norm_map' := by
    intro value
    exact fourierL2.norm_map value

def faceEnergy (value : BurnolL2) : ℝ := ‖value‖ ^ 2

theorem faceFourier_preserves_energy (radius : ℝ)
    (value : burnolFace radius) :
    faceEnergy (faceFourier radius value) = faceEnergy value := by
  change ‖fourierL2 (value : BurnolL2)‖ ^ 2 = ‖(value : BurnolL2)‖ ^ 2
  rw [fourierL2.norm_map]

theorem faceFourier_bijective (radius : ℝ) :
    Function.Bijective (faceFourier radius) := by
  refine ⟨(faceFourier radius).injective, ?_⟩
  intro target
  let source : BurnolL2 := fourierL2.symm (target : BurnolL2)
  have fourierSource : fourierL2 source ∈ burnolFace radius := by
    change fourierL2 (fourierL2.symm (target : BurnolL2)) ∈ burnolFace radius
    rw [fourierL2.apply_symm_apply]
    exact target.property
  have sourceMem : source ∈ burnolFace radius :=
    fourierL2_mem_burnolFace_iff.mp fourierSource
  refine ⟨⟨source, sourceMem⟩, ?_⟩
  apply Subtype.ext
  exact fourierL2.apply_symm_apply (target : BurnolL2)

/-- Fourier restricted to the even/cosine physical face. -/
def evenFaceFourier (radius : ℝ) :
    (evenBurnolClosedFace radius).toSubmodule →ₗᵢ[ℂ]
      (evenBurnolClosedFace radius).toSubmodule where
  toLinearMap :=
    { toFun := fun value ↦
        ⟨fourierL2 value,
          fourierL2_mem_evenBurnolClosedFace value.property⟩
      map_add' := by
        intro left right
        apply Subtype.ext
        exact fourierL2.map_add left right
      map_smul' := by
        intro coefficient value
        apply Subtype.ext
        exact fourierL2.map_smul coefficient value }
  norm_map' := fun value ↦ fourierL2.norm_map value

theorem evenFaceFourier_preserves_energy (radius : ℝ)
    (value : (evenBurnolClosedFace radius).toSubmodule) :
    faceEnergy (evenFaceFourier radius value) = faceEnergy value := by
  change ‖fourierL2 (value : BurnolL2)‖ ^ 2 = ‖(value : BurnolL2)‖ ^ 2
  rw [fourierL2.norm_map]

end

end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.fourierL2_fourierL2
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.faceFourier_bijective
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.faceFourier_preserves_energy
