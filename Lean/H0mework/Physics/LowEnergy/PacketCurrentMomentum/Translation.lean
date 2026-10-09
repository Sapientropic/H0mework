import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Modulation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! The external spatial Fourier transform turns the outgoing phase into a
translation of the full Hilbert-valued spectrum, with the source sign retained. -/
set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
open FullQuantum FullSpace PacketField PacketNoise
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def translation (shift : Position) : FieldSpace E →ₗᵢ[ℂ] FieldSpace E :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun frequency : Position => frequency-shift)
    (measurePreserving_sub_right volume shift)

theorem translation_ae (shift : Position) (field : FieldSpace E) :
    translation shift field=ᵐ[volume] fun frequency => field (frequency-shift) :=
  Lp.coeFn_compMeasurePreserving field (measurePreserving_sub_right volume shift)

theorem schwartz_translation (shift : Position) (field : SchwartzMap Position E) :
    translation shift (field.toLp 2 volume)=(field.compSubConstCLM ℂ shift).toLp 2 volume := by
  apply Lp.ext
  have moved := (measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae (field.coeFn_toLp 2 volume)
  filter_upwards [translation_ae shift (field.toLp 2 volume),moved,
    (field.compSubConstCLM ℂ shift).coeFn_toLp 2 volume] with point translated source target
  rw [translated,source,target]
  rfl

theorem fourier_function_translation (shift : Position) (field : Position → E) (position : Position) :
    𝓕 (fun frequency => field (frequency-shift)) position=
      positionPhase (-shift) position • 𝓕 field position := by
  have translated := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ Position) field (-shift)) position
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Position)
    (fun frequency => field (frequency-shift)) position=
      positionPhase (-shift) position • VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Position) field position
  simpa [positionPhase,Function.comp_def,sub_eq_add_neg,Circle.smul_def,Real.fourierChar_apply] using translated

variable [CompleteSpace E]

theorem schwartz_phase (shift : Position) (field : SchwartzMap Position E) :
    spatialFourier (translation shift (field.toLp 2 volume))=
      phaseMap (-shift) (spatialFourier (field.toLp 2 volume)) := by
  rw [schwartz_translation]
  change 𝓕 ((field.compSubConstCLM ℂ shift).toLp 2 volume)=phaseMap (-shift) (𝓕 (field.toLp 2 volume))
  rw [SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (field.compSubConstCLM ℂ shift)).coeFn_toLp 2 volume,
    phaseMap_ae (-shift) ((𝓕 field).toLp 2 volume),(𝓕 field).coeFn_toLp 2 volume] with position left right source
  rw [left,right,source]
  simp only [SchwartzMap.fourier_coe]
  exact fourier_function_translation shift field position

theorem spatialFourier_translation (shift : Position) (field : FieldSpace E) :
    spatialFourier (translation shift field)=phaseMap (-shift) (spatialFourier field) := by
  apply DenseRange.induction_on (p := fun field : FieldSpace E =>
    spatialFourier (translation shift field)=phaseMap (-shift) (spatialFourier field))
    (SchwartzMap.denseRange_toLpCLM (E := Position) (F := E) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) field
  · exact isClosed_eq (spatialFourier.continuous.comp (translation shift).continuous)
      ((phaseMap (-shift)).continuous.comp spatialFourier.continuous)
  · exact schwartz_phase shift

theorem translated_pair (shift : Position) (left right : FieldSpace E) :
    inner ℂ (spatialFourier left) (phaseMap (-shift) (spatialFourier right))=
      inner ℂ left (translation shift right) := by
  rw [← spatialFourier_translation]
  exact spatialFourier.inner_map_map left (translation shift right)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
