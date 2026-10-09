import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Translation

/-! A nonzero outgoing momentum is a true translated spectral overlap of two
whole matter-state vectors. The real current retains both ordered pairings. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
open FullQuantum FullSpace PacketField PacketNoise
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem phasePair_integrable (shift : Position) (left right : FieldSpace E) :
    Integrable (fun position : Position => positionPhase shift position*inner ℂ (left position) (right position)) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) left (phaseMap shift right)).congr
  filter_upwards [phaseMap_ae shift right] with position value
  rw [value,inner_smul_right]

theorem phasePair_integral (shift : Position) (left right : FieldSpace E) :
    (∫ position : Position, positionPhase shift position*inner ℂ (left position) (right position))=
      inner ℂ left (phaseMap shift right) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [phaseMap_ae shift right] with position value
  rw [value,inner_smul_right]

theorem phaseRealPair_integral (shift : Position) (left right : FieldSpace E) :
    (∫ position : Position, positionPhase shift position*((inner ℂ (left position) (right position)).re : ℂ))=
      (inner ℂ left (phaseMap shift right)+inner ℂ right (phaseMap shift left))/2 := by
  have formula (position : Position) :
      positionPhase shift position*((inner ℂ (left position) (right position)).re : ℂ)=
        (positionPhase shift position*inner ℂ (left position) (right position)+
          positionPhase shift position*inner ℂ (right position) (left position))/2 := by
    rw [Complex.re_eq_add_conj,inner_conj_symm]
    ring
  simp_rw [formula]
  rw [integral_div,integral_add (phasePair_integrable shift left right) (phasePair_integrable shift right left),
    phasePair_integral,phasePair_integral]

variable [CompleteSpace E]

theorem phaseRealPair_spectrum (shift : Position) (left right : FieldSpace E) :
    (∫ position : Position, positionPhase (-shift) position*
      ((inner ℂ (spatialFourier left position) (spatialFourier right position)).re : ℂ))=
      (inner ℂ left (translation shift right)+inner ℂ right (translation shift left))/2 := by
  rw [phaseRealPair_integral,translated_pair,translated_pair]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
