import H0mework.Physics.LowEnergy.PacketNoise.Shift

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace
noncomputable section

theorem frequencyShift_zero (field : FullMatterL2) : frequencyShift 0 field=field := by
  apply Lp.ext
  filter_upwards [frequencyShift_ae 0 field] with frequency shifted
  simpa only [sub_zero] using shifted

theorem frequencyShift_add (first second : Position) (field : FullMatterL2) :
    frequencyShift first (frequencyShift second field)=frequencyShift (first+second) field := by
  apply Lp.ext
  have inner := (measurePreserving_sub_right volume first).quasiMeasurePreserving.ae
    (frequencyShift_ae second field)
  filter_upwards [frequencyShift_ae first (frequencyShift second field),inner,
    frequencyShift_ae (first+second) field] with frequency outside inside together
  rw [outside,inside,together,sub_sub]

theorem phaseShift_zero (field : FullMatterL2) : phaseShift 0 field=field := by
  apply fourier.injective
  rw [phaseShift_fourier,frequencyShift_zero]

theorem phaseShift_add (first second : Position) (field : FullMatterL2) :
    phaseShift first (phaseShift second field)=phaseShift (first+second) field := by
  apply fourier.injective
  rw [phaseShift_fourier,phaseShift_fourier,frequencyShift_add,phaseShift_fourier]

theorem phaseShift_inverse (shift : Position) (field : FullMatterL2) :
    phaseShift shift (phaseShift (-shift) field)=field := by
  rw [phaseShift_add,add_neg_cancel,phaseShift_zero]

theorem phaseShift_adjoint (shift : Position) :
    (phaseShift shift).toContinuousLinearMap.adjoint=(phaseShift (-shift)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro field
  apply ext_inner_left ℂ
  intro test
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (phaseShift shift test) field=inner ℂ test (phaseShift (-shift) field)
  nth_rw 1 [← phaseShift_inverse shift field]
  exact (phaseShift shift).inner_map_map test (phaseShift (-shift) field)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
