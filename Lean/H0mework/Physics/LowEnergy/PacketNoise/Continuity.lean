import H0mework.Physics.LowEnergy.PacketNoise.Cosine

/-! Momentum transfer varies strongly continuously on the fixed whole L² carrier, so its current weights can be integrated without orthogonalizing each momentum anew. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace
noncomputable section

def shiftMap (shift : Position) : C(Position,Position) := ⟨fun frequency => frequency-shift,by fun_prop⟩

theorem shiftMap_continuous : Continuous shiftMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun pair : Position×Position => pair.2-pair.1)
  fun_prop

theorem frequencyShift_continuous (field : FullMatterL2) :
    Continuous (fun shift : Position => frequencyShift shift field) := by
  have generated := (continuous_const (y := field)).compMeasurePreservingLp shiftMap_continuous
    (fun shift => measurePreserving_sub_right volume shift) ENNReal.ofNat_ne_top
  exact generated

theorem phaseShift_continuous (field : FullMatterL2) :
    Continuous (fun shift : Position => phaseShift shift field) :=
  fourier.symm.continuous.comp (frequencyShift_continuous (fourier field))

theorem cosineShift_continuous (field : FullMatterL2) :
    Continuous (fun shift : Position => cosineShift shift field) :=
  ((phaseShift_continuous field).add ((phaseShift_continuous field).comp continuous_neg)).const_smul (1/2 : ℂ)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
