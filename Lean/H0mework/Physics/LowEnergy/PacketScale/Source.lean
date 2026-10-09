import H0mework.Physics.LowEnergy.PacketScale.Cutoff
import H0mework.Physics.LowEnergy.PacketFieldTime.Initial

/-! Finite scales act on the already generated source field and its strong
time derivative. The scale is a Fourier read operation, not a new preparation. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketScale
open FullQuantum FullSpace PacketField PacketFieldTime PacketPairResponse
noncomputable section
variable {ι : Type*} [Fintype ι]
attribute [local irreducible] PacketField.spectrum spectralVelocity sourceSeed cutoff

def scaleField (radius : ℝ) (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) : FieldSpace FullMatterL2 :=
  spatialFourier (cutoff radius (PacketField.spectrum circleY circleZ numerator energy damping positive time row))

def scaleVelocity (radius : ℝ) (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) : FieldSpace FullMatterL2 :=
  spatialFourier (cutoff radius (spectralVelocity circleY circleZ numerator energy damping positive time row))

def scaleSeed (radius : ℝ) (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (row : ι) : FieldSpace FullMatterL2 :=
  spatialFourier (cutoff radius (sourceSeed circleY circleZ numerator energy damping positive row))

def physicalRead (radius : ℝ) : FieldSpace FullMatterL2 →L[ℝ] FieldSpace FullMatterL2 :=
  ((spatialFourier : FieldSpace FullMatterL2 ≃ₗᵢ[ℂ] FieldSpace FullMatterL2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (cutoff radius)).restrictScalars ℝ

theorem physicalRead_apply (radius : ℝ) (field : FieldSpace FullMatterL2) :
    physicalRead radius field=spatialFourier (cutoff radius field) := rfl

theorem scaleField_derivative (radius : ℝ) (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) :
    HasDerivAt (fun t => scaleField radius circleY circleZ numerator energy damping positive t row)
      (scaleVelocity radius circleY circleZ numerator energy damping positive time row) time :=
  (physicalRead radius).hasFDerivAt.comp_hasDerivAt time
    (spectrum_derivative circleY circleZ numerator energy damping positive time row)

theorem scaleVelocity_continuous (radius : ℝ) (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (row : ι) :
    Continuous (fun t => scaleVelocity radius circleY circleZ numerator energy damping positive t row) :=
  (physicalRead radius).continuous.comp (spectralVelocity_continuous circleY circleZ numerator energy damping positive row)

theorem scaleField_initial (radius : ℝ) (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (row : ι) :
    scaleField radius circleY circleZ numerator energy damping positive 0 row=0 := by
  exact (congrArg (physicalRead radius) (spectrum_initial circleY circleZ numerator energy damping positive row)).trans
    (physicalRead radius).map_zero

theorem scaleField_strong_slope (radius : ℝ) (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (row : ι) :
    Tendsto (fun t : ℝ => t⁻¹ • scaleField radius circleY circleZ numerator energy damping positive t row)
      (𝓝[≠] 0) (𝓝 (scaleSeed radius circleY circleZ numerator energy damping positive row)) := by
  have generated := (physicalRead radius).continuous.continuousAt.tendsto.comp
    (spectrum_strong_initial_slope circleY circleZ numerator energy damping positive row)
  simpa only [Function.comp_def,map_smul,physicalRead_apply,scaleField,scaleSeed] using generated

theorem cutoff_spectrum_original (radius : ℝ) (covers : bandRadius≤radius)
    (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) :
    cutoff radius (PacketField.spectrum circleY circleZ numerator energy damping positive time row)=
      PacketField.spectrum circleY circleZ numerator energy damping positive time row := by
  apply Lp.ext
  filter_upwards [cutoff_ae radius (PacketField.spectrum circleY circleZ numerator energy damping positive time row),
    spectrum_ae circleY circleZ numerator energy damping positive time row] with frequency cut source
  rw [cut]
  by_cases inside : frequency∈scaleSet radius
  · rw [if_pos inside]
  · rw [if_neg inside,source]
    have outside : ¬‖(2*Real.pi) • frequency‖≤bandRadius := fun h => inside (h.trans covers)
    exact (PacketFieldTime.physicalBand_outside _ _ outside).symm

theorem scaleField_original (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0<damping) (time : ℝ) (row : ι) :
    scaleField bandRadius circleY circleZ numerator energy damping positive time row=
      reconstructedField circleY circleZ numerator energy damping positive time row := by
  rw [scaleField,cutoff_spectrum_original bandRadius le_rfl]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketScale
