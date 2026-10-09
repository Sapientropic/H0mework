import H0mework.Physics.LowEnergy.PacketField.Retarded
import H0mework.Physics.LowEnergy.PacketField.SpatialPair

/-! Genuine primitive-field L² representatives are reconstructed with the
source's negative spatial phase and read by the original quadratic current. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
attribute [local irreducible] retardedField
variable {ι : Type*} [Fintype ι]

theorem spectrum_memLp (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) :
    MemLp (physicalBand (fun point => retardedField circleY circleZ numerator energy damping positive time point row))
      2 (volume : Measure Position) := by
  obtain ⟨bound,nonnegative,bounded⟩ := retardedField_bounded circleY circleZ numerator energy damping positive time row
  exact physicalBand_memLp _ (retardedField_stronglyMeasurable circleY circleZ numerator energy damping positive time row)
    bound nonnegative bounded

def spectrum (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) : FieldSpace FullMatterL2 :=
  (spectrum_memLp circleY circleZ numerator energy damping positive time row).toLp _

def reconstructedField (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) : FieldSpace FullMatterL2 :=
  spatialFourier (spectrum circleY circleZ numerator energy damping positive time row)

theorem spectrum_ae (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) :
    spectrum circleY circleZ numerator energy damping positive time row=ᵐ[volume]
      physicalBand (fun point => retardedField circleY circleZ numerator energy damping positive time point row) :=
  (spectrum_memLp circleY circleZ numerator energy damping positive time row).coeFn_toLp

theorem reconstructedField_fourier (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (row : ι) :
    spatialFourier.symm (reconstructedField circleY circleZ numerator energy damping positive time row)=
      spectrum circleY circleZ numerator energy damping positive time row :=
  spatialFourier.symm_apply_apply _

theorem reconstructedField_pair (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (first second : ι) :
    (∫ position : Position, (inner ℂ
      (reconstructedField circleY circleZ numerator energy damping positive time first position)
      (reconstructedField circleY circleZ numerator energy damping positive time second position)).re)=
    fourierDensity*∫ point : LightBand, (inner ℂ
      (retardedField circleY circleZ numerator energy damping positive time point first)
      (retardedField circleY circleZ numerator energy damping positive time point second)).re ∂bandMeasure := by
  rw [reconstructedField,reconstructedField,spatial_pair]
  rw [← physicalBand_pair]
  apply integral_congr_ae
  filter_upwards [spectrum_ae circleY circleZ numerator energy damping positive time first,
    spectrum_ae circleY circleZ numerator energy damping positive time second] with frequency left right
  rw [left,right]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
