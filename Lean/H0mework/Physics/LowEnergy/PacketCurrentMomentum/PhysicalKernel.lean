import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Overlap

/-! The outgoing physical momentum shifts the second complete field from k
to k-p. The actual source band and the physical Fourier density are retained. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
open FullQuantum FullSpace PacketField PacketNoise PacketPairResponse
noncomputable section
attribute [local irreducible] PacketField.spectrum retardedField physicalBand extendBand
variable {ι : Type*} [Fintype ι]

theorem physicalTransfer_scale (momentum : Position) : (2*Real.pi) • physicalTransfer momentum=momentum := by
  rw [physicalTransfer,smul_smul,mul_inv_cancel₀ (by positivity : (2*Real.pi : ℝ)≠0),one_smul]

theorem spectrum_pair_physical (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (first second : ι) (momentum : Position) :
    inner ℂ (PacketField.spectrum circleY circleZ numerator energy damping positive time first)
      (translation (physicalTransfer momentum) (PacketField.spectrum circleY circleZ numerator energy damping positive time second))=
    (fourierDensity : ℂ)*∫ internal : Position, inner ℂ
      (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point first) internal)
      (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point second) (internal-momentum)) := by
  rw [L2.inner_def]
  have moved := (measurePreserving_sub_right volume (physicalTransfer momentum)).quasiMeasurePreserving.ae
    (spectrum_ae circleY circleZ numerator energy damping positive time second)
  calc
    _ = ∫ frequency : Position, inner ℂ
        (physicalBand (fun point => retardedField circleY circleZ numerator energy damping positive time point first) frequency)
        (physicalBand (fun point => retardedField circleY circleZ numerator energy damping positive time point second)
          (frequency-physicalTransfer momentum)) := by
      apply integral_congr_ae
      filter_upwards [spectrum_ae circleY circleZ numerator energy damping positive time first,moved,
        translation_ae (physicalTransfer momentum) (PacketField.spectrum circleY circleZ numerator energy damping positive time second)]
        with frequency left right translated
      rw [left,translated,right]
    _ = ∫ frequency : Position, inner ℂ
        (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point first) ((2*Real.pi) • frequency))
        (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point second)
          ((2*Real.pi) • frequency-momentum)) := by
      simp_rw [physicalBand,smul_sub,physicalTransfer_scale]
    _ = _ := by
      have generated := physicalFourier_measure (fun internal : Position => inner ℂ
        (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point first) internal)
        (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point second) (internal-momentum)))
      simpa only [fourierDensity,one_div,Complex.real_smul] using generated

theorem outgoing_source_kernel (current : Matrix ι ι ℝ)
    (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (momentum : Position) :
    outgoing current (reconstructedField circleY circleZ numerator energy damping positive time) momentum=
      (1/4 : ℂ)*∑ first, ∑ second, (current first second : ℂ)*
        ((fourierDensity : ℂ)*(∫ internal : Position, inner ℂ
          (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point first) internal)
          (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point second) (internal-momentum)))+
          (fourierDensity : ℂ)*(∫ internal : Position, inner ℂ
          (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point second) internal)
          (extendBand (fun point => retardedField circleY circleZ numerator energy damping positive time point first) (internal-momentum)))) := by
  unfold reconstructedField
  rw [outgoing_spectrum]
  simp_rw [spectrum_pair_physical]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
