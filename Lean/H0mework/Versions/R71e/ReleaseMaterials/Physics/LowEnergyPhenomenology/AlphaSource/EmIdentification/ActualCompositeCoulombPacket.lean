import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeCoulombIR
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeStaticCurrent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeCoulombPacket
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualWholeStatic ActualEMCarrierOwn ActualMasslessStaticPair
open ActualCompositeFieldCurrent ActualCompositeStaticCurrent MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩

theorem composite_matrix_read_complex_smul (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (a : ℂ) (M : WholeMatrix) :
    compositeMatrixRead branch pd ps dL dR sL sR (a • M) =
      a * compositeMatrixRead branch pd ps dL dR sL sR M := by
  rw [composite_matrix_read, composite_matrix_read, Matrix.smul_mulVec, dotProduct_smul]
  rfl

/-- The same fullY/independent-sharp norm1 composite endpoints read the original full289 packet. -/
def compositeCoulombPacket (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (scale : ℝ)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) : ℂ :=
  compositeMatrixRead branch pd ps dL dR sL sR (wholeCoulombIRPacket scale test x)

/-- Every field slot of the original action current enters the literal Fourier integral. -/
theorem composite_coulomb_packet_original (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (scale : ℝ)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    compositeCoulombPacket branch pd ps dL dR sL sR scale test x =
      ∫ frequency, sourceSpatialPhase frequency x * test frequency *
        dotProduct (compositeDetector branch pd dL dR)
          (wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency) *ᵥ ActualCompositeFieldCurrent.compositeCurrent ps sL sR) := by
  unfold compositeCoulombPacket wholeCoulombIRPacket
  rw [←(compositeMatrixRead branch pd ps dL dR sL sR).integral_comp_comm
    (whole_coulomb_ir_packet_integrable scale test x)]
  apply integral_congr_ae
  filter_upwards with frequency
  rw [composite_matrix_read_complex_smul, composite_matrix_read]

/-- The original source profile and spatial dilation are consumed by the actual N3 detector. -/
theorem composite_coulomb_packet_original_dilation (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (scale : ℝ) (positive : 0 < scale)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    compositeCoulombPacket branch pd ps dL dR sL sR scale test x = scale⁻¹ •
      compositeCoulombPacket branch pd ps dL dR sL sR 1
        (PreparationPhysicalCausalSpatialDilation.sourceDilatedTest scale⁻¹ (inv_ne_zero positive.ne') test)
        (scale⁻¹ • x) := by
  unfold compositeCoulombPacket
  rw [whole_coulomb_ir_packet_original_dilation scale positive, map_smul]

/-- The complete N3 source response generates the actual long-range Fourier coefficient. -/
theorem composite_coulomb_packet_limit (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => compositeCoulombPacket branch pd ps dL dR sL sR scale test x)
      (𝓝[>] 0) (𝓝 (emNewtonPacket 0 0 test x *
        (actualStaticPairSeed * compositeMasslessWeight pd dL dR * compositeMasslessWeight ps sL sR /
          ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)))) := by
  have actual := (compositeMatrixRead branch pd ps dL dR sL sR).continuous.tendsto _ |>.comp
    (whole_coulomb_ir_packet_limit test x)
  rw [composite_matrix_read_complex_smul, composite_matrix_read, composite_full_green_coefficient] at actual
  exact actual

/-- The source-generated N3 coefficient consumes exactly one original spatial Fourier4pi. -/
theorem composite_coulomb_spatial_limit (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => compositeCoulombPacket branch pd ps dL dR sL sR scale test x)
      (𝓝[>] 0) (𝓝 ((∫ y, (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹ * emPacket test (x-y)) *
        (actualStaticPairSeed * compositeMasslessWeight pd dL dR * compositeMasslessWeight ps sL sR /
          ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)))) := by
  simpa only [em_newton_massless_convolution] using
    composite_coulomb_packet_limit branch pd ps dL dR sL sR test x

end LowEnergy.GaussComposite.ActualCompositeCoulombPacket
