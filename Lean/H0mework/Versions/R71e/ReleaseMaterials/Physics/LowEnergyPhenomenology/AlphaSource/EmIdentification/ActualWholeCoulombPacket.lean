import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeCoulombIR
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualWholeStatic
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalFeedback CanonicalGradedSpatialSource
open Stage10 PreparationVacuumStaticSpatialSource PreparationVacuumPhysicalPoleSheet
open ActualEMCarrierOwn ActualEMCurrentSplit ActualEMResponseSplit ActualEMObservable ActualMasslessCurrent
open ActualMasslessStaticPair ActualElectronOwnerTest MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩
attribute [local irreducible] actualWholeMatrixRead actualElectronFieldTest

theorem actual_whole_matrix_read_complex_smul (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) (a : ℂ) (M : WholeMatrix) :
    actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S (a • M) =
      a * actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S M := by
  unfold actualWholeMatrixRead
  change actualElectronFieldTest branch qd dL dR lambda T
    ((a • M) *ᵥ emUnitSourceCurrent qs sL sR mu S) =
      a * actualElectronFieldTest branch qd dL dR lambda T
        (M *ᵥ emUnitSourceCurrent qs sL sR mu S)
  rw [Matrix.smul_mulVec, map_smul]
  rfl

/-- The actual independently prepared detector reads the original full289 Fourier packet with one hc. -/
def actualWholeCoulombPacket (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S scale : ℝ)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) : ℂ :=
  actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S
    (wholeCoulombIRPacket scale test x)

theorem actual_whole_coulomb_packet_original (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S scale : ℝ)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    actualWholeCoulombPacket branch qd qs dL dR sL sR lambda mu T S scale test x =
      ∫ frequency, sourceSpatialPhase frequency x * test frequency *
        emCurrentObservation (wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency))
          (emUnitDetectorCovector branch qd dL dR lambda T)
          (emUnitSourceCurrent qs sL sR mu S) := by
  unfold actualWholeCoulombPacket wholeCoulombIRPacket
  rw [←(actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S).integral_comp_comm
    (whole_coulomb_ir_packet_integrable scale test x)]
  apply integral_congr_ae
  filter_upwards with frequency
  rw [actual_whole_matrix_read_complex_smul, actual_whole_matrix_read_original]

/-- The actual detector consumes the same original profile and position dilation. -/
theorem actual_whole_coulomb_packet_original_dilation (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S scale : ℝ) (positive : 0 < scale)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    actualWholeCoulombPacket branch qd qs dL dR sL sR lambda mu T S scale test x = scale⁻¹ •
      actualWholeCoulombPacket branch qd qs dL dR sL sR lambda mu T S 1
        (PreparationPhysicalCausalSpatialDilation.sourceDilatedTest scale⁻¹ (inv_ne_zero positive.ne') test)
        (scale⁻¹ • x) := by
  unfold actualWholeCoulombPacket
  rw [whole_coulomb_ir_packet_original_dilation scale positive, map_smul]

/-- The source-generated full-current Coulomb strength multiplies the true Newton packet. -/
theorem actual_whole_coulomb_packet_limit (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => actualWholeCoulombPacket branch qd qs dL dR sL sR lambda mu T S scale test x)
      (𝓝[>] 0) (𝓝 (emNewtonPacket 0 0 test x *
        (actualStaticPairSeed * actualUnitMasslessWeight qd dL dR lambda T *
          actualUnitMasslessWeight qs sL sR mu S /
          ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)))) := by
  have actual := (actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S).continuous.tendsto _ |>.comp
    (whole_coulomb_ir_packet_limit test x)
  rw [actual_whole_matrix_read_complex_smul, actual_whole_matrix_read_origin] at actual
  exact actual

/-- Exactly one Fourier 4pi enters the actual complete source-current long-range observation. -/
theorem actual_whole_coulomb_spatial_limit (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ)
    (test : 𝓢(PhysicalMomentum, ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => actualWholeCoulombPacket branch qd qs dL dR sL sR lambda mu T S scale test x)
      (𝓝[>] 0) (𝓝 ((∫ y, (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹ * emPacket test (x-y)) *
        (actualStaticPairSeed * actualUnitMasslessWeight qd dL dR lambda T *
          actualUnitMasslessWeight qs sL sR mu S /
          ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)))) := by
  simpa only [em_newton_massless_convolution] using
    actual_whole_coulomb_packet_limit branch qd qs dL dR sL sR lambda mu T S test x

end LowEnergy.GaussComposite.ActualWholeStatic
