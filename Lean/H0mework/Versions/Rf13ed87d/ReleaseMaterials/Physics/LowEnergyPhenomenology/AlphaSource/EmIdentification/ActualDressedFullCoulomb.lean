import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedJointCompletion
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeCoulombIR
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTransferCurrent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFullCoulomb
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullFieldRiesz PreparationVacuumFullOriginResponse
open ActualWholeStatic ActualEMCarrierOwn MeasureTheory Filter Set
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldCovector
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard ActualDressedActionPhase
open PhysicalEMTransferCurrent PhysicalEMTransferResolver CanonicalPhysicalYResolvent
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap InnerProductSpace
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩

attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition sourceProfile finiteFull sourceDressedResponse currentVertex

/-- One actual fixed creation preparation and its two frequency-matched original fullY legs. -/
structure DressedEvent where
  epsilon : ℝ
  precision : 0<epsilon
  momentum : PhysicalMomentum
  frame : GaussUnitaryHistory.Index
  cut : ℕ
  energy : ℂ
  nonreal : energy.im≠0

/-- The vertex momentum is minus the physical transfer, on the same original two-leg occurrence. -/
def dressedCurrent (event : DressedEvent) (transfer : PhysicalMomentum) : Fin 289→ℂ :=
  sourceDressedConnectedCurrent event.epsilon event.precision event.momentum (-transfer)
    event.frame event.cut event.energy event.energy

theorem dressed_current_physical_transfer (event : DressedEvent) (transfer : PhysicalMomentum) :
    PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalTransfer (event.momentum-transfer) event.momentum=transfer := by
  unfold PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalTransfer
  abel

/-- The source and detector are the actual opposite Fourier restrictions of this same Green momentum. -/
theorem dressed_pair_static_same_fourier (detector source : DressedEvent) (r : ℝ) (n : PhysicalMomentum) :
    actualMomentum (source.momentum-r • n) source.momentum 0=sourceStaticSpatialMomentum n r ∧
    actualMomentum (detector.momentum+r • n) detector.momentum 0= -sourceStaticSpatialMomentum n r := by
  constructor
  all_goals
    unfold actualMomentum fullMomentum sourcePhysicalTransfer PreparationVacuumPhysicalFeedback.physicalSpatial sourceStaticSpatialMomentum
    funext i
    fin_cases i <;> simp [Fin.cases,Fin.induction,Fin.induction.go,Pi.smul_apply,smul_eq_mul]

/-- The original raw action source difference retains the excited and background preparations independently. -/
theorem dressed_current_original (event : DressedEvent) (transfer : PhysicalMomentum) :
    dressedCurrent event transfer=
      sourceCovector event.momentum
        (sourceTestApprox event.frame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
          (sourceDressedUnit event.epsilon event.precision)))
        (sourceTestApprox event.frame (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))-
      sourceCovector event.momentum
        (sourceTestApprox event.frame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))))
        (sourceTestApprox event.frame (finiteFull event.momentum event.frame event.cut event.energy
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))) := by
  exact source_dressed_connected_current_original event.epsilon event.precision event.momentum (-transfer)
    event.frame event.cut event.energy event.energy

theorem dressed_current_continuous (event : DressedEvent) : Continuous (dressedCurrent event) := by
  apply continuous_pi
  intro i
  have vertex:=(currentVertex_transfer_continuous (fieldBasis i) event.momentum event.frame
    event.cut event.energy event.energy event.nonreal).comp continuous_neg
  have unit : Continuous (fun k : PhysicalMomentum=>inner ℂ (sourceDressedUnit event.epsilon event.precision)
      (currentVertex (fieldBasis i) event.momentum (-k) event.frame event.cut event.energy event.energy
        (sourceDressedUnit event.epsilon event.precision))) :=
    continuous_const.inner (vertex.clm_apply continuous_const)
  have background : Continuous (fun k : PhysicalMomentum=>inner ℂ
      (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))
      (currentVertex (fieldBasis i) event.momentum (-k) event.frame event.cut event.energy event.energy
        (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))) :=
    continuous_const.inner (vertex.clm_apply continuous_const)
  change Continuous (fun k : PhysicalMomentum =>
    inner ℂ (sourceDressedUnit event.epsilon event.precision)
      (currentVertex (fieldBasis i) event.momentum (-k) event.frame event.cut event.energy event.energy
        (sourceDressedUnit event.epsilon event.precision)) -
    inner ℂ (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))
      (currentVertex (fieldBasis i) event.momentum (-k) event.frame event.cut event.energy event.energy
        (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))))
  exact unit.sub background

/-- No extra scalar action/velocity normalizer is inserted in the whole-kernel read. -/
def dressedMatrixRead (detector source : DressedEvent) (transfer : PhysicalMomentum) : WholeMatrix→L[ℝ]ℂ :=
  ({toFun:=fun M=>dotProduct (dressedCurrent detector (-transfer)) (M*ᵥdressedCurrent source transfer)
    map_add':=fun M N=>by rw [Matrix.add_mulVec,dotProduct_add]
    map_smul':=fun r M=>by simp only [Matrix.smul_mulVec,dotProduct_smul,RingHom.id_apply,Complex.real_smul]} :
    WholeMatrix→ₗ[ℝ]ℂ).toContinuousLinearMap

theorem dressed_matrix_read (detector source : DressedEvent) (transfer : PhysicalMomentum) (M : WholeMatrix) :
    dressedMatrixRead detector source transfer M=
      dotProduct (dressedCurrent detector (-transfer)) (M*ᵥdressedCurrent source transfer) := rfl

theorem dressed_matrix_read_complex_smul (detector source : DressedEvent) (transfer : PhysicalMomentum)
    (a : ℂ) (M : WholeMatrix) :
    dressedMatrixRead detector source transfer (a • M)=a*dressedMatrixRead detector source transfer M := by
  rw [dressed_matrix_read,dressed_matrix_read,Matrix.smul_mulVec,dotProduct_smul]
  rfl

/-- Every original field component enters the full padded origin carrier. -/
def dressedOriginCurrent (event : DressedEvent) : Fin 289→ℂ :=
  fullNativeOrigin.transpose*ᵥdressedCurrent event 0

theorem dressed_static_full_origin (detector source : DressedEvent) :
    dressedMatrixRead detector source 0 wholeStaticLimit=
      -dotProduct (dressedOriginCurrent detector) (staticInverse*ᵥdressedOriginCurrent source) := by
  rw [dressed_matrix_read,wholeStaticLimit,Matrix.neg_mulVec,dotProduct_neg]
  simp only [neg_zero]
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  congr 1
  exact (Matrix.dotProduct_transpose_mulVec fullNativeOrigin
    (staticInverse*ᵥ(fullNativeOrigin.transpose*ᵥdressedCurrent source 0)) (dressedCurrent detector 0)).symm.trans
      (dotProduct_comm _ _)

/-- The original algebraic field contact stays separate from its active propagating inverse. -/
theorem dressed_green_contact (detector source : DressedEvent) (transfer : PhysicalMomentum) (p : regularSource) :
    dressedMatrixRead detector source transfer (sourceGreen p)=
      dressedMatrixRead detector source transfer (originalChange p*contactInverse p*originalReadback p)+
      dressedMatrixRead detector source transfer
        (originalChange p*(activeProjection*(extendedKernel p)⁻¹)*originalReadback p) := by
  rw [sourceGreen,Matrix.mul_add,Matrix.add_mul,map_add]

/-- This held zero-transfer test reads the original whole289 Fourier packet. -/
def dressedCoulombPacket (detector source : DressedEvent) (scale : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  dressedMatrixRead detector source 0 (wholeCoulombIRPacket scale test x)

theorem dressed_coulomb_packet_original (detector source : DressedEvent) (scale : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    dressedCoulombPacket detector source scale test x=
      ∫ frequency,sourceSpatialPhase frequency x*test frequency*
        dotProduct (dressedCurrent detector 0)
          (wholeCoulombIRSymbol scale (sourceSpatialMomentum frequency)*ᵥdressedCurrent source 0) := by
  unfold dressedCoulombPacket wholeCoulombIRPacket
  rw [←(dressedMatrixRead detector source 0).integral_comp_comm (whole_coulomb_ir_packet_integrable scale test x)]
  apply integral_congr_ae
  filter_upwards with frequency
  rw [dressed_matrix_read_complex_smul,dressed_matrix_read]
  simp only [neg_zero]

theorem dressed_coulomb_packet_limit (detector source : DressedEvent)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ=>dressedCoulombPacket detector source scale test x) (𝓝[>] 0)
      (𝓝 (emNewtonPacket 0 0 test x*
        (-dotProduct (dressedOriginCurrent detector) (staticInverse*ᵥdressedOriginCurrent source)))) := by
  have paid:=(dressedMatrixRead detector source 0).continuous.tendsto _ |>.comp (whole_coulomb_ir_packet_limit test x)
  rw [dressed_matrix_read_complex_smul,dressed_static_full_origin] at paid
  exact paid

theorem dressed_coulomb_spatial_limit (detector source : DressedEvent)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ=>dressedCoulombPacket detector source scale test x) (𝓝[>] 0)
      (𝓝 ((∫ y,(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y))*
        (-dotProduct (dressedOriginCurrent detector) (staticInverse*ᵥdressedOriginCurrent source)))) := by
  simpa only [em_newton_massless_convolution] using dressed_coulomb_packet_limit detector source test x

end LowEnergy.GaussComposite.ActualDressedFullCoulomb
