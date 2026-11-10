import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMWeightedTorque
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTemporalPrice
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldUniformVariation
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationHalfDensityCompressionFeed

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMAgeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumGradedTransport
open PreparationVacuumFieldPerturbation PreparationVacuumYukawaTransport PreparationVacuumHalfDensityFiber
open PreparationVacuumUncutYukawa ActualDressedNumberZero ActualDressedNumberField
open ActualDressedEMTemporal ActualDressedLeftFreeJet ActualDressedFullCoulomb ActualDressedNoether
open ActualDressedSourcePreparation ActualSourcePreparedEMWeightedTorque
open ActualSourcePreparedEMPhaseField PhysicalEMVoltage
open PhysicalEMGaugeRealization
open ActualEMAction PreparationVacuumSourcePreparedResponse
open LowEnergy.GaussComposite.SourceGraph
open Filter
open scoped Topology InnerProductSpace
abbrev Op := H →L[ℂ] H
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointCompression emTemporalReader jointCResolvent
  dressedEulerObserver freeCompressionCurrent

private theorem actual_free_resolvent_commutes (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im ≠ 0) : Commute (jointCompression p F 0) (jointCResolvent p F z 0) := by
  have unit := (actual_joint_free_units_near_zero p F z nonreal).self_of_nhds
  have core : Commute (jointCompression p F 0) (jointCompression p F 0-z • (1:Op)) :=
    (Commute.refl _).sub_right ((Commute.one_right _).smul_right _)
  unfold jointCResolvent
  exact inverse_commuting _ _ unit core

/-- The zero-transfer time derivative is the actual resolvent-dressed
compression/weighted-reader residual, with its original Fourier sign. -/
theorem source_em_zero_transfer_age_derivative (event : DressedEvent) (age : ℝ) :
    HasDerivAt (fun t : ℝ => emTemporalFreeKernel event 0 t 0)
      (Complex.I •
        (SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) (-age)*
          jointCResolvent event.momentum event.frame event.energy 0*
          (jointCompression event.momentum event.frame 0*emTemporalReader event.momentum event.frame-
            emTemporalReader event.momentum event.frame*jointCompression event.momentum event.frame 0)*
          jointCResolvent event.momentum event.frame event.energy 0*
          SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age)) age := by
  let C := jointCompression event.momentum event.frame 0
  let R := jointCResolvent event.momentum event.frame event.energy 0
  let J := emTemporalReader event.momentum event.frame
  have left := (time_operator_derivative C (-age)).scomp age ((hasDerivAt_id age).neg)
  have right := time_operator_derivative C age
  have generated := (((left.mul_const R).mul_const J).mul_const R).mul right
  have commuteR := (actual_free_resolvent_commutes event.momentum event.frame event.energy event.nonreal).eq
  have commuteT := (SourceFiniteUnitary.time_commutes C C (Commute.refl C) age).eq
  change C*R=R*C at commuteR
  convert! generated using 1
  · funext t
    simp only [emTemporalFreeKernel,sub_zero,C,R,J,Function.comp_apply,Pi.mul_apply]
  · simp only [Function.comp_apply,neg_smul]
    change Complex.I •
      (SourceFiniteUnitary.time C (-age)*R*(C*J-J*C)*R*SourceFiniteUnitary.time C age) = _
    simp only [mul_sub,sub_mul,smul_sub]
    have first : SourceFiniteUnitary.time C (-age)*R*C*J*R*SourceFiniteUnitary.time C age =
        SourceFiniteUnitary.time C (-age)*C*R*J*R*SourceFiniteUnitary.time C age := by
      calc
        _ = SourceFiniteUnitary.time C (-age)*(R*C)*J*R*SourceFiniteUnitary.time C age := by noncomm_ring
        _ = _ := by rw [←commuteR];noncomm_ring
    have second : SourceFiniteUnitary.time C (-age)*R*J*C*R*SourceFiniteUnitary.time C age =
        SourceFiniteUnitary.time C (-age)*R*J*R*SourceFiniteUnitary.time C age*C := by
      calc
        _ = SourceFiniteUnitary.time C (-age)*R*J*(C*R)*SourceFiniteUnitary.time C age := by noncomm_ring
        _ = SourceFiniteUnitary.time C (-age)*R*J*R*(C*SourceFiniteUnitary.time C age) := by
          rw [commuteR];noncomm_ring
        _ = _ := by rw [commuteT];noncomm_ring
    simp only [one_smul,mul_neg,neg_neg,mul_smul_comm,smul_mul_assoc,
      ←mul_assoc,first,second,sub_eq_add_neg]

/-- Both dual legs remain actual Hilbert adjoints, on the same event/frame. -/
def sourceEMAgeLeft (event : DressedEvent) (age : ℝ) (v : H) : H :=
  (SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) (-age)*
    jointCResolvent event.momentum event.frame event.energy 0).adjoint v

def sourceEMAgeRight (event : DressedEvent) (age : ℝ) (v : H) : H :=
  (jointCResolvent event.momentum event.frame event.energy 0*
    SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age) v

def sourceEMAgePhysicalRead (event : DressedEvent) (age : ℝ) (v : H) : ℂ :=
  sourceEMPhysicalCompressionTorque event.momentum event.frame
    (sourceEMAgeLeft event age v) (sourceEMAgeRight event age v)

private theorem age_pair_read (event : DressedEvent) (age : ℝ) (v : H) :
    inner ℂ v
      ((SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) (-age)*
        jointCResolvent event.momentum event.frame event.energy 0*
        (jointCompression event.momentum event.frame 0*emTemporalReader event.momentum event.frame-
          emTemporalReader event.momentum event.frame*jointCompression event.momentum event.frame 0)*
        jointCResolvent event.momentum event.frame event.energy 0*
        SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age) v) =
      sourceEMAgePhysicalRead event age v := by
  unfold sourceEMAgePhysicalRead
  rw [← source_em_physical_compression_torque]
  unfold sourceEMAgeLeft sourceEMAgeRight
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [mul_apply_eq_comp]

/-- The actual created-minus-background Euler sign is retained. The source
CAR/dilation/frame residual is computed, rather than postulated to vanish. -/
theorem source_em_actual_observer_age_derivative (event : DressedEvent) (age : ℝ) :
    HasDerivAt (fun t : ℝ => dressedEulerObserver event (emTemporalFreeKernel event 0 t 0))
      (Complex.I * (-sourceEMAgePhysicalRead event age (sourceDressedUnit event.epsilon event.precision)+
        sourceEMAgePhysicalRead event age (prepared (sourceProfile event.epsilon event.precision)))) age := by
  have generated := ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age
    (source_em_zero_transfer_age_derivative event age)
  simpa only [ContinuousLinearMap.coe_restrictScalars',Function.comp_def,
    map_smul,smul_eq_mul,dressed_euler_observer_original,age_pair_read] using generated

/-- The original dressed Noether observer consumes the generated age
residual at zero transfer on its actual prepared occurrence. -/
theorem source_em_dressed_noether_age_derivative (event : DressedEvent) (age : ℝ) :
    HasDerivAt (fun t : ℝ => dressedEulerObserver event
      (dressedNoetherKernel event 0 (emGaugeField 0) t 0))
      (Complex.I * (-sourceEMAgePhysicalRead event age (sourceDressedUnit event.epsilon event.precision)+
        sourceEMAgePhysicalRead event age (prepared (sourceProfile event.epsilon event.precision)))) age := by
  have same := (actual_em_temporal_observer_germ event 0).self_of_nhds
  apply (source_em_actual_observer_age_derivative event age).congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => by rw [source_em_phase_field];exact same t)

/-- Every original 289-field force is the original source current assembly,
not a fitted or charge-only insertion. -/
theorem source_em_free_current_assembly (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) :
    freeCompressionCurrent p F force = sourceAssembly p F
      (fun i j => fixedCurrentEntry force p (bareTest p F i) (bareTest p F j)) := by
  have actual := free_compression_direction p F force
  have original := (transportedCompression_first force p F).congr_of_eventuallyEq
    (jointCompression_ray force p F)
  rw [actual.unique original,compression_current_source]

/-- The real nonlinear field family differentiates the age residual in
all original force directions; no field-dependent EM reader is invented. -/
theorem source_em_field_residual_direction (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) :
    HasDerivAt (fun r : ℝ =>
      jointCompression p F (r • force)*emTemporalReader p F-
        emTemporalReader p F*jointCompression p F (r • force))
      (sourceAssembly p F (fun i j => fixedCurrentEntry force p (bareTest p F i) (bareTest p F j))*
        emTemporalReader p F-
        emTemporalReader p F*sourceAssembly p F
          (fun i j => fixedCurrentEntry force p (bareTest p F i) (bareTest p F j))) 0 := by
  have generated := ((free_compression_direction p F force).mul_const (emTemporalReader p F)).sub
    ((free_compression_direction p F force).const_mul (emTemporalReader p F))
  convert! generated using 1
  simp only [source_em_free_current_assembly]

end LowEnergy.GaussComposite.ActualSourcePreparedEMAgeReturn
