import H0mework.Physics.SourceCoframe.Field
import H0mework.Physics.SourceDirac.Adjoint
import H0mework.Physics.SourceGauge.Equation
import H0mework.Physics.SourceFamily.Qualification

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineCClassicalWorldAcceptance
open StageNineDiracDualFormNativeJointResidualCarrier

noncomputable section

/-- All nine complete channels are generated for the same source, field and
spacetime point. No acceptance or zero-fiber witness enters the constructor. -/
theorem pointwise_zero (step : ℕ) (point : BasePoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber (sourceAt step) (fieldAt step) point := by
  obtain ⟨multiplier, auxiliary, gaugeAuxiliary, lorentz⟩ := algebraic_channels step point
  obtain ⟨matter, dual⟩ := Dirac.dirac_channels_zero step point
  exact (onDiracDualFormNativePointwiseJointZeroFiber_iff_components _ _ _).2
    ⟨multiplier, auxiliary, gaugeAuxiliary, lorentz, Gauge.gauge_euler_zero step point,
      Scalar.residual_zero step point, matter, dual, Coframe.residual_zero step point⟩

theorem joint_zero (step : ℕ) :
    DiracDualFormNativeJointZeroFiber (sourceAt step) (fieldAt step) :=
  (diracDualFormNativeJointZeroFiber_iff_pointwise _ _).2 (pointwise_zero step)

/-- Complete physical acceptance is an output of the generated source and
its actual coupled field equations, for every generated index. -/
theorem accepted (step : ℕ) : ClassicalWorldAcceptance (sourceAt step) (fieldAt step) where
  smooth := field_smooth step
  nondegenerate := field_nondegenerate step
  gravityConnectionLorentzAdmissible := Qualification.lorentz_admissible step
  jointZeroFiber := joint_zero step
  dynamicScalarSourceContact := Qualification.scalar_source_contact step
  simultaneousSixPhysicalSectorNonzero := Qualification.physical_sectors step

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily
