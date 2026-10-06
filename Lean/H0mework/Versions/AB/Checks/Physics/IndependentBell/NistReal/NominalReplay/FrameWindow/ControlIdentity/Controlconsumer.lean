import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.FrameWindow.ControlIdentity.Controlsource

set_option autoImplicit false

namespace P23.FrameWindow.ControlIdentity.Consumer

noncomputable section

theorem snapshot_and_calibration_ambiguity {α β : Type*} (state : Gain → α)
    (calibrationReadout : Gain → β) (calibration : Gain) {h v : ℝ}
    (hh : 0 < h) (hv : 0 < v) :
    power (circleDrive h v hh) = 1 ∧ power (ellipseDrive h v hv) = 1 ∧
    state (generatedGain (circlePlant h v hh) (circleDrive h v hh)) =
      state (generatedGain (ellipsePlant h v hv) (ellipseDrive h v hv)) ∧
    calibrationReadout (generatedGain (circlePlant h v hh)
      (inverseDrive (circlePlant h v hh) calibration)) =
      calibrationReadout (generatedGain (ellipsePlant h v hv)
        (inverseDrive (ellipsePlant h v hv) calibration)) ∧
    normTangent (circlePlant h v hh) (circleDrive h v hh) = 0 ∧
    normTangent (ellipsePlant h v hv) (ellipseDrive h v hv) = -3*h*v ∧ -3*h*v < 0 :=
  ⟨circleDrive_unit hh, ellipseDrive_unit hv, snapshot_readout_eq state hh hv,
    calibration_readout_eq calibrationReadout hh hv calibration, circle_normTangent hh,
    ellipse_normTangent hv, (snapshot_control_tangents_differ hh hv).2.2⟩

theorem same_plant_actual_update {α : Type*} (readout : Gain → α) (p : Plant)
    (current : Drive) (desired : Gain) (hu : current.u ≠ 0) (hv : current.v ≠ 0)
    (hh : 0 < desired.h) (hV : 0 < desired.v) :
    recoveredCouplings current (generatedGain p current) = ⟨p.kH,p.kV⟩ ∧
    (generatedGain p current).h ≠ 0 ∧ (generatedGain p current).v ≠ 0 ∧
    generatedGain p (feedbackDrive current (generatedGain p current) desired) = desired ∧
    0 < (feedbackDrive current (generatedGain p current) desired).u ∧
    0 < (feedbackDrive current (generatedGain p current) desired).v ∧
    readout (generatedGain p (feedbackDrive current (generatedGain p current) desired)) = readout desired ∧
    power (feedbackDrive current (generatedGain p current) desired) =
      (desired.h/p.kH)^2+(desired.v/p.kV)^2 ∧
    hwpRatio (feedbackDrive current (generatedGain p current) desired) =
      desired.v*p.kH/(desired.h*p.kV) := by
  have hobs := observed_gains_nonzero p current hu hv
  have hpos := feedback_positive p current desired hu hv hh hV
  exact ⟨same_plant_coupling_recovery p current hu hv, hobs.1, hobs.2,
    same_plant_feedback_generated p current desired hu hv, hpos.1, hpos.2,
    feedback_state_readout readout p current desired hu hv,
    feedback_power_readout p current desired hu hv, feedback_hwp_readout p current desired hu hv hh⟩

end
end P23.FrameWindow.ControlIdentity.Consumer
