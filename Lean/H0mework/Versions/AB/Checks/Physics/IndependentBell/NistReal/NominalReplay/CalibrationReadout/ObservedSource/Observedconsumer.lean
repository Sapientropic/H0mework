import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.CalibrationReadout.ObservedSource.Observedgain
import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.FrameWindow.ControlIdentity.Controlconsumer

set_option autoImplicit false

namespace P23.GaussianWindow.Calibration.Observed.Consumer

open P23.FrameWindow.ControlIdentity
noncomputable section

theorem same_plant_count_feedback {α : Type*} (readout : Gain → α) (p : Plant)
    (current : Drive) (hu : 0 < current.u) (hv : 0 < current.v)
    (desired : Gain) (hh : 0 < desired.h) (hV : 0 < desired.v)
    (aH bH aV bV : Transmission) :
    let source := gainKernel (generatedGain p current)
    let counts := matchedCounts source aH bH aV bV
    let observed := inverseGain counts
    let update := feedbackDrive current observed desired
    Domain counts.h ∧ Domain counts.v ∧
    observed = generatedGain p current ∧
    generatedGain p update = desired ∧ 0 < update.u ∧ 0 < update.v ∧
    readout (generatedGain p update) = readout desired ∧
    power update = (desired.h/p.kH)^2+(desired.v/p.kV)^2 ∧
    hwpRatio update = desired.v*p.kH/(desired.h*p.kV) := by
  have hgH : 0 < (generatedGain p current).h := mul_pos p.kH_pos hu
  have hgV : 0 < (generatedGain p current).v := mul_pos p.kV_pos hv
  have hr := same_kernel_gain_recovery (generatedGain p current) hgH hgV aH bH aV bV
  dsimp only
  refine ⟨hr.1,hr.2.1,hr.2.2,?_⟩
  rw [hr.2.2]
  have hc := P23.FrameWindow.ControlIdentity.Consumer.same_plant_actual_update
    readout p current desired (ne_of_gt hu) (ne_of_gt hv) hh hV
  exact hc.2.2.2

end
end P23.GaussianWindow.Calibration.Observed.Consumer
