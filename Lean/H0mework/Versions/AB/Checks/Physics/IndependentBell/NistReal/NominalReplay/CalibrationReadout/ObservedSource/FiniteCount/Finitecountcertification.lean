import H0mework.Versions.AB.Checks.Physics.IndependentBell.NistReal.NominalReplay.CalibrationReadout.ObservedSource.FiniteCount.Boundedfeedback
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent deterministic transport of source-observation coverage to actual feedback bounds. -/
set_option autoImplicit false

open Lean Elab Command

private partial def finiteClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then finiteClosure env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => info.getUsedConstantsAsSet.toArray.toList
        | none => []
      finiteClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let roots := [``P23.GaussianWindow.Calibration.Observed.FiniteCount.same_plant_bounded_count_feedback,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gain_midpoint_rational,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gainEnvelope_legality,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.boxCenter_mem]
  let closure := finiteClosure env roots
  let required := [``P23.GaussianWindow.countPGF,
    ``P23.GaussianWindow.countPGF_hasSum,
    ``P23.GaussianWindow.countPGF_eq,
    ``P23.GaussianWindow.Calibration.noClickA_eq,
    ``P23.GaussianWindow.Calibration.noClickAB_eq,
    ``P23.GaussianWindow.Calibration.Observed.Domain,
    ``P23.GaussianWindow.Calibration.Observed.recoveredT,
    ``P23.GaussianWindow.Calibration.Observed.recoveredGain,
    ``P23.GaussianWindow.Calibration.Observed.scalar_recovery,
    ``P23.GaussianWindow.Calibration.Observed.gainKernel,
    ``P23.GaussianWindow.Calibration.Observed.matchedCounts,
    ``P23.GaussianWindow.Calibration.Observed.same_kernel_gain_recovery,
    ``P23.GaussianWindow.Calibration.Observed.horizontal_counts_eq,
    ``P23.GaussianWindow.Calibration.Observed.vertical_counts_eq,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.Bounds,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.ObservationBox,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.WholeDomain,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.InObservation,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.whole_box_domain,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.tLo,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.tHi,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.inverse_t_bounds,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.t_envelope_legal,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gainOf,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gainOf_mono,
    ``Real.artanh_le_artanh, ``Real.sqrt_le_sqrt,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.inverse_gain_bounds,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.dyadicLo,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.dyadicHi,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.dyadicLo_le,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.le_dyadicHi,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gainEnvelope,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gainEnvelope_legality,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gain_midpoint_rational,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.inverse_gain_enclosed,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.same_kernel_box_readback,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.estimatedGain,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.feedback_gain_formula,
    ``P23.FrameWindow.ControlIdentity.Plant,
    ``P23.FrameWindow.ControlIdentity.generatedGain,
    ``P23.FrameWindow.ControlIdentity.feedbackDrive,
    ``P23.FrameWindow.ControlIdentity.power,
    ``P23.FrameWindow.ControlIdentity.hwpRatio]
  for name in required do
    unless closure.contains name do throwError "MISSING_SOURCE_COVERAGE_TRANSPORT_OR_ACTUAL_UPDATE {name}"
  let primitive := finiteClosure env [``P23.GaussianWindow.Calibration.Observed.FiniteCount.Bounds,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.ObservationBox,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.WholeDomain,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.InObservation,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.tLo,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.tHi,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.dyadicLo,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.dyadicHi]
  for name in [``P23.GaussianWindow.Calibration.Observed.FiniteCount.whole_box_domain,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.inverse_t_bounds,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.inverse_gain_enclosed,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.gainEnvelope,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.same_kernel_box_readback,
    ``P23.GaussianWindow.Calibration.Observed.FiniteCount.same_plant_bounded_count_feedback] do
    if primitive.contains name then throwError "GAIN_BOUND_OR_TARGET_ENDPOINT_IN_BOX_PRIMITIVE {name}"
  for name in closure.toArray do
    let label := (privateToUserName name).toString
    if "SaturationMonoid.".isPrefixOf label || "ProbabilityTheory.".isPrefixOf label then
      throwError "ROOT_OR_NEW_PROBABILITY_AUTHORITY_IN_DETERMINISTIC_FEEDBACK {name}"
  let declarations := env.constants.toList.filter fun (n, _) =>
    let label := (privateToUserName n).toString
    "P23.GaussianWindow.".isPrefixOf label || "P23.FrameWindow.ControlIdentity.".isPrefixOf label
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_BOUNDED_FEEDBACK_AXIOMS {name}: {axioms}"
  logInfo m!"FINITE_COUNT_FEEDBACK_CERTIFIED declarations={declarations.length} nodes={closure.size} required={required.length} primitive={primitive.size}"
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"FINITE_COUNT_FEEDBACK_AXIOMS {root}: {axioms}"

namespace P23.GaussianWindow.Calibration.Observed.FiniteCount.IndependentCertification

noncomputable section

private def around (x : ℝ) : Bounds := ⟨x-1/1000,x+1/1000,by linarith⟩
private def box : ObservationBox := ⟨around (1/3),around (1/3),around (5/21)⟩
private def counts : Counts := ⟨1/3,1/3,5/21⟩

theorem nonempty_raw_box : WholeDomain box := by
  constructor <;> norm_num [box,around,deltaLo,vacuumHi]

theorem source_observation_box_member : InObservation box counts := by
  norm_num [InObservation,InBounds,box,around,counts]

theorem generated_gain_encloses_count_inverse (m : ℕ) :
    InBounds (gainEnvelope box nonempty_raw_box m) (recoveredGain counts) :=
  inverse_gain_enclosed nonempty_raw_box m source_observation_box_member

theorem every_precision_generates_legal_estimate (m : ℕ) :
    0 < midpoint (gainEnvelope box nonempty_raw_box m) ∧
    ∃ q : ℚ, (q : ℝ) = midpoint (gainEnvelope box nonempty_raw_box m) :=
  ⟨(gainEnvelope_legality nonempty_raw_box m).2.2,
    gain_midpoint_rational box nonempty_raw_box m⟩

theorem coarse_precision_outer_rounding : dyadicLo 0 (3/4) = 0 ∧ dyadicHi 0 (3/4) = 1 := by
  norm_num [dyadicLo,dyadicHi]

theorem nonintegral_scaled_outer_rounding :
    dyadicLo 3 (5/16) = 1/4 ∧ dyadicHi 3 (5/16) = 3/8 := by
  norm_num [dyadicLo,dyadicHi]

theorem coarse_lower_zero_keeps_positive_midpoint : midpoint ⟨0,1,by norm_num⟩ = 1/2 := by
  norm_num [midpoint]

theorem actual_update_uses_actual_current_gain
    (p : P23.FrameWindow.ControlIdentity.Plant) (d : P23.FrameWindow.ControlIdentity.Drive)
    (estimate desired : P23.FrameWindow.ControlIdentity.Gain) :
    P23.FrameWindow.ControlIdentity.generatedGain p
      (P23.FrameWindow.ControlIdentity.feedbackDrive d estimate desired) =
      ⟨(P23.FrameWindow.ControlIdentity.generatedGain p d).h*desired.h/estimate.h,
        (P23.FrameWindow.ControlIdentity.generatedGain p d).v*desired.v/estimate.v⟩ :=
  feedback_gain_formula p d estimate desired

end
end P23.GaussianWindow.Calibration.Observed.FiniteCount.IndependentCertification

run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (n, _) =>
    "P23.GaussianWindow.Calibration.Observed.FiniteCount.IndependentCertification.".isPrefixOf
      (privateToUserName n).toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in declarations do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "UNAUTHORIZED_INDEPENDENT_FINITE_FEEDBACK_AXIOMS {name}: {axioms}"
  logInfo m!"FINITE_COUNT_FEEDBACK_INDEPENDENT_AXIOMS declarations={declarations.length}"
