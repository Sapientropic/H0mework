import H0mework.Physics.LCDesign.Components

/-!
# LC/transducer parameter sensitivity

The operator-level tolerance is reduced to component/run coordinates.  The
compiled scalar phase is Lipschitz in accumulated phase `omega * time`, and
the complete transducer operator is bounded by transfer-gain error plus the
reference gain times accumulated-phase error.

These are upstream analytic estimates.  No coupling receipt, consciousness
or body verdict appears in their hypotheses.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Producer

open _root_.SaturationMonoid.AffineRelaxation
open Physical.Interface

noncomputable section

theorem unitComplexPhase_norm_sub_le (left right : ℝ) :
    ‖unitComplexPhase left - unitComplexPhase right‖ ≤ |left - right| := by
  have factor :
      unitComplexPhase left - unitComplexPhase right =
        unitComplexPhase right * (unitComplexPhase (left - right) - 1) := by
    rw [mul_sub, mul_one, ← unitComplexPhase_add]
    congr 2
    ring
  rw [factor, norm_mul, unitComplexPhase_norm, one_mul]
  simpa [unitComplexPhase, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := left - right))

theorem schrodingerScalarPhase_norm_sub_le
    (leftOmega leftTime rightOmega rightTime : ℝ) :
    ‖schrodingerScalarPhase leftOmega leftTime -
        schrodingerScalarPhase rightOmega rightTime‖ ≤
      |leftOmega * leftTime - rightOmega * rightTime| := by
  unfold schrodingerScalarPhase unitComplexPhaseWithRate
  calc
    _ ≤ |(-leftOmega) * leftTime - (-rightOmega) * rightTime| :=
      unitComplexPhase_norm_sub_le
        (-leftOmega * leftTime) (-rightOmega * rightTime)
    _ = |leftOmega * leftTime - rightOmega * rightTime| := by
      rw [show (-leftOmega) * leftTime - (-rightOmega) * rightTime =
        -(leftOmega * leftTime - rightOmega * rightTime) by ring]
      exact abs_neg _

theorem schrodingerScalarPhase_norm (omega time : ℝ) :
    ‖schrodingerScalarPhase omega time‖ = 1 := by
  exact unitComplexPhaseWithRate_norm (-omega) time

def scalarPhaseOperator (omega time : ℝ) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  (schrodingerScalarPhase omega time) •
    ContinuousLinearMap.id ℂ HilbertEmbodimentState

theorem compiledLCResonatorOperator_eq_scalarPhaseOperator
    (design : UniformFiniteLCTransducerNetworkDesign) (time : ℝ) :
    compiledLCResonatorOperator design time =
      scalarPhaseOperator (normalizedLCAngularFrequency design) time := by
  ext state
  simp [compiledLCResonatorOperator, scalarPhaseOperator,
    schrodingerScalarPhaseFlowHom,
    unitComplexPhaseWithRateFlowHom_apply,
    unitComplexPhaseWithRateLinearIsometryEquiv_apply,
    relaxModule_zero_target_eq_residual_smul,
    schrodingerScalarPhase, unitComplexPhaseWithRate]

theorem compiledLCTransducerOperator_eq_scalarPhaseOperator
    (design : UniformFiniteLCTransducerNetworkDesign) (time : ℝ) :
    compiledLCTransducerOperator design time =
      (((design.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency design) time) •
        ContinuousLinearMap.id ℂ HilbertEmbodimentState) := by
  rw [compiledLCTransducerOperator,
    compiledLCResonatorOperator_eq_scalarPhaseOperator]
  ext state
  simp [scalarPhaseOperator, smul_smul]

theorem norm_scalarPhaseOperator_sub_le
    (leftOmega leftTime rightOmega rightTime : ℝ) :
    ‖scalarPhaseOperator leftOmega leftTime -
        scalarPhaseOperator rightOmega rightTime‖ ≤
      |leftOmega * leftTime - rightOmega * rightTime| := by
  rw [show scalarPhaseOperator leftOmega leftTime -
      scalarPhaseOperator rightOmega rightTime =
      ((schrodingerScalarPhase leftOmega leftTime -
        schrodingerScalarPhase rightOmega rightTime) •
          ContinuousLinearMap.id ℂ HilbertEmbodimentState) by
    ext state
    simp [scalarPhaseOperator, sub_smul]]
  rw [norm_smul]
  calc
    _ ≤ ‖schrodingerScalarPhase leftOmega leftTime -
          schrodingerScalarPhase rightOmega rightTime‖ * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ |leftOmega * leftTime - rightOmega * rightTime| := by
      simpa using schrodingerScalarPhase_norm_sub_le
        leftOmega leftTime rightOmega rightTime

theorem transducerCoefficient_sub_norm_le
    (leftGain rightGain leftOmega leftTime rightOmega rightTime : ℝ) :
    ‖(leftGain : ℂ) * schrodingerScalarPhase leftOmega leftTime -
        (rightGain : ℂ) * schrodingerScalarPhase rightOmega rightTime‖ ≤
      |leftGain - rightGain| + |rightGain| *
        |leftOmega * leftTime - rightOmega * rightTime| := by
  let leftPhase := schrodingerScalarPhase leftOmega leftTime
  let rightPhase := schrodingerScalarPhase rightOmega rightTime
  rw [show (leftGain : ℂ) * leftPhase - (rightGain : ℂ) * rightPhase =
      (((leftGain - rightGain : ℝ) : ℂ) * leftPhase) +
        (rightGain : ℂ) * (leftPhase - rightPhase) by push_cast; ring]
  calc
    _ ≤ ‖(((leftGain - rightGain : ℝ) : ℂ) * leftPhase)‖ +
        ‖(rightGain : ℂ) * (leftPhase - rightPhase)‖ := norm_add_le _ _
    _ = |leftGain - rightGain| * ‖leftPhase‖ +
        |rightGain| * ‖leftPhase - rightPhase‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ = |leftGain - rightGain| +
        |rightGain| * ‖leftPhase - rightPhase‖ := by
      rw [show ‖leftPhase‖ = 1 by
        exact schrodingerScalarPhase_norm leftOmega leftTime]
      ring
    _ ≤ |leftGain - rightGain| + |rightGain| *
        |leftOmega * leftTime - rightOmega * rightTime| := by
      gcongr
      exact schrodingerScalarPhase_norm_sub_le
        leftOmega leftTime rightOmega rightTime

/-- Component/run sensitivity of the complete compiled operator. -/
theorem norm_compiledLCTransducerOperator_sub_le
    (leftDesign rightDesign : UniformFiniteLCTransducerNetworkDesign)
    (leftTime rightTime : ℝ) :
    ‖compiledLCTransducerOperator leftDesign leftTime -
        compiledLCTransducerOperator rightDesign rightTime‖ ≤
      |leftDesign.branch.transferGain - rightDesign.branch.transferGain| +
        |rightDesign.branch.transferGain| *
          |normalizedLCAngularFrequency leftDesign * leftTime -
            normalizedLCAngularFrequency rightDesign * rightTime| := by
  rw [compiledLCTransducerOperator_eq_scalarPhaseOperator,
    compiledLCTransducerOperator_eq_scalarPhaseOperator]
  rw [show (((leftDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency leftDesign) leftTime) •
        ContinuousLinearMap.id ℂ HilbertEmbodimentState) -
      (((rightDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency rightDesign) rightTime) •
        ContinuousLinearMap.id ℂ HilbertEmbodimentState) =
      ((((leftDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency leftDesign) leftTime) -
        ((rightDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency rightDesign) rightTime)) •
        ContinuousLinearMap.id ℂ HilbertEmbodimentState) by
    ext state
    simp [sub_smul]]
  rw [norm_smul]
  calc
    _ ≤ ‖(leftDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency leftDesign) leftTime -
        (rightDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency rightDesign) rightTime‖ * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ = ‖(leftDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency leftDesign) leftTime -
        (rightDesign.branch.transferGain : ℂ) *
          schrodingerScalarPhase
            (normalizedLCAngularFrequency rightDesign) rightTime‖ := by ring
    _ ≤ _ := transducerCoefficient_sub_norm_le _ _ _ _ _ _

end

end Producer
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.schrodingerScalarPhase_norm_sub_le
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.norm_compiledLCTransducerOperator_sub_le
