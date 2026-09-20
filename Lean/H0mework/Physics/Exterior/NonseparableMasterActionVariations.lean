import H0mework.Physics.Gauge.NonseparableGravityGaugeSourceAction

/-!
# All variations of the nonseparable gravity--gauge action

This module keeps the Stage-5 claim at the level of one scalar action.  It
proves actual Fréchet derivatives in all four live gravity coordinates and in
the curvature, auxiliary two-form, and constitutive multiplier of each of the
three gauge blocks.

The tetrad derivative is also identified with the sum of the source-relative
gravity covector and the three gauge stress covectors.  Thus gauge stress is
not a separately stored field: it is the contribution produced when the live
tetrad coordinate of the same master action is varied.

Boundary: the gauge curvature remains a finite two-form coordinate, not yet
the curvature of a smooth mother gauge connection.  These are all real field
coordinates present in the current finite action; continuum connection and
matter variations remain later gates.
-/

namespace SaturationMonoid.PhysicsCore.NonseparableMasterActionVariations

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction
open SourceRelativePhysicalStationaryFamily
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open NonseparableGravityGaugeSourceAction

noncomputable section

theorem dynamicStandardModelGaugeAction_tetrad_contDiff
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : StandardModelGaugeConfiguration) :
    ContDiff ℝ ⊤
      (fun tetrad : TetradVector =>
        dynamicStandardModelGaugeAction source tetrad boundary q) :=
  ((dynamicGaugeSectorAction_tetrad_contDiff source
      boundary.strongCouplingSquared q.strong).add
    (dynamicGaugeSectorAction_tetrad_contDiff source
      boundary.weakCouplingSquared q.weak)).add
    (dynamicGaugeSectorAction_tetrad_contDiff source
      boundary.hyperchargeCouplingSquared q.hypercharge)

theorem nonseparableMasterAction_tetrad_contDiff
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    ContDiff ℝ ⊤
      (fun tetrad : TetradVector =>
        nonseparableMasterAction source boundary
          (q.withGravityTetrad tetrad)) := by
  simpa [nonseparableMasterAction, UnifiedConfiguration.withGravityTetrad,
    Configuration.withTetrad] using
    (sourceRelativeMasterAction_tetrad_contDiff source q.gravity).add
      (dynamicStandardModelGaugeAction_tetrad_contDiff
        source boundary q.gauge)

theorem nonseparable_actual_gravity_connection_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun connection : ConnectionJet =>
        nonseparableMasterAction source boundary
          (q.withGravityConnection connection))
      (deltaOmega source q.gravity) q.gravity.connection := by
  simpa [nonseparableMasterAction,
    UnifiedConfiguration.withGravityConnection, Configuration.withConnection]
    using
      (actual_connection_derivative source q.gravity).add_const
        (dynamicStandardModelGaugeAction source q.gravity.tetrad
          boundary q.gauge)

theorem nonseparable_actual_gravity_bivector_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun bivector : BivectorVector =>
        nonseparableMasterAction source boundary
          (q.withGravityBivector bivector))
      (deltaB source q.gravity) q.gravity.bivector := by
  simpa [nonseparableMasterAction,
    UnifiedConfiguration.withGravityBivector, Configuration.withBivector]
    using
      (actual_bivector_derivative source q.gravity).add_const
        (dynamicStandardModelGaugeAction source q.gravity.tetrad
          boundary q.gauge)

theorem nonseparable_actual_gravity_multiplier_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun multiplier : BivectorVector =>
        nonseparableMasterAction source boundary
          (q.withGravityMultiplier multiplier))
      (deltaPhi source q.gravity) q.gravity.multiplier := by
  simpa [nonseparableMasterAction,
    UnifiedConfiguration.withGravityMultiplier, Configuration.withMultiplier]
    using
      (actual_multiplier_derivative source q.gravity).add_const
        (dynamicStandardModelGaugeAction source q.gravity.tetrad
          boundary q.gauge)

theorem nonseparable_actual_gravity_tetrad_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
      (fun tetrad : TetradVector =>
        nonseparableMasterAction source boundary
          (q.withGravityTetrad tetrad))
      (nonseparableDeltaTetrad source boundary q) q.gravity.tetrad :=
  ((nonseparableMasterAction_tetrad_contDiff source boundary q)
    |>.differentiable (by simp)).differentiableAt.hasFDerivAt

/-- The total live-tetrad derivative is exactly gravity plus the three gauge
stress covectors generated by varying the same scalar action. -/
theorem nonseparableDeltaTetrad_eq_gravity_add_gaugeStress
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    nonseparableDeltaTetrad source boundary q =
      deltaE source q.gravity +
        ((dynamicGaugeStressCovector source q.gravity.tetrad
              boundary.strongCouplingSquared q.gauge.strong +
            dynamicGaugeStressCovector source q.gravity.tetrad
              boundary.weakCouplingSquared q.gauge.weak) +
          dynamicGaugeStressCovector source q.gravity.tetrad
            boundary.hyperchargeCouplingSquared q.gauge.hypercharge) := by
  have hsum :=
    (actual_tetrad_derivative source q.gravity).add
      (((actual_dynamicGauge_tetrad_derivative source q.gravity.tetrad
          boundary.strongCouplingSquared q.gauge.strong).add
        (actual_dynamicGauge_tetrad_derivative source q.gravity.tetrad
          boundary.weakCouplingSquared q.gauge.weak)).add
        (actual_dynamicGauge_tetrad_derivative source q.gravity.tetrad
          boundary.hyperchargeCouplingSquared q.gauge.hypercharge))
  have htotal :
      HasFDerivAt
        (fun tetrad : TetradVector =>
          nonseparableMasterAction source boundary
            (q.withGravityTetrad tetrad))
        (deltaE source q.gravity +
          ((dynamicGaugeStressCovector source q.gravity.tetrad
                boundary.strongCouplingSquared q.gauge.strong +
              dynamicGaugeStressCovector source q.gravity.tetrad
                boundary.weakCouplingSquared q.gauge.weak) +
            dynamicGaugeStressCovector source q.gravity.tetrad
              boundary.hyperchargeCouplingSquared q.gauge.hypercharge))
        q.gravity.tetrad := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards [] with tetrad
    rfl
  exact (nonseparable_actual_gravity_tetrad_derivative
    source boundary q).unique htotal

theorem nonseparable_all_four_gravity_variations_from_one_action
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) :
    HasFDerivAt
        (fun connection : ConnectionJet =>
          nonseparableMasterAction source boundary
            (q.withGravityConnection connection))
        (deltaOmega source q.gravity) q.gravity.connection ∧
      HasFDerivAt
        (fun bivector : BivectorVector =>
          nonseparableMasterAction source boundary
            (q.withGravityBivector bivector))
        (deltaB source q.gravity) q.gravity.bivector ∧
      HasFDerivAt
        (fun multiplier : BivectorVector =>
          nonseparableMasterAction source boundary
            (q.withGravityMultiplier multiplier))
        (deltaPhi source q.gravity) q.gravity.multiplier ∧
      HasFDerivAt
        (fun tetrad : TetradVector =>
          nonseparableMasterAction source boundary
            (q.withGravityTetrad tetrad))
        (nonseparableDeltaTetrad source boundary q) q.gravity.tetrad :=
  ⟨nonseparable_actual_gravity_connection_derivative source boundary q,
    nonseparable_actual_gravity_bivector_derivative source boundary q,
    nonseparable_actual_gravity_multiplier_derivative source boundary q,
    nonseparable_actual_gravity_tetrad_derivative source boundary q⟩

/-- The three empirical blocks are labels for selecting a coordinate of the
current finite action; this is not a mother-group unification claim. -/
inductive GaugeBlock where
  | strong
  | weak
  | hypercharge
deriving DecidableEq

def selectedGaugeCoupling
    (boundary : EmpiricalReferenceScaleCouplings) : GaugeBlock → ℝˣ
  | .strong => boundary.strongCouplingSquared
  | .weak => boundary.weakCouplingSquared
  | .hypercharge => boundary.hyperchargeCouplingSquared

def selectedGaugeConfiguration
    (q : StandardModelGaugeConfiguration) :
    GaugeBlock → GaugeSectorConfiguration
  | .strong => q.strong
  | .weak => q.weak
  | .hypercharge => q.hypercharge

def replaceGaugeBlock
    (q : StandardModelGaugeConfiguration) (block : GaugeBlock)
    (sector : GaugeSectorConfiguration) : StandardModelGaugeConfiguration :=
  match block with
  | .strong => { q with strong := sector }
  | .weak => { q with weak := sector }
  | .hypercharge => { q with hypercharge := sector }

def withSelectedGaugeCurvature
    (q : UnifiedConfiguration) (block : GaugeBlock)
    (curvature : DynamicGaugeVector) : UnifiedConfiguration :=
  { q with
    gauge := replaceGaugeBlock q.gauge block
      (withGaugeCurvature (selectedGaugeConfiguration q.gauge block)
        curvature) }

def withSelectedGaugeAuxiliary
    (q : UnifiedConfiguration) (block : GaugeBlock)
    (auxiliary : DynamicGaugeVector) : UnifiedConfiguration :=
  { q with
    gauge := replaceGaugeBlock q.gauge block
      (withGaugeAuxiliary (selectedGaugeConfiguration q.gauge block)
        auxiliary) }

def withSelectedGaugeMultiplier
    (q : UnifiedConfiguration) (block : GaugeBlock)
    (multiplier : DynamicGaugeVector) : UnifiedConfiguration :=
  { q with
    gauge := replaceGaugeBlock q.gauge block
      ((selectedGaugeConfiguration q.gauge block).withConstitutiveMultiplier
        multiplier) }

private theorem dynamicStandardModel_selected_curvature_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun curvature : DynamicGaugeVector =>
        dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
          (replaceGaugeBlock q.gauge block
            (withGaugeCurvature
              (selectedGaugeConfiguration q.gauge block) curvature)))
      (dynamicGaugeDeltaCurvature source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).curvature := by
  cases block with
  | strong =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        ((actual_dynamicGauge_curvature_derivative source q.gravity.tetrad
          boundary.strongCouplingSquared q.gauge.strong).add_const
            (dynamicGaugeSectorAction source q.gravity.tetrad
              boundary.weakCouplingSquared q.gauge.weak)).add_const
          (dynamicGaugeSectorAction source q.gravity.tetrad
            boundary.hyperchargeCouplingSquared q.gauge.hypercharge)
  | weak =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        ((actual_dynamicGauge_curvature_derivative source q.gravity.tetrad
          boundary.weakCouplingSquared q.gauge.weak).const_add
            (dynamicGaugeSectorAction source q.gravity.tetrad
              boundary.strongCouplingSquared q.gauge.strong)).add_const
          (dynamicGaugeSectorAction source q.gravity.tetrad
            boundary.hyperchargeCouplingSquared q.gauge.hypercharge)
  | hypercharge =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        (actual_dynamicGauge_curvature_derivative source q.gravity.tetrad
          boundary.hyperchargeCouplingSquared q.gauge.hypercharge).const_add
            (dynamicGaugeSectorAction source q.gravity.tetrad
                boundary.strongCouplingSquared q.gauge.strong +
              dynamicGaugeSectorAction source q.gravity.tetrad
                boundary.weakCouplingSquared q.gauge.weak)

private theorem dynamicStandardModel_selected_auxiliary_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun auxiliary : DynamicGaugeVector =>
        dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
          (replaceGaugeBlock q.gauge block
            (withGaugeAuxiliary
              (selectedGaugeConfiguration q.gauge block) auxiliary)))
      (dynamicGaugeDeltaAuxiliary source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).auxiliary := by
  cases block with
  | strong =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        ((actual_dynamicGauge_auxiliary_derivative source q.gravity.tetrad
          boundary.strongCouplingSquared q.gauge.strong).add_const
            (dynamicGaugeSectorAction source q.gravity.tetrad
              boundary.weakCouplingSquared q.gauge.weak)).add_const
          (dynamicGaugeSectorAction source q.gravity.tetrad
            boundary.hyperchargeCouplingSquared q.gauge.hypercharge)
  | weak =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        ((actual_dynamicGauge_auxiliary_derivative source q.gravity.tetrad
          boundary.weakCouplingSquared q.gauge.weak).const_add
            (dynamicGaugeSectorAction source q.gravity.tetrad
              boundary.strongCouplingSquared q.gauge.strong)).add_const
          (dynamicGaugeSectorAction source q.gravity.tetrad
            boundary.hyperchargeCouplingSquared q.gauge.hypercharge)
  | hypercharge =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        (actual_dynamicGauge_auxiliary_derivative source q.gravity.tetrad
          boundary.hyperchargeCouplingSquared q.gauge.hypercharge).const_add
            (dynamicGaugeSectorAction source q.gravity.tetrad
                boundary.strongCouplingSquared q.gauge.strong +
              dynamicGaugeSectorAction source q.gravity.tetrad
                boundary.weakCouplingSquared q.gauge.weak)

private theorem dynamicStandardModel_selected_multiplier_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun multiplier : DynamicGaugeVector =>
        dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
          (replaceGaugeBlock q.gauge block
            ((selectedGaugeConfiguration q.gauge block)
              |>.withConstitutiveMultiplier multiplier)))
      (dynamicGaugeDeltaMultiplier source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier := by
  cases block with
  | strong =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        ((actual_dynamicGauge_multiplier_derivative source q.gravity.tetrad
          boundary.strongCouplingSquared q.gauge.strong).add_const
            (dynamicGaugeSectorAction source q.gravity.tetrad
              boundary.weakCouplingSquared q.gauge.weak)).add_const
          (dynamicGaugeSectorAction source q.gravity.tetrad
            boundary.hyperchargeCouplingSquared q.gauge.hypercharge)
  | weak =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        ((actual_dynamicGauge_multiplier_derivative source q.gravity.tetrad
          boundary.weakCouplingSquared q.gauge.weak).const_add
            (dynamicGaugeSectorAction source q.gravity.tetrad
              boundary.strongCouplingSquared q.gauge.strong)).add_const
          (dynamicGaugeSectorAction source q.gravity.tetrad
            boundary.hyperchargeCouplingSquared q.gauge.hypercharge)
  | hypercharge =>
      simpa only [selectedGaugeConfiguration, selectedGaugeCoupling,
        replaceGaugeBlock, dynamicStandardModelGaugeAction] using
        (actual_dynamicGauge_multiplier_derivative source q.gravity.tetrad
          boundary.hyperchargeCouplingSquared q.gauge.hypercharge).const_add
            (dynamicGaugeSectorAction source q.gravity.tetrad
                boundary.strongCouplingSquared q.gauge.strong +
              dynamicGaugeSectorAction source q.gravity.tetrad
                boundary.weakCouplingSquared q.gauge.weak)

theorem nonseparable_actual_selectedGauge_curvature_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun curvature : DynamicGaugeVector =>
        nonseparableMasterAction source boundary
          (withSelectedGaugeCurvature q block curvature))
      (dynamicGaugeDeltaCurvature source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).curvature := by
  simpa [nonseparableMasterAction, withSelectedGaugeCurvature] using
    (dynamicStandardModel_selected_curvature_derivative
      source boundary q block).const_add
        (sourceRelativeMasterAction source q.gravity)

theorem nonseparable_actual_selectedGauge_auxiliary_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun auxiliary : DynamicGaugeVector =>
        nonseparableMasterAction source boundary
          (withSelectedGaugeAuxiliary q block auxiliary))
      (dynamicGaugeDeltaAuxiliary source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).auxiliary := by
  simpa [nonseparableMasterAction, withSelectedGaugeAuxiliary] using
    (dynamicStandardModel_selected_auxiliary_derivative
      source boundary q block).const_add
        (sourceRelativeMasterAction source q.gravity)

theorem nonseparable_actual_selectedGauge_multiplier_derivative
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
      (fun multiplier : DynamicGaugeVector =>
        nonseparableMasterAction source boundary
          (withSelectedGaugeMultiplier q block multiplier))
      (dynamicGaugeDeltaMultiplier source q.gravity.tetrad
        (selectedGaugeCoupling boundary block)
        (selectedGaugeConfiguration q.gauge block))
      (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier := by
  simpa [nonseparableMasterAction, withSelectedGaugeMultiplier] using
    (dynamicStandardModel_selected_multiplier_derivative
      source boundary q block).const_add
        (sourceRelativeMasterAction source q.gravity)

/-- For every one of the three blocks, every live finite gauge coordinate is
an actual derivative of the same nonseparable master action. -/
theorem nonseparable_all_selectedGauge_variations_from_one_action
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (q : UnifiedConfiguration) (block : GaugeBlock) :
    HasFDerivAt
        (fun curvature : DynamicGaugeVector =>
          nonseparableMasterAction source boundary
            (withSelectedGaugeCurvature q block curvature))
        (dynamicGaugeDeltaCurvature source q.gravity.tetrad
          (selectedGaugeCoupling boundary block)
          (selectedGaugeConfiguration q.gauge block))
        (selectedGaugeConfiguration q.gauge block).curvature ∧
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector =>
          nonseparableMasterAction source boundary
            (withSelectedGaugeAuxiliary q block auxiliary))
        (dynamicGaugeDeltaAuxiliary source q.gravity.tetrad
          (selectedGaugeCoupling boundary block)
          (selectedGaugeConfiguration q.gauge block))
        (selectedGaugeConfiguration q.gauge block).auxiliary ∧
      HasFDerivAt
        (fun multiplier : DynamicGaugeVector =>
          nonseparableMasterAction source boundary
            (withSelectedGaugeMultiplier q block multiplier))
        (dynamicGaugeDeltaMultiplier source q.gravity.tetrad
          (selectedGaugeCoupling boundary block)
          (selectedGaugeConfiguration q.gauge block))
        (selectedGaugeConfiguration q.gauge block).constitutiveMultiplier :=
  ⟨nonseparable_actual_selectedGauge_curvature_derivative
      source boundary q block,
    nonseparable_actual_selectedGauge_auxiliary_derivative
      source boundary q block,
    nonseparable_actual_selectedGauge_multiplier_derivative
      source boundary q block⟩

end
end SaturationMonoid.PhysicsCore.NonseparableMasterActionVariations
