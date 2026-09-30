import H0mework.NavierStokes.Fourier.CoarseFilterCore

/-!
# The quadratic coarse-correlation residual

The concrete coarse filter is applied to the full quadratic velocity tensor.
The keep is the quadratic tensor formed after filtering the velocity.  Their
difference is the source-generated subscale stress.

This is the exact residual-transport split

`filtered correlation = resolved correlation + subscale trace`.

It is an infinite-carrier T0/T1 accounting theorem.  It is not yet the
divergence of the stress inside a Navier--Stokes generator, a local energy
identity, a nonzero flux theorem, or a regularity saving.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicCoarseCorrelationResidual

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore

noncomputable section

abbrev Velocity := PhysicalSpace

abbrev VelocityField := PhysicalSpace → Velocity

/--
The two `Fin 3` indices are physical tensor coordinates.  The spatial
function carrier is still the full infinite function space.
-/
abbrev Stress := Coordinate → Coordinate → ℝ

abbrev StressField := PhysicalSpace → Stress

/-- The pointwise quadratic velocity correlation `u ⊗ u`. -/
def velocityTensor (u : VelocityField) : StressField :=
  fun x i j => u x i * u x j

theorem velocityTensor_continuous (u : VelocityField)
    (hu : Continuous u) :
    Continuous (velocityTensor u) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun x => u x i * u x j)
  exact ((EuclideanSpace.proj i).continuous.comp hu).mul
    ((EuclideanSpace.proj j).continuous.comp hu)

theorem velocityTensor_contDiff (u : VelocityField) {n : ℕ∞}
    (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (velocityTensor u) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  exact ((contDiff_piLp_apply 2).comp hu).mul
    ((contDiff_piLp_apply 2).comp hu)

/-- The velocity after the source-generated coarse update. -/
noncomputable def filteredVelocity (s : CoarseScale)
    (u : VelocityField) : VelocityField :=
  coarseFilter s u

/-- The old quadratic residual transported through the coarse filter. -/
noncomputable def filteredVelocityTensor (s : CoarseScale)
    (u : VelocityField) : StressField :=
  coarseFilter s (velocityTensor u)

/-- The quadratic keep reconstructed from the filtered velocity. -/
noncomputable def resolvedVelocityTensor (s : CoarseScale)
    (u : VelocityField) : StressField :=
  velocityTensor (filteredVelocity s u)

/-- The uniquely forced complement of the resolved quadratic keep. -/
noncomputable def subscaleStress (s : CoarseScale)
    (u : VelocityField) : StressField :=
  filteredVelocityTensor s u - resolvedVelocityTensor s u

theorem filteredVelocity_contDiff
    (s : CoarseScale) (u : VelocityField)
    (hu : LocallyIntegrable u volume) :
    ContDiff ℝ (⊤ : ℕ∞) (filteredVelocity s u) :=
  coarseFilter_contDiff s u hu

theorem filteredVelocityTensor_contDiff
    (s : CoarseScale) (u : VelocityField)
    (huu : LocallyIntegrable (velocityTensor u) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (filteredVelocityTensor s u) :=
  coarseFilter_contDiff s (velocityTensor u) huu

theorem resolvedVelocityTensor_contDiff
    (s : CoarseScale) (u : VelocityField)
    (hu : LocallyIntegrable u volume) :
    ContDiff ℝ (⊤ : ℕ∞) (resolvedVelocityTensor s u) :=
  velocityTensor_contDiff _
    (filteredVelocity_contDiff s u hu)

theorem subscaleStress_contDiff
    (s : CoarseScale) (u : VelocityField)
    (hu : LocallyIntegrable u volume)
    (huu : LocallyIntegrable (velocityTensor u) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (subscaleStress s u) :=
  (filteredVelocityTensor_contDiff s u huu).sub
    (resolvedVelocityTensor_contDiff s u hu)

theorem filteredVelocityTensor_locallyIntegrable
    (s : CoarseScale) (u : VelocityField)
    (huu : LocallyIntegrable (velocityTensor u) volume) :
    LocallyIntegrable (filteredVelocityTensor s u) volume :=
  (coarseFilter_contDiff s (velocityTensor u) huu).continuous.locallyIntegrable

theorem resolvedVelocityTensor_locallyIntegrable
    (s : CoarseScale) (u : VelocityField)
    (hu : LocallyIntegrable u volume) :
    LocallyIntegrable (resolvedVelocityTensor s u) volume := by
  apply Continuous.locallyIntegrable
  exact velocityTensor_continuous _
    (coarseFilter_contDiff s u hu).continuous

/-- The actual one-scale quadratic residual transport law. -/
theorem filteredVelocityTensor_eq_resolved_add_subscaleStress
    (s : CoarseScale) (u : VelocityField) :
    filteredVelocityTensor s u =
      resolvedVelocityTensor s u + subscaleStress s u := by
  simp only [subscaleStress]
  abel

/--
Conservation forces the trace uniquely; it is not an independently supplied
field of a certificate.
-/
theorem subscaleStress_unique (s : CoarseScale) (u : VelocityField)
    (trace : StressField) :
    filteredVelocityTensor s u = resolvedVelocityTensor s u + trace ↔
      trace = subscaleStress s u := by
  constructor
  · intro h
    funext x i j
    have hij := congrFun (congrFun (congrFun h x) i) j
    dsimp [subscaleStress] at hij ⊢
    linarith
  · rintro rfl
    exact filteredVelocityTensor_eq_resolved_add_subscaleStress s u

theorem velocityTensor_latticePeriodic (u : VelocityField)
    (hu : LatticePeriodic u) :
    LatticePeriodic (velocityTensor u) := by
  intro z x
  exact
    congrArg (fun v : Velocity => fun i j => v i * v j) (hu z x)

theorem filteredVelocity_latticePeriodic (s : CoarseScale)
    (u : VelocityField) (hu : LatticePeriodic u) :
    LatticePeriodic (filteredVelocity s u) :=
  coarseFilter_latticePeriodic s u hu

theorem filteredVelocityTensor_latticePeriodic (s : CoarseScale)
    (u : VelocityField) (hu : LatticePeriodic u) :
    LatticePeriodic (filteredVelocityTensor s u) :=
  coarseFilter_latticePeriodic s (velocityTensor u)
    (velocityTensor_latticePeriodic u hu)

theorem resolvedVelocityTensor_latticePeriodic (s : CoarseScale)
    (u : VelocityField) (hu : LatticePeriodic u) :
    LatticePeriodic (resolvedVelocityTensor s u) :=
  velocityTensor_latticePeriodic (filteredVelocity s u)
    (filteredVelocity_latticePeriodic s u hu)

/--
The same source event preserves periodicity of the generated trace; this is
proved on the trace carrier rather than stored as a faithfulness premise.
-/
theorem subscaleStress_latticePeriodic (s : CoarseScale)
    (u : VelocityField) (hu : LatticePeriodic u) :
    LatticePeriodic (subscaleStress s u) := by
  intro z x
  rw [subscaleStress, Pi.sub_apply, Pi.sub_apply,
    filteredVelocityTensor_latticePeriodic s u hu z x,
    resolvedVelocityTensor_latticePeriodic s u hu z x]

theorem filteredVelocity_const (s : CoarseScale) (c : Velocity) :
    filteredVelocity s (fun _ => c) = fun _ => c :=
  coarseFilter_const s c

/--
Constant flow is the required silent control: no theorem in this module can
upgrade the exact stress ledger to unconditional nonzero flux.
-/
theorem subscaleStress_const (s : CoarseScale) (c : Velocity) :
    subscaleStress s (fun _ => c) = 0 := by
  rw [subscaleStress, filteredVelocityTensor, resolvedVelocityTensor,
    filteredVelocity_const]
  have hv : velocityTensor (fun _ : PhysicalSpace => c) =
      fun _ => (fun i j => c i * c j) := by
    rfl
  rw [hv, coarseFilter_const]
  simp

end

end ThreeDimensionalPeriodicCoarseCorrelationResidual
end NavierStokes
end SaturationMonoid
