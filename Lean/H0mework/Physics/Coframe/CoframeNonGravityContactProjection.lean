import H0mework.Physics.Coframe.CoframeSectorStress

/-!
# Stage-9 coframe non-gravity contact projection

The gauge, scalar, and matter coframe sectors do not read the three gravity
slots of a continuum point field.  This module exposes the corresponding
projection once, as a low-level proof device:

```text
gravity curvature, auxiliary, multiplier ↦ 0
all non-gravity fields                         ↦ unchanged.
```

The projection is neither a physical quotient nor a producer.  It carries no
equation, residual, response, or stationarity certificate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeNonGravityContactProjection

open ProofFreeRicherAnholonomicSource
open StageNineCoframeSectorStress
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction

noncomputable section

set_option autoImplicit false

/-- Forget exactly the gravity slots that the non-gravity coframe action does
not consume. -/
def coframeNonGravityContactProjection
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

@[simp] theorem coframeNonGravityContactProjection_coframe
    (field : StageNineContinuumPointField) :
    (coframeNonGravityContactProjection field).coframe = field.coframe :=
  rfl

@[simp] theorem coframeGaugeSectorStressCovector_projection
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    coframeGaugeSectorStressCovector source
        (coframeNonGravityContactProjection field) =
      coframeGaugeSectorStressCovector source field :=
  rfl

@[simp] theorem coframeScalarSectorStressCovector_projection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    coframeScalarSectorStressCovector source point
        (coframeNonGravityContactProjection field) =
      coframeScalarSectorStressCovector source point field :=
  rfl

@[simp] theorem coframeMatterSectorStressCovector_projection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    coframeMatterSectorStressCovector source point
        (coframeNonGravityContactProjection field) =
      coframeMatterSectorStressCovector source point field :=
  rfl

@[simp] theorem coframeGaugeSectorLocalDensity_projection
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity source
        (coframeNonGravityContactProjection field) candidate =
      coframeGaugeSectorLocalDensity source field candidate :=
  rfl

@[simp] theorem coframeScalarSectorLocalDensity_projection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (candidate : LorentzianCoframe) :
    coframeScalarSectorLocalDensity source point
        (coframeNonGravityContactProjection field) candidate =
      coframeScalarSectorLocalDensity source point field candidate :=
  rfl

@[simp] theorem coframeMatterSectorLocalDensity_projection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity source point
        (coframeNonGravityContactProjection field) candidate =
      coframeMatterSectorLocalDensity source point field candidate :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeNonGravityContactProjection
