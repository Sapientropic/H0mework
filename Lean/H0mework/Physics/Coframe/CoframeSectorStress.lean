import H0mework.Physics.Coframe.CoframeLocalDifferentiability

/-!
# S9-C3f4: actual coframe stress split by action sector

The total coframe Euler covector is not a matter stress tensor.  This module
splits it into gravity, gauge, scalar, and exterior-matter contributions by
first retaining the complete densitized term `abs(det e) * L_sector` and only
then taking the actual Fréchet derivative with respect to the coframe.

That order is essential: the source-generated scalar potential and the
Yukawa interaction have no inner coframe derivative, but they still carry a
real volume-stress contribution.  The matter sector follows current action
ownership and therefore contains the continuum Dirac plus Yukawa density.

No stress, derivative, regularity, equation, balance, or nonzero witness is
accepted as data.  This module proves only the exact off-shell decomposition;
the pointwise on-shell balance remains a downstream consumer.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeSectorStress

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

/-! ## Complete densitized sector functions -/

def coframeGravitySectorLocalDensity
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedVolumeDensity (withCoframe field coframe) *
    (generatedGravitySimplicityDensity (withCoframe field coframe) +
      generatedGravityBFDensity (withCoframe field coframe))

def coframeGaugeSectorLocalDensity
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  let boundary := sourceGeneratedUnifiedCouplings source
  let spacetimeHodge := coframeGaugeSpacetimeHodgeLinear coframe
  generatedVolumeDensity (withCoframe field coframe) *
    (generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 3) _ _)
        coframe spacetimeHodge
        ((boundary.strongCouplingSquared : ℝ) • spacetimeHodge)
        (fun pair => (field.gaugeCurvature pair).1)
        (fun pair => (field.gaugeAuxiliary pair).1) +
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 2) _ _)
        coframe spacetimeHodge
        ((boundary.weakCouplingSquared : ℝ) • spacetimeHodge)
        (fun pair => (field.gaugeCurvature pair).2.1)
        (fun pair => (field.gaugeAuxiliary pair).2.1) +
      generatedGaugeSectorBFDensity hyperchargeLiePairing
        coframe spacetimeHodge
        ((boundary.hyperchargeCouplingSquared : ℝ) • spacetimeHodge)
        (fun pair => (field.gaugeCurvature pair).2.2)
        (fun pair => (field.gaugeAuxiliary pair).2.2))

def coframeScalarSectorLocalDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedVolumeDensity (withCoframe field coframe) *
    (generatedScalarKineticDensity source 0 point
        (withCoframe field coframe) -
      generatedScalarPotential source 0 point field.scalar)

/-- Current action ownership keeps the Dirac kinetic and Yukawa interaction
inside one exterior-matter sector. -/
def coframeMatterSectorLocalDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedVolumeDensity (withCoframe field coframe) *
    generatedContinuumMatterDensity source 0 point
      (withCoframe field coframe)

theorem coframeLocalDensity_eq_sector_sum
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) :
    coframeLocalDensity source point field coframe =
      coframeGravitySectorLocalDensity field coframe +
        coframeGaugeSectorLocalDensity source field coframe +
        coframeScalarSectorLocalDensity source point field coframe +
        coframeMatterSectorLocalDensity source point field coframe := by
  unfold coframeLocalDensity generatedUnifiedLocalDensityAtBoundary
    generatedUnifiedLocalDensityCoreAtBoundary
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
    coframeGravitySectorLocalDensity coframeGaugeSectorLocalDensity
    coframeScalarSectorLocalDensity coframeMatterSectorLocalDensity
  dsimp only
  simp only [withCoframe]
  ring

/-! ## Sector differentiability on the actual nondegenerate branch -/

theorem coframeGravitySectorLocalDensity_contDiffAt
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (coframeGravitySectorLocalDensity field)
      field.coframe := by
  unfold coframeGravitySectorLocalDensity
  exact (generatedVolumeDensity_withCoframe_contDiffAt field nondegenerate).mul
    ((generatedGravitySimplicityDensity_withCoframe_contDiff field).contDiffAt.add
      (generatedGravityBFDensity_withCoframe_contDiffAt field nondegenerate))

theorem coframeGaugeSectorLocalDensity_contDiffAt
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (coframeGaugeSectorLocalDensity source field)
      field.coframe := by
  let boundary := sourceGeneratedUnifiedCouplings source
  unfold coframeGaugeSectorLocalDensity
  exact (generatedVolumeDensity_withCoframe_contDiffAt field nondegenerate).mul
    (((generatedStrongGaugeSector_withCoframe_contDiffAt
        boundary field nondegenerate).add
      (generatedWeakGaugeSector_withCoframe_contDiffAt
        boundary field nondegenerate)).add
      (generatedHyperchargeGaugeSector_withCoframe_contDiffAt
        boundary field nondegenerate))

theorem coframeScalarSectorLocalDensity_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (coframeScalarSectorLocalDensity source point field)
      field.coframe := by
  unfold coframeScalarSectorLocalDensity
  exact (generatedVolumeDensity_withCoframe_contDiffAt field nondegenerate).mul
    ((generatedScalarKineticDensity_withCoframe_contDiffAt
      source point field nondegenerate).sub contDiffAt_const)

theorem coframeMatterSectorLocalDensity_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (coframeMatterSectorLocalDensity source point field)
      field.coframe := by
  unfold coframeMatterSectorLocalDensity
  exact (generatedVolumeDensity_withCoframe_contDiffAt field nondegenerate).mul
    (generatedContinuumMatterDensity_withCoframe_contDiffAt
      source point field nondegenerate)

/-! ## Actual Fréchet sector stress covectors -/

def coframeGravitySectorStressCovector
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (coframeGravitySectorLocalDensity field) field.coframe

def coframeGaugeSectorStressCovector
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (coframeGaugeSectorLocalDensity source field) field.coframe

def coframeScalarSectorStressCovector
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (coframeScalarSectorLocalDensity source point field)
    field.coframe

def coframeMatterSectorStressCovector
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (coframeMatterSectorLocalDensity source point field)
    field.coframe

theorem coframeGravitySectorLocalDensity_hasFDerivAt
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (coframeGravitySectorLocalDensity field)
      (coframeGravitySectorStressCovector field) field.coframe :=
  ((coframeGravitySectorLocalDensity_contDiffAt field nondegenerate).differentiableAt
    (by simp)).hasFDerivAt

theorem coframeGaugeSectorLocalDensity_hasFDerivAt
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (coframeGaugeSectorLocalDensity source field)
      (coframeGaugeSectorStressCovector source field) field.coframe :=
  ((coframeGaugeSectorLocalDensity_contDiffAt source field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

theorem coframeScalarSectorLocalDensity_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (coframeScalarSectorLocalDensity source point field)
      (coframeScalarSectorStressCovector source point field) field.coframe :=
  ((coframeScalarSectorLocalDensity_contDiffAt source point field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

theorem coframeMatterSectorLocalDensity_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (coframeMatterSectorLocalDensity source point field)
      (coframeMatterSectorStressCovector source point field) field.coframe :=
  ((coframeMatterSectorLocalDensity_contDiffAt source point field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

/-- Exact off-shell decomposition of the total coframe Euler covector into
the four action-owned sector derivatives. -/
theorem coframeLocalStressCovector_eq_sector_sum
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    coframeLocalStressCovector source point field =
      coframeGravitySectorStressCovector field +
        coframeGaugeSectorStressCovector source field +
        coframeScalarSectorStressCovector source point field +
        coframeMatterSectorStressCovector source point field := by
  have sectorDerivative :=
    (((coframeGravitySectorLocalDensity_hasFDerivAt field nondegenerate).add
      (coframeGaugeSectorLocalDensity_hasFDerivAt
        source field nondegenerate)).add
      (coframeScalarSectorLocalDensity_hasFDerivAt
        source point field nondegenerate)).add
      (coframeMatterSectorLocalDensity_hasFDerivAt
        source point field nondegenerate)
  have totalDerivative : HasFDerivAt
      (coframeLocalDensity source point field)
      (coframeGravitySectorStressCovector field +
        coframeGaugeSectorStressCovector source field +
        coframeScalarSectorStressCovector source point field +
        coframeMatterSectorStressCovector source point field)
      field.coframe := by
    apply sectorDerivative.congr_of_eventuallyEq
    filter_upwards [] with candidate
    exact coframeLocalDensity_eq_sector_sum source point field candidate
  exact (coframeLocalDensity_hasFDerivAt
    source point field nondegenerate).unique totalDerivative

end

end SaturationMonoid.PhysicsCore.StageNineCoframeSectorStress
