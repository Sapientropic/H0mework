import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceBoundarySequence
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationCausalFieldResponse

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumSourcePreparedResponse
open PreparationVacuumSourcePreparedState PreparationVacuumCausalFieldResponse
open GaussCoreHilbert GaussComposite GaussComposite.SourceGraph SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open CanonicalPhysicalSpatial CanonicalPhysicalLaplace
open CanonicalGradedSpatialSource PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open FullYSourceCutoffVolterra SourceFamilyOperator SourceFiniteUnitary
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates
open scoped Topology InnerProductSpace

theorem checked_same_generated_preparation_response (epsilon : ℝ) (precision : 0<epsilon) :
    let generated:=sourcePreparation epsilon precision
    let u:=zeroLocalizedProfile actualNativeLocalizer generated.point.val
    ‖prepared u‖=1 ∧
    ‖sourceOperator generated.point-(sourceEnergy : ℂ) • generated.point.val‖<epsilon ∧
    prepared u=sourceCreated (GaussHalfDensity.halfDensityEquiv 0 generated.point.val.val) ∧
    (∃ h : prepared u∈GaussRadialDomain.closedY.domain,
      ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared u,h⟩-cutoff n (prepared u)‖ ≤
        (915/916 : ℝ)^(n+1)*916*GaussYukawaCoefficient.bound) ∧
    ∀ (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p k ell : PhysicalMomentum) (t s : ℝ)
      (left right : Bool) (lc ls rc rs : Fin 2),
      ‖preparedCausal cut f g phi psi p k ell t s left right lc ls rc rs u u‖ ≤
        legBound^2*kernelBound cut f g phi psi p k ell t s*‖u‖*‖u‖ ∧
      ‖preparedContact cut f g (contactLocalizer phi psi) p k ell t left right lc ls rc rs u u‖ ≤
        legBound^2*contactTimeBound cut f g (contactLocalizer phi psi) p t*‖u‖*‖u‖ ∧
      ∀ (frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T),
        ‖SourceGraph.response (responseTail cut f g phi psi p k ell s frequency damping T positive future)
          left right lc ls rc rs u u‖ ≤
          legBound^2*(dampingTail damping T*fieldScale cut f g phi psi p k ell s)*‖u‖*‖u‖ := by
  intro generated u
  refine ⟨generated.unit,generated.near,generated.created,
    ⟨generated.yukawaDomain,generated.yukawaCutoff⟩,?_⟩
  intro cut f g phi psi p k ell t s left right lc ls rc rs
  exact ⟨preparedCausal_bound cut f g phi psi p k ell t s left right lc ls rc rs u u,
    preparedContact_bound cut f g (contactLocalizer phi psi) p k ell t left right lc ls rc rs u u,
    fun frequency damping T positive future=>prepared_response_tail cut f g phi psi p k ell s frequency damping T
      positive future left right lc ls rc rs u u⟩

structure CausalState (epsilon : ℝ) extends SourcePreparation epsilon where
  responses :
    let u:=zeroLocalizedProfile actualNativeLocalizer point.val
    ∀ (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p k ell : PhysicalMomentum) (t s : ℝ)
      (left right : Bool) (lc ls rc rs : Fin 2),
      ‖preparedCausal cut f g phi psi p k ell t s left right lc ls rc rs u u‖ ≤
        legBound^2*kernelBound cut f g phi psi p k ell t s*‖u‖*‖u‖ ∧
      ‖preparedContact cut f g (contactLocalizer phi psi) p k ell t left right lc ls rc rs u u‖ ≤
        legBound^2*contactTimeBound cut f g (contactLocalizer phi psi) p t*‖u‖*‖u‖ ∧
      ∀ (frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T),
        ‖SourceGraph.response (responseTail cut f g phi psi p k ell s frequency damping T positive future)
          left right lc ls rc rs u u‖ ≤
          legBound^2*(dampingTail damping T*fieldScale cut f g phi psi p k ell s)*‖u‖*‖u‖

def sourceCausalState (epsilon : ℝ) (precision : 0<epsilon) : CausalState epsilon where
  toSourcePreparation:=sourcePreparation epsilon precision
  responses:=(checked_same_generated_preparation_response epsilon precision).2.2.2.2

theorem sourceCausalState_same_preparation (epsilon : ℝ) (precision : 0<epsilon) :
    (sourceCausalState epsilon precision).toSourcePreparation=sourcePreparation epsilon precision := rfl

end LowEnergy.PreparationVacuumSourcePreparedResponse
