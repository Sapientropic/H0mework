import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Fields
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Normed
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Frame

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open ContinuousLinearMap
open CPS1ElectronicSource
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

abbrev ActualIndex (state : CPS1ElectronicSource.State frame) :=
  FiniteNormed.Index (𝕜 := ℂ) (rawField state)

def currentBasis (state : CPS1ElectronicSource.State frame) : ActualIndex state → SpinSpace :=
  FiniteNormed.field (𝕜 := ℂ) (rawField state)

/-- The current source coefficients stay fixed while each actual centre moves. -/
def fieldCurve (state : CPS1ElectronicSource.State frame) (time : ℝ) (index : ActualIndex state) : SpinSpace :=
  ∑ source, FiniteNormed.coefficients (𝕜 := ℂ) (rawField state) source index • rawCurve state time source

def fieldRate (state : CPS1ElectronicSource.State frame) (time : ℝ) (index : ActualIndex state) : SpinSpace :=
  ∑ source, FiniteNormed.coefficients (𝕜 := ℂ) (rawField state) source index • rawRate state time source

theorem field_curve_initial (state : CPS1ElectronicSource.State frame) : fieldCurve state 0 = currentBasis state := by
  funext index
  unfold fieldCurve currentBasis
  rw [raw_curve_initial]
  exact (FiniteNormed.field_synthesis (rawField state) index).symm

theorem field_curve_derivative (state : CPS1ElectronicSource.State frame) (index : ActualIndex state) (time : ℝ) :
    HasDerivAt (fun t => fieldCurve state t index) (fieldRate state time index) time :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun source _ =>
    (raw_curve_derivative state source time).const_smul
      (FiniteNormed.coefficients (𝕜 := ℂ) (rawField state) source index))

def frameCurve (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    EuclideanSpace ℂ (ActualIndex state) →L[ℂ] SpinSpace := fieldFrame (fieldCurve state time)

def frameRate (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    EuclideanSpace ℂ (ActualIndex state) →L[ℂ] SpinSpace := fieldFrame (fieldRate state time)

theorem frame_curve_initial (state : CPS1ElectronicSource.State frame) :
    frameCurve state 0 = fieldFrame (currentBasis state) := by rw [frameCurve,field_curve_initial]

theorem frame_curve_derivative (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    HasDerivAt (frameCurve state) (frameRate state time) time :=
  field_frame_equation (fieldCurve state) (fieldRate state time) time (fun index =>
    field_curve_derivative state index time)

theorem current_frame_unit (state : CPS1ElectronicSource.State frame) :
    IsUnit (LAlanineSpatialProjection.gram (frameCurve state 0)) := by
  rw [frame_curve_initial]
  exact orthonormal_frame_unit _ (FiniteNormed.field_orthonormal (rawField state))

def currentProjection (state : CPS1ElectronicSource.State frame) : SpinSpace →L[ℂ] SpinSpace :=
  LAlanineSpatialProjection.projection (frameCurve state 0) (current_frame_unit state)

def currentProjectionRate (state : CPS1ElectronicSource.State frame) : SpinSpace →L[ℂ] SpinSpace :=
  LAlanineSpatialProjection.projectionRate (frameCurve state 0) (frameRate state 0) (current_frame_unit state)

def spatialHamiltonian (state : CPS1ElectronicSource.State frame) : SpinSpace →L[ℂ] SpinSpace :=
  LAlanineSpatialProjection.hamiltonian (frameCurve state 0) (frameRate state 0) (current_frame_unit state)

def verticalResponse (state : CPS1ElectronicSource.State frame) :
    EuclideanSpace ℂ (ActualIndex state) →L[ℂ] EuclideanSpace ℂ (ActualIndex state) :=
  LAlanineSpatialProjection.verticalResponse (frameCurve state 0) (frameRate state 0) (current_frame_unit state)

theorem current_projection_selfadjoint (state : CPS1ElectronicSource.State frame) :
    (currentProjection state).adjoint = currentProjection state :=
  LAlanineSpatialProjection.projection_adjoint _ _

theorem current_projection_idempotent (state : CPS1ElectronicSource.State frame) :
    currentProjection state ∘L currentProjection state = currentProjection state :=
  LAlanineSpatialProjection.projection_idempotent _ _

theorem spatial_hamiltonian_selfadjoint (state : CPS1ElectronicSource.State frame) :
    (spatialHamiltonian state).adjoint = spatialHamiltonian state :=
  LAlanineSpatialProjection.hamiltonian_adjoint _ _ _

theorem source_projection_derivative (state : CPS1ElectronicSource.State frame) :
    HasDerivAt (fun time => LAlanineSpatialProjection.totalProjection (frameCurve state time))
      (currentProjectionRate state) 0 :=
  LAlanineSpatialProjection.total_projection_curve_derivative _ _ _
    (frame_curve_derivative state 0) (current_frame_unit state)

theorem source_projection_controlled (state : CPS1ElectronicSource.State frame) :
    HasDerivAt (fun time => LAlanineSpatialProjection.totalProjection (frameCurve state time))
      ((-Complex.I) • LAlanineSpatialProjection.commutator (spatialHamiltonian state) (currentProjection state)) 0 := by
  have source := LAlanineSpatialProjection.spatial_projection_controlled_equation _ _ _
    (frame_curve_derivative state 0) (current_frame_unit state)
  unfold spatialHamiltonian currentProjection
  rw [← LAlanineSpatialProjection.total_projection_source (frameCurve state 0) (current_frame_unit state)]
  exact source

theorem source_frame_lift (state : CPS1ElectronicSource.State frame) :
    Complex.I • frameRate state 0 = spatialHamiltonian state ∘L frameCurve state 0 +
      frameCurve state 0 ∘L (Complex.I • verticalResponse state) :=
  LAlanineSpatialProjection.full_frame_lift _ _ _

theorem source_vertical_gram_rate (state : CPS1ElectronicSource.State frame) :
    (verticalResponse state).adjoint ∘L LAlanineSpatialProjection.gram (frameCurve state 0) +
      LAlanineSpatialProjection.gram (frameCurve state 0) ∘L verticalResponse state =
      LAlanineSpatialProjection.gramRate (frameCurve state 0) (frameRate state 0) :=
  LAlanineSpatialProjection.vertical_gram_rate _ _ _

end
end CPS1MolecularFrame
