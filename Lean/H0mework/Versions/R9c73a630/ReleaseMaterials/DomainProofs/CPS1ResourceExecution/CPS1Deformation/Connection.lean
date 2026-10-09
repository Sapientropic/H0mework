import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Frame

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource ContinuousLinearMap
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

def connectionAt (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) :
    CoefficientSpace source →L[ℂ] CoefficientSpace source :=
  Ring.inverse (gramAt source positions) ∘L (frameAt source positions).adjoint ∘L
    frameFDeriv source positions direction

def connectionMatrixAt (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (connectionAt source positions direction)

def connectionMatrix (source : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  connectionMatrixAt source (sourcePositions source) direction

def gramMatrixAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (gramAt source positions)

def gramRateMatrixAt (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (gramFDeriv source positions direction)

theorem connection_at_unit (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) (unit : IsUnit (gramAt source positions)) :
    connectionAt source positions direction = LAlanineSpatialProjection.verticalResponse
      (frameAt source positions) (frameFDeriv source positions direction) unit := by
  rw [connectionAt,Ring.inverse_of_isUnit unit]
  rfl

theorem source_connection (source : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration source) :
    connectionAt source (sourcePositions source) direction =
      (frameAt source (sourcePositions source)).adjoint ∘L
        frameFDeriv source (sourcePositions source) direction := by
  rw [connectionAt,gram_source_one,Ring.inverse_one]
  ext coefficient
  rfl

theorem gram_matrix_source (source : CPS1ElectronicSource.State frame) :
    gramMatrixAt source (sourcePositions source) = 1 := by
  rw [gramMatrixAt,gram_source_one,map_one]

theorem connection_matrix_operator (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ)) (connectionMatrixAt source positions direction) =
      connectionAt source positions direction := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _

theorem connection_gram_at_unit (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) (unit : IsUnit (gramAt source positions)) :
    (connectionAt source positions direction).adjoint ∘L gramAt source positions +
      gramAt source positions ∘L connectionAt source positions direction =
      gramFDeriv source positions direction := by
  rw [connection_at_unit source positions direction unit,gram_fderiv_apply]
  exact LAlanineSpatialProjection.vertical_gram_rate _ _ unit

theorem connection_matrix_gram_at_unit (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) (unit : IsUnit (gramAt source positions)) :
    (connectionMatrixAt source positions direction).conjTranspose * gramMatrixAt source positions +
      gramMatrixAt source positions * connectionMatrixAt source positions direction =
      gramRateMatrixAt source positions direction := by
  have generated := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm
    (connection_gram_at_unit source positions direction unit)
  change (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm
      (star (connectionAt source positions direction) * gramAt source positions +
        gramAt source positions * connectionAt source positions direction) = _ at generated
  simp only [map_add,map_mul] at generated
  have adjoint : (Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm
      (star (connectionAt source positions direction)) =
      star (connectionMatrixAt source positions direction) :=
    (Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm.map_star' _
  rw [adjoint] at generated
  exact generated

theorem connection_matrix_source_gram (source : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration source) :
    (connectionMatrix source direction).conjTranspose + connectionMatrix source direction =
      gramRateMatrixAt source (sourcePositions source) direction := by
  have generated := connection_matrix_gram_at_unit source (sourcePositions source) direction
    (source_gram_unit source)
  simpa only [gram_matrix_source,Matrix.mul_one,Matrix.one_mul,connectionMatrix] using generated

def occupiedConnectionRate (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source)
    (occupied : Matrix (CPS1MolecularFrame.ActualIndex source) (ElectronIndex source.geometry) ℂ) :=
  -(connectionMatrixAt source positions direction * occupied)

theorem occupied_connection_tangent (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source)
    (occupied : Matrix (CPS1MolecularFrame.ActualIndex source) (ElectronIndex source.geometry) ℂ)
    (unit : IsUnit (gramAt source positions)) :
    (occupiedConnectionRate source positions direction occupied).conjTranspose *
        gramMatrixAt source positions * occupied +
      occupied.conjTranspose * gramRateMatrixAt source positions direction * occupied +
      occupied.conjTranspose * gramMatrixAt source positions *
        occupiedConnectionRate source positions direction occupied = 0 := by
  rw [← connection_matrix_gram_at_unit source positions direction unit]
  simp only [occupiedConnectionRate,Matrix.conjTranspose_neg,Matrix.conjTranspose_mul,
    Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
  abel

def spatialGenerator (source : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration source) : SpinSpace →L[ℂ] SpinSpace :=
  LAlanineSpatialProjection.hamiltonian (frameAt source (sourcePositions source))
    (frameFDeriv source (sourcePositions source) direction) (source_gram_unit source)

theorem spatial_generator_selfadjoint (source : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration source) :
    (spatialGenerator source direction).adjoint = spatialGenerator source direction :=
  LAlanineSpatialProjection.hamiltonian_adjoint _ _ _

theorem full_source_frame_lift (source : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration source) :
    Complex.I • frameFDeriv source (sourcePositions source) direction =
      spatialGenerator source direction ∘L frameAt source (sourcePositions source) +
      frameAt source (sourcePositions source) ∘L
        (Complex.I • connectionAt source (sourcePositions source) direction) := by
  rw [connection_at_unit source (sourcePositions source) direction (source_gram_unit source)]
  exact LAlanineSpatialProjection.full_frame_lift _ _ _

end
end CPS1Deformation
