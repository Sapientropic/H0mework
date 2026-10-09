import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Connection

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource ContinuousLinearMap
open scoped Matrix
variable {frame : CPS1Recycling.Frame}

abbrev OccupiedSpace (source : CPS1ElectronicSource.State frame) :=
  Matrix (CPS1MolecularFrame.ActualIndex source) (ElectronIndex source.geometry) ℂ

def connectionLinearAt (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) :
    NuclearConfiguration source →ₗ[ℝ] (CoefficientSpace source →L[ℂ] CoefficientSpace source) where
  toFun := connectionAt source positions
  map_add' := by
    intro first second
    simp only [connectionAt,map_add,comp_add]
  map_smul' := by
    intro scalar direction
    simp only [connectionAt,map_smul,comp_smul,RingHom.id_apply]

def connectionMatrixLinearAt (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) :
    NuclearConfiguration source →ₗ[ℝ]
      Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  let readout := (Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm
  (readout.toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ).comp (connectionLinearAt source positions)

def connectionDifferentialAt (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) :
    NuclearConfiguration source →L[ℝ]
      Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  (connectionMatrixLinearAt source positions).toContinuousLinearMap

theorem connection_differential_apply (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) :
    connectionDifferentialAt source positions direction =
      connectionMatrixAt source positions direction := rfl

def occupiedConnectionLinear (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedSpace source) :
    NuclearConfiguration source →ₗ[ℝ] OccupiedSpace source where
  toFun := fun direction first slot =>
    -(∑ second : CPS1MolecularFrame.ActualIndex source,
      connectionDifferentialAt source positions direction first second * occupied second slot)
  map_add' := by
    intro first second
    ext index slot
    simp only [map_add,Matrix.add_apply,add_mul,Finset.sum_add_distrib,neg_add]
    rfl
  map_smul' := by
    intro scalar direction
    ext index slot
    simp only [map_smul,Matrix.smul_apply,smul_mul_assoc,← Finset.smul_sum,RingHom.id_apply]
    exact (smul_neg scalar _).symm

def occupiedConnectionDifferential (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedSpace source) :
    NuclearConfiguration source →L[ℝ] OccupiedSpace source :=
  (occupiedConnectionLinear source positions occupied).toContinuousLinearMap

def covariantTangent (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedSpace source) :
    NuclearConfiguration source →L[ℝ] (NuclearConfiguration source × OccupiedSpace source) :=
  (ContinuousLinearMap.id ℝ (NuclearConfiguration source)).prod
    (occupiedConnectionDifferential source positions occupied)

theorem covariant_tangent_apply (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) (occupied : OccupiedSpace source) :
    covariantTangent source positions occupied direction =
      (direction,occupiedConnectionRate source positions direction occupied) := rfl

theorem covariant_tangent_gram (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) (occupied : OccupiedSpace source)
    (unit : IsUnit (gramAt source positions)) :
    (covariantTangent source positions occupied direction).2.conjTranspose *
        gramMatrixAt source positions * occupied +
      occupied.conjTranspose * gramRateMatrixAt source positions direction * occupied +
      occupied.conjTranspose * gramMatrixAt source positions *
        (covariantTangent source positions occupied direction).2 = 0 :=
  occupied_connection_tangent source positions direction occupied unit

end
end CPS1Deformation
