import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.State
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Connection
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.EnergyDefs
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Symmetries

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

abbrev NormedBasisIndex (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :=
  CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (basisAt source positions)

def normedBasisAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    NormedBasisIndex source positions → SpinSpace :=
  CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (basisAt source positions)

def basisSynthesis (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (NormedBasisIndex source positions) ℂ :=
  CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (basisAt source positions)

def basisReadback (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    Matrix (NormedBasisIndex source positions) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (basisAt source positions)

def normedOccupation (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) :
    Matrix (NormedBasisIndex source positions) (ElectronIndex source.geometry) ℂ :=
  basisReadback source positions * occupied

theorem normed_basis_orthonormal (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) : Orthonormal ℂ (normedBasisAt source positions) :=
  CPS1MolecularFrame.FiniteNormed.field_orthonormal _

theorem normed_basis_complete (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) :
    Submodule.span ℂ (Set.range (normedBasisAt source positions)) =
      Submodule.span ℂ (Set.range (basisAt source positions)) :=
  CPS1MolecularFrame.FiniteNormed.span_exact _

theorem normed_basis_synthesis (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) :
    CPS1ElectronicEvolution.fields (basisAt source positions) (basisSynthesis source positions) =
      normedBasisAt source positions := by
  funext index
  exact (CPS1MolecularFrame.FiniteNormed.field_synthesis (basisAt source positions) index).symm

theorem normed_basis_readback (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) :
    CPS1ElectronicEvolution.fields (normedBasisAt source positions) (basisReadback source positions) =
      basisAt source positions := by
  funext index
  exact (CPS1MolecularFrame.FiniteNormed.raw_synthesis (basisAt source positions) index).symm

theorem normed_occupation_fields (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) :
    CPS1ElectronicEvolution.fields (normedBasisAt source positions) (normedOccupation source positions occupied) =
      occupiedFieldsAt source positions occupied := by
  funext slot
  rw [normedOccupation,fields_mul,normed_basis_readback]
  rfl

theorem source_occupation_synthesis (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source)
    (occupied : Matrix (NormedBasisIndex source positions) (ElectronIndex source.geometry) ℂ) :
    occupiedFieldsAt source positions (basisSynthesis source positions * occupied) =
      CPS1ElectronicEvolution.fields (normedBasisAt source positions) occupied := by
  funext slot
  rw [occupiedFieldsAt,fields_mul,normed_basis_synthesis]

theorem normed_occupation_gram (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (good : Orthonormal ℂ (occupiedFieldsAt source positions occupied)) :
    (normedOccupation source positions occupied).conjTranspose * normedOccupation source positions occupied = 1 := by
  classical
  ext first second
  rw [← CPS1ElectronicEvolution.field_gram _ (normed_basis_orthonormal source positions),
    normed_occupation_fields,orthonormal_iff_ite.mp good]
  rfl

theorem canonical_readback_fields (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) :
    occupiedFieldsAt source positions (basisSynthesis source positions * normedOccupation source positions occupied) =
      occupiedFieldsAt source positions occupied := by
  rw [source_occupation_synthesis,normed_occupation_fields]

theorem fields_injective_at_unit (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (unit : IsUnit (gramAt source positions))
    (first second : Occupation source)
    (same : occupiedFieldsAt source positions first = occupiedFieldsAt source positions second) : first = second := by
  classical
  have gram_operator : gramAt source positions =
      (Matrix.toEuclideanCLM (𝕜 := ℂ)) (Matrix.gram ℂ (basisAt source positions)) :=
    CPS1MolecularFrame.field_frame_gram _
  rw [gram_operator] at unit
  have matrixUnit : IsUnit (Matrix.gram ℂ (basisAt source positions)) := by
    have mapped := unit.map ((Matrix.toEuclideanCLM
      (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm.toMonoidHom)
    change IsUnit ((Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm
      ((Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ))
        (Matrix.gram ℂ (basisAt source positions)))) at mapped
    rw [(Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm_apply_apply] at mapped
    exact mapped
  have sameGram : Matrix.gram ℂ (basisAt source positions) * first =
      Matrix.gram ℂ (basisAt source positions) * second := by
    ext index slot
    have measured := congrArg (fun fields => inner ℂ (basisAt source positions index) (fields slot)) same
    simpa only [occupiedFieldsAt,CPS1ElectronicEvolution.fields,inner_sum,inner_smul_right,
      Matrix.mul_apply,Matrix.gram,Matrix.of_apply,mul_comm] using measured
  have recovered := congrArg (fun value => (Matrix.gram ℂ (basisAt source positions))⁻¹ * value) sameGram
  simpa only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp matrixUnit),Matrix.one_mul] using recovered

def normedPhysicalFock (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) : Matrix (NormedBasisIndex source positions) (NormedBasisIndex source positions) ℂ :=
  (basisSynthesis source positions).conjTranspose * physicalFockAt source positions occupied *
    basisSynthesis source positions

theorem normed_physical_fock_hermitian (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) :
    (normedPhysicalFock source positions occupied).IsHermitian := by
  unfold normedPhysicalFock
  exact Matrix.isHermitian_conjTranspose_mul_mul _ (physical_fock_hermitian source positions occupied)

def physicalFockResponse (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) (time : ℝ) : Occupation source :=
  basisSynthesis source positions * CPS1ElectronicEvolution.occupiedUpdate
    (normedPhysicalFock source positions occupied) (time/2) (normedOccupation source positions occupied)

theorem physical_fock_response_good (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (time : ℝ)
    (good : Orthonormal ℂ (occupiedFieldsAt source positions occupied)) :
    Orthonormal ℂ (occupiedFieldsAt source positions (physicalFockResponse source positions occupied time)) := by
  rw [physicalFockResponse,source_occupation_synthesis]
  exact CPS1ElectronicEvolution.updated_fields _ (normed_basis_orthonormal source positions)
    _ (normed_physical_fock_hermitian source positions occupied) _ _
    (normed_occupation_gram source positions occupied good)

theorem physical_fock_response_equation (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (time : ℝ) :
    CPS1ElectronicEvolution.denominator (normedPhysicalFock source positions occupied) (time/2) *
      CPS1ElectronicEvolution.occupiedUpdate (normedPhysicalFock source positions occupied) (time/2)
        (normedOccupation source positions occupied) =
      (1-CPS1ElectronicEvolution.generator (normedPhysicalFock source positions occupied) (time/2)) *
        normedOccupation source positions occupied := by
  rw [CPS1ElectronicEvolution.occupiedUpdate,← Matrix.mul_assoc,
    CPS1ElectronicEvolution.actual_equation _ (normed_physical_fock_hermitian source positions occupied)]

theorem physical_fock_response_zero (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) :
    occupiedFieldsAt source positions (physicalFockResponse source positions occupied 0) =
      occupiedFieldsAt source positions occupied := by
  simp only [physicalFockResponse,zero_div,CPS1ElectronicEvolution.occupiedUpdate,
    CPS1ElectronicEvolution.zero_time,Matrix.one_mul]
  exact canonical_readback_fields source positions occupied

theorem physical_fock_response_coefficients_zero (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (unit : IsUnit (gramAt source positions)) :
    physicalFockResponse source positions occupied 0 = occupied :=
  fields_injective_at_unit source positions unit _ _ (physical_fock_response_zero source positions occupied)

def physicalAction (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) : SpinSpace →L[ℂ] SpinSpace :=
  ∑ first, ∑ second, normedPhysicalFock source positions occupied first second •
    (innerSL ℂ (normedBasisAt source positions second)).smulRight (normedBasisAt source positions first)

theorem physical_action_fields (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (coordinates : Matrix (NormedBasisIndex source positions) (ElectronIndex source.geometry) ℂ)
    (slot : ElectronIndex source.geometry) :
    physicalAction source positions occupied (CPS1ElectronicEvolution.fields (normedBasisAt source positions) coordinates slot) =
      CPS1ElectronicEvolution.fields (normedBasisAt source positions) (normedPhysicalFock source positions occupied * coordinates) slot := by
  simp only [physicalAction,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,CPS1ElectronicEvolution.fields,
    (normed_basis_orthonormal source positions).inner_right_fintype,
    Matrix.mul_apply,smul_smul,Finset.sum_smul]

theorem physical_fock_midpoint (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (time : ℝ)
    (slot : ElectronIndex source.geometry) :
    let before := occupiedFieldsAt source positions occupied slot
    let after := occupiedFieldsAt source positions (physicalFockResponse source positions occupied time) slot
    after+(Complex.I*((time/2 : ℝ) : ℂ)) • physicalAction source positions occupied after =
      before-(Complex.I*((time/2 : ℝ) : ℂ)) • physicalAction source positions occupied before := by
  dsimp only
  have matrix := congrArg (fun operator => operator * normedOccupation source positions occupied)
    (CPS1ElectronicEvolution.actual_equation (normedPhysicalFock source positions occupied)
      (normed_physical_fock_hermitian source positions occupied) (time/2))
  have paid : CPS1ElectronicEvolution.occupiedUpdate (normedPhysicalFock source positions occupied) (time/2)
      (normedOccupation source positions occupied) + (Complex.I*((time/2 : ℝ) : ℂ)) •
      (normedPhysicalFock source positions occupied * CPS1ElectronicEvolution.occupiedUpdate
        (normedPhysicalFock source positions occupied) (time/2) (normedOccupation source positions occupied)) =
      normedOccupation source positions occupied - (Complex.I*((time/2 : ℝ) : ℂ)) •
        (normedPhysicalFock source positions occupied * normedOccupation source positions occupied) := by
    simpa only [CPS1ElectronicEvolution.denominator,CPS1ElectronicEvolution.generator,
      Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.mul_assoc,
      CPS1ElectronicEvolution.occupiedUpdate] using matrix
  have fields := congrArg (fun coordinates => CPS1ElectronicEvolution.fields (normedBasisAt source positions) coordinates slot) paid
  rw [CPS1ElectronicSource.fields_add,CPS1ElectronicSource.fields_sub,
    CPS1ElectronicSource.fields_smul,CPS1ElectronicSource.fields_smul] at fields
  rw [physicalFockResponse,source_occupation_synthesis,← normed_occupation_fields]
  rw [physical_action_fields,physical_action_fields]
  exact fields

def covariantWork (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) : NuclearConfiguration source →L[ℝ] ℝ :=
  (energyDifferential source positions occupied).comp (covariantTangent source positions occupied)

def coordinateDirection (source : CPS1ElectronicSource.State frame)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) (axis : Fin 3) : NuclearConfiguration source := by
  classical
  exact fun current component => if current = nuclear then if component = axis then 1 else 0 else 0

def covariantForce (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) : NuclearConfiguration source :=
  fun nuclear axis => -(covariantWork source positions occupied (coordinateDirection source nuclear axis))

theorem configuration_coordinates (source : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration source) :
    direction = ∑ nuclear, ∑ axis : Fin 3, direction nuclear axis • coordinateDirection source nuclear axis := by
  classical
  funext nuclear axis
  simp [coordinateDirection]

theorem covariant_force_work (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) (occupied : Occupation source) :
    energyDifferential source positions occupied (direction,occupiedConnectionRate source positions direction occupied) =
      -(∑ nuclear, inner ℝ (euclideanPoint (covariantForce source positions occupied nuclear))
        (euclideanPoint (direction nuclear))) := by
  have linear := congrArg (covariantWork source positions occupied) (configuration_coordinates source direction)
  simp only [map_sum,map_smul,smul_eq_mul] at linear
  rw [← covariant_tangent_apply source positions direction occupied]
  change covariantWork source positions occupied direction = _
  rw [linear]
  simp only [covariantForce,euclideanPoint,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
    star_trivial,mul_neg,Finset.sum_neg_distrib,neg_neg]

def Material.energy (state : Material frame) : ℝ :=
  energyWithMomenta state.reference state.positions state.momenta state.occupied

def Material.action (state : Material frame) : SpinSpace →L[ℂ] SpinSpace :=
  physicalAction state.reference state.positions state.occupied

theorem material_reprice_energy (state : Material frame) (reserve : ℝ) :
    (state.reprice reserve).energy = state.energy := rfl

def velocityAt (source : CPS1ElectronicSource.State frame) (momenta : NuclearConfiguration source) :
    NuclearConfiguration source :=
  fun nuclear axis => momenta nuclear axis / CPS1MolecularFrame.inertia source nuclear

def kickPositions (source : CPS1ElectronicSource.State frame) (positions momenta force : NuclearConfiguration source)
    (time : ℝ) : NuclearConfiguration source :=
  fun nuclear => positions nuclear + (time / CPS1MolecularFrame.inertia source nuclear) • momenta nuclear +
    (time^2 / (2 * CPS1MolecularFrame.inertia source nuclear)) • force nuclear

def kickMomenta (source : CPS1ElectronicSource.State frame) (momenta force : NuclearConfiguration source)
    (time : ℝ) : NuclearConfiguration source := momenta + time • force

theorem kick_positions_zero (source : CPS1ElectronicSource.State frame)
    (positions momenta force : NuclearConfiguration source) : kickPositions source positions momenta force 0 = positions := by
  funext nuclear
  simp only [kickPositions,zero_div,zero_pow (by decide : 2 ≠ 0),zero_smul,add_zero]

theorem kick_momenta_zero (source : CPS1ElectronicSource.State frame)
    (momenta force : NuclearConfiguration source) : kickMomenta source momenta force 0 = momenta := by
  simp only [kickMomenta,zero_smul,add_zero]

theorem nuclear_midpoint_work (source : CPS1ElectronicSource.State frame)
    (positions momenta force : NuclearConfiguration source) (time : ℝ)
    (nuclear : CPS1MolecularFrame.NuclearIndex source)
    (positive : 0 < CPS1MolecularFrame.inertia source nuclear) :
    CPS1AtomicDynamics.Coulomb.kinetic (CPS1MolecularFrame.inertia source nuclear)
        (euclideanPoint (kickMomenta source momenta force time nuclear)) -
      CPS1AtomicDynamics.Coulomb.kinetic (CPS1MolecularFrame.inertia source nuclear)
        (euclideanPoint (momenta nuclear)) =
      inner ℝ (euclideanPoint (force nuclear))
        (euclideanPoint (kickPositions source positions momenta force time nuclear) -
          euclideanPoint (positions nuclear)) := by
  exact CPS1AtomicDynamics.Coulomb.midpoint_work _ positive
    (euclideanPoint (positions nuclear)) (euclideanPoint (momenta nuclear)) (euclideanPoint (force nuclear)) time

end
end CPS1Deformation
