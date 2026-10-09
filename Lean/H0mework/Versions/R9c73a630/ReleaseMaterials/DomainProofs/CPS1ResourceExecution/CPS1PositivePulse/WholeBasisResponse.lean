import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.CanonicalContinuity
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.OccupiedNormalization
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Mechanics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Energy
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1PositivePulse
noncomputable section
open CPS1Deformation CPS1ElectronicSource InnerProductSpace
open CPS1MolecularFrame.FiniteNormed
open scoped BigOperators Topology

variable {X ι κ E : Type*} [TopologicalSpace X] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def totalReadback (raw : ι → E) : Matrix ι ι ℂ :=
  fun slot source => inner ℂ
    (gramSchmidtNormed ℂ (ordered raw) (Fintype.equivFin ι slot)) (raw source)

theorem total_readback_continuousAt (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent ℂ (raw currentPoint)) :
    ContinuousAt (fun point => totalReadback (raw point)) currentPoint := by
  apply continuousAt_pi.mpr
  intro slot
  apply continuousAt_pi.mpr
  intro source
  exact (canonical_normed_continuousAt raw currentPoint continuous independent
    (Fintype.equivFin ι slot)).inner (continuous source)

theorem matrix_mul_continuousAt {α β γ : Type*} [Fintype β]
    (left : X → Matrix α β ℂ) (right : X → Matrix β γ ℂ) (currentPoint : X)
    (leftContinuous : ContinuousAt left currentPoint)
    (rightContinuous : ContinuousAt right currentPoint) :
    ContinuousAt (fun point => left point * right point) currentPoint :=
  (continuous_fst.matrix_mul continuous_snd).continuousAt.comp
    (leftContinuous.prodMk rightContinuous)

theorem occupied_update_continuousAt [DecidableEq ι]
    (hamiltonian : X → Matrix ι ι ℂ) (time : X → ℝ) (occupied : X → Matrix ι κ ℂ)
    (currentPoint : X) (hamiltonianContinuous : ContinuousAt hamiltonian currentPoint)
    (timeContinuous : ContinuousAt time currentPoint) (occupiedContinuous : ContinuousAt occupied currentPoint)
    (hermitian : (hamiltonian currentPoint).IsHermitian) :
    ContinuousAt (fun point => CPS1ElectronicEvolution.occupiedUpdate
      (hamiltonian point) (time point) (occupied point)) currentPoint := by
  have scalarContinuous : ContinuousAt (fun point => Complex.I * (time point : ℂ)) currentPoint :=
    continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp timeContinuous)
  have generatorContinuous : ContinuousAt (fun point => CPS1ElectronicEvolution.generator
      (hamiltonian point) (time point)) currentPoint :=
    scalarContinuous.smul hamiltonianContinuous
  have denominatorContinuous : ContinuousAt (fun point => CPS1ElectronicEvolution.denominator
      (hamiltonian point) (time point)) currentPoint :=
    continuousAt_const.add generatorContinuous
  have determinantNonzero : (CPS1ElectronicEvolution.denominator
      (hamiltonian currentPoint) (time currentPoint)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (CPS1ElectronicEvolution.denominator_unit _ hermitian _))
  have inverseContinuous : ContinuousAt (Inv.inv : Matrix ι ι ℂ → Matrix ι ι ℂ)
      (CPS1ElectronicEvolution.denominator (hamiltonian currentPoint) (time currentPoint)) :=
    continuousAt_matrix_inv _ (by
      have scalarInverse : ContinuousAt (fun value : ℂ => value⁻¹)
          (CPS1ElectronicEvolution.denominator (hamiltonian currentPoint) (time currentPoint)).det :=
        continuousAt_id.inv₀ determinantNonzero
      simpa only [Ring.inverse_eq_inv'] using scalarInverse)
  have composedInverse : ContinuousAt (fun point : X =>
      (CPS1ElectronicEvolution.denominator (hamiltonian point) (time point))⁻¹) currentPoint :=
    Filter.Tendsto.comp inverseContinuous denominatorContinuous
  have stepContinuous : ContinuousAt (fun point => CPS1ElectronicEvolution.step
      (hamiltonian point) (time point)) currentPoint :=
    composedInverse.mul denominatorContinuous.star
  exact matrix_mul_continuousAt _ _ currentPoint stepContinuous occupiedContinuous

def fixedPhysicalResponse [DecidableEq ι] (raw : ι → E) (hamiltonian : Matrix ι ι ℂ)
    (occupied : Matrix ι κ ℂ) (time : ℝ) : Matrix ι κ ℂ :=
  totalNormalization (𝕜 := ℂ) raw * CPS1ElectronicEvolution.occupiedUpdate
    ((totalNormalization (𝕜 := ℂ) raw).conjTranspose * hamiltonian * totalNormalization (𝕜 := ℂ) raw)
    (time/2) (totalReadback raw * occupied)

theorem fixed_physical_response_continuousAt [DecidableEq ι]
    (raw : X → ι → E) (hamiltonian : X → Matrix ι ι ℂ) (occupied : X → Matrix ι κ ℂ)
    (time : X → ℝ) (currentPoint : X)
    (rawContinuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent ℂ (raw currentPoint))
    (hamiltonianContinuous : ContinuousAt hamiltonian currentPoint)
    (occupiedContinuous : ContinuousAt occupied currentPoint) (timeContinuous : ContinuousAt time currentPoint)
    (hermitian : (hamiltonian currentPoint).IsHermitian) :
    ContinuousAt (fun point => fixedPhysicalResponse
      (raw point) (hamiltonian point) (occupied point) (time point)) currentPoint := by
  have synthesisContinuous := total_normalization_continuousAt raw currentPoint rawContinuous independent
  have readbackContinuous := total_readback_continuousAt raw currentPoint rawContinuous independent
  have fockContinuous := (synthesisContinuous.star.mul hamiltonianContinuous).mul synthesisContinuous
  have normedOccupiedContinuous := matrix_mul_continuousAt _ _ currentPoint readbackContinuous occupiedContinuous
  have normedHermitian : ((totalNormalization (𝕜 := ℂ) (raw currentPoint)).conjTranspose *
      hamiltonian currentPoint * totalNormalization (𝕜 := ℂ) (raw currentPoint)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul _ hermitian
  exact matrix_mul_continuousAt _ _ currentPoint synthesisContinuous
    (occupied_update_continuousAt _ _ _ currentPoint fockContinuous
      (timeContinuous.div_const 2) normedOccupiedContinuous normedHermitian)

def fullNormedIndex (raw : ι → E)
    (nonzero : ∀ index, gramSchmidtNormed ℂ (ordered raw) index ≠ 0) : ι ≃ Index (𝕜 := ℂ) raw where
  toFun slot := ⟨Fintype.equivFin ι slot,nonzero _⟩
  invFun index := (Fintype.equivFin ι).symm index.val
  left_inv slot := (Fintype.equivFin ι).symm_apply_apply slot
  right_inv index := Subtype.ext ((Fintype.equivFin ι).apply_symm_apply index.val)

theorem step_submatrix {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hamiltonian : Matrix α α ℂ) (index : β ≃ α) (time : ℝ) :
    CPS1ElectronicEvolution.step (hamiltonian.submatrix index index) time =
      (CPS1ElectronicEvolution.step hamiltonian time).submatrix index index := by
  have denominator : CPS1ElectronicEvolution.denominator (hamiltonian.submatrix index index) time =
      (CPS1ElectronicEvolution.denominator hamiltonian time).submatrix index index := by
    change 1 + (Complex.I * (time : ℂ)) • hamiltonian.submatrix index index =
      (1 : Matrix α α ℂ).submatrix index index +
        (Complex.I * (time : ℂ)) • hamiltonian.submatrix index index
    rw [Matrix.submatrix_one_equiv]
  simp only [CPS1ElectronicEvolution.step,denominator,Matrix.inv_submatrix_equiv,
    Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]

variable {frame : CPS1Recycling.Frame}

theorem physical_fock_response_fixed (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (time : ℝ)
    (nonzero : ∀ index, gramSchmidtNormed ℂ (ordered (basisAt source positions)) index ≠ 0) :
    physicalFockResponse source positions occupied time =
      fixedPhysicalResponse (basisAt source positions) (physicalFockAt source positions occupied) occupied time := by
  classical
  let index := fullNormedIndex (basisAt source positions) nonzero
  have synthesis : (basisSynthesis source positions).submatrix id index =
      totalNormalization (𝕜 := ℂ) (basisAt source positions) := rfl
  have readback : (basisReadback source positions).submatrix index id =
      totalReadback (basisAt source positions) := rfl
  have fock : (normedPhysicalFock source positions occupied).submatrix index index =
      (totalNormalization (𝕜 := ℂ) (basisAt source positions)).conjTranspose *
        physicalFockAt source positions occupied * totalNormalization (𝕜 := ℂ) (basisAt source positions) := by
    unfold normedPhysicalFock
    rw [← Matrix.submatrix_mul_equiv _ _ index (Equiv.refl _) index]
    simp only [Equiv.coe_refl]
    rw [← Matrix.submatrix_mul_equiv _ _ index (Equiv.refl _) id]
    simp only [Matrix.submatrix_id_id,Equiv.coe_refl,← Matrix.conjTranspose_submatrix,synthesis]
  have occupation : (normedOccupation source positions occupied).submatrix index id =
      totalReadback (basisAt source positions) * occupied := by
    unfold normedOccupation
    rw [← Matrix.submatrix_mul_equiv _ _ index (Equiv.refl _) id]
    simp only [Equiv.coe_refl,Matrix.submatrix_id_id,readback]
  have step := step_submatrix (normedPhysicalFock source positions occupied) index (time/2)
  have generated : (physicalFockResponse source positions occupied time).submatrix id id =
      fixedPhysicalResponse (basisAt source positions) (physicalFockAt source positions occupied) occupied time := by
    unfold physicalFockResponse fixedPhysicalResponse CPS1ElectronicEvolution.occupiedUpdate
    rw [← Matrix.submatrix_mul_equiv _ _ id index id,
      ← Matrix.submatrix_mul_equiv _ _ index index id,synthesis,occupation,← step,fock]
  simpa only [Matrix.submatrix_id_id] using generated

theorem basis_independent_at_unit (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (unit : IsUnit (gramAt source positions)) :
    LinearIndependent ℂ (basisAt source positions) := by
  classical
  have gramOperator : gramAt source positions =
      (Matrix.toEuclideanCLM (𝕜 := ℂ)) (Matrix.gram ℂ (basisAt source positions)) :=
    CPS1MolecularFrame.field_frame_gram _
  rw [gramOperator] at unit
  have matrixUnit : IsUnit (Matrix.gram ℂ (basisAt source positions)) := by
    have mapped := unit.map ((Matrix.toEuclideanCLM
      (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm.toMonoidHom)
    change IsUnit ((Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm
      ((Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ))
        (Matrix.gram ℂ (basisAt source positions)))) at mapped
    rw [(Matrix.toEuclideanCLM (n := CPS1MolecularFrame.ActualIndex source) (𝕜 := ℂ)).symm_apply_apply] at mapped
    exact mapped
  exact Matrix.linearIndependent_of_det_gram_ne_zero
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp matrixUnit))

theorem basis_unit_eventually (source : CPS1ElectronicSource.State frame)
    (positions : X → NuclearConfiguration source) (currentPoint : X)
    (continuous : ContinuousAt positions currentPoint)
    (unit : IsUnit (gramAt source (positions currentPoint))) :
    ∀ᶠ point in 𝓝 currentPoint, IsUnit (gramAt source (positions point)) :=
  ((gram_hasFDerivAt source (positions currentPoint)).continuousAt.comp continuous).eventually_mem
    (Units.isOpen.mem_nhds unit)

theorem physical_fock_continuousAt (source : CPS1ElectronicSource.State frame)
    (positions : X → NuclearConfiguration source) (occupied : X → Occupation source) (currentPoint : X)
    (positionsContinuous : ContinuousAt positions currentPoint)
    (occupiedContinuous : ContinuousAt occupied currentPoint) :
    ContinuousAt (fun point => physicalFockAt source (positions point) (occupied point)) currentPoint := by
  classical
  have adjointContinuous : ContinuousAt (fun point => (occupied point).conjTranspose) currentPoint :=
    (continuous_id.matrix_conjTranspose).continuousAt.comp occupiedContinuous
  have densityContinuous : ContinuousAt (fun point => densityAt source (occupied point)) currentPoint :=
    matrix_mul_continuousAt _ _ currentPoint occupiedContinuous adjointContinuous
  apply continuousAt_pi.mpr
  intro first
  apply continuousAt_pi.mpr
  intro third
  have coreContinuous : ContinuousAt (fun point => coreAt source (positions point) first third) currentPoint :=
    (core_differentiable source (positions currentPoint) first third).continuousAt.comp positionsContinuous
  have responseContinuous : ContinuousAt (fun point => ∑ second, ∑ fourth,
      densityAt source (occupied point) fourth second *
        (twoBodyAt source (positions point) first second third fourth -
          twoBodyAt source (positions point) first second fourth third)) currentPoint :=
    tendsto_finsetSum Finset.univ fun second _ =>
      tendsto_finsetSum Finset.univ fun fourth _ =>
        ((continuous_apply_apply fourth second).continuousAt.comp densityContinuous).mul
          (((two_body_differentiable source (positions currentPoint) first second third fourth).continuousAt.comp
            positionsContinuous).sub
            ((two_body_differentiable source (positions currentPoint) first second fourth third).continuousAt.comp
              positionsContinuous))
  exact coreContinuous.add responseContinuous

theorem physical_fock_response_continuousAt (source : CPS1ElectronicSource.State frame)
    (positions : X → NuclearConfiguration source) (occupied : X → Occupation source) (time : X → ℝ)
    (currentPoint : X) (positionsContinuous : ContinuousAt positions currentPoint)
    (occupiedContinuous : ContinuousAt occupied currentPoint) (timeContinuous : ContinuousAt time currentPoint)
    (unit : IsUnit (gramAt source (positions currentPoint))) :
    ContinuousAt (fun point => physicalFockResponse source (positions point) (occupied point) (time point))
      currentPoint := by
  classical
  have independent := basis_independent_at_unit source (positions currentPoint) unit
  have rawContinuous (index : CPS1MolecularFrame.ActualIndex source) :
      ContinuousAt (fun point => basisAt source (positions point) index) currentPoint :=
    (basis_hasFDerivAt source (positions currentPoint) index).continuousAt.comp positionsContinuous
  have fixedContinuous := fixed_physical_response_continuousAt
    (fun point => basisAt source (positions point))
    (fun point => physicalFockAt source (positions point) (occupied point)) occupied time currentPoint
    rawContinuous independent (physical_fock_continuousAt source positions occupied currentPoint
      positionsContinuous occupiedContinuous) occupiedContinuous timeContinuous
    (physical_fock_hermitian source (positions currentPoint) (occupied currentPoint))
  have nonzero (index : Fin (Fintype.card (CPS1MolecularFrame.ActualIndex source))) :
      gramSchmidtNormed ℂ (ordered (basisAt source (positions currentPoint))) index ≠ 0 := by
    have length := gramSchmidtNormed_unit_length index (ordered_independent _ independent)
    intro zero
    rw [zero,norm_zero] at length
    exact zero_ne_one length
  have eventuallyNonzero : ∀ᶠ point in 𝓝 currentPoint,
      ∀ index : Fin (Fintype.card (CPS1MolecularFrame.ActualIndex source)),
        gramSchmidtNormed ℂ (ordered (basisAt source (positions point))) index ≠ 0 :=
    Filter.eventually_all.mpr fun index =>
      (canonical_normed_continuousAt (fun point => basisAt source (positions point)) currentPoint
        rawContinuous independent index).eventually_ne (nonzero index)
  apply fixedContinuous.congr
  filter_upwards [eventuallyNonzero] with point generated
  exact (physical_fock_response_fixed source (positions point) (occupied point) (time point) generated).symm

end
end CPS1PositivePulse
