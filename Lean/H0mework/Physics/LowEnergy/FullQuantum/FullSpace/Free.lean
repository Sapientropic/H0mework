import H0mework.Physics.LowEnergy.FullQuantum.FullSpace.Source

/-! A self-adjoint, continuous complete free Hamiltonian, generated from the
same physical-time source before any Hilbert evolution is requested. -/
set_option autoImplicit false
open scoped Matrix InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Triangular
noncomputable section
local instance : DecidableEq Sector := Classical.decEq _

private theorem operator_sum {ι : Type*} [Fintype ι] (A : ι → Mother) :
    operator (∑ i, A i)=∑ i, operator (A i) := by
  ext v
  simp [operator]

theorem spin_operator (matrix : DiracMatrix) :
    operator (diracMatrixMatterAction matrix) =
      (Matrix.toEuclideanCLM (n := Index) (𝕜 := ℂ)) (spinMatrix matrix) := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨v,rfl⟩ := naturalCoordinates.surjective v
  rw [operator_coordinates,spin_coordinates]

theorem principal_operator (momentum : Fin 3 → ℝ) :
    operator (principalMother momentum) =
      (Matrix.toEuclideanCLM (n := Index) (𝕜 := ℂ)) (principalMatrix momentum) := by
  simp only [principalMother,operator_sum,operator_smul,spin_operator,
    principalMatrix,map_sum,map_smul]

theorem source_gauge_selfAdjoint : star (operator gaugeMother)=operator gaugeMother := by
  have same := Stage10.Recovery.stageOneThroughTenClosure.final.recoversStageNine.trans
    Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.actualGenerated
  have source := YangMills.Response.Skew.insertion_skew sourceGaugeCoordinates 0
  rw [same] at source
  rw [gaugeMother,operator_smul,star_smul,source]
  simp

theorem source_spin_selfAdjoint : star (operator spinMother)=operator spinMother := by
  have matrix : diracGammaFive.conjTranspose=diracGammaFive := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracGammaFive,Matrix.conjTranspose_apply]
  have self : star (operator (diracMatrixMatterAction diracGammaFive))=
      operator (diracMatrixMatterAction diracGammaFive) := by
    rw [spin_operator,← map_star]
    congr 1
    exact spin_hermitian _ matrix
  rw [spinMother,operator_smul,star_smul,self]
  simp

def freeOperator (momentum : Fin 3 → ℝ) : Hilbert →L[ℂ] Hilbert :=
  operator (freeHamiltonian actual 0 momentum)

theorem freeOperator_original (point : BasePoint) (momentum : Fin 3 → ℝ) :
    freeOperator momentum=operator (freeHamiltonian actual point momentum) := by
  rw [freeOperator,source_free_original,source_free_original]

theorem freeOperator_formula (momentum : Fin 3 → ℝ) :
    freeOperator momentum =
      (Matrix.toEuclideanCLM (n := Index) (𝕜 := ℂ)) (principalMatrix momentum)+
        operator spinMother+operator gaugeMother := by
  rw [freeOperator,source_free_original,operator_add,operator_add,principal_operator]

theorem freeOperator_selfAdjoint (momentum : Fin 3 → ℝ) :
    star (freeOperator momentum)=freeOperator momentum := by
  rw [freeOperator_formula]
  change ContinuousLinearMap.adjoint (_+_+_)=_
  simp only [map_add ContinuousLinearMap.adjoint,← ContinuousLinearMap.star_eq_adjoint]
  rw [source_spin_selfAdjoint,source_gauge_selfAdjoint]
  congr 2
  rw [← map_star]
  congr 1
  exact principalMatrix_hermitian momentum

theorem freeOperator_continuous : Continuous freeOperator := by
  change Continuous (fun momentum : Fin 3 → ℝ => freeOperator momentum)
  simp only [freeOperator_formula]
  exact (((Matrix.toEuclideanCLM (n := Index) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp
    principalMatrix_continuous).add continuous_const).add continuous_const

theorem original_freeHamiltonian_selfAdjoint (point : BasePoint) (momentum : Fin 3 → ℝ) :
    star (operator (freeHamiltonian actual point momentum))=
      operator (freeHamiltonian actual point momentum) := by
  rw [← freeOperator_original point momentum]
  exact freeOperator_selfAdjoint momentum

theorem original_freeHamiltonian_continuous (point : BasePoint) :
    Continuous (fun momentum : Fin 3 → ℝ => operator (freeHamiltonian actual point momentum)) := by
  simp only [← freeOperator_original point]
  exact freeOperator_continuous

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
