import H0mework.Physics.LowEnergy.FullQuantum.StateGreen.Algebra

/-! The fixed positive initial state is exactly the normalized original matter
field; every full Fock word is read only after its complete action. -/
set_option autoImplicit false
open scoped Matrix InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateGreen
open QuantizationCheck.Fermion Fermion ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair YangMills.FullPairing DiracExteriorMatterAction
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

def preparedMatter (point : BasePoint) : DiracExteriorMatterCarrier := (1/2 : ℂ) • actual.matter point

def preparedVector (point : BasePoint) : Quantum.Index → ℂ := Quantum.coordinates (preparedMatter point)

theorem preparedMatter_original (point : BasePoint) :
    naturalCoordinates (preparedMatter point)=prepared point := by
  rw [preparedMatter,map_smul,actual_eq_twice_prepared,smul_smul]
  norm_num

theorem preparedVector_unit (point : BasePoint) : modePair (preparedVector point) (preparedVector point)=1 := by
  change Quantum.coordinatePair (preparedMatter point) (preparedMatter point)=1
  rw [Quantum.coordinatePair_full,← natural_inner,preparedMatter_original,
    inner_self_eq_norm_sq_to_K,prepared_norm]
  norm_num

def occupation (point : BasePoint) : Matrix Quantum.Index Quantum.Index ℂ :=
  PreparedWeight.occupation (preparedVector point)

theorem occupation_square (point : BasePoint) : occupation point*occupation point=occupation point := by
  rw [occupation,PreparedWeight.occupation,Matrix.vecMulVec_mul_vecMulVec]
  have unit : star (preparedVector point) ⬝ᵥ preparedVector point=1 := preparedVector_unit point
  rw [unit,one_smul]

theorem occupation_adjoint (point : BasePoint) : (occupation point).conjTranspose=occupation point := by
  simp [occupation,PreparedWeight.occupation,Matrix.conjTranspose_vecMulVec]

def sourceWordMother (word : Module.End ℂ (Fock Quantum.Index)) : Mother :=
  Quantum.operatorMatrix.toLinearEquiv.symm (PreparedWeight.wholeCompression word)

theorem source_word_pair (point : BasePoint) (word : Module.End ℂ (Fock Quantum.Index)) :
    read (preparedVector point) word =
      inner ℂ (prepared point) (operator (sourceWordMother word) (prepared point)) := by
  rw [← preparedMatter_original point,operator_coordinates,natural_inner,← Quantum.coordinatePair_full]
  change read (preparedVector point) word=modePair (preparedVector point)
    (Quantum.coordinates (sourceWordMother word (preparedMatter point)))
  rw [← Quantum.matrix_action]
  have restored : Quantum.operatorMatrix (sourceWordMother word)=PreparedWeight.wholeCompression word :=
    Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply _
  rw [restored]
  exact (PreparedWeight.wholeCompression_pair word (preparedVector point)).symm

theorem source_word_readback (point : BasePoint) (word : Module.End ℂ (Fock Quantum.Index)) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1 (sourceWordMother word)))=
      read (preparedVector point) word := by
  rw [source_gram,source_word_pair]
  congr 1
  simp [operator]

theorem source_word_boundary (point : BasePoint) (word : Module.End ℂ (Fock Quantum.Index)) :
    read (preparedVector point) word = PreparedWeight.boundaryDeterminant (preparedVector point)
      (PreparedWeight.wholeCompression word) := by
  rw [PreparedWeight.boundaryDeterminant_pair _ _ (preparedVector_unit point),
    PreparedWeight.wholeCompression_pair]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateGreen
