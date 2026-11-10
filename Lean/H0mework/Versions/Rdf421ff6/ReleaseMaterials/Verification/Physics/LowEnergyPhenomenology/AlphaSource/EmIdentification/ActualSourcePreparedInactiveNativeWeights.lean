import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedInactiveNativeData

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedInactiveNativeWeights
open PreparationVacuumOriginalGreenFeedback ActualSourcePreparedInactiveNativeData
open PreparationVacuumPhysicalCharacteristic CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open scoped Matrix BigOperators

def nativeSpatialSquare (p : Fin 4 → ℂ) : ℂ := p 1^2+p 2^2+p 3^2

def nativeInactiveWeight (p : Fin 4 → ℂ) (i : Fin 289) : ℂ :=
  if (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val then
    if i ∈ sourceInactivePoleIndices then nativeSpatialSquare p*(nativeSpatialSquare p+72/25)
    else if i ∈ sourceInactiveMassIndices then nativeSpatialSquare p+81/50 else 1
  else 0

private def poleAtoms : List SourceAtom := [
  (⟨0,4,0,0⟩,1),(⟨0,0,4,0⟩,1),(⟨0,0,0,4⟩,1),
  (⟨0,2,2,0⟩,2),(⟨0,2,0,2⟩,2),(⟨0,0,2,2⟩,2),
  (⟨0,2,0,0⟩,⟨⟨(72/25:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨(72/25:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨(72/25:ℚ),0⟩,⟨0,0⟩⟩)]
private def massAtoms : List SourceAtom := [
  (⟨0,2,0,0⟩,1),(⟨0,0,2,0⟩,1),(⟨0,0,0,2⟩,1),
  (⟨0,0,0,0⟩,⟨⟨(81/50:ℚ),0⟩,⟨0,0⟩⟩)]
private def rowAtoms (i : Fin 289) : List SourceAtom :=
  if (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val then
    if i ∈ sourceInactivePoleIndices then poleAtoms
    else if i ∈ sourceInactiveMassIndices then massAtoms else [(⟨0,0,0,0⟩,1)]
  else []
private def liftRow (i : Fin 289) (atoms : List SourceAtom) : List SourceTerm :=
  atoms.map (fun a => ⟨i,i,a.1,a.2⟩)
private def expectedWeightTerms : List SourceTerm :=
  (List.finRange 289).flatMap (fun i => liftRow i (rowAtoms i))

private theorem weight_terms_certificate :
    fastNormalizeTerms (sourceInactiveWeightTerms++negativeTerms expectedWeightTerms)=[] := by
  decide +kernel

private def atomsScalar (atoms : List SourceAtom) (p : Fin 4 → ℂ) : ℂ :=
  (atoms.map (fun a => coefficientValue a.2*a.1.value p)).sum

private theorem lift_row_value (i : Fin 289) (atoms : List SourceAtom) (p : Fin 4 → ℂ) :
    sourceMatrix (liftRow i atoms) p=Matrix.single i i (atomsScalar atoms p) := by
  induction atoms with
  | nil => simp [liftRow,sourceMatrix,atomsScalar]
  | cons a rest ih =>
      simp only [liftRow,List.map_cons,sourceMatrix_cons] at ih ⊢
      rw [ih]
      simp only [SourceTerm.matrix,atomsScalar,List.map_cons,List.sum_cons,Matrix.single_add]

private theorem row_scalar (i : Fin 289) (p : Fin 4 → ℂ) :
    atomsScalar (rowAtoms i) p=nativeInactiveWeight p i := by
  unfold rowAtoms nativeInactiveWeight
  split_ifs
  · norm_num [atomsScalar,poleAtoms,coefficientValue,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,Powers.value,nativeSpatialSquare]
    ring
  · norm_num [atomsScalar,massAtoms,coefficientValue,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,Powers.value,nativeSpatialSquare]
    ring
  · simp [atomsScalar,coefficientValue,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,Powers.value]
  · rfl

private theorem source_flatMap {I : Type*} (items : List I) (rows : I → List SourceTerm) (p : Fin 4 → ℂ) :
    sourceMatrix (items.flatMap rows) p=(items.map (fun i => sourceMatrix (rows i) p)).sum := by
  induction items with
  | nil => rfl
  | cons i rest ih => simp only [List.flatMap_cons,sourceMatrix_append,List.map_cons,List.sum_cons,ih]

/-- The literal inverse weights are precisely the generated massless,
massive and algebraic source factors; the spatial pole is retained. -/
theorem source_inactive_native_weight_matrix (p : Fin 4 → ℂ) :
    sourceMatrix sourceInactiveWeightTerms p=Matrix.diagonal (nativeInactiveWeight p) := by
  rw [normalization_equal _ _ weight_terms_certificate p]
  unfold expectedWeightTerms
  rw [source_flatMap]
  simp_rw [lift_row_value,row_scalar]
  rw [←List.ofFn_eq_map,List.sum_ofFn]
  exact Matrix.sum_single_eq_diagonal _

@[local simp] private theorem momentum_one (spatial : Fin 3 → ℂ) (z : ℂ) :
    Fin.cases z spatial (1 : Fin 4)=spatial 0 := rfl
@[local simp] private theorem momentum_two (spatial : Fin 3 → ℂ) (z : ℂ) :
    Fin.cases z spatial (2 : Fin 4)=spatial 1 := rfl
@[local simp] private theorem momentum_three (spatial : Fin 3 → ℂ) (z : ℂ) :
    Fin.cases z spatial (3 : Fin 4)=spatial 2 := rfl

theorem source_inactive_native_physical_square (eps : ℝ) (n : PhysicalMomentum) :
    nativeSpatialSquare (frequencyRay eps 0 n)= -(eps:ℂ)^4*(spatialSquare n:ℂ) := by
  norm_num [nativeSpatialSquare,frequencyRay,physicalFrequencyMomentum,spatialSquare,mul_pow,Pi.smul_apply,smul_eq_mul,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

/-- A fixed source small ball pays both nonzero native mass factors.
Neither a full Green chart nor any quantum endpoint enters this domain. -/
theorem source_inactive_native_weight_nonzero (eps : ℝ) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) :
    nativeInactiveWeight (frequencyRay eps 0 n) i≠0 := by
  have square : eps^2≤1/4 := by nlinarith
  have fourth : eps^4≤1/16 := by nlinarith [sq_nonneg (eps^2)]
  have a : 0<(72/25:ℝ)-eps^4 := by linarith
  have b : 0<(81/50:ℝ)-eps^4 := by linarith
  have ac : -(eps:ℂ)^4+72/25≠0 := by
    have value : -(eps:ℂ)^4+72/25=(((72/25:ℝ)-eps^4:ℝ):ℂ) := by push_cast; ring
    rw [value]
    exact Complex.ofReal_ne_zero.mpr a.ne'
  have bc : -(eps:ℂ)^4+81/50≠0 := by
    have value : -(eps:ℂ)^4+81/50=(((81/50:ℝ)-eps^4:ℝ):ℂ) := by push_cast; ring
    rw [value]
    exact Complex.ofReal_ne_zero.mpr b.ne'
  unfold nativeInactiveWeight
  rw [if_pos outside,source_inactive_native_physical_square,unit,Complex.ofReal_one,mul_one]
  split_ifs
  · exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr positive.ne'))) ac
  · exact bc
  · exact one_ne_zero

end LowEnergy.GaussComposite.ActualSourcePreparedInactiveNativeWeights
