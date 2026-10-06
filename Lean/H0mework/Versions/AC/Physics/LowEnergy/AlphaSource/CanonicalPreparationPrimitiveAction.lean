import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarCoordinates
import Mathlib.LinearAlgebra.ExteriorPower.Basis

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumPrimitiveMatrix
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineExteriorMotherLieRepresentation
open scoped BigOperators
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective
set_option linter.unusedSimpArgs false

def complexAbs (z : ℂ) : ℝ := |z.re|+|z.im|

theorem complexAbs_nonnegative (z : ℂ) : 0≤complexAbs z := add_nonneg (abs_nonneg _) (abs_nonneg _)

@[simp] theorem complexAbs_zero : complexAbs 0=0 := by simp [complexAbs]
@[simp] theorem complexAbs_one : complexAbs 1=1 := by simp [complexAbs]
@[simp] theorem complexAbs_neg (z : ℂ) : complexAbs (-z)=complexAbs z := by simp [complexAbs]

theorem complexAbs_add (z w : ℂ) : complexAbs (z+w)≤complexAbs z+complexAbs w := by
  simpa [complexAbs,add_assoc,add_comm,add_left_comm] using add_le_add (abs_add_le z.re w.re) (abs_add_le z.im w.im)

theorem complexAbs_mul (z w : ℂ) : complexAbs (z*w)≤complexAbs z*complexAbs w := by
  have h1 : |z.re*w.re-z.im*w.im|≤|z.re*w.re|+|z.im*w.im| := by
    simpa [sub_eq_add_neg] using abs_add_le (z.re*w.re) (-(z.im*w.im))
  have h2:=abs_add_le (z.re*w.im) (z.im*w.re)
  simp only [abs_mul] at h1 h2
  dsimp [complexAbs]
  simp only [Complex.mul_re,Complex.mul_im]
  nlinarith

theorem complexAbs_sum {ι : Type*} (s : Finset ι) (f : ι→ℂ) :
    complexAbs (∑ i∈s,f i)≤∑ i∈s,complexAbs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (complexAbs_add _ _).trans (add_le_add le_rfl ih)

def exteriorL1 (v : ⋀[ℂ]^4 SU7FundamentalCarrier) : ℝ :=
  ∑ i : ExteriorBasisIndex 4,complexAbs ((su7ExteriorBasis 4).repr v i)

@[simp] theorem exteriorL1_zero : exteriorL1 0=0 := by simp [exteriorL1]
@[simp] theorem exteriorL1_neg (v : ⋀[ℂ]^4 SU7FundamentalCarrier) : exteriorL1 (-v)=exteriorL1 v := by simp [exteriorL1]

theorem exteriorL1_add (v w : ⋀[ℂ]^4 SU7FundamentalCarrier) :
    exteriorL1 (v+w)≤exteriorL1 v+exteriorL1 w := by
  unfold exteriorL1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa using complexAbs_add ((su7ExteriorBasis 4).repr v i) ((su7ExteriorBasis 4).repr w i)

theorem exteriorL1_sum {ι : Type*} (s : Finset ι) (f : ι→⋀[ℂ]^4 SU7FundamentalCarrier) :
    exteriorL1 (∑ i∈s,f i)≤∑ i∈s,exteriorL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (exteriorL1_add _ _).trans (add_le_add le_rfl ih)

theorem exteriorL1_smul (c : ℂ) (v : ⋀[ℂ]^4 SU7FundamentalCarrier) :
    exteriorL1 (c•v)≤complexAbs c*exteriorL1 v := by
  unfold exteriorL1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa using complexAbs_mul c ((su7ExteriorBasis 4).repr v i)

@[simp] theorem exteriorL1_basis (i : ExteriorBasisIndex 4) : exteriorL1 (su7ExteriorBasis 4 i)=1 := by
  classical
  simp [exteriorL1,Module.Basis.repr_self,Finsupp.single_apply,apply_ite,complexAbs,eq_comm]

/-- Single-occupancy generation: an arbitrary four-slot basis wedge is zero or a signed basis vector. -/
theorem basisWedge_bound (a : Fin 4→SU7MotherIndex) :
    exteriorL1 ((exteriorPower.ιMulti ℂ 4) (su7FundamentalBasis ∘ a))≤1 := by
  classical
  by_cases injective : Function.Injective a
  · have card : (Finset.image a Finset.univ).card=4 :=
      (Finset.card_image_of_injective Finset.univ injective).trans (Finset.card_fin 4)
    let s : ExteriorBasisIndex 4 := ⟨Finset.image a Finset.univ,card⟩
    let perm : Equiv.Perm (Fin 4) :=
      (Finset.orderIsoOfFin (Finset.image a Finset.univ) card).toEquiv.trans
        ((Equiv.setCongr Fintype.coe_image_univ).trans (Equiv.ofInjective a injective).symm)
    have sorted : (exteriorPower.ιMulti ℂ 4) ((su7FundamentalBasis ∘ a) ∘ perm)=su7ExteriorBasis 4 s := by
      rw [su7ExteriorBasis,exteriorPower.basis_apply,exteriorPower.ιMulti_family,Function.comp_assoc]
      congr 1
      funext i
      simp [perm,Equiv.apply_ofInjective_symm,s,Set.powersetCard.ofFinEmbEquiv_symm_apply]
      rfl
    rw [AlternatingMap.map_perm] at sorted
    rcases Int.units_eq_one_or perm.sign with hp|hp
    · simpa [hp] using (congrArg exteriorL1 sorted).le
    · have h:=congrArg exteriorL1 sorted
      simpa [hp] using h.le
  · have zero : (exteriorPower.ιMulti ℂ 4) (su7FundamentalBasis ∘ a)=0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => injective (Function.Injective.of_comp h))
    simp [zero]


theorem fundamental_action_basis (M : SU7MotherLieMatrix) (i : SU7MotherIndex) :
    fundamentalMotherLieAction M (su7FundamentalBasis i)=
      ∑ j : SU7MotherIndex,(M.val j i) • su7FundamentalBasis j := by
  ext j
  simp [fundamentalMotherLieAction,Matrix.mulVecLin,su7FundamentalBasis,Matrix.mulVec,
    dotProduct,Pi.single_apply,eq_comm]

def occupancy (i : ExteriorBasisIndex 4) (s : Fin 4) : SU7MotherIndex :=
  (exteriorPositionEquiv i s).val

theorem source_slot_expansion (M : SU7MotherLieMatrix) (i : ExteriorBasisIndex 4) :
    exteriorBasisLieAction 4 M i=
      ∑ s : Fin 4,∑ j : SU7MotherIndex,M.val j (occupancy i s) •
        (exteriorPower.ιMulti ℂ 4) (su7FundamentalBasis ∘ Function.update (occupancy i) s j) := by
  classical
  unfold exteriorBasisLieAction
  apply Finset.sum_congr rfl
  intro s hs
  have update : (fun t : Fin 4 => if t=s then
      fundamentalMotherLieAction M (su7FundamentalBasis (exteriorPositionEquiv i t).val)
      else su7FundamentalBasis (exteriorPositionEquiv i t).val)=
      Function.update (su7FundamentalBasis ∘ occupancy i) s
        (fundamentalMotherLieAction M (su7FundamentalBasis (occupancy i s))) := by
    funext t
    by_cases h : t=s <;> simp [h,occupancy,Function.update]
  rw [update,fundamental_action_basis,AlternatingMap.map_update_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [AlternatingMap.map_update_smul]
  congr 2
  funext t
  by_cases h : t=s <;> simp [h,Function.update]

/-- The source's four literal slot writes produce the bound; there is no supplied action matrix. -/
theorem exterior_action_column_bound (M : SU7MotherLieMatrix)
    (fundamental : ∀ j,∑ i : SU7MotherIndex,complexAbs (M.val i j)≤1)
    (input : ExteriorBasisIndex 4) : exteriorL1 (exteriorBasisLieAction 4 M input)≤4 := by
  rw [source_slot_expansion]
  calc
    _ ≤ ∑ s : Fin 4,exteriorL1 (∑ j : SU7MotherIndex,M.val j (occupancy input s) •
        (exteriorPower.ιMulti ℂ 4) (su7FundamentalBasis ∘ Function.update (occupancy input) s j)) :=
      exteriorL1_sum _ _
    _ ≤ ∑ s : Fin 4,∑ j : SU7MotherIndex,complexAbs (M.val j (occupancy input s)) := by
      apply Finset.sum_le_sum
      intro s hs
      refine (exteriorL1_sum _ _).trans ?_
      apply Finset.sum_le_sum
      intro j hj
      exact (exteriorL1_smul _ _).trans (by
        have h:=mul_le_mul_of_nonneg_left (basisWedge_bound (Function.update (occupancy input) s j))
          (complexAbs_nonnegative (M.val j (occupancy input s)))
        simpa using h)
    _ ≤ ∑ _s : Fin 4,(1 : ℝ) := Finset.sum_le_sum (fun s _ => fundamental (occupancy input s))
    _ = 4 := by norm_num

end LowEnergy.PreparationVacuumPrimitiveMatrix
