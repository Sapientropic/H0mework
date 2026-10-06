import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailConfigurationMoments
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylDecay

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailFourier
open PreparationVacuumWholeTail PreparationVacuumTailSupport PreparationVacuumCanonicalMoyal PreparationVacuumLocalizedTail
open PreparationVacuumWeyl PreparationActualFactor CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev ArrayBound := ℕ → ℝ

def coordinateVector (i : Fin 100) : PhysicalMomentum := WithLp.toLp 2 (Pi.single i 1)

theorem coordinate_expansion (v : PhysicalMomentum) :
    v=∑ i : Fin 100,v i • coordinateVector i := by
  ext j
  simp [coordinateVector,Pi.single_apply]

theorem coordinate_multilinear_norm (m : ℕ)
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin m=>PhysicalMomentum) ℝ)
    (C : ℝ) (positive : 0 ≤ C)
    (actual : ∀ w : Fin m→Fin 100,|D (coordinateVector∘w)|≤C) :
    ‖D‖≤100^m*C := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) positive)
  intro v
  have same : v=(fun a=>∑ i : Fin 100,v a i • coordinateVector i) :=
    funext (fun a=>coordinate_expansion (v a))
  have expanded : D v=∑ w : Fin m→Fin 100,D (fun a=>v a (w a) • coordinateVector (w a)) := by
    conv_lhs => rw [same]
    rw [D.map_sum]
  rw [expanded]
  calc
    ‖∑ w : Fin m→Fin 100,D (fun a=>v a (w a) • coordinateVector (w a))‖
      ≤∑ w : Fin m→Fin 100,‖D (fun a=>v a (w a) • coordinateVector (w a))‖ := norm_sum_le _ _
    _≤∑ _w : Fin m→Fin 100,(∏ a : Fin m,‖v a‖)*C := by
      apply Finset.sum_le_sum
      intro w _
      rw [D.map_smul_univ,norm_smul]
      have prodBound : ‖∏ a : Fin m,v a (w a)‖≤∏ a : Fin m,‖v a‖ := by
        rw [norm_prod]
        exact Finset.prod_le_prod (fun _a _=>norm_nonneg _)
          (fun a _=>PiLp.norm_apply_le (v a) (w a))
      exact mul_le_mul prodBound (actual w) (norm_nonneg _) (Finset.prod_nonneg (fun _a _=>norm_nonneg _))
    _=100^m*C*∏ a : Fin m,‖v a‖ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

def tailRealSlice (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) : PhysicalMomentum → ℝ :=
  fun x=>energyTailFor B (flatPosition x,p)

def positionInclusion : PhysicalMomentum →L[ℝ] Phase :=
  (ContinuousLinearMap.inl ℝ FlatConfiguration PhysicalMomentum).comp flatPosition.toContinuousLinearMap

theorem tailRealSlice_smooth (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) :
    ContDiff ℝ ∞ (tailRealSlice B p) :=
  (energyTailFor_global_smooth B).comp (flatPosition.contDiff.prodMk contDiff_const)

theorem positionInclusion_coordinate (i : Fin 100) : positionInclusion (coordinateVector i)=qDirection i := rfl

theorem tailRealSlice_coordinate (B : ℕ → Fin 5 → ArrayBound) (m : ℕ)
    (w : Fin m→Fin 100) (p x : PhysicalMomentum) :
    iteratedFDeriv ℝ m (tailRealSlice B p) x (coordinateVector∘w)=
      positionJet B m (fun a=>(w a,false)) p (flatPosition x) := by
  let shifted : Phase → ℝ := fun y=>energyTailFor B (y+(0,p))
  have smooth : ContDiff ℝ ∞ shifted:=
    (energyTailFor_global_smooth B).comp (contDiff_id.add contDiff_const)
  have same : tailRealSlice B p=shifted ∘ positionInclusion := by
    funext y
    simp [tailRealSlice,shifted,positionInclusion]
  rw [same,positionInclusion.iteratedFDeriv_comp_right smooth x
    (by exact_mod_cast (le_top : (m : ℕ∞)≤⊤))]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  dsimp only [shifted]
  rw [iteratedFDeriv_comp_add_right]
  have point : positionInclusion x+(0,p)=(flatPosition x,p) := by simp [positionInclusion]
  rw [point]
  change iteratedFDeriv ℝ m (energyTailFor B) (flatPosition x,p)
    (fun a=>positionInclusion (coordinateVector (w a)))=_
  rw [positionJet,tailJet_actual]
  rfl

def tailDerivativeBound (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) : ℝ := 100^m*originalTailBudget B m

theorem tailRealSlice_derivative_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (N m : ℕ) (order : m≤N)
    (input : UnitEnergyInputs B N) (p x : PhysicalMomentum) :
    ‖iteratedFDeriv ℝ m (tailRealSlice B p) x‖≤tailDerivativeBound B m := by
  apply coordinate_multilinear_norm m _ _ (originalTailBudget_nonnegative B positive m)
  intro w
  rw [tailRealSlice_coordinate]
  by_cases inside : flatPosition x∈thetaPositionClosed
  · exact source_positionJet_bound B positive N m order _ input p (flatPosition x) inside
  · have zero:=tailJet_position_zero B m (fun a=>(w a,false)) (flatPosition x,p) inside
    simpa only [positionJet,zero,abs_zero] using originalTailBudget_nonnegative B positive m

end LowEnergy.PreparationVacuumTailFourier
