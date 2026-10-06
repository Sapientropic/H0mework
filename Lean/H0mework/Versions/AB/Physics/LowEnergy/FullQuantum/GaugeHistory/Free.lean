import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Flow

/-! The actual complete free Dirac flow supplies the spatial interaction picture. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace Triangular YangMills.FullPairing Stage9C.Material.SpinPair
noncomputable section
local instance freeReal : NormedAlgebra ℝ FiberOperators := NormedAlgebra.restrictScalars ℝ ℂ _
local instance freeRational : NormedAlgebra ℚ FiberOperators := NormedAlgebra.restrictScalars ℚ ℂ _

def freeMatrices (time : ℝ) (frequency : Position) : FiberOperators :=
  freeEvolution actual 0 (physicalMomentum frequency) time

theorem freeMatrices_continuous : Continuous (fun tx : ℝ × Position => freeMatrices tx.1 tx.2) := by
  have coefficients : Continuous (fun frequency : Position => operator (freeDrift actual 0 (physicalMomentum frequency))) := by
    simp only [← free_hamiltonian_drift,operator_smul]
    exact ((original_freeHamiltonian_continuous 0).comp physicalMomentum_continuous).const_smul (-Complex.I)
  exact NormedSpace.exp_continuous.comp
    ((Complex.continuous_ofReal.comp continuous_fst).smul (coefficients.comp continuous_snd))

theorem freeMatrices_bound (time : ℝ) (frequency : Position) : ‖freeMatrices time frequency‖≤1+|time| * 0 := by
  simpa only [freeMatrices,mul_zero,add_zero] using!
    freeEvolution_norm_le_one actual 0 (physicalMomentum frequency) (original_freeHamiltonian_selfAdjoint 0 _) time

def momentumFree (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  liftedFamily freeMatrices freeMatrices_continuous 0 (by norm_num) freeMatrices_bound time

theorem momentumFree_ae (time : ℝ) (initial : FullMatterL2) :
    momentumFree time initial=ᵐ[volume] fun frequency => freeMatrices time frequency (initial frequency) :=
  liftedFamily_ae freeMatrices freeMatrices_continuous 0 (by norm_num) freeMatrices_bound time initial

theorem momentumFree_norm (time : ℝ) : ‖momentumFree time‖≤1 := by
  simpa only [momentumFree,mul_zero,add_zero] using!
    liftedFamily_norm freeMatrices freeMatrices_continuous 0 (by norm_num) freeMatrices_bound time

theorem momentumFree_zero (initial : FullMatterL2) : momentumFree 0 initial=initial := by
  apply Lp.ext
  filter_upwards [momentumFree_ae 0 initial] with frequency value
  rw [value,freeMatrices,freeEvolution,flow_zero]
  rfl

theorem momentumFree_add (first second : ℝ) (initial : FullMatterL2) :
    momentumFree (first+second) initial=momentumFree first (momentumFree second initial) := by
  apply Lp.ext
  filter_upwards [momentumFree_ae (first+second) initial,momentumFree_ae first (momentumFree second initial),
    momentumFree_ae second initial] with frequency whole outer inside
  rw [whole,outer,inside,freeMatrices,freeEvolution,flow_add]
  rfl

theorem momentumFree_continuous (initial : FullMatterL2) : Continuous (fun time => momentumFree time initial) :=
  liftedFamily_stronglyContinuous freeMatrices freeMatrices_continuous 0 (by norm_num) freeMatrices_bound initial

def spatialFree (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((momentumFree time).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem spatialFree_fourier (time : ℝ) (initial : FullMatterL2) :
    fourier (spatialFree time initial)=momentumFree time (fourier initial) := fourier.apply_symm_apply _

theorem spatialFree_zero (initial : FullMatterL2) : spatialFree 0 initial=initial := by
  apply fourier.injective
  rw [spatialFree_fourier,momentumFree_zero]

theorem spatialFree_add (first second : ℝ) (initial : FullMatterL2) :
    spatialFree (first+second) initial=spatialFree first (spatialFree second initial) := by
  apply fourier.injective
  rw [spatialFree_fourier,spatialFree_fourier,spatialFree_fourier,momentumFree_add]

theorem spatialFree_inverse (time : ℝ) (initial : FullMatterL2) :
    spatialFree (-time) (spatialFree time initial)=initial := by
  rw [← spatialFree_add,neg_add_cancel,spatialFree_zero]

theorem spatialFree_norm (time : ℝ) : ‖spatialFree time‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro initial
  change ‖fourier.symm (momentumFree time (fourier initial))‖≤_
  rw [fourier.symm.norm_map,one_mul]
  exact ((momentumFree time).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (momentumFree_norm time) (norm_nonneg _)).trans_eq
      (by rw [one_mul,fourier.norm_map]))

theorem spatialFree_norm_eq (time : ℝ) (initial : FullMatterL2) : ‖spatialFree time initial‖=‖initial‖ := by
  have contract (s : ℝ) (v : FullMatterL2) : ‖spatialFree s v‖≤‖v‖ :=
    ((spatialFree s).le_opNorm v).trans ((mul_le_mul_of_nonneg_right (spatialFree_norm s) (norm_nonneg v)).trans_eq (one_mul _))
  apply le_antisymm (contract time initial)
  have reverse := contract (-time) (spatialFree time initial)
  rwa [spatialFree_inverse] at reverse

theorem spatialFree_continuous (initial : FullMatterL2) : Continuous (fun time => spatialFree time initial) :=
  fourier.symm.continuous.comp (momentumFree_continuous (fourier initial))

def freeUnitary (time : ℝ) : FullMatterL2 ≃ₗᵢ[ℂ] FullMatterL2 where
  toFun := spatialFree time
  invFun := spatialFree (-time)
  map_add' := (spatialFree time).map_add
  map_smul' := (spatialFree time).map_smul
  left_inv := spatialFree_inverse time
  right_inv initial := by simpa only [neg_neg] using spatialFree_inverse (-time) initial
  norm_map' := spatialFree_norm_eq time

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
