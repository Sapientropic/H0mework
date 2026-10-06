import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Free
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Continuity

/-! Complete source matter evolves on all of physical space, retaining the original Yukawa arrow. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open YangMills.FullPairing Triangular Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
noncomputable section
local instance : NormedAlgebra ℚ (Hilbert →L[ℂ] Hilbert) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Hilbert →L[ℂ] Hilbert) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem original_drift_continuous (point : BasePoint) :
    Continuous (fun momentum : Fin 3 → ℝ => operator (drift actual point momentum)) := by
  simp only [source_split,operator_add,← free_hamiltonian_drift,operator_smul]
  exact ((original_freeHamiltonian_continuous point).const_smul (-Complex.I)).add continuous_const

def physicalMomentum (frequency : Position) : Fin 3 → ℝ := fun j => 2*Real.pi*frequency j

theorem physicalMomentum_continuous : Continuous physicalMomentum := by
  unfold physicalMomentum
  fun_prop

def fullMatrices (point : BasePoint) (time : ℝ) (frequency : Position) : FiberOperators :=
  evolution actual point (physicalMomentum frequency) time

theorem fullMatrices_continuous (point : BasePoint) :
    Continuous (fun tx : ℝ × Position => fullMatrices point tx.1 tx.2) := by
  have generator : Continuous (fun tx : ℝ × Position =>
      operator (drift actual point (physicalMomentum tx.2))) :=
    (original_drift_continuous point).comp (physicalMomentum_continuous.comp continuous_snd)
  exact NormedSpace.exp_continuous.comp (continuous_fst.smul generator)

def sourceRate (point : BasePoint) : ℝ := ‖operator (interaction actual point)‖

theorem fullMatrices_bound (point : BasePoint) (time : ℝ) (frequency : Position) :
    ‖fullMatrices point time frequency‖≤1+|time| * sourceRate point :=
  complete_evolution_bound actual point (physicalMomentum frequency)
    (original_freeHamiltonian_selfAdjoint point _) time

def momentumFlow (point : BasePoint) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  liftedFamily (fullMatrices point) (fullMatrices_continuous point) (sourceRate point)
    (norm_nonneg _) (fullMatrices_bound point) time

theorem momentumFlow_ae (point : BasePoint) (time : ℝ) (initial : FullMatterL2) :
    momentumFlow point time initial=ᵐ[volume] fun frequency =>
      evolution actual point (physicalMomentum frequency) time (initial frequency) :=
  liftedFamily_ae (fullMatrices point) (fullMatrices_continuous point) (sourceRate point)
    (norm_nonneg _) (fullMatrices_bound point) time initial

theorem momentumFlow_norm (point : BasePoint) (time : ℝ) :
    ‖momentumFlow point time‖≤1+|time| * sourceRate point :=
  liftedFamily_norm (fullMatrices point) (fullMatrices_continuous point) (sourceRate point)
    (norm_nonneg _) (fullMatrices_bound point) time

theorem momentumFlow_zero (point : BasePoint) (initial : FullMatterL2) : momentumFlow point 0 initial=initial := by
  apply Lp.ext
  filter_upwards [momentumFlow_ae point 0 initial] with frequency atFrequency
  rw [atFrequency,evolution_zero]
  rfl

theorem momentumFlow_add (point : BasePoint) (first second : ℝ) (initial : FullMatterL2) :
    momentumFlow point (first+second) initial=momentumFlow point first (momentumFlow point second initial) := by
  apply Lp.ext
  filter_upwards [momentumFlow_ae point (first+second) initial,
    momentumFlow_ae point first (momentumFlow point second initial),
    momentumFlow_ae point second initial] with frequency whole outer inner
  rw [whole,outer,inner,evolution_add]
  rfl

theorem momentumFlow_stronglyContinuous (point : BasePoint) (initial : FullMatterL2) :
    Continuous (fun time => momentumFlow point time initial) :=
  liftedFamily_stronglyContinuous (fullMatrices point) (fullMatrices_continuous point) (sourceRate point)
    (norm_nonneg _) (fullMatrices_bound point) initial

def fourier : FullMatterL2 ≃ₗᵢ[ℂ] FullMatterL2 := Lp.fourierTransformₗᵢ Position Hilbert

def spatialFlow (point : BasePoint) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((momentumFlow point time).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem spatialFlow_fourier (point : BasePoint) (time : ℝ) (initial : FullMatterL2) :
    fourier (spatialFlow point time initial)=momentumFlow point time (fourier initial) :=
  fourier.apply_symm_apply _

theorem spatialFlow_fourier_ae (point : BasePoint) (time : ℝ) (initial : FullMatterL2) :
    fourier (spatialFlow point time initial)=ᵐ[volume] fun frequency =>
      evolution actual point (physicalMomentum frequency) time (fourier initial frequency) := by
  rw [spatialFlow_fourier]
  exact momentumFlow_ae point time (fourier initial)

theorem spatialFlow_zero (point : BasePoint) (initial : FullMatterL2) : spatialFlow point 0 initial=initial := by
  apply fourier.injective
  rw [spatialFlow_fourier,momentumFlow_zero]

theorem spatialFlow_add (point : BasePoint) (first second : ℝ) (initial : FullMatterL2) :
    spatialFlow point (first+second) initial=spatialFlow point first (spatialFlow point second initial) := by
  apply fourier.injective
  rw [spatialFlow_fourier,spatialFlow_fourier,spatialFlow_fourier,momentumFlow_add]

theorem spatialFlow_inverse (point : BasePoint) (time : ℝ) (initial : FullMatterL2) :
    spatialFlow point (-time) (spatialFlow point time initial)=initial := by
  rw [← spatialFlow_add,neg_add_cancel,spatialFlow_zero]

theorem spatialFlow_norm (point : BasePoint) (time : ℝ) :
    ‖spatialFlow point time‖≤1+|time| * sourceRate point := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by dsimp [sourceRate]; positivity)
  intro initial
  change ‖fourier.symm (momentumFlow point time (fourier initial))‖≤_
  rw [fourier.symm.norm_map]
  exact ((momentumFlow point time).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (momentumFlow_norm point time) (norm_nonneg _)).trans_eq
      (by rw [fourier.norm_map]))

theorem spatialFlow_stronglyContinuous (point : BasePoint) (initial : FullMatterL2) :
    Continuous (fun time => spatialFlow point time initial) :=
  fourier.symm.continuous.comp (momentumFlow_stronglyContinuous point (fourier initial))

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
