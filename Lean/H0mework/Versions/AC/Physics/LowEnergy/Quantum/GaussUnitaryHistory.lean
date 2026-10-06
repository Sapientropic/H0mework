import H0mework.Physics.LowEnergy.Quantum.SourceFamilyOperator
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussCARHistory

/-! The same finite H0 compression occurrence retains its unitary time algebra. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussUnitaryHistory
open GaussCoreHilbert GaussDiagonalHistory SourceFamilyOperator
open SourceFamilyHilbert (Hilbert embed pair inner_coe)
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped Topology InnerProductSpace

abbrev Index := Finset diagonal.domain
def sourceFilter : Ultrafilter Index := WeakCoreEvolution.sourceFilter diagonal
abbrev HistorySpace := Hilbert H sourceFilter
def inclusion : H →ₗᵢ[ℂ] HistorySpace := embed sourceFilter

def finiteTime (t : ℝ) : Operator Index H :=
  ⟨fun F => FiniteCoreEvolution.evolution diagonal F t, 1, zero_le_one, fun F x => by
    rw [FiniteCoreEvolution.evolution_norm diagonal diagonal_pair, one_mul]⟩

def time (t : ℝ) : HistorySpace →L[ℂ] HistorySpace := lift sourceFilter (finiteTime t)
def reader (A : H →L[ℂ] H) : HistorySpace →L[ℂ] HistorySpace := lift sourceFilter (constant A)

local instance : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem finite_add (F : Index) (s t : ℝ) :
    FiniteCoreEvolution.evolution diagonal F (s+t) =
      FiniteCoreEvolution.evolution diagonal F s * FiniteCoreEvolution.evolution diagonal F t := by
  change NormedSpace.exp ((s+t) • ((-Complex.I) • FiniteCoreEvolution.compression diagonal F)) = _
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute
    ((Commute.refl ((-Complex.I) • FiniteCoreEvolution.compression diagonal F)).smul_left s |>.smul_right t)

theorem time_zero : time 0 = 1 := by
  apply (lift_congr sourceFilter (finiteTime 0) (constant 1) ?_).trans (lift_identity sourceFilter)
  intro F
  change NormedSpace.exp ((0 : ℝ) • ((-Complex.I) • FiniteCoreEvolution.compression diagonal F)) = 1
  rw [zero_smul, NormedSpace.exp_zero]

theorem time_add (s t : ℝ) : time (s+t) = time s * time t := by
  apply (lift_congr sourceFilter (finiteTime (s+t)) (comp (finiteTime s) (finiteTime t)) ?_).trans
    (lift_comp sourceFilter _ _)
  exact fun F => finite_add F s t

theorem time_inverse_left (t : ℝ) : time (-t) * time t = 1 := by
  rw [← time_add, neg_add_cancel, time_zero]
theorem time_inverse_right (t : ℝ) : time t * time (-t) = 1 := by
  rw [← time_add, add_neg_cancel, time_zero]

theorem time_norm (t : ℝ) (f : HistorySpace) : ‖time t f‖ = ‖f‖ :=
  lift_isometry sourceFilter (finiteTime t)
    (fun F x => FiniteCoreEvolution.evolution_norm diagonal diagonal_pair F t x) f

def timeEquiv (t : ℝ) : HistorySpace ≃ₗᵢ[ℂ] HistorySpace where
  toLinearEquiv := {
    toLinearMap := (time t).toLinearMap
    invFun := time (-t)
    left_inv := fun x => congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A x) (time_inverse_left t)
    right_inv := fun x => congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A x) (time_inverse_right t) }
  norm_map' := time_norm t

theorem time_pair (t : ℝ) (f g : HistorySpace) :
    inner ℂ (time t f) g = inner ℂ f (time (-t) g) := by
  have h := (timeEquiv t).inner_map_map f (time (-t) g)
  have hi : time t (time (-t) g) = g :=
    congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A g) (time_inverse_right t)
  change inner ℂ (time t f) (time t (time (-t) g)) = _ at h
  rwa [hi] at h

theorem reader_inclusion (A : H →L[ℂ] H) (x : H) : reader A (inclusion x) = inclusion (A x) :=
  lift_constant_embed sourceFilter A x

theorem weak_readback (t : ℝ) (x y : H) :
    inner ℂ (time t (inclusion x)) (inclusion y) = inner ℂ (GaussDiagonalHistory.history t x) y := by
  change inner ℂ (lift sourceFilter (finiteTime t) ((SourceFamilyHilbert.constant sourceFilter x) : HistorySpace))
    ((SourceFamilyHilbert.constant sourceFilter y) : HistorySpace) = _
  rw [lift_coe, inner_coe]
  change _ = inner ℂ (WeakCoreEvolution.weakEvolution diagonal diagonal_pair t x) y
  rw [WeakCoreEvolution.weak_evolution_pair]
  rfl

theorem reader_one : reader (1 : H →L[ℂ] H) = 1 := lift_identity (E := H) sourceFilter

theorem reader_zero : reader (0 : H →L[ℂ] H) = 0 := lift_zero (E := H) sourceFilter

theorem reader_add (A B : H →L[ℂ] H) : reader (A+B) = reader A + reader B :=
  constant_add sourceFilter A B

theorem reader_mul (A B : H →L[ℂ] H) : reader (A*B) = reader A * reader B :=
  constant_mul sourceFilter A B

def heisenberg (t : ℝ) (A : H →L[ℂ] H) : HistorySpace →L[ℂ] HistorySpace :=
  time (-t) * reader A * time t

theorem heisenberg_identity (t : ℝ) : heisenberg t 1 = 1 := by
  rw [heisenberg, reader_one, mul_one, time_inverse_left]

theorem heisenberg_add (t : ℝ) (A B : H →L[ℂ] H) :
    heisenberg t (A+B) = heisenberg t A + heisenberg t B := by
  simp only [heisenberg, reader_add, mul_add, add_mul]

private theorem sandwich_mul {R : Type*} [Monoid R] (u v a b : R) (h : u*v=1) :
    v*(a*b)*u = (v*a*u)*(v*b*u) := by
  symm
  calc
    (v*a*u)*(v*b*u) = v*a*((u*v)*(b*u)) := by simp only [mul_assoc]
    _ = v*a*(b*u) := by rw [h, one_mul]
    _ = v*(a*b)*u := by simp only [mul_assoc]

theorem heisenberg_mul (t : ℝ) (A B : H →L[ℂ] H) :
    heisenberg t (A*B) = heisenberg t A * heisenberg t B := by
  unfold heisenberg
  rw [reader_mul]
  exact sandwich_mul (time t) (time (-t)) (reader A) (reader B) (time_inverse_right t)

theorem heisenberg_zero (t : ℝ) : heisenberg t 0 = 0 := by
  simp only [heisenberg, reader_zero, mul_zero, zero_mul]

theorem car_all_time (t : ℝ) (i j : Mode) :
    heisenberg t (GaussCARHistory.annihilate i) * heisenberg t (GaussCARHistory.create j) +
      heisenberg t (GaussCARHistory.create j) * heisenberg t (GaussCARHistory.annihilate i) =
        if i=j then 1 else 0 := by
  calc
    _ = heisenberg t (GaussCARHistory.annihilate i * GaussCARHistory.create j) +
        heisenberg t (GaussCARHistory.create j * GaussCARHistory.annihilate i) :=
      congrArg₂ (· + ·) (heisenberg_mul t _ _).symm (heisenberg_mul t _ _).symm
    _ = heisenberg t (GaussCARHistory.annihilate i * GaussCARHistory.create j +
        GaussCARHistory.create j * GaussCARHistory.annihilate i) := (heisenberg_add t _ _).symm
    _ = heisenberg t (if i=j then 1 else 0) := congrArg (heisenberg t) (GaussCARHistory.car i j)
    _ = _ := by
      split_ifs
      · exact heisenberg_identity t
      · exact heisenberg_zero t

#print axioms time_add
#print axioms time_norm
#print axioms weak_readback
#print axioms car_all_time
end LowEnergy.GaussUnitaryHistory
