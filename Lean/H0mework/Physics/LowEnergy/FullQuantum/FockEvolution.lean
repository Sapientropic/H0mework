import H0mework.Physics.LowEnergy.FullQuantum.CAR

/-! The same full source generator acts on every finite occupation sector. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum
open ProofFreeRicherAnholonomicSource StageNineHolonomicField QuantizationCheck.Fermion
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance : Fintype (Finset Quantum.Index) := Fintype.ofFinite _
local instance : CompleteSpace (Fock Quantum.Index) :=
  inferInstanceAs (CompleteSpace (Finset Quantum.Index → ℂ))
local instance : NormedAlgebra ℚ (Fock Quantum.Index →L[ℂ] Fock Quantum.Index) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Fock Quantum.Index →L[ℂ] Fock Quantum.Index) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

def fockGenerator (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : Fock Quantum.Index →L[ℂ] Fock Quantum.Index :=
  (-Complex.I) • LinearMap.toContinuousLinearMap (quantumGenerator C p k)

def fockEvolution (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) : Fock Quantum.Index →L[ℂ] Fock Quantum.Index :=
  NormedSpace.exp (t • fockGenerator C p k)

theorem fockEvolution_zero (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) : fockEvolution C p k 0 = 1 := by
  have zero : (0 : ℝ) • fockGenerator C p k = 0 := by ext v i; simp
  rw [fockEvolution, zero, NormedSpace.exp_zero]

theorem fockEvolution_add (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t s : ℝ) :
    fockEvolution C p k (t+s) = fockEvolution C p k t * fockEvolution C p k s := by
  have scalarAdd : (t+s) • fockGenerator C p k =
      t • fockGenerator C p k + s • fockGenerator C p k := by
    ext v i
    simp
    ring
  unfold fockEvolution
  rw [scalarAdd]
  apply NormedSpace.exp_add_of_commute
  show (t • fockGenerator C p k) * (s • fockGenerator C p k) =
    (s • fockGenerator C p k) * (t • fockGenerator C p k)
  ext v i
  simp
  ring

theorem fockEvolution_inverse (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    fockEvolution C p k (-t) * fockEvolution C p k t = 1 := by
  rw [← fockEvolution_add, neg_add_cancel, fockEvolution_zero]

theorem fockEvolution_derivative (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fockEvolution C p k)
      (fockGenerator C p k * fockEvolution C p k t) t := by
  have generated := hasDerivAt_exp_smul_const (fockGenerator C p k) t
  have commute : Commute (t • fockGenerator C p k) (fockGenerator C p k) := by
    show (t • fockGenerator C p k) * fockGenerator C p k =
      fockGenerator C p k * (t • fockGenerator C p k)
    ext v i
    simp
  rw [commute.exp_left.eq] at generated
  exact generated

theorem original_allFock_evolution (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (state : Fock Quantum.Index) :
    HasDerivAt (fun time => fockEvolution C p k time state)
      ((-Complex.I) • secondQuantize (Quantum.operatorMatrix (hamiltonian C p k))
        (fockEvolution C p k t state)) t := by
  let evaluate := (ContinuousLinearMap.apply ℂ (Fock Quantum.Index) state).restrictScalars ℝ
  have generated := evaluate.hasFDerivAt.comp_hasDerivAt t (fockEvolution_derivative C p k t)
  change HasDerivAt (fun time => fockEvolution C p k time state)
    (fockGenerator C p k (fockEvolution C p k t state)) t at generated
  simpa only [fockGenerator, smul_apply,
    LinearMap.coe_toContinuousLinearMap', quantumGenerator, Fermion.quantize_apply] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum
