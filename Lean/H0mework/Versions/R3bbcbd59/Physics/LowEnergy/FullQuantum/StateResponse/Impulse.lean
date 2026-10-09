import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.StateResponse.Connected

/-! A genuine finite-coupling full-Fock exponential pulse generates the Kubo
word as its parameter derivative. Its inverse remains algebraic. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
open QuantizationCheck.Fermion Fermion StateGreen
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
local instance : Fintype (Finset ι) := Fintype.ofFinite _
local instance : CompleteSpace (Fock ι) := inferInstanceAs (CompleteSpace (Finset ι → ℂ))
local instance : NormedAlgebra ℚ (Fock ι →L[ℂ] Fock ι) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Fock ι →L[ℂ] Fock ι) := NormedAlgebra.restrictScalars ℝ ℂ _

def quantumOperator (A : Matrix ι ι ℂ) : Fock ι →L[ℂ] Fock ι :=
  LinearMap.toContinuousLinearMap (quantize A)

def pulseGenerator (R : Matrix ι ι ℂ) : Fock ι →L[ℂ] Fock ι :=
  (-Complex.I) • quantumOperator R

def pulse (R : Matrix ι ι ℂ) (epsilon : ℝ) : Fock ι →L[ℂ] Fock ι :=
  NormedSpace.exp (epsilon • pulseGenerator R)

theorem pulse_zero (R : Matrix ι ι ℂ) : pulse R 0=1 := by
  have zero : (0 : ℝ) • pulseGenerator R=0 := by ext v i; simp
  rw [pulse,zero,NormedSpace.exp_zero]

theorem pulse_add (R : Matrix ι ι ℂ) (first second : ℝ) :
    pulse R (first+second)=pulse R first*pulse R second := by
  have addition : (first+second) • pulseGenerator R=first • pulseGenerator R+second • pulseGenerator R := by
    ext state occupied
    simp
    ring
  rw [pulse,addition]
  apply NormedSpace.exp_add_of_commute
  show (first • pulseGenerator R)*(second • pulseGenerator R)=
    (second • pulseGenerator R)*(first • pulseGenerator R)
  ext v i
  simp
  ring

theorem pulse_inverse (R : Matrix ι ι ℂ) (epsilon : ℝ) : pulse R (-epsilon)*pulse R epsilon=1 := by
  rw [← pulse_add,neg_add_cancel,pulse_zero]

theorem pulse_derivative (R : Matrix ι ι ℂ) (epsilon : ℝ) :
    HasDerivAt (pulse R) (pulse R epsilon*pulseGenerator R) epsilon :=
  hasDerivAt_exp_smul_const (pulseGenerator R) epsilon

def pulseObservable (R B : Matrix ι ι ℂ) (epsilon : ℝ) : Fock ι →L[ℂ] Fock ι :=
  pulse R (-epsilon)*quantumOperator B*pulse R epsilon

theorem pulseObservable_derivative (R B : Matrix ι ι ℂ) :
    HasDerivAt (pulseObservable R B)
      (Complex.I • (quantumOperator R*quantumOperator B-quantumOperator B*quantumOperator R)) 0 := by
  have right := pulse_derivative R 0
  have left := (pulse_derivative R (-0)).scomp 0 (hasDerivAt_neg 0)
  have generated := (left.mul_const (quantumOperator B)).mul right
  convert! generated using 1
  ext v i
  simp [pulse_zero,pulseGenerator]
  ring

def readOperatorLinear (w : ι → ℂ) : (Fock ι →L[ℂ] Fock ι) →ₗ[ℂ] ℂ where
  toFun A := read w A.toLinearMap
  map_add' A B := (read w).map_add A.toLinearMap B.toLinearMap
  map_smul' c A := (read w).map_smul c A.toLinearMap

def readOperator (w : ι → ℂ) : (Fock ι →L[ℂ] Fock ι) →L[ℂ] ℂ :=
  (readOperatorLinear w).toContinuousLinearMap

def pulseRead (w : ι → ℂ) (R B : Matrix ι ι ℂ) (epsilon : ℝ) : ℂ :=
  readOperator w (pulseObservable R B epsilon)

theorem pulseRead_derivative (w : ι → ℂ) (R B : Matrix ι ι ℂ) :
    HasDerivAt (pulseRead w R B) (read w (kuboWord R B)) 0 := by
  have generated := ((readOperator w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (pulseObservable_derivative R B)
  convert! generated using 1

theorem pulseRead_connected (w : ι → ℂ) (R B : Matrix ι ι ℂ) :
    HasDerivAt (pulseRead w R B) (Complex.I*(connected w R B-connected w B R)) 0 := by
  rw [← kubo_generated]
  exact pulseRead_derivative w R B

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.StateResponse
