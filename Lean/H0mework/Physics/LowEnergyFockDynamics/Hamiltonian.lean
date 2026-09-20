import H0mework.Physics.LowEnergyFockDynamics.Response
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! A finite source Hamiltonian generates its unitary orbit and the original CAR evolution. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion
open scoped Matrix InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
local instance : NormedAlgebra ℚ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

def hamiltonianOperator (H : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H

def timeGenerator (H : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (-Complex.I) • hamiltonianOperator H

def timeEvolution (H : Matrix ι ι ℂ) (t : ℝ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  NormedSpace.exp (t • timeGenerator H)

theorem timeGenerator_skew (H : Matrix ι ι ℂ) (selfAdjoint : H.conjTranspose=H) :
    star (timeGenerator H)=-timeGenerator H := by
  have actual : star (hamiltonianOperator H)=hamiltonianOperator H := by
    change star ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H)=
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H
    rw [← map_star]
    exact congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) selfAdjoint
  simp only [timeGenerator,star_smul,actual,star_neg,Complex.star_def,Complex.conj_I,neg_neg]
  ext u i
  simp

theorem timeEvolution_unitary (H : Matrix ι ι ℂ) (selfAdjoint : H.conjTranspose=H) (t : ℝ) :
    timeEvolution H t ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star ((t : ℂ) • timeGenerator H)=-((t : ℂ) • timeGenerator H)
  rw [star_smul,timeGenerator_skew H selfAdjoint]
  simp
  ext u i
  rfl

theorem timeEvolution_pair (H : Matrix ι ι ℂ) (selfAdjoint : H.conjTranspose=H)
    (t : ℝ) (u v : EuclideanSpace ℂ ι) :
    inner ℂ (timeEvolution H t u) (timeEvolution H t v)=inner ℂ u v :=
  ContinuousLinearMap.inner_map_map_of_mem_unitary (timeEvolution_unitary H selfAdjoint t) u v

theorem timeEvolution_zero (H : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    timeEvolution H 0 u=u := by
  have zero : (0 : ℝ) • timeGenerator H=0 := by ext v i; simp
  rw [timeEvolution,zero,NormedSpace.exp_zero]
  rfl

theorem timeEvolution_derivative (H : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (timeEvolution H)
      (timeEvolution H t*timeGenerator H) t := by
  exact hasDerivAt_exp_smul_const (timeGenerator H) t

theorem timeEvolution_generator_commute (H : Matrix ι ι ℂ) (t : ℝ) :
    timeEvolution H t*timeGenerator H=timeGenerator H*timeEvolution H t := by
  have scaled : Commute ((t : ℝ) • timeGenerator H) (timeGenerator H) := by
    show ((t : ℝ) • timeGenerator H)*timeGenerator H=timeGenerator H*((t : ℝ) • timeGenerator H)
    ext u i
    simp
  exact scaled.exp_left.eq

def sourceWave (H : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) (t : ℝ) : ι → ℂ :=
  timeEvolution H t u

theorem sourceWave_derivative (H : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) (t : ℝ) :
    HasDerivAt (sourceWave H u) ((-Complex.I) • (H*ᵥsourceWave H u t)) t := by
  have orbit := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ ι) u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    t (timeEvolution_derivative H t)
  rw [timeEvolution_generator_commute] at orbit
  let forget := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)
  have coordinates := (forget.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t orbit
  convert! coordinates using 1

theorem original_hamiltonian_fock_evolution (H : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) (t : ℝ) :
    HasDerivAt (fun time => oneParticle (sourceWave H u time))
      ((-Complex.I) • secondQuantize H (oneParticle (sourceWave H u t))) t :=
  original_fock_schrodinger _ H t (sourceWave_derivative H u t)

theorem original_hamiltonian_current_evolution (H B : Matrix ι ι ℂ)
    (selfAdjoint : H.conjTranspose=H) (u : EuclideanSpace ℂ ι) (t : ℝ) :
    HasDerivAt (fun time => pairing (oneParticle (sourceWave H u time))
      (secondQuantize B (oneParticle (sourceWave H u time))))
      (Complex.I*pairing (oneParticle (sourceWave H u t))
        (secondQuantize H (secondQuantize B (oneParticle (sourceWave H u t))) -
          secondQuantize B (secondQuantize H (oneParticle (sourceWave H u t))))) t :=
  original_fock_current_derivative _ H B t selfAdjoint (sourceWave_derivative H u t)

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
