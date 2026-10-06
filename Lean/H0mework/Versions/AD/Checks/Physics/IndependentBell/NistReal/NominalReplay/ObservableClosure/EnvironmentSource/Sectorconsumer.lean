import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.EnvironmentSource.Sectorsource

set_option autoImplicit false

namespace P23.EnvironmentSource.Sector.Consumer

open Matrix
open P23.GaussianWindow P23.GaussianWindow.NativeEffects
open scoped BigOperators ComplexOrder
noncomputable section

def environmentJointNoClick (dA dB : EnvironmentPrim) (a b : ℝ) : NumberConservingEffect where
  block n := pairedBlock (P23.EnvironmentSource.gamma dA a n) (P23.EnvironmentSource.gamma dB b n)
  positive n := (pairedBlock_bounds (P23.EnvironmentSource.gamma_bounds dA a n).1
    (P23.EnvironmentSource.gamma_bounds dA a n).2
    (P23.EnvironmentSource.gamma_bounds dB b n).1 (P23.EnvironmentSource.gamma_bounds dB b n).2).1
  complement_positive n := (pairedBlock_bounds (P23.EnvironmentSource.gamma_bounds dA a n).1
    (P23.EnvironmentSource.gamma_bounds dA a n).2
    (P23.EnvironmentSource.gamma_bounds dB b n).1 (P23.EnvironmentSource.gamma_bounds dB b n).2).2

def generatedMatrix (s : RawKernel) (dA dB : EnvironmentPrim) (a b : ℝ) : Matrix Bool Bool ℂ :=
  (pairMatrix s)ᴴ * noClickGram dA a * pairMatrix s * (noClickGram dB b)ᵀ

theorem environment_sector_identity (s : RawKernel) (dA dB : EnvironmentPrim)
    (a b : ℝ) (n : ℕ) :
    sectorBorn s (environmentJointNoClick dA dB a b) n =
      (sourceZ s * symmetricTrace (generatedMatrix s dA dB a b) n).re := by
  have h := paired_sector_trace s (noClickGram dA a) (noClickGram dB b) n
  exact congrArg Complex.re h

theorem actual_ports_sector_consumer (s : RawKernel) (dA dB : EnvironmentPrim) (a b : ℝ) :
    ∀ n : ℕ,
      (environmentJointNoClick dA dB a b).block n =
        pairedBlock ((numberPorts dA a n)ᴴ * numberPorts dA a n)
          ((numberPorts dB b n)ᴴ * numberPorts dB b n) ∧
      sectorBorn s (environmentJointNoClick dA dB a b) n =
        (sourceZ s * symmetricTrace (generatedMatrix s dA dB a b) n).re ∧
      0 ≤ sectorBorn s (environmentJointNoClick dA dB a b) n ∧
      sectorBorn s (environmentJointNoClick dA dB a b) n ≤ sectorMass s n := by
  intro n
  refine ⟨?_, environment_sector_identity s dA dB a b n,
    (sectorBorn_bounds s (environmentJointNoClick dA dB a b) n).1,
    (sectorBorn_bounds s (environmentJointNoClick dA dB a b) n).2⟩
  change pairedBlock (P23.EnvironmentSource.gamma dA a n) (P23.EnvironmentSource.gamma dB b n) = _
  rw [P23.EnvironmentSource.gamma_port_born, P23.EnvironmentSource.gamma_port_born]

theorem sector_source_consumer (s : RawKernel) (dA dB : EnvironmentPrim) (a b : ℝ) :
    symmetricTrace (generatedMatrix s dA dB a b) 0 = 1 ∧
      symmetricTrace (generatedMatrix s dA dB a b) 1 = Matrix.trace (generatedMatrix s dA dB a b) ∧
      ∀ n : ℕ,
        sectorBorn s (environmentJointNoClick dA dB a b) n =
          (sourceZ s * symmetricTrace (generatedMatrix s dA dB a b) n).re ∧
        0 ≤ sectorBorn s (environmentJointNoClick dA dB a b) n ∧
        sectorBorn s (environmentJointNoClick dA dB a b) n ≤ sectorMass s n := by
  refine ⟨symmetricTrace_zero _, symmetricTrace_one _, ?_⟩
  intro n
  exact ⟨environment_sector_identity s dA dB a b n,
    (sectorBorn_bounds s (environmentJointNoClick dA dB a b) n).1,
    (sectorBorn_bounds s (environmentJointNoClick dA dB a b) n).2⟩

end
end P23.EnvironmentSource.Sector.Consumer
