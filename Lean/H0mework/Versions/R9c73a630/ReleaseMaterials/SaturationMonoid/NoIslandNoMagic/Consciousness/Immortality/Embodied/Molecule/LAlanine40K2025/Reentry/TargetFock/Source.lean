import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock.Reifier
import H0mework.Chemistry.LAlanineEntropy.JointEnergyReadout

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock
open Lean Elab Term Command Inertia.SourceParsing Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator

generateOriginalM3Fock

noncomputable section
def fockRat (i j : Basis) : ℚ :=
  let entry := (upperRows[min i.val j.val]!)[max i.val j.val-min i.val j.val]!
  (entry.1 : ℚ)/entry.2

theorem fock_rat_symmetric (i j : Basis) : fockRat i j=fockRat j i := by
  simp only [fockRat,min_comm,max_comm]

def fock : Matrix Basis Basis ℂ := fun i j => ((fockRat i j : ℝ) : ℂ)
def frame : Matrix Basis Basis ℂ := fun i j => (UnifiedOrbitals.Frame.realInverse i j : ℂ)

theorem fock_hermitian : fock.IsHermitian := by
  ext i j
  change star (((fockRat j i : ℚ) : ℝ) : ℂ)=(((fockRat i j : ℚ) : ℝ) : ℂ)
  rw [Complex.star_def,Complex.conj_ofReal,fock_rat_symmetric]

def rawPullback : Matrix Basis Basis ℂ := frame*fock*frame
def hamiltonian : Matrix Basis Basis ℂ := (1/2 : ℝ) • (rawPullback+star rawPullback)
def sourceLift (rho : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  (1/2 : ℝ) • (frame*rho*frame+star (frame*rho*frame))

theorem hamiltonian_hermitian : hamiltonian.IsHermitian := by
  have sum : (rawPullback+star rawPullback).IsHermitian := by
    change star (rawPullback+star rawPullback)=rawPullback+star rawPullback
    simp only [star_add,star_star,add_comm]
  exact sum.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock
