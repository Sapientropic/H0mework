import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorDual24Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorPairedSourceFrame

/-! The original independent-dual24 department, transported by the same
complete paired source frame. Its source map is the actual constant Lorentz
readback; no canonical adjoint graph removes these source currents. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.MixedSpectatorDual24Exchange
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActiveMatterSectorCharge MixedSpectatorCandidate
open MixedSpectatorContactVertices MixedSpectatorDual24Data MixedSpectatorPairedSourceFrame
open scoped BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

def RegularMomentum (x : ℂ) (k : Fin 3 → ℝ) : Prop :=
  ∀a : Fin 6, denominator x (signedRadius k : ℂ) a ≠ 0

/-- D(p) is literally constant in the paid source; both oriented ends retain
this same readback and the same paired frame. -/
def worldSourceMap (k : Fin 3 → ℝ) (a : Fin 24) (b : Fin 97) : ℂ :=
  ∑c : Fin 97, axialSourceMap a c * pairedSourceFrame k b c

def dualCoefficient (x : ℂ) (k : Fin 3 → ℝ) (a b : Fin 97) : ℂ :=
  ∑i : Fin 24, ∑j : Fin 24,
    worldSourceMap k i a * axialInverse x (signedRadius k : ℂ) i j * worldSourceMap k j b

/-- The full independent source momenta and original real-action -1/2 survive
before the actual full504 CAR normal contraction. -/
def actualDualTree (x : ℂ) (k : Fin 3 → ℝ) (pLeft pRight : Fin 4 → ℂ)
    (_regular : RegularMomentum x k) : Module.End ℂ (Fock Mode) :=
  ∑a : Fin 97, ∑b : Fin 97,
    ((-1/2 : ℂ) * dualCoefficient x k a b) •
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b)

theorem actual_dual_occupation (x : ℂ) (k : Fin 3 → ℝ) (pLeft pRight : Fin 4 → ℂ)
    (regular : RegularMomentum x k) :
    ActiveMatterSectorCharge.occupation * actualDualTree x k pLeft pRight regular =
      actualDualTree x k pLeft pRight regular * ActiveMatterSectorCharge.occupation := by
  have each (a b : Fin 97) : ActiveMatterSectorCharge.occupation *
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b) =
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b) *
        ActiveMatterSectorCharge.occupation :=
    LowEnergy.Fermion.occupationCharge_normalProduct _ _ _
      (actual_source_vertex_preserves pLeft a) (actual_source_vertex_preserves pRight b)
  simp only [actualDualTree,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,each]

/-- The fixed actual candidate has zero active-neutral amplitude in the
complete independent-dual24 world exchange. -/
theorem actual_dual_candidate_neutral (x : ℂ) (k : Fin 3 → ℝ)
    (pLeft pRight : Fin 4 → ℂ) (regular : RegularMomentum x k) (dual : Bool)
    (word : Occupation) (neutral : ∑i ∈ word, modeWeight i = 0) :
    pairing (occupationBasis word)
      (actualDualTree x k pLeft pRight regular (fiberCoordinates (candidate dual))) = 0 := by
  apply LowEnergy.Fermion.occupationCharge_selection modeWeight _
    (actual_dual_occupation x k pLeft pRight regular)
    (fiberCoordinates (candidate dual)) (occupationBasis word)
    (if dual then (-3 : ℝ) else 3) 0
  · cases dual <;> norm_num
  · have h := actual_candidate_active_sector dual
    cases dual <;> simpa [ActiveMatterSectorCharge.occupation] using h
  · have h := SourceFockRaising.basis_eigenstate (fun i => (modeWeight i : ℂ)) word
    have hc : (∑i ∈ word, (modeWeight i : ℂ)) = 0 := by exact_mod_cast neutral
    simpa only [hc,zero_smul,Complex.ofReal_zero] using h

end LowEnergy.MixedSpectatorDual24Exchange
