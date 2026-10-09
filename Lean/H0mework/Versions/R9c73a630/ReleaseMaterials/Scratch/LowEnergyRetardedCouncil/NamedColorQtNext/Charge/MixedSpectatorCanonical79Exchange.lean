import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorCanonical79Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorPairedSourceFrame

/-! The canonical79 department of the original paid world exchange.
The paired source frame is generated from the full real spatial momentum;
opposite momenta use this same frame and opposite signed axial radius.
The original exact Python producer owns the N/d inverse identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.MixedSpectatorCanonical79Exchange
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActiveMatterSectorCharge MixedSpectatorCandidate
open MixedSpectatorContactVertices MixedSpectatorCanonical79Data MixedSpectatorPairedSourceFrame
open scoped BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

/-- The ten actual paid denominators define the regular source domain. -/
def RegularMomentum (x : ℂ) (k : Fin 3 → ℝ) : Prop :=
  ∀a : Fin 10, denominator x (signedRadius k : ℂ) a ≠ 0

def worldSourceMap (negative : Bool) (x : ℂ) (k : Fin 3 → ℝ) (a : Fin 79) (b : Fin 97) : ℂ :=
  ∑c : Fin 97, axialSourceMap (if negative then -x else x)
    (if negative then -(signedRadius k : ℂ) else (signedRadius k : ℂ)) a c * pairedSourceFrame k b c

/-- Literal C(-p)^T A(p)^-1 C(p), with the paid normalization S N/d S/lapse
and the complete source97 world frame. No caller supplies a kernel or frame. -/
def canonicalCoefficient (x : ℂ) (k : Fin 3 → ℝ) (a b : Fin 97) : ℂ :=
  ∑i : Fin 79, ∑j : Fin 79,
    worldSourceMap true x k i a * axialInverse x (signedRadius k : ℂ) i j * worldSourceMap false x k j b

/-- The real-action -1/2 and both independent matter-leg momenta are retained
before the original full504 CAR normal product. -/
def actualCanonicalTree (x : ℂ) (k : Fin 3 → ℝ) (pLeft pRight : Fin 4 → ℂ)
    (_regular : RegularMomentum x k) : Module.End ℂ (Fock Mode) :=
  ∑a : Fin 97, ∑b : Fin 97,
    ((-1/2 : ℂ) * canonicalCoefficient x k a b) •
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b)

theorem actual_canonical_occupation (x : ℂ) (k : Fin 3 → ℝ) (pLeft pRight : Fin 4 → ℂ)
    (regular : RegularMomentum x k) :
    ActiveMatterSectorCharge.occupation * actualCanonicalTree x k pLeft pRight regular =
      actualCanonicalTree x k pLeft pRight regular * ActiveMatterSectorCharge.occupation := by
  have each (a b : Fin 97) : ActiveMatterSectorCharge.occupation *
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b) =
      LowEnergy.Fermion.normalProduct (sourceVertex pLeft a) (sourceVertex pRight b) *
        ActiveMatterSectorCharge.occupation :=
    LowEnergy.Fermion.occupationCharge_normalProduct _ _ _
      (actual_source_vertex_preserves pLeft a) (actual_source_vertex_preserves pRight b)
  simp only [actualCanonicalTree,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,each]

/-- The concrete mixed-spectator source has zero neutral amplitude in this
complete canonical79 world exchange, with no supplied preservation certificate. -/
theorem actual_canonical_candidate_neutral (x : ℂ) (k : Fin 3 → ℝ)
    (pLeft pRight : Fin 4 → ℂ) (regular : RegularMomentum x k) (dual : Bool)
    (word : Occupation) (neutral : ∑i ∈ word, modeWeight i = 0) :
    pairing (occupationBasis word)
      (actualCanonicalTree x k pLeft pRight regular (fiberCoordinates (candidate dual))) = 0 := by
  apply LowEnergy.Fermion.occupationCharge_selection modeWeight _
    (actual_canonical_occupation x k pLeft pRight regular)
    (fiberCoordinates (candidate dual)) (occupationBasis word)
    (if dual then (-3 : ℝ) else 3) 0
  · cases dual <;> norm_num
  · have h := actual_candidate_active_sector dual
    cases dual <;> simpa [ActiveMatterSectorCharge.occupation] using h
  · have h := SourceFockRaising.basis_eigenstate (fun i => (modeWeight i : ℂ)) word
    have hc : (∑i ∈ word, (modeWeight i : ℂ)) = 0 := by exact_mod_cast neutral
    simpa only [hc,zero_smul,Complex.ofReal_zero] using h

end LowEnergy.MixedSpectatorCanonical79Exchange
