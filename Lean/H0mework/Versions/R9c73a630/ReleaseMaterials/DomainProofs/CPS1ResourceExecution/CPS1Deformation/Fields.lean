import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Projection
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Integrals
import Mathlib.Analysis.Calculus.FDeriv.Pi

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.SpatialControl
variable {frame : CPS1Recycling.Frame}

abbrev NuclearConfiguration (state : CPS1ElectronicSource.State frame) :=
  CPS1MolecularFrame.NuclearIndex state → Point

def sourcePositions (state : CPS1ElectronicSource.State frame) : NuclearConfiguration state :=
  CPS1MolecularFrame.position state

def sourceVelocity (state : CPS1ElectronicSource.State frame) : NuclearConfiguration state :=
  CPS1MolecularFrame.velocity state

def sourceLine (state : CPS1ElectronicSource.State frame) (time : ℝ) : NuclearConfiguration state :=
  fun nuclear => CPS1MolecularFrame.centreLine state nuclear time

def rawJetAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state)
    (index : CPS1MolecularFrame.PrimitiveIndex state) (jet : Fin 3 → Nat) : SpinSpace :=
  PiLp.single 2 index.2 (orbitalField (positions index.1.1) index.1.2.val jet)

def orbitalJetFDeriv (mode : Nat) (jet : Fin 3 → Nat) (centre : Point) : Point →L[ℝ] SpatialLp :=
  CPS1Following.realEmbedding.comp
    (translationDerivative [primitive mode] (primitive_positive mode) jet centre)

theorem orbital_jet_hasFDerivAt (mode : Nat) (jet : Fin 3 → Nat) (centre : Point) :
    HasFDerivAt (fun point => orbitalField point mode jet) (orbitalJetFDeriv mode jet centre) centre := by
  have source := CPS1Following.realEmbedding.hasFDerivAt.comp centre
    (shifted_field_hasFDerivAt [primitive mode] (primitive_positive mode) jet centre)
  simpa only [Function.comp_def,CPS1Following.real_embedding_primitive,orbitalJetFDeriv] using source

def rawJetFDeriv (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state)
    (index : CPS1MolecularFrame.PrimitiveIndex state) (jet : Fin 3 → Nat) :
    NuclearConfiguration state →L[ℝ] SpinSpace :=
  (CPS1Following.spinInjection index.2).comp
    ((orbitalJetFDeriv index.1.2.val jet (positions index.1.1)).comp
      (ContinuousLinearMap.proj index.1.1))

theorem raw_jet_hasFDerivAt (state : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration state) (index : CPS1MolecularFrame.PrimitiveIndex state)
    (jet : Fin 3 → Nat) :
    HasFDerivAt (fun next => rawJetAt state next index jet) (rawJetFDeriv state positions index jet) positions := by
  have coordinates := (ContinuousLinearMap.proj index.1.1 :
    NuclearConfiguration state →L[ℝ] Point).hasFDerivAt (x := positions)
  have orbital := (orbital_jet_hasFDerivAt index.1.2.val jet (positions index.1.1)).comp positions coordinates
  have spin := (CPS1Following.spinInjection index.2).hasFDerivAt.comp positions orbital
  simpa only [Function.comp_def,rawJetAt,rawJetFDeriv,CPS1Following.spin_injection_apply] using! spin

theorem raw_jet_fderiv_apply (state : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration state) (index : CPS1MolecularFrame.PrimitiveIndex state)
    (jet : Fin 3 → Nat) :
    rawJetFDeriv state positions index jet direction =
      -(∑ axis : Fin 3, direction index.1.1 axis • rawJetAt state positions index (raise jet axis)) := by
  simp only [rawJetFDeriv,orbitalJetFDeriv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    translation_derivative_apply,map_neg,map_sum,map_smul,CPS1Following.real_embedding_primitive,
    CPS1Following.spin_injection_apply,rawJetAt]

def basisJetAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state)
    (index : CPS1MolecularFrame.ActualIndex state) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ primitive, CPS1MolecularFrame.basisCoefficient state primitive index • rawJetAt state positions primitive jet

def basisJetFDeriv (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state)
    (index : CPS1MolecularFrame.ActualIndex state) (jet : Fin 3 → Nat) :
    NuclearConfiguration state →L[ℝ] SpinSpace :=
  ∑ primitive, CPS1MolecularFrame.basisCoefficient state primitive index • rawJetFDeriv state positions primitive jet

theorem basis_jet_hasFDerivAt (state : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration state) (index : CPS1MolecularFrame.ActualIndex state)
    (jet : Fin 3 → Nat) :
    HasFDerivAt (fun next => basisJetAt state next index jet) (basisJetFDeriv state positions index jet) positions := by
  exact HasFDerivAt.fun_sum (u := Finset.univ) (fun primitive _ =>
    (raw_jet_hasFDerivAt state positions primitive jet).const_smul
      (CPS1MolecularFrame.basisCoefficient state primitive index))

def basisAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state)
    (index : CPS1MolecularFrame.ActualIndex state) : SpinSpace := basisJetAt state positions index 0

def basisFDeriv (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state)
    (index : CPS1MolecularFrame.ActualIndex state) : NuclearConfiguration state →L[ℝ] SpinSpace :=
  basisJetFDeriv state positions index 0

theorem basis_hasFDerivAt (state : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration state) (index : CPS1MolecularFrame.ActualIndex state) :
    HasFDerivAt (fun next => basisAt state next index) (basisFDeriv state positions index) positions :=
  basis_jet_hasFDerivAt state positions index 0

theorem raw_jet_source (state : CPS1ElectronicSource.State frame)
    (index : CPS1MolecularFrame.PrimitiveIndex state) (jet : Fin 3 → Nat) :
    rawJetAt state (sourcePositions state) index jet = CPS1MolecularFrame.rawJet state index jet := rfl

theorem basis_jet_source (state : CPS1ElectronicSource.State frame)
    (index : CPS1MolecularFrame.ActualIndex state) (jet : Fin 3 → Nat) :
    basisJetAt state (sourcePositions state) index jet = CPS1MolecularFrame.basisJet state jet index := rfl

theorem basis_source (state : CPS1ElectronicSource.State frame) :
    basisAt state (sourcePositions state) = CPS1MolecularFrame.currentBasis state := by
  funext index
  exact CPS1MolecularFrame.basis_jet_zero state index

theorem raw_jet_line (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (index : CPS1MolecularFrame.PrimitiveIndex state) (jet : Fin 3 → Nat) :
    rawJetAt state (sourceLine state time) index jet = CPS1MolecularFrame.rawJetCurve state time index jet := rfl

theorem basis_line (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    basisAt state (sourceLine state time) = CPS1MolecularFrame.fieldCurve state time := rfl

theorem basis_rate_source (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (index : CPS1MolecularFrame.ActualIndex state) :
    basisFDeriv state (sourceLine state time) index (sourceVelocity state) =
      CPS1MolecularFrame.fieldRate state time index := by
  simp only [basisFDeriv,basisJetFDeriv,sum_apply,smul_apply,
    raw_jet_fderiv_apply,raw_jet_line]
  rfl

theorem source_line_hasDerivAt (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    HasDerivAt (sourceLine state) (sourceVelocity state) time := by
  exact hasDerivAt_pi.mpr (fun nuclear => CPS1MolecularFrame.source_centre_derivative state nuclear time)

theorem actual_curve_from_frechet (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (index : CPS1MolecularFrame.ActualIndex state) :
    HasDerivAt (fun next => basisAt state (sourceLine state next) index)
      (CPS1MolecularFrame.fieldRate state time index) time := by
  have source := (basis_hasFDerivAt state (sourceLine state time) index).comp_hasDerivAt time
    (source_line_hasDerivAt state time)
  simpa only [Function.comp_def,basis_rate_source] using source

end
end CPS1Deformation
