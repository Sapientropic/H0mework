import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFiniteYukawaPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceTensorPriceEnvelopeOwn
open SaturationMonoid.PhysicsCore
open StageNineDynamicBreakingVacuum SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa SU7ExteriorYukawaMassSpectrum
open DiracCliffordRepresentation DiracExteriorMatterAction StageNineDiracDualYukawaSpinJurisdiction
open ActualSourceFiniteYukawaPriceOwn
open scoped BigOperators
local instance : DecidableEq ScalarBasisIndex := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

abbrev lapse := Stage9C.Material.SpinPair.lapse

def spinEntry (s t : DiracSpinorIndex) : ℂ := (diracGammaZero * rightChiralityProjector) s t

def internalEntry (a : ScalarBasisIndex) (i j : LowEnergy.Quantum.InternalIndex) : ℂ :=
  match i, j with
  | Sum.inl six, Sum.inr (Sum.inl two) =>
      (su7ExteriorBasis 6).repr (exteriorYukawaMassMap (su7ExteriorBasis 4 a)
        (su7ExteriorBasis 2 two)) six
  | _, _ => 0

theorem sourceTensor_basis_return (a : ScalarBasisIndex) (i j : LowEnergy.Quantum.Index) :
    sourceTensor a i j =
      (LowEnergy.Quantum.wholeBasis.repr
        (LowEnergy.FullQuantum.yukawaHamiltonian (su7ExteriorBasis 4 a)
          (LowEnergy.Quantum.wholeBasis j))) i := by
  have scalar : scalarCoordinateEquiv.symm (EuclideanSpace.single a 1) =
      su7ExteriorBasis 4 a := by
    rw [← original_scalar_basis_coordinate, LinearEquiv.symm_apply_apply]
  change LowEnergy.Quantum.operatorMatrix
    (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm
      (EuclideanSpace.single a 1))) i j = _
  rw [scalar]
  exact LinearMap.toMatrixAlgEquiv_apply _ _ _ _


theorem spin_internal_matrix (A : DiracMatrix)
    (B : Module.End ℂ SU7ExteriorSpinorMatterCarrier) (i j : LowEnergy.Quantum.Index) :
    LowEnergy.Quantum.operatorMatrix
      ((internalMatterLinearAction B).comp (diracMatrixMatterAction A)) i j =
      A i.1 j.1 * (LowEnergy.Quantum.internalBasis.repr
        (B (LowEnergy.Quantum.internalBasis j.2))) i.2 := by
  rw [LowEnergy.Quantum.operatorMatrix, LinearMap.toMatrixAlgEquiv_apply]
  simp [LowEnergy.Quantum.wholeBasis, Pi.basis_apply, Pi.basis_repr,
    diracMatrixMatterAction, internalMatterLinearAction, Pi.single_apply, smul_eq_mul]

theorem original_internal_entry (a : ScalarBasisIndex) (i j : LowEnergy.Quantum.InternalIndex) :
    (LowEnergy.Quantum.internalBasis.repr
      (exteriorYukawaInternalAction (su7ExteriorBasis 4 a)
        (LowEnergy.Quantum.internalBasis j))) i = internalEntry a i j := by
  rcases i with six | two | four <;> rcases j with six' | two' | four' <;>
    simp [LowEnergy.Quantum.internalBasis, exteriorYukawaInternalAction, internalEntry]

theorem original_yukawa_separated (a : ScalarBasisIndex) :
    LowEnergy.FullQuantum.yukawaHamiltonian (su7ExteriorBasis 4 a) =
      (lapse : ℂ) • (internalMatterLinearAction
        (exteriorYukawaInternalAction (su7ExteriorBasis 4 a))).comp
          (diracMatrixMatterAction (diracGammaZero * rightChiralityProjector)) := by
  unfold LowEnergy.FullQuantum.yukawaHamiltonian diracDualRightChiralYukawaAction
    diracExteriorYukawaInternalAction
  rw [← LinearMap.comp_assoc, diracMatrixMatterAction_commutes_internal,
    LinearMap.comp_assoc, ← diracMatrixMatterAction_mul]

theorem original_tensor_entry (a : ScalarBasisIndex) (i j : LowEnergy.Quantum.Index) :
    sourceTensor a i j = (lapse : ℂ) * spinEntry i.1 j.1 * internalEntry a i.2 j.2 := by
  change LowEnergy.Quantum.operatorMatrix
    (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm
      (EuclideanSpace.single a 1))) i j = _
  rw [← original_scalar_basis_coordinate, LinearEquiv.symm_apply_apply,
    original_yukawa_separated]
  simp only [map_smul, Matrix.smul_apply, smul_eq_mul, spin_internal_matrix,
    original_internal_entry, spinEntry, mul_assoc]

end LowEnergy.ActualSourceTensorPriceEnvelopeOwn
