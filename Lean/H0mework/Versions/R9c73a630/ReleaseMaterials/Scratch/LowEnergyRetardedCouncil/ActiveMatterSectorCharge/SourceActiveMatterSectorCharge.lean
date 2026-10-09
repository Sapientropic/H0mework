import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussFockLabel
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussYukawaCoefficient
import H0mework.Physics.LowEnergyFermion.Charge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActiveMatterSectorCharge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineHolonomicField
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open GaussNativeMatter GaussYukawaCoefficient QuantizationCheck.Fermion
open StageNineDynamicBreakingVacuum
open scoped BigOperators Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

/-- The original Lambda6+Lambda2 source sector, before any particle naming. -/
def primalWeight (i : Quantum.Index) : ℝ :=
  match i.2 with
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

/-- The independent-dual branch keeps the opposite phase weight. -/
def modeWeight : Mode → ℝ := Sum.elim primalWeight (fun i => -primalWeight i)

def activeProjection : Module.End ℂ DiracExteriorMatterCarrier where
  toFun field := fun spin => ((field spin).1, (field spin).2.1, 0)
  map_add' := by intros; funext spin; simp
  map_smul' := by intros; funext spin; simp

theorem activeProjection_original :
    activeProjection = MixedSymbol.degreeSix + MixedSymbol.degreeTwo := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [activeProjection, MixedSymbol.degreeSix, MixedSymbol.degreeTwo]

theorem coordinates_active (v : DiracExteriorMatterCarrier) (i : Quantum.Index) :
    Quantum.coordinates (activeProjection v) i =
      (primalWeight i : ℂ) * Quantum.coordinates v i := by
  rcases i with ⟨spin, six | two | four⟩ <;>
    simp [Quantum.coordinates, Quantum.wholeBasis, Quantum.internalBasis,
      Module.Basis.equivFun_apply, activeProjection, primalWeight]

theorem activeProjection_matrix :
    Quantum.operatorMatrix activeProjection =
      Matrix.diagonal (fun i : Quantum.Index => (primalWeight i : ℂ)) := by
  apply Matrix.ext
  intro i j
  have h := congrFun (Quantum.matrix_action activeProjection
    (Quantum.coordinates.symm (Pi.single j 1))) i
  rw [coordinates_active, LinearEquiv.apply_symm_apply] at h
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at h
  by_cases same : i = j
  · subst j
    simpa only [Pi.single_eq_same, mul_one, Matrix.diagonal_apply_eq] using h
  · simpa only [Pi.single_eq_of_ne same, mul_zero, Matrix.diagonal_apply_ne _ same] using h

theorem activeProjection_gauge (matrix : SU7MotherLieAlgebra.SU7MotherLieMatrix) :
    activeProjection * diracExteriorMotherLieAction matrix =
      diracExteriorMotherLieAction matrix * activeProjection := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [activeProjection, diracExteriorMotherLieAction, internalMatterLinearAction,
    exteriorSpinorMotherLieAction]

theorem activeProjection_spin (matrix : DiracMatrix) :
    activeProjection * diracMatrixMatterAction matrix =
      diracMatrixMatterAction matrix * activeProjection := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [activeProjection, diracMatrixMatterAction, Fin.sum_univ_four]

theorem activeProjection_yukawa (scalar : SU7ExteriorBreakingYukawa.ExteriorBreakingScalarCarrier) :
    activeProjection * StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction scalar =
      StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction scalar * activeProjection := by
  apply LinearMap.ext
  intro field
  funext spin
  simp [activeProjection, StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction,
    SU7ExteriorBreakingYukawa.diracExteriorYukawaInternalAction,
    internalMatterLinearAction, SU7ExteriorBreakingYukawa.exteriorYukawaInternalAction,
    diracMatrixMatterAction, Fin.sum_univ_four]

def PrimalPreserves (A : Matrix Quantum.Index Quantum.Index ℂ) : Prop :=
  ∀ i j, ((primalWeight i : ℂ) - (primalWeight j : ℂ)) * A i j = 0

def Preserves (A : Matrix Mode Mode ℂ) : Prop :=
  ∀ i j, ((modeWeight i : ℂ) - (modeWeight j : ℂ)) * A i j = 0

theorem operator_preserves (A : Module.End ℂ DiracExteriorMatterCarrier)
    (law : activeProjection * A = A * activeProjection) :
    PrimalPreserves (Quantum.operatorMatrix A) := by
  have hm := congrArg Quantum.operatorMatrix law
  have mul (B C : Module.End ℂ DiracExteriorMatterCarrier) :
      Quantum.operatorMatrix (B * C) = Quantum.operatorMatrix B * Quantum.operatorMatrix C :=
    Quantum.matrix_composition B C
  rw [mul, mul, activeProjection_matrix] at hm
  intro i j
  have h := congrFun (congrFun hm i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  linear_combination h

theorem preserves_branches (A B : Matrix Quantum.Index Quantum.Index ℂ)
    (hA : PrimalPreserves A) (hB : PrimalPreserves B) :
    Preserves (Matrix.fromBlocks A 0 0 B) := by
  intro i j
  cases i with
  | inl i => cases j with
    | inl j => exact hA i j
    | inr j => simp [Matrix.fromBlocks]
  | inr i => cases j with
    | inl j => simp [Matrix.fromBlocks]
    | inr j =>
      simp only [modeWeight, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, Complex.ofReal_neg]
      linear_combination -(hB i j)

theorem primalPreserves_star {A : Matrix Quantum.Index Quantum.Index ℂ}
    (hA : PrimalPreserves A) : PrimalPreserves (A.map (starRingEnd ℂ)) := by
  intro i j
  change ((primalWeight i : ℂ) - (primalWeight j : ℂ)) * (starRingEnd ℂ) (A i j) = 0
  have h := congrArg (starRingEnd ℂ) (hA i j)
  simpa only [map_mul, map_sub, Complex.conj_ofReal, map_zero] using h

theorem primalPreserves_neg {A : Matrix Quantum.Index Quantum.Index ℂ}
    (hA : PrimalPreserves A) : PrimalPreserves (-A) := by
  intro i j
  change ((primalWeight i : ℂ) - (primalWeight j : ℂ)) * (-A i j) = 0
  rw [mul_neg, hA i j, neg_zero]

theorem native_preserves (a : NativeLie) : Preserves (nativeFull a) := by
  have hp : PrimalPreserves (nativePrimal a) :=
    operator_preserves _ (activeProjection_gauge _)
  exact preserves_branches _ _ hp (primalPreserves_star hp)

theorem preserves_add {A B : Matrix Mode Mode ℂ}
    (hA : Preserves A) (hB : Preserves B) : Preserves (A + B) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hA i j, hB i j, add_zero]

theorem preserves_smul {A : Matrix Mode Mode ℂ} (hA : Preserves A) (c : ℂ) :
    Preserves (c • A) := by
  intro i j
  change ((modeWeight i : ℂ) - (modeWeight j : ℂ)) * (c * A i j) = 0
  rw [mul_left_comm, hA i j, mul_zero]

theorem preserves_mul {A B : Matrix Mode Mode ℂ}
    (hA : Preserves A) (hB : Preserves B) : Preserves (A * B) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro k _
  calc
    ((modeWeight i : ℂ) - (modeWeight j : ℂ)) * (A i k * B k j) =
        (((modeWeight i : ℂ) - (modeWeight k : ℂ)) * A i k) * B k j +
          A i k * (((modeWeight k : ℂ) - (modeWeight j : ℂ)) * B k j) := by ring
    _ = 0 := by rw [hA i k, hB k j, zero_mul, mul_zero, add_zero]

theorem preserves_adjoint {A : Matrix Mode Mode ℂ} (hA : Preserves A) :
    Preserves A.conjTranspose := by
  intro i j
  have h := congrArg (starRingEnd ℂ) (hA j i)
  have hs : ((modeWeight j : ℂ) - (modeWeight i : ℂ)) * (starRingEnd ℂ) (A j i) = 0 := by
    simpa only [map_mul, map_sub, Complex.conj_ofReal, map_zero] using h
  change ((modeWeight i : ℂ) - (modeWeight j : ℂ)) * (starRingEnd ℂ) (A j i) = 0
  linear_combination -hs

theorem spin_preserves (a : Fin 7) : Preserves (GaussCoframeSpin.full a) := by
  have hp : PrimalPreserves (GaussCoframeSpin.primal a) := by
    rw [GaussCoframeSpin.primal, ← GaussCoframeSpin.spinLift_source]
    exact operator_preserves _ (activeProjection_spin _)
  unfold GaussCoframeSpin.full
  split_ifs
  · exact preserves_branches _ _ hp (primalPreserves_star hp)
  · exact preserves_branches _ _ hp (primalPreserves_neg (primalPreserves_star hp))

theorem matter_preserves (i b : Fin 3)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    Preserves (GaussMatterCore.localMatrix i b z) :=
  preserves_smul (preserves_mul (preserves_smul (spin_preserves _) Complex.I)
    (native_preserves _)) _

theorem yukawa_preserves (scalar : Scalar) : Preserves (fullMatrix scalar) := by
  have hp : PrimalPreserves (primal scalar) := by
    apply operator_preserves
    let S := diracMatrixMatterAction diracGammaZero
    let Y := StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm scalar)
    have hs : activeProjection * S = S * activeProjection := activeProjection_spin _
    have hy : activeProjection * Y = Y * activeProjection := activeProjection_yukawa _
    change activeProjection * ((Stage9C.Material.SpinPair.lapse : ℂ) • (S * Y)) =
      ((Stage9C.Material.SpinPair.lapse : ℂ) • (S * Y)) * activeProjection
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [← mul_assoc, hs, mul_assoc, hy, ← mul_assoc]
  exact preserves_branches _ _ hp (primalPreserves_neg (primalPreserves_star hp))

def occupation : Module.End ℂ (Fock Mode) :=
  Fermion.occupationCharge (fun i => (modeWeight i : ℂ))

theorem native_occupation_commutes (a : NativeLie) :
    occupation * Fermion.quantize (nativeFull a) =
      Fermion.quantize (nativeFull a) * occupation :=
  Fermion.occupationCharge_quantize _ _ (native_preserves a)

theorem yukawa_occupation_commutes (scalar : Scalar) :
    occupation * Fermion.quantize (fullMatrix scalar) =
      Fermion.quantize (fullMatrix scalar) * occupation :=
  Fermion.occupationCharge_quantize _ _ (yukawa_preserves scalar)

theorem source_native_exchange_commutes (a b : NativeLie) :
    occupation * Fermion.normalProduct (nativeFull a) (nativeFull b) =
      Fermion.normalProduct (nativeFull a) (nativeFull b) * occupation :=
  Fermion.occupationCharge_normalProduct _ _ _ (native_preserves a) (native_preserves b)

theorem source_scalar_exchange_commutes (phi psi : Scalar) :
    occupation * Fermion.normalProduct (fullMatrix phi) (fullMatrix psi) =
      Fermion.normalProduct (fullMatrix phi) (fullMatrix psi) * occupation :=
  Fermion.occupationCharge_normalProduct _ _ _ (yukawa_preserves phi) (yukawa_preserves psi)

theorem source_mixed_exchange_commutes (a : NativeLie) (phi : Scalar) :
    occupation * Fermion.normalProduct (nativeFull a) (fullMatrix phi) =
      Fermion.normalProduct (nativeFull a) (fullMatrix phi) * occupation :=
  Fermion.occupationCharge_normalProduct _ _ _ (native_preserves a) (yukawa_preserves phi)

theorem source_dual_scalar_exchange_commutes (phi psi : Scalar) :
    occupation * Fermion.normalProduct (fullMatrix phi).conjTranspose (fullMatrix psi) =
      Fermion.normalProduct (fullMatrix phi).conjTranspose (fullMatrix psi) * occupation :=
  Fermion.occupationCharge_normalProduct _ _ _
    (preserves_adjoint (yukawa_preserves phi)) (yukawa_preserves psi)

/-- The occupation operator is the original full504 second quantization on
the existing positive Fock fibre, rather than a charge assigned to labels. -/
def fiberCharge : FockFiber →L[ℂ] FockFiber :=
  GaussQuantumMultiplier.quantized (Matrix.diagonal (fun i => (modeWeight i : ℂ)))

theorem fiberCharge_original (v : FockFiber) :
    fiberCoordinates (fiberCharge v) = occupation (fiberCoordinates v) := by
  change Fermion.quantize (Matrix.diagonal (fun i => (modeWeight i : ℂ)))
      (fiberCoordinates v) = occupation (fiberCoordinates v)
  exact LinearMap.congr_fun
    (Fermion.occupationCharge_original_quantize (fun i : Mode => (modeWeight i : ℂ)))
    (fiberCoordinates v)

/-- Arbitrary source gauge/scalar directions retain the source sector in
their full normal product, including all CAR exchange contractions. -/
theorem source_mixed_exchange_selection (a : NativeLie) (phi : Scalar)
    (input output : Fock Mode) (incoming outgoing : ℝ)
    (different : outgoing ≠ incoming)
    (hinput : occupation input = (incoming : ℂ) • input)
    (houtput : occupation output = (outgoing : ℂ) • output) :
    pairing output (Fermion.normalProduct (nativeFull a) (fullMatrix phi) input) = 0 :=
  Fermion.occupationCharge_selection modeWeight _ (source_mixed_exchange_commutes a phi)
    input output incoming outgoing different hinput houtput

theorem source_dual_scalar_exchange_selection (phi psi : Scalar)
    (input output : Fock Mode) (incoming outgoing : ℝ)
    (different : outgoing ≠ incoming)
    (hinput : occupation input = (incoming : ℂ) • input)
    (houtput : occupation output = (outgoing : ℂ) • output) :
    pairing output (Fermion.normalProduct (fullMatrix phi).conjTranspose (fullMatrix psi) input) = 0 :=
  Fermion.occupationCharge_selection modeWeight _ (source_dual_scalar_exchange_commutes phi psi)
    input output incoming outgoing different hinput houtput

end LowEnergy.ActiveMatterSectorCharge
