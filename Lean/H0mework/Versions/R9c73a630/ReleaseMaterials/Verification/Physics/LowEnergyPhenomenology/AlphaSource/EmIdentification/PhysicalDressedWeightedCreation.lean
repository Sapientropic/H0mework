import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedP286Character
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeightedChargeCoreWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section

namespace LowEnergy.WeightedActualSeed

open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussComposite GaussComposite.SourceGraph Electromagnetic.Identification GaussNativeMatter
open CanonicalGradedCurrent GaussQuantumMultiplier CanonicalGradedSpatialSource GaussDensityCore
open CanonicalGradedCharge SourceQuantumResidualGaugeSlice
open PreparationPhysicalPhaseGaugeRealization
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open SU7ExteriorMatterRepresentation StageNineExteriorMotherLieRepresentation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286LinkedActiveScalarPairingSkew
open PreparationPhysicalDressedSpinChargeReturn PreparationVacuumSourcePreparedResponse
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMDressedCharacter GaussComposite.PhysicalEMDressedPreparedRead
open GaussComposite.ActualDressedSourcePreparation
open NamedMatterWedgeQt NamedColorQtNext
open DressedColourY DressedColourYScalarColumns DressedColourYScalarRows
open PreparationVacuumWeightedChargeActionWard PreparationVacuumTemporalCharge
open PreparationVacuumLowerClassical PreparationVacuumSourceFieldFamily
open PreparationVacuumSourceActionJets PreparationVacuumNoetherChart
open PreparationVacuumFullElectricWard PreparationVacuumActionFieldLift
open PreparationVacuumRawJointFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumNonlinearFieldCurve PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization FullQuantum.StateGreen GaussHistoryHilbert
open Filter Set
open scoped BigOperators ContDiff InnerProductSpace Matrix Matrix.Norms.L2Operator Topology

attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq
local instance : NormedAlgebra ℝ FiberOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

/-- The weighted dressed creation: the actual CAR commutator of the quantized
full-mode matrix `W` against the original two-channel creation fibre. -/
def weightedCreation (W : FullMatrix) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) : FiberOp :=
  quantized W * fiberCreation channel s phi -
    fiberCreation channel s phi * quantized W

/-- The scalar-varied weighted creation: `W` against the `a`-varied scalar. -/
def scalarWeightedCreation (a : NativeLie) (W : FullMatrix) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) : FiberOp :=
  weightedCreation W channel s
    (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi)

/-- The original two-channel modes are the positive root modes of the shared
matter carrier. -/
private theorem mode_eq (spin : Fin 2) (c : Fin 3) :
    mode spin c = rootMode false ⟨spin.castLE (by decide), c⟩ := rfl

private theorem root_collapse_full {V : Type*} [AddCommGroup V] [Module ℂ V]
    (i : NamedMode) (b : Fin 3 → ℂ) (h : ℂ) (X : Mode → V) :
    (∑ j : Mode, ((∑ r : Fin 3, b r *
          (if j = rootMode false (i.1, r) then 1 else 0)) +
        h * (if j = rootMode false i then 1 else 0)) •
        X j) =
      (∑ r : Fin 3, b r • X (rootMode false (i.1, r))) +
        h • X (rootMode false i) := by
  rw [Finset.sum_congr rfl (fun j _ => add_smul _ _ _), Finset.sum_add_distrib]
  have collapse : ∑ j : Mode, (∑ r : Fin 3, b r *
        (if j = rootMode false (i.1, r) then 1 else 0)) • X j =
      ∑ r : Fin 3, b r • X (rootMode false (i.1, r)) := by
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [collapse]
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The full native column collapses a mode-sum into the colour row plus the
hypercharge diagonal, applied to any mode-indexed fibre operator. -/
private theorem weighted_column_collapse (a : NativeLie) (i : NamedMode)
    (X : Mode → FiberOp) :
    (∑ k : Mode, nativeFull a k (rootMode false i) • X k) =
      (∑ r : Fin 3, colorEntry false (nativeData a).1 r i.2 •
        X (rootMode false (i.1, r))) +
        (nativeHyper false a) • X (rootMode false i) := by
  rw [Finset.sum_congr rfl (fun k _ => congrArg (· • X k)
    (actual_full_native_column false a i k))]
  exact root_collapse_full i (fun r => colorEntry false (nativeData a).1 r i.2)
    (nativeHyper false a) X

/-- The `W·G` column law: the weighted creation commutator on a named original
mode decomposes into the colour column against the same `W`-commutators plus
the hypercharge term, using only matrix-product column linearity. -/
private theorem weighted_create_column (W : FullMatrix) (a : NativeLie)
    (spin : Fin 2) (c : Fin 3) :
    quantized (W * nativeFull a) * GaussCARHistory.createFiber (mode spin c) -
      GaussCARHistory.createFiber (mode spin c) * quantized (W * nativeFull a) =
    (∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r c •
        (quantized W * GaussCARHistory.createFiber (mode spin r) -
          GaussCARHistory.createFiber (mode spin r) * quantized W)) +
      (nativeData a).2.2.1 •
        (quantized W * GaussCARHistory.createFiber (mode spin c) -
          GaussCARHistory.createFiber (mode spin c) * quantized W) := by
  rw [quantized_creation_column]
  unfold creationColumn
  rw [mode_eq spin c]
  have reshape : (∑ j : Mode, (W * nativeFull a) j
        (rootMode false ⟨spin.castLE (by decide), c⟩) •
        GaussCARHistory.createFiber j) =
      ∑ k : Mode, (nativeFull a) k (rootMode false ⟨spin.castLE (by decide), c⟩) •
        (quantized W * GaussCARHistory.createFiber k -
          GaussCARHistory.createFiber k * quantized W) := by
    have perK : ∀ k : Mode,
        ∑ j : Mode, (W j k * (nativeFull a) k
            (rootMode false ⟨spin.castLE (by decide), c⟩)) •
            GaussCARHistory.createFiber j =
          (nativeFull a) k (rootMode false ⟨spin.castLE (by decide), c⟩) •
            (quantized W * GaussCARHistory.createFiber k -
              GaussCARHistory.createFiber k * quantized W) := by
      intro k
      have fold : (∑ j : Mode, W j k • GaussCARHistory.createFiber j) =
          quantized W * GaussCARHistory.createFiber k -
            GaussCARHistory.createFiber k * quantized W :=
        (quantized_creation_column W k).symm
      calc ∑ j : Mode, (W j k * (nativeFull a) k
              (rootMode false ⟨spin.castLE (by decide), c⟩)) •
              GaussCARHistory.createFiber j
          = ∑ j : Mode, (nativeFull a) k
              (rootMode false ⟨spin.castLE (by decide), c⟩) •
              (W j k • GaussCARHistory.createFiber j) :=
            Finset.sum_congr rfl (fun j _ => by
              rw [mul_comm (W j k), mul_smul])
        _ = (nativeFull a) k (rootMode false ⟨spin.castLE (by decide), c⟩) •
            (∑ j : Mode, W j k • GaussCARHistory.createFiber j) := by
            rw [← Finset.smul_sum]
        _ = (nativeFull a) k (rootMode false ⟨spin.castLE (by decide), c⟩) •
            (quantized W * GaussCARHistory.createFiber k -
              GaussCARHistory.createFiber k * quantized W) :=
            congrArg _ fold
    calc ∑ j : Mode, (W * nativeFull a) j
            (rootMode false ⟨spin.castLE (by decide), c⟩) •
            GaussCARHistory.createFiber j
        = ∑ j : Mode, (∑ k : Mode, W j k * (nativeFull a) k
            (rootMode false ⟨spin.castLE (by decide), c⟩)) •
            GaussCARHistory.createFiber j :=
          Finset.sum_congr rfl (fun j _ =>
            congrArg (· • GaussCARHistory.createFiber j) Matrix.mul_apply)
      _ = ∑ j : Mode, ∑ k : Mode, (W j k * (nativeFull a) k
            (rootMode false ⟨spin.castLE (by decide), c⟩)) •
            GaussCARHistory.createFiber j :=
          Finset.sum_congr rfl (fun j _ =>
            Finset.sum_smul (s := Finset.univ)
              (f := fun k => W j k * (nativeFull a) k
                (rootMode false ⟨spin.castLE (by decide), c⟩))
              (x := GaussCARHistory.createFiber j))
      _ = ∑ k : Mode, ∑ j : Mode, (W j k * (nativeFull a) k
            (rootMode false ⟨spin.castLE (by decide), c⟩)) •
            GaussCARHistory.createFiber j :=
          Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
            (f := fun j k => (W j k * (nativeFull a) k
              (rootMode false ⟨spin.castLE (by decide), c⟩)) •
              GaussCARHistory.createFiber j)
      _ = ∑ k : Mode, (nativeFull a) k
          (rootMode false ⟨spin.castLE (by decide), c⟩) •
          (quantized W * GaussCARHistory.createFiber k -
            GaussCARHistory.createFiber k * quantized W) :=
        Finset.sum_congr rfl (fun k _ => perK k)
  rw [reshape, weighted_column_collapse a ⟨spin.castLE (by decide), c⟩
    (fun k => quantized W * GaussCARHistory.createFiber k -
      GaussCARHistory.createFiber k * quantized W)]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r _
    show colorEntry false (nativeData a).1 r c •
        (quantized W * GaussCARHistory.createFiber (mode spin r) -
          GaussCARHistory.createFiber (mode spin r) * quantized W) =
      ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r c •
        (quantized W * GaussCARHistory.createFiber (mode spin r) -
          GaussCARHistory.createFiber (mode spin r) * quantized W)
    simp [colorEntry]
  · show nativeHyper false a •
        (quantized W * GaussCARHistory.createFiber (mode spin c) -
          GaussCARHistory.createFiber (mode spin c) * quantized W) =
      (nativeData a).2.2.1 •
        (quantized W * GaussCARHistory.createFiber (mode spin c) -
          GaussCARHistory.createFiber (mode spin c) * quantized W)
    simp [nativeHyper]

/-- The quantized commutator against `fiberCreation` distributes over the
creation sum for any full-mode matrix. -/
private theorem weighted_creation_distribute (M : FullMatrix) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    quantized M * fiberCreation channel s phi -
      fiberCreation channel s phi * quantized M =
    ∑ d : Fin 3, star (scalarCoefficient channel d phi) •
      (quantized M * GaussCARHistory.createFiber (mode s d) -
        GaussCARHistory.createFiber (mode s d) * quantized M) := by
  unfold fiberCreation
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_smul_comm, smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [smul_sub]

/-- Special-unitary colour matrices are skew-adjoint pointwise. -/
private theorem colour_conjugate (data : P286LieBlockData) (c d : Fin 3) :
    star ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) c d) =
      -((data.1 : Matrix (Fin 3) (Fin 3) ℂ) d c) := by
  have skewed := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M d c)
    (specialUnitaryLieMatrix_star data.1)
  simpa [Matrix.star_apply, Matrix.neg_apply] using skewed

/-- The scalar-varied coefficient conjugates to the transposed colour
combination of the original coefficients. -/
private theorem coeff_star_swap (a : NativeLie) (channel : Fin 2)
    (d : Fin 3) (phi : ScalarCoordinateCarrier) :
    star (scalarCoefficient channel d
        (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi)) =
      ∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
        star (scalarCoefficient channel r phi) := by
  rw [scalar_action_row, star_neg, star_sum]
  simp_rw [star_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [colour_conjugate (nativeData a) r d]
  ring

private theorem weighted_decomp (W : FullMatrix) (a : NativeLie)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) (d : Fin 3) :
    star (scalarCoefficient channel d phi) •
      ((∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d •
          (quantized W * GaussCARHistory.createFiber (mode s r) -
            GaussCARHistory.createFiber (mode s r) * quantized W)) +
        (nativeData a).2.2.1 • (quantized W * GaussCARHistory.createFiber
          (mode s d) - GaussCARHistory.createFiber (mode s d) * quantized W)) =
    (∑ r : Fin 3, (star (scalarCoefficient channel d phi) *
        ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d) •
        (quantized W * GaussCARHistory.createFiber (mode s r) -
          GaussCARHistory.createFiber (mode s r) * quantized W)) +
      ((nativeData a).2.2.1 * star (scalarCoefficient channel d phi)) •
        (quantized W * GaussCARHistory.createFiber (mode s d) -
          GaussCARHistory.createFiber (mode s d) * quantized W) := by
  rw [smul_add, Finset.smul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun r _ =>
      smul_smul (star (scalarCoefficient channel d phi))
        (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d)
        (quantized W * GaussCARHistory.createFiber (mode s r) -
          GaussCARHistory.createFiber (mode s r) * quantized W)
  · rw [smul_smul, mul_comm]

private theorem weighted_lhs_entry (W : FullMatrix) (a : NativeLie)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) (d : Fin 3) :
    (∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
        star (scalarCoefficient channel r phi)) •
      (quantized W * GaussCARHistory.createFiber (mode s d) -
        GaussCARHistory.createFiber (mode s d) * quantized W) =
    ∑ r : Fin 3, (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
        star (scalarCoefficient channel r phi)) •
        (quantized W * GaussCARHistory.createFiber (mode s d) -
          GaussCARHistory.createFiber (mode s d) * quantized W) :=
  Finset.sum_smul (s := Finset.univ)
    (f := fun r => ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
      star (scalarCoefficient channel r phi))
    (x := quantized W * GaussCARHistory.createFiber (mode s d) -
      GaussCARHistory.createFiber (mode s d) * quantized W)

private theorem weighted_hyper_pull (W : FullMatrix) (a : NativeLie)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    (∑ d : Fin 3, ((nativeData a).2.2.1 * star (scalarCoefficient channel d phi)) •
        (quantized W * GaussCARHistory.createFiber (mode s d) -
          GaussCARHistory.createFiber (mode s d) * quantized W)) =
      (nativeData a).2.2.1 •
        (∑ d : Fin 3, star (scalarCoefficient channel d phi) •
          (quantized W * GaussCARHistory.createFiber (mode s d) -
            GaussCARHistory.createFiber (mode s d) * quantized W)) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← smul_smul]

private theorem weighted_colsum (W : FullMatrix) (a : NativeLie)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    (∑ d : Fin 3, ∑ r : Fin 3, (star (scalarCoefficient channel d phi) *
        ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d) •
        (quantized W * GaussCARHistory.createFiber (mode s r) -
          GaussCARHistory.createFiber (mode s r) * quantized W)) =
      ∑ d : Fin 3, ∑ r : Fin 3, (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
          star (scalarCoefficient channel r phi)) •
        (quantized W * GaussCARHistory.createFiber (mode s d) -
          GaussCARHistory.createFiber (mode s d) * quantized W) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  ring

/-- The weighted native coupling on creation: the `W·G` commutator equals the
scalar-varied weighted creation plus the hypercharge-weighted one. -/
private theorem weighted_creation_native (W : FullMatrix) (a : NativeLie)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    quantized (W * nativeFull a) * fiberCreation channel s phi -
        fiberCreation channel s phi * quantized (W * nativeFull a) =
      scalarWeightedCreation a W channel s phi +
        (nativeData a).2.2.1 • weightedCreation W channel s phi := by
  rw [weighted_creation_distribute]
  rw [Finset.sum_congr rfl (fun d _ =>
    congrArg (fun X => star (scalarCoefficient channel d phi) • X)
      (weighted_create_column W a s d))]
  rw [Finset.sum_congr rfl (fun d _ => weighted_decomp W a channel s phi d)]
  rw [Finset.sum_add_distrib, weighted_hyper_pull W a channel s phi]
  unfold scalarWeightedCreation weightedCreation
  rw [weighted_creation_distribute W channel s
    (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi),
    weighted_creation_distribute W channel s phi]
  rw [Finset.sum_congr rfl (fun d _ =>
    congrArg₂ (· • ·) (coeff_star_swap a channel d phi) rfl)]
  rw [Finset.sum_congr rfl (fun d _ => weighted_lhs_entry W a channel s phi d)]
  rw [weighted_colsum W a channel s phi]

/-- The quantized charge-matrix coupling: no `W`/`a` commuting premise; the
scalar row variation cancels the colour column and the hypercharge remains. -/
theorem weighted_creation_coupling (W : FullMatrix) (a : NativeLie)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    (quantizer (W * chargeMatrix a) * fiberCreation channel s phi -
        fiberCreation channel s phi * quantizer (W * chargeMatrix a)) -
      Complex.I • scalarWeightedCreation a W channel s phi =
    (Complex.I • (nativeData a).2.2.1) • weightedCreation W channel s phi := by
  have hWQ : (quantizer (W * chargeMatrix a) : FiberOp) =
      Complex.I • quantized (W * nativeFull a) := by
    have hprod : W * chargeMatrix a = Complex.I • (W * nativeFull a) := by
      show W * (Complex.I • nativeFull a) = _
      rw [Matrix.mul_smul]
    show quantizer (W * chargeMatrix a) = Complex.I • quantized (W * nativeFull a)
    rw [hprod]
    exact map_smul quantizer Complex.I (W * nativeFull a)
  rw [hWQ, smul_mul_assoc, mul_smul_comm]
  have scaled := congrArg (fun Z : FiberOp => Complex.I • Z)
    (weighted_creation_native W a channel s phi)
  simp only [smul_sub, smul_add, smul_smul] at scaled
  rw [sub_eq_iff_eq_add]
  rw [scaled]
  simp only [smul_eq_mul]
  exact add_comm _ _

/-- The actual raw temporal charge density against the dressed creation letter
of the original scalar: the weighted Ward fibre with only the hypercharge
block surviving. This is the pointwise creator coupling. -/
theorem raw_charge_weighted_creation (a : Fin 12) (z : physicalChart)
    (channel s : Fin 2) :
    (rawChargeFiber a z.val * fiberCreation channel s
        (GaussNativePotential.scalarField z.val) -
      fiberCreation channel s (GaussNativePotential.scalarField z.val) *
        rawChargeFiber a z.val) -
      Complex.I • scalarWeightedCreation (originalUnit a)
        (sourceWeightSymbol z.val) channel s
        (GaussNativePotential.scalarField z.val) =
    (Complex.I • (nativeData (originalUnit a)).2.2.1) •
      weightedCreation (sourceWeightSymbol z.val) channel s
        (GaussNativePotential.scalarField z.val) := by
  have raw_eq : rawChargeFiber a z.val =
      quantized (sourceWeightSymbol z.val * chargeMatrix (originalUnit a)) := by
    rw [rawChargeFiber_source]
    unfold normalChargeFiber weightFiber
    rw [pairFiber_sub]
    show quantizer (sourceWeightSymbol z.val) *
        quantizer (chargeMatrix (originalUnit a)) -
        (quantizer (sourceWeightSymbol z.val) *
          quantizer (chargeMatrix (originalUnit a)) -
          quantizer (sourceWeightSymbol z.val *
            chargeMatrix (originalUnit a))) = _
    rw [sub_sub_self]
    rfl
  rw [raw_eq]
  exact weighted_creation_coupling (sourceWeightSymbol z.val) (originalUnit a)
    channel s (GaussNativePotential.scalarField z.val)

/-- The explicit normal-ordered version: the weight-charge product with the
normal pair retained on the left. -/
theorem raw_charge_weighted_creation_explicit (a : Fin 12) (z : physicalChart)
    (channel s : Fin 2) :
    (weightFiber z.val * quantizer (chargeMatrix (originalUnit a)) -
        normalChargeFiber a z.val) *
      fiberCreation channel s (GaussNativePotential.scalarField z.val) -
      fiberCreation channel s (GaussNativePotential.scalarField z.val) *
        (weightFiber z.val * quantizer (chargeMatrix (originalUnit a)) -
          normalChargeFiber a z.val) -
      Complex.I • scalarWeightedCreation (originalUnit a)
        (sourceWeightSymbol z.val) channel s
        (GaussNativePotential.scalarField z.val) =
    (Complex.I • (nativeData (originalUnit a)).2.2.1) •
      weightedCreation (sourceWeightSymbol z.val) channel s
        (GaussNativePotential.scalarField z.val) := by
  have same : weightFiber z.val * quantizer (chargeMatrix (originalUnit a)) -
        normalChargeFiber a z.val =
      rawChargeFiber a z.val := (rawChargeFiber_source a z).symm
  rw [same]
  exact raw_charge_weighted_creation a z channel s

/-- The weighted creation fibre is smooth on the original physical chart. -/
private theorem weighted_fiber_smooth (channel s : Fin 2) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice =>
      weightedCreation (sourceWeightSymbol w) channel s
        (GaussNativePotential.scalarField w)) z.val := by
  unfold weightedCreation
  show ContDiffAt ℝ ∞ (fun w =>
      quantized (sourceWeightSymbol w) * fiberCreation channel s
        (GaussNativePotential.scalarField w) -
      fiberCreation channel s (GaussNativePotential.scalarField w) *
        quantized (sourceWeightSymbol w)) z.val
  exact ((weightFiber_smooth z).mul
    (creation_matrix_smooth channel s).contDiffAt).sub
    ((creation_matrix_smooth channel s).contDiffAt.mul (weightFiber_smooth z))

/-- The scalar Lie action is a bounded linear endomorphism of the scalar
carrier, bundled for smoothness transport. -/
private def scalarActionLinear (matrix : SU7MotherLieMatrix) :
    ScalarCoordinateCarrier →ₗ[ℂ] ScalarCoordinateCarrier :=
  scalarCoordinateEquiv.toLinearMap.comp
    ((exteriorMotherLieAction 4 matrix).comp
      scalarCoordinateEquiv.symm.toLinearMap)

private def scalarActionCLM (matrix : SU7MotherLieMatrix) :
    ScalarCoordinateCarrier →L[ℂ] ScalarCoordinateCarrier :=
  (scalarActionLinear matrix).toContinuousLinearMap

private theorem scalarActionCLM_apply (matrix : SU7MotherLieMatrix)
    (phi : ScalarCoordinateCarrier) :
    scalarActionCLM matrix phi = scalarMotherLieAction matrix phi := rfl

/-- The `a`-varied scalar field is smooth on the original chart. -/
private theorem scalar_action_smooth (a : NativeLie) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => scalarMotherLieAction
      (p286LieBlockEmbed (nativeData a))
      (GaussNativePotential.scalarField w)) z.val := by
  have hlin : (fun w : SourceCoordinateSlice => scalarMotherLieAction
      (p286LieBlockEmbed (nativeData a)) (GaussNativePotential.scalarField w)) =
      ⇑(scalarActionCLM (p286LieBlockEmbed (nativeData a))) ∘
        GaussNativePotential.scalarField := rfl
  rw [hlin]
  exact (((scalarActionCLM (p286LieBlockEmbed (nativeData a))).restrictScalars ℝ).contDiff.contDiffAt).comp
    z.val GaussNativePotential.scalarField_smooth.contDiffAt

/-- The `a`-varied creation fibre is smooth on the original chart. -/
private theorem creation_delta_smooth (a : NativeLie) (channel s : Fin 2)
    (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => fiberCreation channel s
      (scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
        (GaussNativePotential.scalarField w))) z.val := by
  have hcoef : ∀ c : Fin 3, ContDiffAt ℝ ∞ (fun w =>
      scalarCoefficient channel c
        (scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
          (GaussNativePotential.scalarField w))) z.val := by
    intro c
    have hlin : (fun w : SourceCoordinateSlice =>
        scalarCoefficient channel c
          (scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
            (GaussNativePotential.scalarField w))) =
        ⇑(((scalarCoefficient channel c).toContinuousLinearMap).restrictScalars ℝ) ∘
          (fun w => scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
            (GaussNativePotential.scalarField w)) := rfl
    rw [hlin]
    exact ((ContinuousLinearMap.restrictScalars ℝ
      ((scalarCoefficient channel c).toContinuousLinearMap)).contDiff.contDiffAt).comp
        z.val (scalar_action_smooth a z)
  change ContDiffAt ℝ ∞ (fun w => ∑ c : Fin 3,
    star (scalarCoefficient channel c
      (scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
        (GaussNativePotential.scalarField w))) •
        GaussCARHistory.createFiber (mode s c)) z.val
  apply ContDiffAt.sum
  intro c _
  exact ((((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff).contDiffAt).comp
    z.val (hcoef c)).smul contDiffAt_const

/-- The scalar-varied weighted creation fibre is smooth. -/
private theorem scalar_weighted_fiber_smooth (a : NativeLie) (channel s : Fin 2)
    (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice =>
      scalarWeightedCreation a (sourceWeightSymbol w) channel s
        (GaussNativePotential.scalarField w)) z.val := by
  unfold scalarWeightedCreation weightedCreation
  show ContDiffAt ℝ ∞ (fun w =>
      quantized (sourceWeightSymbol w) * fiberCreation channel s
        (scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
          (GaussNativePotential.scalarField w)) -
      fiberCreation channel s
        (scalarMotherLieAction (p286LieBlockEmbed (nativeData a))
          (GaussNativePotential.scalarField w)) *
        quantized (sourceWeightSymbol w)) z.val
  exact ((weightFiber_smooth z).mul
    (creation_delta_smooth a channel s z)).sub
    ((creation_delta_smooth a channel s z).mul (weightFiber_smooth z))

/-- The weighted dressed creation core: the original root-volume
normalization and the original `localMultiplier`, on the original scalar
field and the actual source weight. -/
def weightedCreationCore (channel s : Fin 2) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => (rootVolume z : ℂ)⁻¹ •
      weightedCreation (sourceWeightSymbol z) channel s
        (GaussNativePotential.scalarField z))
    (fun z => ((root_volume_complex_smooth z).inv
      (Complex.ofReal_ne_zero.mpr (root_volume_pos z).ne')).smul
        (weighted_fiber_smooth channel s z))

/-- The scalar-varied weighted creation core: the same original normalization
against the `a`-varied scalar. -/
def scalarWeightedCore (a : NativeLie) (channel s : Fin 2) :
    QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => (rootVolume z : ℂ)⁻¹ •
      scalarWeightedCreation a (sourceWeightSymbol z) channel s
        (GaussNativePotential.scalarField z))
    (fun z => ((root_volume_complex_smooth z).inv
      (Complex.ofReal_ne_zero.mpr (root_volume_pos z).ne')).smul
        (scalar_weighted_fiber_smooth a channel s z))

/-- The raw temporal charge core against the original creation test: the
weighted Ward return with the scalar counter-variation and the hypercharge
weighted current on the right. -/
theorem raw_charge_core_ward (a : Fin 12) (channel s : Fin 2) (f : QuantumTest) :
    rawChargeCore a (creationTest channel s f) -
      creationTest channel s (rawChargeCore a f) =
    Complex.I • scalarWeightedCore (originalUnit a) channel s f +
      (Complex.I • (nativeData (originalUnit a)).2.2.1) •
        weightedCreationCore channel s f := by
  apply DFunLike.ext
  intro z
  have hsub : ∀ g h : QuantumTest, (g - h) z = g z - h z := fun _ _ => rfl
  have hadd : ∀ g h : QuantumTest, (g + h) z = g z + h z := fun _ _ => rfl
  have hsmul : ∀ (c : ℂ) (g : QuantumTest), (c • g) z = c • g z :=
    fun _ _ => rfl
  simp only [hsub, hadd, hsmul]
  by_cases inside : z ∈ physicalChart
  · have e1 : (rawChargeCore a (creationTest channel s f)) z =
        (rootVolume z : ℂ)⁻¹ •
          (rawChargeFiber a z * fiberCreation channel s
            (GaussNativePotential.scalarField z)) (f z) := by
      show rawChargeFiber a z ((creationTest channel s f) z) = _
      have hcre : (creationTest channel s f) z =
          (rootVolume z : ℂ)⁻¹ •
            fiberCreation channel s (GaussNativePotential.scalarField z)
              (f z) := rfl
      rw [hcre, map_smul]
      rfl
    have e2 : (creationTest channel s (rawChargeCore a f)) z =
        (rootVolume z : ℂ)⁻¹ •
          (fiberCreation channel s (GaussNativePotential.scalarField z) *
            rawChargeFiber a z) (f z) := by
      show (rootVolume z : ℂ)⁻¹ •
          fiberCreation channel s (GaussNativePotential.scalarField z)
            ((rawChargeCore a f) z) = _
      have hraw : (rawChargeCore a f) z = rawChargeFiber a z (f z) := rfl
      rw [hraw]
      rfl
    have e3 : (scalarWeightedCore (originalUnit a) channel s f) z =
        (rootVolume z : ℂ)⁻¹ •
          (scalarWeightedCreation (originalUnit a) (sourceWeightSymbol z)
            channel s (GaussNativePotential.scalarField z)) (f z) := rfl
    have e4 : (weightedCreationCore channel s f) z =
        (rootVolume z : ℂ)⁻¹ •
          (weightedCreation (sourceWeightSymbol z) channel s
            (GaussNativePotential.scalarField z)) (f z) := rfl
    rw [e1, e2, e3, e4, ← smul_sub]
    have hfiber : (rawChargeFiber a z * fiberCreation channel s
          (GaussNativePotential.scalarField z)) (f z) -
        (fiberCreation channel s (GaussNativePotential.scalarField z) *
          rawChargeFiber a z) (f z) =
      Complex.I • (scalarWeightedCreation (originalUnit a)
          (sourceWeightSymbol z) channel s
          (GaussNativePotential.scalarField z)) (f z) +
        (Complex.I • (nativeData (originalUnit a)).2.2.1) •
          (weightedCreation (sourceWeightSymbol z) channel s
            (GaussNativePotential.scalarField z)) (f z) := by
      have h := congrArg (fun T : FiberOp => T (f z))
        (raw_charge_weighted_creation a ⟨z, inside⟩ channel s)
      simp only [sub_apply, smul_apply] at h
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      exact add_comm _ _
    rw [hfiber, smul_add]
    apply congrArg₂ (· + ·)
    · exact smul_comm (rootVolume z : ℂ)⁻¹ Complex.I _
    · exact smul_comm (rootVolume z : ℂ)⁻¹
        (Complex.I • (nativeData (originalUnit a)).2.2.1) _
  · have outside : f z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz => inside
        (f.tsupport_subset hz))
    have c0 : (creationTest channel s f) z = 0 := by
      show (rootVolume z : ℂ)⁻¹ •
          fiberCreation channel s (GaussNativePotential.scalarField z)
            (f z) = 0
      rw [outside, map_zero, smul_zero]
    have r0 : (rawChargeCore a f) z = 0 := by
      show rawChargeFiber a z (f z) = 0
      rw [outside, map_zero]
    have s0 : (scalarWeightedCore (originalUnit a) channel s f) z = 0 := by
      show (rootVolume z : ℂ)⁻¹ •
          scalarWeightedCreation (originalUnit a) (sourceWeightSymbol z)
            channel s (GaussNativePotential.scalarField z) (f z) = 0
      rw [outside, map_zero, smul_zero]
    have w0 : (weightedCreationCore channel s f) z = 0 := by
      show (rootVolume z : ℂ)⁻¹ •
          weightedCreation (sourceWeightSymbol z) channel s
            (GaussNativePotential.scalarField z) (f z) = 0
      rw [outside, map_zero, smul_zero]
    rw [show (rawChargeCore a (creationTest channel s f)) z =
          rawChargeFiber a z ((creationTest channel s f) z) from rfl,
        c0, map_zero]
    rw [show (creationTest channel s (rawChargeCore a f)) z =
          (rootVolume z : ℂ)⁻¹ • fiberCreation channel s
            (GaussNativePotential.scalarField z) ((rawChargeCore a f) z)
        from rfl, r0, map_zero, smul_zero]
    rw [s0, w0, smul_zero, smul_zero, add_zero, sub_zero]

/-- The canonical actual-seed Ward return: the raw charge current on the
created seed section equals the seed current plus the scalar countervariation
and the hypercharge weighted current. The seed is the original
`CanonicalCompletedSector.seed` leg, not a guessed eigenstate. -/
theorem raw_charge_seed_ward (a : Fin 12) (channel s : Fin 2)
    (g : ScalarTest) :
    rawChargeCore a (creationTest channel s (seedSection g)) -
      creationTest channel s (rawChargeCore a (seedSection g)) =
    Complex.I • scalarWeightedCore (originalUnit a) channel s
        (seedSection g) +
      (Complex.I • (nativeData (originalUnit a)).2.2.1) •
        weightedCreationCore channel s (seedSection g) :=
  raw_charge_core_ward a channel s (seedSection g)

/-- The seed-current form: the full raw current on the created seed is the
created raw seed plus the scalar counter-variation plus the generated
hypercharge weighted current. -/
theorem raw_charge_seed_current (a : Fin 12) (channel s : Fin 2)
    (g : ScalarTest) :
    rawChargeCore a (creationTest channel s (seedSection g)) =
      creationTest channel s (rawChargeCore a (seedSection g)) +
        Complex.I • scalarWeightedCore (originalUnit a) channel s
          (seedSection g) +
        (Complex.I • (nativeData (originalUnit a)).2.2.1) •
          weightedCreationCore channel s (seedSection g) := by
  have h := raw_charge_seed_ward a channel s g
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- The weighted creation on a seed section evaluates to the fibre commutator
applied to the original canonical seed vector. -/
theorem weighted_creation_seed_eval (channel s : Fin 2) (g : ScalarTest)
    (z : physicalChart) :
    (weightedCreationCore channel s (seedSection g)) z.val =
      (rootVolume z.val : ℂ)⁻¹ •
        (weightedCreation (sourceWeightSymbol z.val) channel s
          (GaussNativePotential.scalarField z.val))
          (g z.val • CanonicalCompletedSector.seed) := by
  show (rootVolume z.val : ℂ)⁻¹ •
      weightedCreation (sourceWeightSymbol z.val) channel s
        (GaussNativePotential.scalarField z.val) ((seedSection g) z.val) = _
  rw [seedSection_apply]

/-- The actual EM phase vertex of the weighted Ward coupling: the `+1/2`
increment, from the public phase character `joint_phase_character` and the
certified `emDressedChargeUnit = 1/2`. -/
theorem weighted_creation_phase_vertex (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) (z : physicalChart) :
    (quantizer (sourceWeightSymbol z.val * chargeMatrix sourcePhaseGaugeLie) *
        fiberCreation channel s phi -
      fiberCreation channel s phi *
        quantizer (sourceWeightSymbol z.val * chargeMatrix sourcePhaseGaugeLie)) -
      Complex.I • scalarWeightedCreation sourcePhaseGaugeLie
        (sourceWeightSymbol z.val) channel s phi =
    (1 / 2 : ℂ) •
      weightedCreation (sourceWeightSymbol z.val) channel s phi := by
  rw [weighted_creation_coupling]
  have hH : (nativeData sourcePhaseGaugeLie).2.2.1 =
      emDressedCharacter false := by
    simpa using joint_phase_character false
  have hval : Complex.I • (nativeData sourcePhaseGaugeLie).2.2.1 =
      (1 / 2 : ℂ) := by
    rw [hH]
    show Complex.I * emDressedCharacter false = 1 / 2
    simp only [emDressedCharacter, Bool.false_eq_true, if_false,
      emDressedChargeUnit_value]
    push_cast
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
    ring
  rw [hval]

/-- At the original native `Y` direction the weighted vertex is `-1`: the
source-native hypercharge increment of the created test. -/
theorem weighted_creation_nativeY_vertex (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) (z : physicalChart) :
    (quantizer (sourceWeightSymbol z.val * chargeMatrix nativeY) *
        fiberCreation channel s phi -
      fiberCreation channel s phi *
        quantizer (sourceWeightSymbol z.val * chargeMatrix nativeY)) -
      Complex.I • scalarWeightedCreation nativeY
        (sourceWeightSymbol z.val) channel s phi =
    (-1 : ℂ) •
      weightedCreation (sourceWeightSymbol z.val) channel s phi := by
  rw [weighted_creation_coupling]
  have hH : (nativeData nativeY).2.2.1 = Complex.I := by
    have hd : nativeData nativeY =
        Stage10.HyperchargeResponse.chargeDirection := by
      show p286CoordinateEquiv.symm
          (p286CoordinateEquiv Stage10.HyperchargeResponse.chargeDirection) = _
      exact LinearEquiv.symm_apply_apply _ _
    rw [hd]
    rfl
  rw [hH]
  show (Complex.I • Complex.I) •
      weightedCreation (sourceWeightSymbol z.val) channel s phi = _
  rw [smul_eq_mul, Complex.I_mul_I]

/-- Colour and weak directions do not vanish as raw currents: their weighted
commutator equals the scalar counter-variation exactly. -/
theorem weighted_creation_colour_compensator (W : FullMatrix) (a : NativeLie)
    (hhyper : (nativeData a).2.2.1 = 0) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    (quantizer (W * chargeMatrix a) * fiberCreation channel s phi -
        fiberCreation channel s phi * quantizer (W * chargeMatrix a)) =
      Complex.I • scalarWeightedCreation a W channel s phi := by
  have h := weighted_creation_coupling W a channel s phi
  rw [hhyper] at h
  apply sub_eq_zero.mp
  rw [smul_zero] at h
  exact h.trans (zero_smul ℂ (weightedCreation W channel s phi))

end LowEnergy.WeightedActualSeed
