import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedP286Scalar

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section

namespace LowEnergy.DressedColourY

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
open DressedColourYScalarColumns DressedColourYScalarRows DressedColourY
open scoped BigOperators ContDiff InnerProductSpace Matrix

attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq
local instance : NormedAlgebra ℝ FiberOp := NormedAlgebra.restrictScalars ℝ ℂ _

/-- The original two-channel modes are the positive root modes of the shared
matter carrier; no identification premise is added. -/
private theorem mode_eq (spin : Fin 2) (c : Fin 3) :
    mode spin c = rootMode false ⟨spin.castLE (by decide), c⟩ := by
  rfl

private theorem root_collapse {V : Type*} [AddCommGroup V] [Module ℂ V]
    (spin : Fin 2) (b : Fin 3 → ℂ) (X : Mode → V) :
    (∑ j : Mode, (∑ r : Fin 3, b r *
          (if j = rootMode false ⟨spin.castLE (by decide), r⟩ then 1 else 0)) • X j) =
      ∑ r : Fin 3, b r • X (rootMode false ⟨spin.castLE (by decide), r⟩) := by
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

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

/-- The original native full creation commutator on a named mode: the colour
column plus the scalar hypercharge weight. -/
private theorem joint_create_column (a : NativeLie) (spin : Fin 2) (c : Fin 3) :
    quantized (nativeFull a) * GaussCARHistory.createFiber (mode spin c) -
      GaussCARHistory.createFiber (mode spin c) * quantized (nativeFull a) =
    (∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r c •
        GaussCARHistory.createFiber (mode spin r)) +
      (nativeData a).2.2.1 • GaussCARHistory.createFiber (mode spin c) := by
  rw [quantized_creation_column]
  unfold creationColumn
  rw [mode_eq spin c]
  rw [Finset.sum_congr rfl (fun j _ =>
    congrArg (fun m => m • GaussCARHistory.createFiber j)
      (actual_full_native_column false a ⟨spin.castLE (by decide), c⟩ j))]
  erw [root_collapse_full ⟨spin.castLE (by decide), c⟩
    (fun r => colorEntry false (nativeData a).1 r c)
    (nativeHyper false a) (fun j => GaussCARHistory.createFiber j)]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r _
    show colorEntry false (nativeData a).1 r c •
        GaussCARHistory.createFiber (mode spin r) =
        ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r c •
          GaussCARHistory.createFiber (mode spin r)
    simp [colorEntry]
  · show nativeHyper false a • GaussCARHistory.createFiber (mode spin c) =
        (nativeData a).2.2.1 • GaussCARHistory.createFiber (mode spin c)
    simp [nativeHyper]

/-- The hypercharge block coefficient is purely imaginary. -/
private theorem hyper_star (a : NativeLie) :
    star (nativeData a).2.2.1 = -(nativeData a).2.2.1 :=
  skewAdjoint.mem_iff.mp (nativeData a).2.2.property

/-- Special-unitary colour matrices are skew-adjoint pointwise. -/
private theorem colour_conjugate (data : P286LieBlockData) (c d : Fin 3) :
    star ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) c d) =
      -((data.1 : Matrix (Fin 3) (Fin 3) ℂ) d c) := by
  have skewed := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M d c)
    (specialUnitaryLieMatrix_star data.1)
  simpa [Matrix.star_apply, Matrix.neg_apply] using skewed

/-- Row entries of the full native matrix on the positive named modes,
transported through the star-column formula. -/
private theorem native_row_entry (a : NativeLie) (i : NamedMode) (j : Mode) :
    nativeFull a (rootMode false i) j =
      (∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) i.2 r *
          (if j = rootMode false (i.1, r) then 1 else 0)) +
        (nativeData a).2.2.1 * (if j = rootMode false i then 1 else 0) := by
  have skew := congrArg (fun M : Matrix Mode Mode ℂ => M (rootMode false i) j)
    (nativeFull_skew a)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at skew
  rw [actual_full_native_column] at skew
  have target : nativeFull a (rootMode false i) j =
      -star ((∑ r : Fin 3, colorEntry false (nativeData a).1 r i.2 *
          (if j = rootMode false (i.1, r) then 1 else 0)) +
        nativeHyper false a * (if j = rootMode false i then 1 else 0)) := by
    linear_combination skew
  rw [target]
  simp only [colorEntry, nativeHyper, Bool.false_eq_true, ite_false, star_add,
    star_sum, star_mul, mul_neg, apply_ite star, star_one, star_zero,
    colour_conjugate, hyper_star, Finset.sum_neg_distrib, neg_neg, neg_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    rw [mul_comm]
  · rw [mul_comm]

/-- The original native full annihilation commutator on a named mode. -/
private theorem joint_annihilate_row (a : NativeLie) (spin : Fin 2) (c : Fin 3) :
    quantized (nativeFull a) * GaussCARHistory.annihilateFiber (mode spin c) -
      GaussCARHistory.annihilateFiber (mode spin c) * quantized (nativeFull a) =
    -((∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) c r •
        GaussCARHistory.annihilateFiber (mode spin r)) +
      (nativeData a).2.2.1 • GaussCARHistory.annihilateFiber (mode spin c)) := by
  rw [quantized_annihilation_row]
  unfold annihilationRow
  rw [mode_eq spin c]
  rw [Finset.sum_congr rfl (fun j _ =>
    congrArg (fun m => m • GaussCARHistory.annihilateFiber j)
      (native_row_entry a ⟨spin.castLE (by decide), c⟩ j))]
  erw [root_collapse_full ⟨spin.castLE (by decide), c⟩
    (fun r => ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) c r)
    (nativeData a).2.2.1 (fun j => GaussCARHistory.annihilateFiber j)]
  congr 1

/-- The joint scalar-plus-matter dressed fibre: the scalar Noether action
minus the original CAR commutator of the full native generator. -/
def jointDressedFiber (a : NativeLie) (addition : Bool) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) : FiberOp :=
  if addition then
    fiberCreation channel s
      (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi) -
      (quantized (nativeFull a) * fiberCreation channel s phi -
        fiberCreation channel s phi * quantized (nativeFull a))
  else
    fiberAnnihilation channel s
      (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi) -
      (quantized (nativeFull a) * fiberAnnihilation channel s phi -
        fiberAnnihilation channel s phi * quantized (nativeFull a))

private theorem creation_distribute (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    quantized (nativeFull a) * fiberCreation channel s phi -
      fiberCreation channel s phi * quantized (nativeFull a) =
    ∑ d : Fin 3, star (scalarCoefficient channel d phi) •
      (quantized (nativeFull a) * GaussCARHistory.createFiber (mode s d) -
        GaussCARHistory.createFiber (mode s d) * quantized (nativeFull a)) := by
  unfold fiberCreation
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_smul_comm, smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [smul_sub]

private theorem annihilation_distribute (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    quantized (nativeFull a) * fiberAnnihilation channel s phi -
      fiberAnnihilation channel s phi * quantized (nativeFull a) =
    ∑ d : Fin 3, (scalarCoefficient channel d phi) •
      (quantized (nativeFull a) * GaussCARHistory.annihilateFiber (mode s d) -
        GaussCARHistory.annihilateFiber (mode s d) * quantized (nativeFull a)) := by
  unfold fiberAnnihilation
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_smul_comm, smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [smul_sub]

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

private theorem create_decomp (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) (d : Fin 3) :
    star (scalarCoefficient channel d phi) •
      ((∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d •
          GaussCARHistory.createFiber (mode s r)) +
        (nativeData a).2.2.1 • GaussCARHistory.createFiber (mode s d)) =
    (∑ r : Fin 3, (star (scalarCoefficient channel d phi) *
        ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d) •
        GaussCARHistory.createFiber (mode s r)) +
      ((nativeData a).2.2.1 * star (scalarCoefficient channel d phi)) •
        GaussCARHistory.createFiber (mode s d) := by
  rw [smul_add, Finset.smul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun r _ =>
      smul_smul (star (scalarCoefficient channel d phi))
        (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d)
        (GaussCARHistory.createFiber (mode s r))
  · rw [smul_smul, mul_comm]

private theorem create_lhs_entry (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) (d : Fin 3) :
    (∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
        star (scalarCoefficient channel r phi)) •
      GaussCARHistory.createFiber (mode s d) =
    ∑ r : Fin 3, (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
        star (scalarCoefficient channel r phi)) •
        GaussCARHistory.createFiber (mode s d) := by
  exact Finset.sum_smul (s := Finset.univ)
    (f := fun r => ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
      star (scalarCoefficient channel r phi))
    (x := GaussCARHistory.createFiber (mode s d))

private theorem create_hyper_pull (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    (∑ d : Fin 3, ((nativeData a).2.2.1 * star (scalarCoefficient channel d phi)) •
        GaussCARHistory.createFiber (mode s d)) =
      (nativeData a).2.2.1 •
        (∑ d : Fin 3, star (scalarCoefficient channel d phi) •
          GaussCARHistory.createFiber (mode s d)) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← smul_smul]

private theorem create_colsum (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    (∑ d : Fin 3, ∑ r : Fin 3, (star (scalarCoefficient channel d phi) *
        ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d) •
        GaussCARHistory.createFiber (mode s r)) =
      ∑ d : Fin 3, ∑ r : Fin 3, (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r *
          star (scalarCoefficient channel r phi)) •
        GaussCARHistory.createFiber (mode s d) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  ring

/-- The creation joint fibre carries the pure hypercharge character `-H`. -/
theorem joint_dressed_creation (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    jointDressedFiber a true channel s phi =
      -(nativeData a).2.2.1 • fiberCreation channel s phi := by
  unfold jointDressedFiber
  simp only [ite_true]
  rw [creation_distribute]
  rw [Finset.sum_congr rfl (fun d _ =>
    congrArg (fun X => star (scalarCoefficient channel d phi) • X)
      (joint_create_column a s d))]
  rw [Finset.sum_congr rfl (fun d _ => create_decomp a channel s phi d)]
  rw [Finset.sum_add_distrib, create_hyper_pull a channel s phi]
  unfold fiberCreation
  rw [Finset.sum_congr rfl (fun d _ =>
    congrArg₂ (· • ·) (coeff_star_swap a channel d phi) rfl)]
  rw [Finset.sum_congr rfl (fun d _ => create_lhs_entry a channel s phi d)]
  rw [create_colsum a channel s phi]
  module

private theorem annih_decomp (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) (d : Fin 3) :
    scalarCoefficient channel d phi •
      (-((∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r •
          GaussCARHistory.annihilateFiber (mode s r)) +
        (nativeData a).2.2.1 • GaussCARHistory.annihilateFiber (mode s d))) =
    -((∑ r : Fin 3, (scalarCoefficient channel d phi *
        ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r) •
        GaussCARHistory.annihilateFiber (mode s r)) +
      ((nativeData a).2.2.1 * scalarCoefficient channel d phi) •
        GaussCARHistory.annihilateFiber (mode s d)) := by
  rw [smul_neg, smul_add, Finset.smul_sum]
  congr 1
  apply congrArg₂ (· + ·)
  · exact Finset.sum_congr rfl fun r _ =>
      smul_smul (scalarCoefficient channel d phi)
        (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r)
        (GaussCARHistory.annihilateFiber (mode s r))
  · rw [smul_smul, mul_comm]

private theorem annih_lhs_entry (a : NativeLie) (channel s : Fin 2)
    (d : Fin 3) (phi : ScalarCoordinateCarrier) :
    (-(∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d *
        scalarCoefficient channel r phi)) •
      GaussCARHistory.annihilateFiber (mode s d) =
    -(∑ r : Fin 3, (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d *
        scalarCoefficient channel r phi) •
        GaussCARHistory.annihilateFiber (mode s d)) := by
  exact (neg_smul (∑ r : Fin 3, ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d *
        scalarCoefficient channel r phi)
        (GaussCARHistory.annihilateFiber (mode s d))).trans
    (congrArg Neg.neg (Finset.sum_smul (s := Finset.univ)
      (f := fun r => ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d *
        scalarCoefficient channel r phi)
      (x := GaussCARHistory.annihilateFiber (mode s d))))

private theorem annih_hyper_pull (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    (∑ d : Fin 3, ((nativeData a).2.2.1 * scalarCoefficient channel d phi) •
        GaussCARHistory.annihilateFiber (mode s d)) =
      (nativeData a).2.2.1 •
        (∑ d : Fin 3, scalarCoefficient channel d phi •
          GaussCARHistory.annihilateFiber (mode s d)) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← smul_smul]

private theorem annih_colsum (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    (∑ d : Fin 3, ∑ r : Fin 3, ((scalarCoefficient channel d phi) *
        ((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) d r) •
        GaussCARHistory.annihilateFiber (mode s r)) =
      ∑ d : Fin 3, ∑ r : Fin 3, (((nativeData a).1 : Matrix (Fin 3) (Fin 3) ℂ) r d *
          scalarCoefficient channel r phi) •
        GaussCARHistory.annihilateFiber (mode s d) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  ring

/-- The annihilation joint fibre carries the pure hypercharge character `+H`. -/
theorem joint_dressed_annihilation (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    jointDressedFiber a false channel s phi =
      (nativeData a).2.2.1 • fiberAnnihilation channel s phi := by
  unfold jointDressedFiber
  simp only [Bool.false_eq_true, ite_false]
  rw [annihilation_distribute]
  rw [Finset.sum_congr rfl (fun d _ =>
    congrArg (fun X => scalarCoefficient channel d phi • X)
      (joint_annihilate_row a s d))]
  rw [Finset.sum_congr rfl (fun d _ => annih_decomp a channel s phi d)]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib,
    annih_hyper_pull a channel s phi]
  unfold fiberAnnihilation
  rw [Finset.sum_congr rfl (fun d _ =>
    congrArg₂ (· • ·) (scalar_action_row a channel d phi) rfl)]
  rw [Finset.sum_congr rfl (fun d _ => annih_lhs_entry a channel s d phi)]
  rw [Finset.sum_neg_distrib, annih_colsum a channel s phi]
  abel

theorem joint_fiber_return (a : NativeLie) (addition : Bool) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    jointDressedFiber a addition channel s phi =
      (if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1) •
        (if addition then fiberCreation channel s phi
          else fiberAnnihilation channel s phi) := by
  cases addition
  · exact joint_dressed_annihilation a channel s phi
  · exact joint_dressed_creation a channel s phi

/-- The joint dressed test: original `scalarField z`, the original root-volume
normalization and the original `localMultiplier`. -/
def jointDressedTest (a : NativeLie) (addition : Bool) (channel s : Fin 2) :
    QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z =>
    (if addition then (rootVolume z : ℂ)⁻¹ else (rootVolume z : ℂ)) •
      jointDressedFiber a addition channel s
        (GaussNativePotential.scalarField z)) (by
    intro z
    simp only [joint_fiber_return]
    cases addition
    · simp only [Bool.false_eq_true, if_false]
      exact (root_volume_complex_smooth z).smul
        (((annihilation_matrix_smooth channel s).contDiffAt).const_smul _)
    · simp only [if_true]
      exact ((root_volume_complex_smooth z).inv
        (Complex.ofReal_ne_zero.mpr (root_volume_pos z).ne')).smul
          (((creation_matrix_smooth channel s).contDiffAt).const_smul _))

/-- The joint test character: pure hypercharge readout on the original legs. -/
theorem jointDressedTest_return (a : NativeLie) (addition : Bool)
    (channel s : Fin 2) (f : QuantumTest) :
    jointDressedTest a addition channel s f =
      (if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1) •
        (if addition then creationTest channel s f
          else annihilationTest channel s f) := by
  apply DFunLike.ext
  intro z
  cases addition
  · change (rootVolume z : ℂ) •
        (jointDressedFiber a false channel s
          (GaussNativePotential.scalarField z) (f z)) =
      (nativeData a).2.2.1 • ((rootVolume z : ℂ) •
        (fiberAnnihilation channel s (GaussNativePotential.scalarField z) (f z)))
    rw [joint_fiber_return]
    exact smul_comm (rootVolume z : ℂ) (nativeData a).2.2.1
      (fiberAnnihilation channel s (GaussNativePotential.scalarField z) (f z))
  · change (rootVolume z : ℂ)⁻¹ •
        (jointDressedFiber a true channel s
          (GaussNativePotential.scalarField z) (f z)) =
      -(nativeData a).2.2.1 • ((rootVolume z : ℂ)⁻¹ •
        (fiberCreation channel s (GaussNativePotential.scalarField z) (f z)))
    rw [joint_fiber_return]
    exact smul_comm (rootVolume z : ℂ)⁻¹ (-(nativeData a).2.2.1)
      (fiberCreation channel s (GaussNativePotential.scalarField z) (f z))

/-- The joint dressed letter embeds the joint dressed test. -/
def jointDressedLetter (a : NativeLie) (addition : Bool) (channel s : Fin 2) :
    QuantumTest →ₗ[ℂ] H :=
  embed.comp (jointDressedTest a addition channel s)

theorem jointDressedLetter_return (a : NativeLie) (addition : Bool)
    (channel s : Fin 2) :
    jointDressedLetter a addition channel s =
      (if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1) •
        leg addition channel s := by
  apply LinearMap.ext
  intro f
  simp only [jointDressedLetter, LinearMap.comp_apply, jointDressedTest_return,
    map_smul, LinearMap.smul_apply]
  cases addition <;> simp only [Bool.false_eq_true, if_false, if_true, leg,
    embed_creation_test, embed_annihilation_test]

/-- The joint dressed core composes the letter with the original seed. -/
def jointDressedCore (a : NativeLie) (addition : Bool) (channel s : Fin 2) :
    ScalarTest →ₗ[ℂ] H :=
  (jointDressedLetter a addition channel s).comp seedSection

theorem jointDressedCore_return (a : NativeLie) (addition : Bool)
    (channel s : Fin 2) (f : ScalarTest) :
    jointDressedCore a addition channel s f =
      (if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1) •
        legCore addition channel s f := by
  rw [jointDressedCore, jointDressedLetter_return]
  rfl

private theorem joint_dressed_bound (a : NativeLie) (addition : Bool)
    (channel s : Fin 2) (f : ScalarTest) :
    ‖jointDressedCore a addition channel s f‖ ≤
      (‖(if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1)‖ *
          legBound) * ‖core f‖ := by
  rw [jointDressedCore_return, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (legCore_bound addition channel s f)
    (norm_nonneg _)

/-- The completed joint leg uses the same original core bound and the same
core-dense completion seam. -/
def jointDressedCompleted (a : NativeLie) (addition : Bool) (channel s : Fin 2) :
    Profile →L[ℂ] H :=
  (jointDressedCore a addition channel s).extendOfNorm core

theorem jointDressedCompleted_core (a : NativeLie) (addition : Bool)
    (channel s : Fin 2) (f : ScalarTest) :
    jointDressedCompleted a addition channel s (core f) =
      jointDressedCore a addition channel s f :=
  LinearMap.extendOfNorm_eq core_dense
    ⟨_, joint_dressed_bound a addition channel s⟩ f

theorem jointDressedCompleted_return (a : NativeLie) (addition : Bool)
    (channel s : Fin 2) (f : Profile) :
    jointDressedCompleted a addition channel s f =
      (if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1) •
        completedLeg addition channel s f := by
  have equality : jointDressedCompleted a addition channel s =
      (if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1) •
        completedLeg addition channel s := by
    apply LinearMap.extendOfNorm_unique core_dense _
      (joint_dressed_bound a addition channel s)
    apply LinearMap.ext
    intro g
    simp only [LinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_coe, completedLeg_core, jointDressedCore_return,
      legCore]
  exact congrArg (fun T : Profile →L[ℂ] H => T f) equality

/-- The joint variation vanishes on every generator with zero hypercharge
block: colour and weak directions are source-neutral here. -/
theorem joint_block_zero (a : NativeLie)
    (hhyper : (nativeData a).2.2.1 = 0) (addition : Bool) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    jointDressedFiber a addition channel s phi = 0 := by
  rw [joint_fiber_return, hhyper]
  cases addition
  · simp only [Bool.false_eq_true, ite_false]
    exact zero_smul ℂ (fiberAnnihilation channel s phi)
  · simp only [ite_true, neg_zero]
    exact zero_smul ℂ (fiberCreation channel s phi)

theorem joint_colour_zero (A : SU3BlockLieMatrix) (addition : Bool)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    jointDressedFiber (colorNative A) addition channel s phi = 0 := by
  apply joint_block_zero
  have hd : nativeData (colorNative A) = colorData A := by
    show p286CoordinateEquiv.symm (p286CoordinateEquiv (colorData A)) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [hd]
  rfl

private theorem nativeY_hyper :
    (nativeData nativeY).2.2.1 = Complex.I := by
  have hd : nativeData nativeY = Stage10.HyperchargeResponse.chargeDirection := by
    show p286CoordinateEquiv.symm
        (p286CoordinateEquiv Stage10.HyperchargeResponse.chargeDirection) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [hd]
  rfl

private theorem colorGenerator_two_hyper_zero :
    (nativeData (SourceQuantumResidualGaugeSlice.colorGenerator 2)).2.2.1 = 0 := by
  have hd : nativeData (SourceQuantumResidualGaugeSlice.colorGenerator 2) =
      sourceColorP286Generator 2 := by
    show p286CoordinateEquiv.symm
        (p286CoordinateEquiv (sourceColorP286Generator 2)) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [hd]
  simp only [sourceColorP286Generator, Prod.smul_snd, smul_zero]
  rfl

private theorem phase_hyper :
    (nativeData sourcePhaseGaugeLie).2.2.1 = -Complex.I / 2 := by
  have hd : nativeData sourcePhaseGaugeLie =
      -(nativeData (SourceQuantumResidualGaugeSlice.colorGenerator 2)) -
        (1 / 2 : ℝ) • nativeData nativeY := by
    show p286CoordinateEquiv.symm
        (-(SourceQuantumResidualGaugeSlice.colorGenerator 2) -
          (1 / 2 : ℝ) • nativeY) = _
    erw [map_sub, map_neg, LinearEquiv.map_smul]
    rfl
  rw [hd]
  show -↑(nativeData (SourceQuantumResidualGaugeSlice.colorGenerator 2)).2.2 -
      (1 / 2 : ℝ) • ↑(nativeData nativeY).2.2 = -Complex.I / 2
  rw [nativeY_hyper, colorGenerator_two_hyper_zero, Complex.real_smul]
  push_cast
  ring

/-- The source phase generator carries the electromagnetic dressed character:
creation `+I/2`, annihilation `-I/2`. -/
theorem joint_phase_character (addition : Bool) :
    (if addition then -(nativeData sourcePhaseGaugeLie).2.2.1
      else (nativeData sourcePhaseGaugeLie).2.2.1) =
      emDressedCharacter addition := by
  rw [phase_hyper]
  cases addition <;>
    simp [emDressedCharacter, emDressedChargeUnit_value] <;> ring

/-- The joint phase-dressed leg is the EM-dressed leg on the actual source
preparation profile. -/
theorem joint_phase_completed (addition : Bool) (channel s : Fin 2)
    (f : Profile) :
    jointDressedCompleted sourcePhaseGaugeLie addition channel s f =
      emDressedCharacter addition • completedLeg addition channel s f := by
  rw [jointDressedCompleted_return, joint_phase_character]

/-- The actual unit creation channel of the actual dressed source excitation
receives the phase joint variation as the EM dressed excitation itself. -/
theorem joint_phase_actual_creation (epsilon : ℝ) (precision : 0 < epsilon) :
    jointDressedCompleted sourcePhaseGaugeLie true 1 0
        (sourceProfile epsilon precision) =
      sourceDressedExcitation epsilon precision := by
  rw [joint_phase_completed, sourceDressedExcitation, sourceDressedAddition,
    emDressedCompleted_return]

/-- The actual unit variation is nonzero whenever the generator's hypercharge
block is nonzero; it consumes the actual norm-one source unit. -/
theorem joint_actual_nonzero (a : NativeLie)
    (hhyper : (nativeData a).2.2.1 ≠ 0) (epsilon : ℝ) (precision : 0 < epsilon) :
    jointDressedCompleted a true 1 0 (sourceProfile epsilon precision) ≠ 0 := by
  rw [jointDressedCompleted_return]
  have leg : completedLeg true 1 0 (sourceProfile epsilon precision) ≠ 0 := by
    intro zero
    have nonzero := actual_dressed_creation_nonzero epsilon precision
    rw [emDressedCompleted_return, zero, smul_zero] at nonzero
    exact nonzero rfl
  intro zero
  rcases smul_eq_zero.mp zero with hzero | hzero
  · exact hhyper (neg_eq_zero.mp hzero)
  · exact leg hzero

/-- The original nativeY variation on the actual source preparation is `-I`
on creation and `+I` on annihilation, and it is nonzero. -/
theorem joint_nativeY_actual (epsilon : ℝ) (precision : 0 < epsilon) :
    jointDressedCompleted nativeY true 1 0 (sourceProfile epsilon precision) =
      -Complex.I • completedLeg true 1 0 (sourceProfile epsilon precision) ∧
    jointDressedCompleted nativeY true 1 0
        (sourceProfile epsilon precision) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [jointDressedCompleted_return, nativeY_hyper]
    simp
  · exact joint_actual_nonzero nativeY (by rw [nativeY_hyper]; simp) epsilon precision

/-- The phase-dressed variation reproduces the existing EM dressed excitation
on the same unit preparation; hence the actual nonzero unit variation. -/
theorem joint_phase_nonzero (epsilon : ℝ) (precision : 0 < epsilon) :
    jointDressedCompleted sourcePhaseGaugeLie true 1 0
        (sourceProfile epsilon precision) ≠ 0 := by
  rw [joint_phase_actual_creation]
  exact source_dressed_excitation_nonzero epsilon precision

end LowEnergy.DressedColourY
