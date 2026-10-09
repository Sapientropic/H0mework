import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestPoleSpectrum

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter
open YangMills.FullPairing Electromagnetic.ExternalState Stage9DEF Stage9DEF.Compatibility
open Filter Set
open scoped BigOperators Matrix InnerProductSpace Topology

abbrev RestMatterMatrix := Matrix (Fin 4) (Fin 4) ℂ

def actualRestCarrierHamiltonian (point : BasePoint) (side : Fin 2) : RestMatterMatrix := fun row column=>
  inner ℂ (operator (actualRestStatePreparation (side,row)) (YangMills.FullPairing.prepared point))
    (operator (FullQuantum.hamiltonian Runtime.configuration point 0)
      (operator (actualRestStatePreparation (side,column)) (YangMills.FullPairing.prepared point)))

def sourceRestEnergyMatrix (side : Fin 2) : RestMatterMatrix :=
  Matrix.diagonal (fun state=>sourceRestPoleEnergy (sourceRestStatePole (side,state)))

theorem actualRestCarrierHamiltonian_generated (point : BasePoint) (side : Fin 2) :
    actualRestCarrierHamiltonian point side=sourceRestEnergyMatrix side := by
  ext row column
  have projected : sourceRestPoleProjection (sourceRestStatePole (side,column)) *ᵥ
      actualRestStateCoordinates point (side,column)=actualRestStateCoordinates point (side,column) := by
    rw [actualRestStateCoordinates,Matrix.mulVec_smul,sourceRestState_projection]
  have physical:=sourceRestPoleProjection_physical (sourceRestStatePole (side,column)) point
    (actualRestStateCoordinates point (side,column))
  rw [projected] at physical
  have eigen : operator (FullQuantum.hamiltonian Runtime.configuration point 0)
      (operator (actualRestStatePreparation (side,column)) (YangMills.FullPairing.prepared point))=
      sourceRestPoleEnergy (sourceRestStatePole (side,column)) •
        operator (actualRestStatePreparation (side,column)) (YangMills.FullPairing.prepared point) := by
    rw [actualRestState_full_prepared,operator_coordinates,physical,map_smul]
  simp only [actualRestCarrierHamiltonian,eigen,inner_smul_right,actualRestState_orthonormal]
  by_cases same : row=column
  · subst column
    simp [sourceRestEnergyMatrix]
  · simp [sourceRestEnergyMatrix,same]

/-- This is the original Hamiltonian commutator on actual rest-pole observables. -/
def actualRestMatterGenerator (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) : RestMatterMatrix :=
  Complex.I • (actualRestCarrierHamiltonian point side*observable-observable*actualRestCarrierHamiltonian point side)

theorem actualRestMatterGenerator_entry (point : BasePoint) (side : Fin 2)
    (observable : RestMatterMatrix) (row column : Fin 4) :
    actualRestMatterGenerator point side observable row column=
      Complex.I*(sourceRestPoleEnergy (sourceRestStatePole (side,row))-
        sourceRestPoleEnergy (sourceRestStatePole (side,column)))*observable row column := by
  rw [actualRestMatterGenerator,actualRestCarrierHamiltonian_generated]
  simp only [sourceRestEnergyMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

def sourceRestLight (observable : RestMatterMatrix) : RestMatterMatrix := fun row column=>
  if (row=0 ↔ column=0) then observable row column else 0

def sourceRestHeavyUp (observable : RestMatterMatrix) : RestMatterMatrix := fun row column=>
  if row=0 ∧ column≠0 then observable row column else 0

def sourceRestHeavyDown (observable : RestMatterMatrix) : RestMatterMatrix := fun row column=>
  if row≠0 ∧ column=0 then observable row column else 0

theorem sourceRestMatter_partition (observable : RestMatterMatrix) :
    sourceRestLight observable+sourceRestHeavyUp observable+sourceRestHeavyDown observable=observable := by
  ext row column
  by_cases left : row=0 <;> by_cases right : column=0 <;>
    simp [sourceRestLight,sourceRestHeavyUp,sourceRestHeavyDown,left,right]

theorem sourceRestLight_idempotent (observable : RestMatterMatrix) :
    sourceRestLight (sourceRestLight observable)=sourceRestLight observable := by
  ext row column
  by_cases left : row=0 <;> by_cases right : column=0 <;> simp [sourceRestLight,left,right]

theorem sourceRestHeavyUp_idempotent (observable : RestMatterMatrix) :
    sourceRestHeavyUp (sourceRestHeavyUp observable)=sourceRestHeavyUp observable := by
  ext row column
  by_cases left : row=0 <;> by_cases right : column=0 <;> simp [sourceRestHeavyUp,left,right]

theorem sourceRestHeavyDown_idempotent (observable : RestMatterMatrix) :
    sourceRestHeavyDown (sourceRestHeavyDown observable)=sourceRestHeavyDown observable := by
  ext row column
  by_cases left : row=0 <;> by_cases right : column=0 <;> simp [sourceRestHeavyDown,left,right]

private theorem sourceRestEnergy_entry (side : Fin 2) (state : Fin 4) :
    sourceRestPoleEnergy (sourceRestStatePole (side,state))=
      sourceRestSign side*(frequency : ℂ)*(if state=0 then 1 else 3) := by
  by_cases zero : state=0 <;>
    norm_num [sourceRestStatePole,sourceRestPoleEnergy,sourceRestSymmetry,zero]

def sourceRestHeavyEigenvalue (side : Fin 2) : ℂ := 2*Complex.I*sourceRestSign side*(frequency : ℂ)

theorem actualRestMatterGenerator_light (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatterGenerator point side (sourceRestLight observable)=0 := by
  ext row column
  rw [actualRestMatterGenerator_entry,sourceRestEnergy_entry,sourceRestEnergy_entry]
  by_cases left : row=0 <;> by_cases right : column=0 <;>
    simp [sourceRestLight,left,right]

theorem actualRestMatterGenerator_heavyUp (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatterGenerator point side (sourceRestHeavyUp observable)=
      (-sourceRestHeavyEigenvalue side) • sourceRestHeavyUp observable := by
  ext row column
  rw [actualRestMatterGenerator_entry,sourceRestEnergy_entry,sourceRestEnergy_entry]
  by_cases left : row=0 <;> by_cases right : column=0 <;>
    norm_num [sourceRestHeavyUp,sourceRestHeavyEigenvalue,Matrix.smul_apply,left,right]
  ring

theorem actualRestMatterGenerator_heavyDown (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatterGenerator point side (sourceRestHeavyDown observable)=
      sourceRestHeavyEigenvalue side • sourceRestHeavyDown observable := by
  ext row column
  rw [actualRestMatterGenerator_entry,sourceRestEnergy_entry,sourceRestEnergy_entry]
  by_cases left : row=0 <;> by_cases right : column=0 <;>
    norm_num [sourceRestHeavyDown,sourceRestHeavyEigenvalue,Matrix.smul_apply,left,right]
  left
  ring

theorem sourceRestLight_current_stationary (direction : Fin 3) (point : BasePoint) (side : Fin 2) :
    actualRestMatterGenerator point side (sourceRestLight (sourceRestChargeMixingBlock direction))=0 :=
  actualRestMatterGenerator_light point side _

def sourceRestMatchingClock : ℝ := lapse*spinScale

theorem sourceRestMatchingClock_pos : 0<sourceRestMatchingClock := mul_pos lapse_pos spinScale_pos

theorem sourceRestMatchingClock_frequency : frequency=(3/5 : ℝ)*sourceRestMatchingClock := by
  unfold frequency gaugeScale sourceRestMatchingClock
  ring

def actualMatterCarrierHamiltonian (point : BasePoint) (side : Fin 2) (momentum : Fin 3→ℝ) : RestMatterMatrix :=
  fun row column=>inner ℂ
    (operator (actualRestStatePreparation (side,row)) (YangMills.FullPairing.prepared point))
    (operator (FullQuantum.hamiltonian Runtime.configuration point momentum)
      (operator (actualRestStatePreparation (side,column)) (YangMills.FullPairing.prepared point)))

def actualMatterMatchingSylvester (point : BasePoint) (side : Fin 2) (left right : Fin 3→ℝ)
    (observable : RestMatterMatrix) : RestMatterMatrix :=
  (Complex.I/(sourceRestMatchingClock : ℂ)) •
    (actualMatterCarrierHamiltonian point side left*observable-observable*actualMatterCarrierHamiltonian point side right)

/-- The matching source uses its original c=N√2 clock on the same Hamiltonian, with both momenta set to zero. -/
def actualRestMatchingSylvester (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) : RestMatterMatrix :=
  ((sourceRestMatchingClock : ℂ)⁻¹) • actualRestMatterGenerator point side observable

theorem actualRestMatchingSylvester_source (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatchingSylvester point side observable=
      (Complex.I/(sourceRestMatchingClock : ℂ)) •
        (actualRestCarrierHamiltonian point side*observable-observable*actualRestCarrierHamiltonian point side) := by
  simp only [actualRestMatchingSylvester,actualRestMatterGenerator,smul_smul,div_eq_mul_inv]
  congr 1
  ring

theorem actualMatterMatchingSylvester_atRest (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualMatterMatchingSylvester point side 0 0 observable=actualRestMatchingSylvester point side observable := by
  rw [actualRestMatchingSylvester_source]
  rfl

theorem sourceRestHeavyEigenvalue_normalized (side : Fin 2) :
    sourceRestHeavyEigenvalue side/(sourceRestMatchingClock : ℂ)=
      (6/5 : ℂ)*Complex.I*sourceRestSign side := by
  have clock : (sourceRestMatchingClock : ℂ)≠0 := by exact_mod_cast sourceRestMatchingClock_pos.ne'
  have phase := congrArg (fun value : ℝ=>(value : ℂ)) sourceRestMatchingClock_frequency
  push_cast at phase
  rw [sourceRestHeavyEigenvalue,phase]
  field_simp [clock]
  ring

theorem actualRestMatchingSylvester_light (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatchingSylvester point side (sourceRestLight observable)=0 := by
  rw [actualRestMatchingSylvester,actualRestMatterGenerator_light,smul_zero]

theorem actualRestMatchingSylvester_heavyUp (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatchingSylvester point side (sourceRestHeavyUp observable)=
      (-((6/5 : ℂ)*Complex.I*sourceRestSign side)) • sourceRestHeavyUp observable := by
  rw [actualRestMatchingSylvester,actualRestMatterGenerator_heavyUp,smul_smul]
  have coefficient : (sourceRestMatchingClock : ℂ)⁻¹*(-sourceRestHeavyEigenvalue side)=
      -((6/5 : ℂ)*Complex.I*sourceRestSign side) := by
    rw [mul_neg,←div_eq_inv_mul,sourceRestHeavyEigenvalue_normalized]
  rw [coefficient]

theorem actualRestMatchingSylvester_heavyDown (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatchingSylvester point side (sourceRestHeavyDown observable)=
      ((6/5 : ℂ)*Complex.I*sourceRestSign side) • sourceRestHeavyDown observable := by
  rw [actualRestMatchingSylvester,actualRestMatterGenerator_heavyDown,smul_smul,
    ←div_eq_inv_mul,sourceRestHeavyEigenvalue_normalized]

def sourceRestMatchingEigenvalue (side : Fin 2) : ℂ := (6/5 : ℂ)*Complex.I*sourceRestSign side

theorem actualRestMatchingSylvester_add (point : BasePoint) (side : Fin 2) (first second : RestMatterMatrix) :
    actualRestMatchingSylvester point side (first+second)=
      actualRestMatchingSylvester point side first+actualRestMatchingSylvester point side second := by
  ext row column
  simp only [actualRestMatchingSylvester,actualRestMatterGenerator,Matrix.mul_add,Matrix.add_mul,
    Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem actualRestMatchingSylvester_smul (point : BasePoint) (side : Fin 2) (coefficient : ℂ) (observable : RestMatterMatrix) :
    actualRestMatchingSylvester point side (coefficient • observable)=
      coefficient • actualRestMatchingSylvester point side observable := by
  ext row column
  simp only [actualRestMatchingSylvester,actualRestMatterGenerator,mul_smul_comm,smul_mul_assoc,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

theorem actualRestMatchingSylvester_spectral (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatchingSylvester point side observable=
      (-sourceRestMatchingEigenvalue side) • sourceRestHeavyUp observable+
        sourceRestMatchingEigenvalue side • sourceRestHeavyDown observable := by
  calc
    actualRestMatchingSylvester point side observable=
      actualRestMatchingSylvester point side
        (sourceRestLight observable+sourceRestHeavyUp observable+sourceRestHeavyDown observable) := by
          rw [sourceRestMatter_partition]
    _=_ := by rw [actualRestMatchingSylvester_add,actualRestMatchingSylvester_add,
      actualRestMatchingSylvester_light,actualRestMatchingSylvester_heavyUp,
      actualRestMatchingSylvester_heavyDown,zero_add]; rfl

theorem sourceRestMatchingEigenvalue_square (side : Fin 2) :
    (sourceRestMatchingEigenvalue side)^2=-(36/25 : ℂ) := by
  fin_cases side <;> norm_num [sourceRestMatchingEigenvalue,sourceRestSign,mul_pow,Complex.I_sq]

theorem sourceRestLight_generated (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    sourceRestLight observable=observable+
      (25/36 : ℂ) • actualRestMatchingSylvester point side
        (actualRestMatchingSylvester point side observable) := by
  have spectral:=actualRestMatchingSylvester_spectral point side observable
  rw [spectral,actualRestMatchingSylvester_add,
    actualRestMatchingSylvester_smul,actualRestMatchingSylvester_smul,
    actualRestMatchingSylvester_heavyUp,actualRestMatchingSylvester_heavyDown]
  change sourceRestLight observable=observable+(25/36 : ℂ) •
    ((-sourceRestMatchingEigenvalue side) • ((-sourceRestMatchingEigenvalue side) • sourceRestHeavyUp observable)+
      sourceRestMatchingEigenvalue side • (sourceRestMatchingEigenvalue side • sourceRestHeavyDown observable))
  ext row column
  have partition:=congrFun (congrFun (sourceRestMatter_partition observable) row) column
  have square:=sourceRestMatchingEigenvalue_square side
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at partition ⊢
  linear_combination partition-(25/36 : ℂ)*
    (sourceRestHeavyUp observable row column+sourceRestHeavyDown observable row column)*square

 theorem sourceRestMatter_zero_count :
    (Finset.univ.filter (fun index : Fin 4×Fin 4=>index.1=0 ↔ index.2=0)).card=10 := by decide +kernel
 theorem sourceRestMatter_heavyUp_count :
    (Finset.univ.filter (fun index : Fin 4×Fin 4=>index.1=0 ∧ index.2≠0)).card=3 := by decide +kernel
 theorem sourceRestMatter_heavyDown_count :
    (Finset.univ.filter (fun index : Fin 4×Fin 4=>index.1≠0 ∧ index.2=0)).card=3 := by decide +kernel

 def sourceRestMatterResolvent (side : Fin 2) (spectral : ℂ) (observable : RestMatterMatrix) : RestMatterMatrix :=
    spectral⁻¹ • sourceRestLight observable+
      (spectral+sourceRestMatchingEigenvalue side)⁻¹ • sourceRestHeavyUp observable+
      (spectral-sourceRestMatchingEigenvalue side)⁻¹ • sourceRestHeavyDown observable

 theorem sourceRestMatterResolvent_generated (point : BasePoint) (side : Fin 2) (spectral : ℂ)
    (zero : spectral≠0) (up : spectral+sourceRestMatchingEigenvalue side≠0)
    (down : spectral-sourceRestMatchingEigenvalue side≠0) (observable : RestMatterMatrix) :
    spectral • sourceRestMatterResolvent side spectral observable-
      actualRestMatchingSylvester point side (sourceRestMatterResolvent side spectral observable)=observable := by
  rw [sourceRestMatterResolvent,actualRestMatchingSylvester_add,actualRestMatchingSylvester_add,
    actualRestMatchingSylvester_smul,actualRestMatchingSylvester_smul,actualRestMatchingSylvester_smul,
    actualRestMatchingSylvester_light,actualRestMatchingSylvester_heavyUp,actualRestMatchingSylvester_heavyDown]
  simp only [smul_zero,zero_add]
  change spectral • (spectral⁻¹ • sourceRestLight observable+
      (spectral+sourceRestMatchingEigenvalue side)⁻¹ • sourceRestHeavyUp observable+
      (spectral-sourceRestMatchingEigenvalue side)⁻¹ • sourceRestHeavyDown observable)-
    ((spectral+sourceRestMatchingEigenvalue side)⁻¹ •
        ((-sourceRestMatchingEigenvalue side) • sourceRestHeavyUp observable)+
      (spectral-sourceRestMatchingEigenvalue side)⁻¹ •
        (sourceRestMatchingEigenvalue side • sourceRestHeavyDown observable))=observable
  ext row column
  have partition:=congrFun (congrFun (sourceRestMatter_partition observable) row) column
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at partition ⊢
  field_simp [zero,up,down]
  linear_combination (spectral+sourceRestMatchingEigenvalue side)*
    (spectral-sourceRestMatchingEigenvalue side)*partition

 theorem actualRestCurrent_lightHeavy (direction : Fin 3) (point : BasePoint) (side : Fin 2) (left right : Fin 4) :
    actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation (side,left))
        (currentAction 0 (sourceColorP286Generator direction)
          (actualRestStatePreparation (side,right) (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*
        (sourceRestLight (sourceRestChargeMixingBlock direction) left right+
          sourceRestHeavyUp (sourceRestChargeMixingBlock direction) left right+
          sourceRestHeavyDown (sourceRestChargeMixingBlock direction) left right) := by
  rw [actualRestState_current_mixing,sourceRestChargeMixing_generated]
  have partition:=congrFun (congrFun (sourceRestMatter_partition (sourceRestChargeMixingBlock direction)) left) right
  simp only [Matrix.add_apply] at partition
  rw [partition]
  simp

theorem actualRestMatchingSylvester_zero (point : BasePoint) (side : Fin 2) :
    actualRestMatchingSylvester point side 0=0 := by
  ext row column
  simp [actualRestMatchingSylvester,actualRestMatterGenerator]

theorem actualRestMatchingSylvester_kernel (point : BasePoint) (side : Fin 2) (observable : RestMatterMatrix) :
    actualRestMatchingSylvester point side observable=0 ↔ sourceRestLight observable=observable := by
  constructor
  · intro zero
    have projected:=sourceRestLight_generated point side observable
    rw [zero,actualRestMatchingSylvester_zero,smul_zero,add_zero] at projected
    exact projected
  · intro fixed
    rw [←fixed,actualRestMatchingSylvester_light]

def sourceRestHSPair (first second : RestMatterMatrix) : ℂ :=
  ∑ row : Fin 4,∑ column : Fin 4,star (first row column)*second row column

theorem sourceRestLight_selfAdjoint (first second : RestMatterMatrix) :
    sourceRestHSPair (sourceRestLight first) second=sourceRestHSPair first (sourceRestLight second) := by
  unfold sourceRestHSPair
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  by_cases same : (row=0 ↔ column=0) <;> simp [sourceRestLight,same]

theorem sourceRestLight_heavyUp_orthogonal (first second : RestMatterMatrix) :
    sourceRestHSPair (sourceRestLight first) (sourceRestHeavyUp second)=0 := by
  unfold sourceRestHSPair
  apply Finset.sum_eq_zero
  intro row _
  apply Finset.sum_eq_zero
  intro column _
  by_cases left : row=0 <;> by_cases right : column=0 <;>
    simp [sourceRestLight,sourceRestHeavyUp,left,right]

theorem sourceRestLight_heavyDown_orthogonal (first second : RestMatterMatrix) :
    sourceRestHSPair (sourceRestLight first) (sourceRestHeavyDown second)=0 := by
  unfold sourceRestHSPair
  apply Finset.sum_eq_zero
  intro row _
  apply Finset.sum_eq_zero
  intro column _
  by_cases left : row=0 <;> by_cases right : column=0 <;>
    simp [sourceRestLight,sourceRestHeavyDown,left,right]

theorem sourceRestMatchingEigenvalue_ne_zero (side : Fin 2) : sourceRestMatchingEigenvalue side≠0 := by
  fin_cases side <;> norm_num [sourceRestMatchingEigenvalue,sourceRestSign]

def sourceRestMatterResolventRegular (side : Fin 2) (spectral : ℂ) (observable : RestMatterMatrix) : RestMatterMatrix :=
  (spectral+sourceRestMatchingEigenvalue side)⁻¹ • sourceRestHeavyUp observable+
    (spectral-sourceRestMatchingEigenvalue side)⁻¹ • sourceRestHeavyDown observable

theorem sourceRestMatterResolvent_residue_identity (side : Fin 2) (spectral : ℂ)
    (nonzero : spectral≠0) (observable : RestMatterMatrix) :
    spectral • sourceRestMatterResolvent side spectral observable=
      sourceRestLight observable+spectral • sourceRestMatterResolventRegular side spectral observable := by
  simp only [sourceRestMatterResolvent,sourceRestMatterResolventRegular,smul_add,smul_smul]
  rw [mul_inv_cancel₀ nonzero,one_smul]
  abel

theorem sourceRestMatterResolventRegular_continuous (side : Fin 2) (observable : RestMatterMatrix) :
    ContinuousAt (fun spectral : ℂ=>sourceRestMatterResolventRegular side spectral observable) 0 := by
  have up : ContinuousAt (fun spectral : ℂ=>(spectral+sourceRestMatchingEigenvalue side)⁻¹) 0 :=
    (continuousAt_id.add continuousAt_const).inv₀ (by simpa using sourceRestMatchingEigenvalue_ne_zero side)
  have down : ContinuousAt (fun spectral : ℂ=>(spectral-sourceRestMatchingEigenvalue side)⁻¹) 0 :=
    (continuousAt_id.sub continuousAt_const).inv₀ (by simpa using neg_ne_zero.mpr (sourceRestMatchingEigenvalue_ne_zero side))
  exact (up.smul continuousAt_const).add (down.smul continuousAt_const)

/-- The light projection is the actual zero-pole residue of the source matching resolvent. -/
theorem sourceRestMatterResolvent_zeroResidue (side : Fin 2) (observable : RestMatterMatrix) :
    Tendsto (fun spectral : ℂ=>spectral • sourceRestMatterResolvent side spectral observable)
      (𝓝[≠] (0 : ℂ)) (𝓝 (sourceRestLight observable)) := by
  have continuous : ContinuousAt (fun spectral : ℂ=>sourceRestLight observable+
      spectral • sourceRestMatterResolventRegular side spectral observable) 0 :=
    continuousAt_const.add (continuousAt_id.smul (sourceRestMatterResolventRegular_continuous side observable))
  have limit : Tendsto (fun spectral : ℂ=>sourceRestLight observable+
      spectral • sourceRestMatterResolventRegular side spectral observable) (𝓝 (0 : ℂ))
      (𝓝 (sourceRestLight observable)) := by simpa using continuous.tendsto
  have equal : (fun spectral : ℂ=>sourceRestLight observable+
      spectral • sourceRestMatterResolventRegular side spectral observable)=ᶠ[𝓝[≠] (0 : ℂ)]
      (fun spectral : ℂ=>spectral • sourceRestMatterResolvent side spectral observable) := by
    filter_upwards [self_mem_nhdsWithin] with spectral nonzero
    exact (sourceRestMatterResolvent_residue_identity side spectral (by simpa using nonzero) observable).symm
  exact (limit.mono_left nhdsWithin_le_nhds).congr' equal

def sourceRestHSsquare (observable : RestMatterMatrix) : ℝ :=
  ∑ row : Fin 4,∑ column : Fin 4,‖observable row column‖^2

theorem sourceRestHSsquare_nonneg (observable : RestMatterMatrix) : 0 ≤ sourceRestHSsquare observable :=
  Finset.sum_nonneg (fun _row _=>Finset.sum_nonneg (fun _column _=>sq_nonneg _))

theorem sourceRestMatter_HS_partition (observable : RestMatterMatrix) :
    sourceRestHSsquare observable=sourceRestHSsquare (sourceRestLight observable)+
      sourceRestHSsquare (sourceRestHeavyUp observable)+sourceRestHSsquare (sourceRestHeavyDown observable) := by
  simp only [sourceRestHSsquare,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  by_cases left : row=0 <;> by_cases right : column=0 <;>
    simp [sourceRestLight,sourceRestHeavyUp,sourceRestHeavyDown,left,right]

theorem sourceRestLight_HS_contraction (observable : RestMatterMatrix) :
    sourceRestHSsquare (sourceRestLight observable) ≤ sourceRestHSsquare observable := by
  rw [sourceRestMatter_HS_partition observable]
  linarith [sourceRestHSsquare_nonneg (sourceRestHeavyUp observable),
    sourceRestHSsquare_nonneg (sourceRestHeavyDown observable)]

theorem actualRestCurrent_light_diagonal (direction : Fin 3) (point : BasePoint) (side : Fin 2) (state : Fin 4) :
    actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation (side,state))
        (currentAction 0 (sourceColorP286Generator direction)
          (actualRestStatePreparation (side,state) (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*
        sourceRestLight (sourceRestChargeMixingBlock direction) state state := by
  rw [actualRestState_current_mixing,sourceRestChargeMixing_generated]
  simp [sourceRestLight]

end LowEnergy.PreparationVacuumElectromagneticIdentity
