import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeDiracRay
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeSourceRecords

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation PointwiseDiracSpinConnectionLift
open StageNineDiracMatterCoordinateCalculus StageNineMatterVariation
open StageNineLorentzConnectionVariation
open SU7MotherGaugeTheory SU7MotherLieAlgebra StageNineP286GaugeConnectionVariationDensity
open SU7ExteriorBreakingYukawa SU7ExteriorMatterGaugeCovariantJet SU7ExteriorMatterRestriction
open SU7ExteriorMatterRepresentation SU7ExteriorYukawaMassSpectrum
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeSourceRestriction
open PreparationVacuumLowerClassical PreparationVacuumCoefficientBudget PreparationCoordinates
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
attribute [local irreducible] Stage9C.Material.SpinPair.actual
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

private theorem diracTriplet_enumeration (color : Fin 3) (position : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm (sourceTripletIndex color) position =
      if position=0 then Sum.inl color else hyperPlusIndex := by
  let family : Fin 2 → SU7MotherIndex :=
    fun position => if position=0 then Sum.inl color else hyperPlusIndex
  have membership (position : Fin 2) : family position ∈ (sourceTripletIndex color).1 := by
    by_cases zero : position=0 <;> simp [family, sourceTripletIndex, zero]
  have unique : family = (sourceTripletIndex color).1.orderEmbOfFin
      (sourceTripletIndex color).prop := by
    apply Finset.orderEmbOfFin_unique _ membership
    intro first second ordered
    fin_cases first <;> fin_cases second
    all_goals try norm_num at ordered
    change smBlockIndexEquivFin7 (Sum.inl color) < smBlockIndexEquivFin7 hyperPlusIndex
    fin_cases color <;> decide
  exact (congrFun unique position).symm

private theorem diracTriplet_position (color : Fin 3) (position : Fin 2) :
    (exteriorPositionEquiv (sourceTripletIndex color) position).1 =
      if position=0 then Sum.inl color else hyperPlusIndex :=
  diracTriplet_enumeration color position

theorem diracTriplet_mother_basis (matrix : SU7MotherLieMatrix) (row column : Fin 3) :
    (su7ExteriorBasis 2).repr
      (exteriorMotherLieAction 2 matrix (su7ExteriorBasis 2 (sourceTripletIndex column)))
      (sourceTripletIndex row) =
      (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ) (Sum.inl row) (Sum.inl column)+
      if row=column then (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
        hyperPlusIndex hyperPlusIndex else 0 := by
  rw [exteriorMotherLieAction_basis_current]
  unfold exteriorBasisLieAction
  rw [map_sum]
  change (∑ position : Fin 2, (su7ExteriorBasis 2).repr
    ((exteriorPower.ιMulti ℂ 2)
      (exteriorBasisLieActionInput 2 matrix (sourceTripletIndex column) position))
      (sourceTripletIndex row)) = _
  simp_rw [exteriorBasisLieActionTerm_eq_update]
  unfold su7ExteriorBasis
  simp_rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.det_fin_two, Fin.sum_univ_two, exteriorBasisInput,
      diracTriplet_position, diracTriplet_enumeration,
      fundamentalMotherLieAction, Matrix.mulVecLin, su7FundamentalBasis, hyperPlusIndex]

def diracTripletGauge (data : P286LieBlockData) (row column : Fin 3) : ℂ :=
  (data.1 : Matrix (Fin 3) (Fin 3) ℂ) row column+if row=column then data.2.2.1 else 0

theorem diracTriplet_gauge_basis (data : P286LieBlockData) (row column : Fin 3) :
    sourceTripletRead (exteriorSpinorMotherLieAction (p286LieBlockEmbed data)
      (sourceTripletMatter column)) row = diracTripletGauge data row column := by
  change (su7ExteriorBasis 2).repr
    (exteriorMotherLieAction 2 (p286LieBlockEmbed data)
      (su7ExteriorBasis 2 (sourceTripletIndex column))) (sourceTripletIndex row) = _
  rw [diracTriplet_mother_basis]
  rfl

abbrev DiracTriplet := Fin 4 → Fin 3 → ℂ

def diracTripletMatter (w : DiracTriplet) : DiracExteriorMatterCarrier :=
  ∑ spin : Fin 4, ∑ color : Fin 3, w spin color • sourceTripletLeg spin color

theorem diracTriplet_read_basis (row column : Fin 3) :
    sourceTripletRead (sourceTripletMatter column) row = if row=column then 1 else 0 := by
  change (su7ExteriorBasis 2).repr (su7ExteriorBasis 2 (sourceTripletIndex column)) (sourceTripletIndex row) = _
  rw [Module.Basis.repr_self]
  simp only [Finsupp.single_apply]
  have injection : Function.Injective sourceTripletIndex := by
    intro a b h
    have sets := congrArg Subtype.val h
    have member : Sum.inl a ∈ (sourceTripletIndex b).1 := by
      rw [←sets]; simp [sourceTripletIndex]
    simpa [sourceTripletIndex, hyperPlusIndex] using member
  simp only [injection.eq_iff, eq_comm]

theorem diracTripletMatter_at (w : DiracTriplet) (spin : Fin 4) :
    diracTripletMatter w spin = ∑ color : Fin 3, w spin color • sourceTripletMatter color := by
  simp only [diracTripletMatter, Finset.sum_apply, Pi.smul_apply, sourceTripletLeg, Pi.single_apply]
  simp only [smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

def diracTripletReadLinear (spin : Fin 4) (color : Fin 3) : DiracExteriorMatterCarrier →ₗ[ℂ] ℂ where
  toFun v := sourceTripletRead (v spin) color
  map_add' v w := by
    simp [sourceTripletRead, Prod.snd_add, Prod.fst_add, Finsupp.add_apply]
  map_smul' z v := by
    simp [sourceTripletRead, Prod.snd_smul, Prod.fst_smul]

private theorem diracTripletReadLinear_value (spin : Fin 4) (color : Fin 3)
    (v : DiracExteriorMatterCarrier) :
    diracTripletReadLinear spin color v = sourceTripletRead (v spin) color := rfl

theorem diracTriplet_read (w : DiracTriplet) (spin : Fin 4) (color : Fin 3) :
    sourceTripletRead (diracTripletMatter w spin) color = w spin color := by
  change diracTripletReadLinear spin color (diracTripletMatter w) = _
  simp only [diracTripletMatter, map_sum, map_smul, smul_eq_mul]
  have basis (s : Fin 4) (c : Fin 3) :
      diracTripletReadLinear spin color (sourceTripletLeg s c) =
        if spin=s then (if color=c then 1 else 0) else 0 := by
    rw [diracTripletReadLinear_value]
    simp only [sourceTripletLeg, Pi.single_apply]
    change sourceTripletRead (if spin=s then sourceTripletMatter c else 0) color = _
    by_cases h : spin=s
    · simp only [if_pos h]; exact diracTriplet_read_basis color c
    · simp only [if_neg h]; simp [sourceTripletRead]
  simp only [basis]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite]


def diracTripletColorReadLinear (color : Fin 3) : SU7ExteriorSpinorMatterCarrier →ₗ[ℂ] ℂ where
  toFun v := sourceTripletRead v color
  map_add' v w := by
    simp [sourceTripletRead, Prod.snd_add, Prod.fst_add, Finsupp.add_apply]
  map_smul' z v := by
    simp [sourceTripletRead, Prod.snd_smul, Prod.fst_smul]

theorem diracTriplet_spin_read (M : DiracMatrix) (v : DiracExteriorMatterCarrier)
    (spin : Fin 4) (color : Fin 3) :
    sourceTripletRead (diracMatrixMatterAction M v spin) color =
      ∑ other : Fin 4, M spin other*sourceTripletRead (v other) color := by
  change diracTripletColorReadLinear color (∑ other : Fin 4, M spin other • v other) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

theorem diracTriplet_gauge_read (data : P286LieBlockData) (w : DiracTriplet)
    (spin : Fin 4) (color : Fin 3) :
    sourceTripletRead (diracExteriorMotherLieAction (p286LieBlockEmbed data)
      (diracTripletMatter w) spin) color =
      ∑ other : Fin 3, diracTripletGauge data color other*w spin other := by
  change diracTripletColorReadLinear color
    (exteriorSpinorMotherLieAction (p286LieBlockEmbed data) (diracTripletMatter w spin)) = _
  rw [diracTripletMatter_at]
  simp only [map_sum, map_smul, smul_eq_mul]
  change (∑ other : Fin 3, w spin other * sourceTripletRead
    (exteriorSpinorMotherLieAction (p286LieBlockEmbed data) (sourceTripletMatter other)) color) = _
  simp only [diracTriplet_gauge_basis]
  apply Finset.sum_congr rfl; intro other _; exact mul_comm _ _

def diracPrepared : DiracTriplet :=
  !![0,1,0; -1,0,0; 0,1,0; -1,0,0]

private theorem sourceColorDiracDual_value (coefficients : Fin 4 → Fin 2 → ℂ)
    (v : DiracExteriorMatterCarrier) :
    sourceColorDiracDual coefficients v = ∑ spin : Fin 4, ∑ state : Fin 2,
      coefficients spin state*sourceColorDoubletDual state (v spin) := rfl
private theorem sourceColorDoubletDual_read (state : Fin 2) (v : SU7ExteriorSpinorMatterCarrier) :
    sourceColorDoubletDual state v = sourceTripletRead v (state.castLE (by decide)) := rfl
private theorem matterReadCLM_value (spin : Fin 4) (color : Fin 3) (v : MatterCoordinateCarrier) :
    matterReadCLM spin color v=sourceTripletRead (matterCoordinateEquiv.symm v spin) color := rfl

theorem diracOriginalDual_read (v : MatterCoordinateCarrier) :
    originalDualCLM v = (spinScale:ℂ)*(∑ spin : Fin 4, ∑ color : Fin 3,
      diracPrepared spin color * matterReadCLM spin color v) := by
  change actual.conjugateMatter 0 (matterCoordinateEquiv.symm v) = _
  rw [actual_conjugateMatter]
  simp only [spinPairDual, sourceColorDiracDual_value, sourceColorDoubletDual_read,
    matterReadCLM_value, upperDualPhase, lowerDualPhase, upperPhase, lowerPhase, phase_zero,
    mul_one, spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two, diracPrepared]
  dsimp only [Matrix.of_apply, Fin.castLE, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases,
    Fin.induction, Fin.induction.go]
  simp only [eq_mpr_eq_cast, cast_eq]
  dsimp only [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  simp only [eq_mpr_eq_cast, cast_eq]
  norm_num only [Fin.coe_ofNat_eq_mod, mul_zero, zero_mul, one_mul, neg_mul, zero_add, add_zero]
  ring_nf!


theorem diracInternal_read (a spin : Fin 4) (color : Fin 3) (v : MatterCoordinateCarrier) :
    matterReadCLM spin color (diracInternalLinear a v) =
      Complex.I * (∑ other : Fin 4, diracGamma a spin other*matterReadCLM other color v) := by
  have identity : diracInternalLinear a v = matterCoordinateEquiv
      (Complex.I • diracMatrixMatterAction (diracGamma a) (matterCoordinateEquiv.symm v)) := by
    rw [map_smul]; rfl
  rw [identity, matterReadCLM_value, LinearEquiv.symm_apply_apply]
  change diracTripletColorReadLinear color
    (Complex.I • diracMatrixMatterAction (diracGamma a) (matterCoordinateEquiv.symm v) spin) = _
  simp only [map_smul, smul_eq_mul]
  change Complex.I * sourceTripletRead
    (diracMatrixMatterAction (diracGamma a) (matterCoordinateEquiv.symm v) spin) color = _
  rw [diracTriplet_spin_read]
  simp only [matterReadCLM_value]

theorem diracSpin_read (M : DiracMatrix) (spin : Fin 4) (color : Fin 3)
    (v : MatterCoordinateCarrier) :
    matterReadCLM spin color (diracSpinAction M v) =
      ∑ other : Fin 4, M spin other*matterReadCLM other color v := by
  have native : diracSpinAction M v = matterCoordinateEquiv
      (diracMatrixMatterAction M (matterCoordinateEquiv.symm v)) := rfl
  rw [native, matterReadCLM_value, LinearEquiv.symm_apply_apply, diracTriplet_spin_read]
  simp only [matterReadCLM_value]

theorem diracGauge_read (A : P286CoordinateCarrier) (w : DiracTriplet)
    (spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color (diracGaugeAction A (matterCoordinateEquiv (diracTripletMatter w))) =
      ∑ other : Fin 3, diracTripletGauge (p286CoordinateEquiv.symm A) color other*w spin other := by
  have native : diracGaugeAction A (matterCoordinateEquiv (diracTripletMatter w)) = matterCoordinateEquiv
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm A))
        (diracTripletMatter w)) := by
    have action (v : MatterCoordinateCarrier) : diracGaugeAction A v = matterCoordinateEquiv
        (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm A))
          (matterCoordinateEquiv.symm v)) := rfl
    rw [action, LinearEquiv.symm_apply_apply]
  rw [native, matterReadCLM_value, LinearEquiv.symm_apply_apply, diracTriplet_gauge_read]

private theorem diracDoublet_triplet (state : Fin 2) :
    sourceColorDoubletMatter state = sourceTripletMatter (state.castLE (by decide)) := rfl

def diracPreparedPair (p q : ℂ) : DiracTriplet :=
  !![0,p,0; -p,0,0; 0,q,0; -q,0,0]

theorem diracSpinPair_triplet (p q : ℂ) : spinPairMatter p q = diracTripletMatter (diracPreparedPair p q) := by
  funext spin
  rw [diracTripletMatter_at]
  simp only [spinPairMatter, sourceColorDiracMatter, diracDoublet_triplet,
    Fin.sum_univ_two, Fin.sum_univ_three, spinPairCoefficients, diracPreparedPair]
  fin_cases spin
  all_goals dsimp only [Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.castLE]
  all_goals simp only [eq_mpr_eq_cast, cast_eq]
  all_goals dsimp only [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast, cast_eq]
  all_goals norm_num only [Fin.coe_ofNat_eq_mod, zero_smul, add_zero, zero_add]
  all_goals rfl

theorem diracPrimalBase_triplet : diracPrimalBase=matterCoordinateEquiv (diracTripletMatter diracPrepared) := by
  unfold diracPrimalBase
  rw [actual_matter]
  simp only [upperPhase, lowerPhase, phase_zero, diracSpinPair_triplet]
  rfl

theorem diracPrimalVariation_triplet (f : Field289) :
    primalInsertionCLM f = matterCoordinateEquiv (diracTripletMatter (fieldPrimalComplex f)) := rfl


def diracGaugeUnit (a : Fin 12) (row column : Fin 3) : ℂ :=
  let x := (Pi.single a 1 : Fin 12 → ℚ)
  (rawMotherReal x (row.castLE (by decide)) (column.castLE (by decide)) : ℂ)+
    (rawMotherImag x (row.castLE (by decide)) (column.castLE (by decide)) : ℂ)*Complex.I+
    if row=column then (rawMotherReal x 5 5 : ℂ)+(rawMotherImag x 5 5 : ℂ)*Complex.I else 0

theorem diracGaugeUnit_source (a : Fin 12) (row column : Fin 3) :
    diracTripletGauge (p286CoordinateEquiv.symm (originalUnit a)) row column =
      diracGaugeUnit a row column := by
  let x := (Pi.single a 1 : Fin 12 → ℚ)
  have unit : rawCoordinates.symm (fun k => (x k:ℝ)) = originalUnit a := by
    unfold originalUnit
    congr 1
    funext k
    by_cases h : k=a <;> simp [x, Pi.single_apply, h]
  have rowAddress : smBlockIndexEquivFin7.symm (row.castLE (by decide)) = Sum.inl row := by
    fin_cases row <;> rfl
  have columnAddress : smBlockIndexEquivFin7.symm (column.castLE (by decide)) = Sum.inl column := by
    fin_cases column <;> rfl
  have hyperAddress : smBlockIndexEquivFin7.symm 5=hyperPlusIndex := rfl
  have hm := rawMother_entry x (row.castLE (by decide)) (column.castLE (by decide))
  have hh := rawMother_entry x 5 5
  rw [unit, rowAddress, columnAddress] at hm
  rw [unit, hyperAddress] at hh
  unfold diracTripletGauge diracGaugeUnit
  change (p286LieBlockEmbed (p286CoordinateEquiv.symm (originalUnit a))).val
    (Sum.inl row) (Sum.inl column)+
    (if row=column then (p286LieBlockEmbed (p286CoordinateEquiv.symm (originalUnit a))).val
      hyperPlusIndex hyperPlusIndex else 0) = _
  rw [hm, hh]

def diracTripletGaugeLinear (row column : Fin 3) : P286LieBlockData →ₗ[ℝ] ℂ where
  toFun data := diracTripletGauge data row column
  map_add' A B := by
    change A.1.val row column+B.1.val row column+(if row=column then A.2.2.1+B.2.2.1 else 0) = _
    simp only [diracTripletGauge]
    split_ifs <;> ring_nf!
  map_smul' r A := by
    change (r:ℂ)*A.1.val row column+(if row=column then (r:ℂ)*A.2.2.1 else 0) = _
    simp only [diracTripletGauge, RingHom.id_apply, RCLike.real_smul_eq_coe_mul]
    split_ifs <;> ring_nf!

private theorem diracTripletGaugeLinear_value (row column : Fin 3) (data : P286LieBlockData) :
    diracTripletGaugeLinear row column data=diracTripletGauge data row column := rfl

theorem diracGauge_raw (A : P286CoordinateCarrier) (row column : Fin 3) :
    diracTripletGauge (p286CoordinateEquiv.symm A) row column =
      ∑ a : Fin 12, (rawCoordinates (show NativeLie from A) a : ℂ)*diracGaugeUnit a row column := by
  have linear (B : P286CoordinateCarrier) :
      diracTripletGaugeLinear row column (p286CoordinateEquiv.symm B) =
        diracTripletGauge (p286CoordinateEquiv.symm B) row column := rfl
  rw [←linear]
  conv_lhs => rw [raw_original_expansion (show NativeLie from A)]
  simp only [map_sum, map_smul, diracTripletGaugeLinear_value, diracGaugeUnit_source,
    RCLike.real_smul_eq_coe_mul]
  rfl

private theorem fieldGauge_raw (f : Field289) (mu : Fin 4) (a : Fin 12) :
    rawCoordinates (fieldGauge f mu) a = f (gaugeSlot mu a) := by
  simp only [fieldGauge, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    originalUnit, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

theorem diracGaugeVariation_raw (jet : NativeFirstJet) (mu : Fin 4) (row column : Fin 3) :
    diracTripletGauge (p286CoordinateEquiv.symm (diracGaugeVariation jet mu)) row column =
      ∑ a : Fin 12, (jet.1 (gaugeSlot mu a) : ℂ)*diracGaugeUnit a row column := by
  rw [diracGauge_raw]
  simp only [diracGaugeVariation, gaugeCoordinateCLM, gaugeCoordinateLinear]
  change (∑ a : Fin 12, (rawCoordinates (fieldGauge jet.1 mu) a:ℂ)*diracGaugeUnit a row column) = _
  simp only [fieldGauge_raw]

theorem diracGaugeBase_raw (mu : Fin 4) (row column : Fin 3) :
    diracTripletGauge (p286CoordinateEquiv.symm (diracGaugeBase mu)) row column =
      ∑ a : Fin 12, (gaugeBackgroundRaw mu a : ℂ)*diracGaugeUnit a row column := by
  rw [diracGauge_raw]
  simp only [diracGaugeBase, gaugeBackgroundRaw_source]


theorem diracPrimalBase_read (spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color diracPrimalBase = diracPrepared spin color := by
  rw [diracPrimalBase_triplet, matterReadCLM_value, LinearEquiv.symm_apply_apply, diracTriplet_read]

theorem diracPrimalVariation_read (f : Field289) (spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color (primalInsertionCLM f) = fieldPrimalComplex f spin color := by
  rw [diracPrimalVariation_triplet, matterReadCLM_value, LinearEquiv.symm_apply_apply, diracTriplet_read]

theorem diracRotatedDerivative_read (jet : NativeFirstJet) (mu spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color (rotatedPrimalDerivative jet mu) =
      (if mu=0 then phaseComponentVelocity spin else 0)*fieldPrimalComplex jet.1 spin color+
        fieldPrimalComplex (jet.2 mu) spin color := by
  have native : rotatedPrimalDerivative jet mu = matterCoordinateEquiv (diracTripletMatter
      (fun s c => (if mu=0 then phaseComponentVelocity s else 0)*fieldPrimalComplex jet.1 s c+
        fieldPrimalComplex (jet.2 mu) s c)) := by
    unfold diracTripletMatter
    simp only [map_sum, map_smul]
    rfl
  rw [native, matterReadCLM_value, LinearEquiv.symm_apply_apply, diracTriplet_read]

theorem diracActualDerivative_read (mu spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color
      (fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu) =
      (if mu=0 then phaseComponentVelocity spin else 0)*diracPrepared spin color := by
  rw [matterReadCLM_value, actual_matterCoordinateDerivative]
  by_cases h : mu=0
  · simp only [if_pos h, upperPhase, lowerPhase, phase_zero, one_mul,
      diracSpinPair_triplet, diracTriplet_read]
    fin_cases spin <;> fin_cases color <;>
      norm_num [diracPreparedPair, diracPrepared, phaseComponentVelocity]

  · simp [h, sourceTripletRead]

def diracSpinRaw (w : Fin 6 → ℝ) : DiracMatrix :=
  ∑ pair : Fin 6, ((w pair:ℂ)/2) • (diracGamma (lorentzBivectorFirst pair)*diracGamma (lorentzBivectorSecond pair))

theorem diracSpinBase_raw (mu : Fin 4) :
    diracSpinBase mu = diracSpinRaw (homogeneousContorsion spinScale mu) := by
  unfold diracSpinBase
  rw [actual_gravityConnection]
  simp only [homogeneousConnection, diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm, diracSpinRaw, div_eq_mul_inv]
  congr 1
  funext pair
  rw [mul_comm]

theorem diracSpinVariation_raw (jet : NativeFirstJet) (mu : Fin 4) :
    diracSpinVariation jet mu = diracSpinRaw (fun pair => jet.1 (lorentzSlot mu pair)) := by
  unfold diracSpinVariation
  change diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm (fieldLorentz jet.1)) mu = _
  simp only [diracSpinConnectionLift, loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    diracSpinRaw, fieldLorentz, div_eq_mul_inv]
  congr 1
  funext pair
  rw [mul_comm]


def diracRawGauge (x : Fin 12 → ℝ) (row column : Fin 3) : ℂ :=
  ∑ a : Fin 12, (x a:ℂ)*diracGaugeUnit a row column

def diracRawCovariantBase (mu : Fin 4) : DiracTriplet := fun spin color =>
  (if mu=0 then phaseComponentVelocity spin else 0)*diracPrepared spin color+
  (∑ other : Fin 4, diracSpinRaw (homogeneousContorsion spinScale mu) spin other*diracPrepared other color)+
  (∑ other : Fin 3, diracRawGauge (gaugeBackgroundRaw mu) color other*diracPrepared spin other)

def diracRawCovariantFirst (jet : NativeFirstJet) (mu : Fin 4) : DiracTriplet := fun spin color =>
  (if mu=0 then phaseComponentVelocity spin else 0)*fieldPrimalComplex jet.1 spin color+
  fieldPrimalComplex (jet.2 mu) spin color+
  (∑ other : Fin 4, diracSpinRaw (homogeneousContorsion spinScale mu) spin other*fieldPrimalComplex jet.1 other color)+
  (∑ other : Fin 4, diracSpinRaw (fun pair => jet.1 (lorentzSlot mu pair)) spin other*diracPrepared other color)+
  (∑ other : Fin 3, diracRawGauge (gaugeBackgroundRaw mu) color other*fieldPrimalComplex jet.1 spin other)+
  (∑ other : Fin 3, diracRawGauge (fun a => jet.1 (gaugeSlot mu a)) color other*diracPrepared spin other)

def diracRawCovariantSecond (jet : NativeFirstJet) (mu : Fin 4) : DiracTriplet := fun spin color =>
  (∑ other : Fin 4, diracSpinRaw (fun pair => jet.1 (lorentzSlot mu pair)) spin other*fieldPrimalComplex jet.1 other color)+
  (∑ other : Fin 3, diracRawGauge (fun a => jet.1 (gaugeSlot mu a)) color other*fieldPrimalComplex jet.1 spin other)

theorem diracCovariantBase_flat (mu spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color (diracCovariantBase mu) = diracRawCovariantBase mu spin color := by
  simp only [diracCovariantBase, map_add, diracActualDerivative_read, diracSpin_read,
    diracPrimalBase_read]
  simp only [diracPrimalBase_triplet, diracGauge_read]
  simp only [diracSpinBase_raw, diracGaugeBase_raw, diracRawCovariantBase, diracRawGauge]

theorem diracCovariantFirst_flat (jet : NativeFirstJet) (mu spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color (diracCovariantFirst jet mu) = diracRawCovariantFirst jet mu spin color := by
  simp only [diracCovariantFirst, map_add, diracRotatedDerivative_read, diracSpin_read,
    diracPrimalBase_read, diracPrimalVariation_read]
  simp only [diracPrimalBase_triplet, diracPrimalVariation_triplet, diracGauge_read]
  simp only [diracSpinBase_raw, diracSpinVariation_raw, diracGaugeBase_raw,
    diracGaugeVariation_raw, diracRawCovariantFirst, diracRawGauge]

theorem diracCovariantSecond_flat (jet : NativeFirstJet) (mu spin : Fin 4) (color : Fin 3) :
    matterReadCLM spin color (diracCovariantSecond jet mu) = diracRawCovariantSecond jet mu spin color := by
  simp only [diracCovariantSecond, map_add, diracSpin_read, diracPrimalVariation_read]
  simp only [diracPrimalVariation_triplet, diracGauge_read]
  simp only [diracSpinVariation_raw, diracGaugeVariation_raw, diracRawCovariantSecond, diracRawGauge]

def diracTripletPair (a : Fin 4) (dual primal : DiracTriplet) : ℂ :=
  ∑ spin : Fin 4, ∑ color : Fin 3,
    dual spin color*(Complex.I*(∑ other : Fin 4, diracGamma a spin other*primal other color))

theorem diracPairZero_read (a : Fin 4) (v : MatterCoordinateCarrier) :
    originalDualCLM (diracInternalLinear a v) = diracTripletPair a
      (fun spin color => (spinScale:ℂ)*diracPrepared spin color)
      (fun spin color => matterReadCLM spin color v) := by
  rw [diracOriginalDual_read]
  simp only [diracInternal_read, diracTripletPair, Finset.mul_sum, mul_assoc]

private theorem dualCoefficientCLM_value (spin : Fin 4) (color : Fin 3) (f : Field289) :
    dualCoefficientCLM spin color f=fieldDualComplex f spin color := rfl

theorem diracPairOne_read (a : Fin 4) (f : Field289) (v : MatterCoordinateCarrier) :
    diracDualVariationLinear f (diracInternalLinear a v) = diracTripletPair a
      (fieldDualComplex f) (fun spin color => matterReadCLM spin color v) := by
  rw [diracDualVariation_value]
  simp only [dualCoefficientCLM_value, diracInternal_read, diracTripletPair]

def diracRawPairCoefficient (jet : NativeFirstJet) (mu a : Fin 4) (degree : Fin 4) : ℂ :=
  let D0 := fun spin color => (spinScale:ℂ)*diracPrepared spin color
  let D1 := fieldDualComplex jet.1
  match degree.val with
  | 0 => diracTripletPair a D0 (diracRawCovariantBase mu)
  | 1 => diracTripletPair a D0 (diracRawCovariantFirst jet mu)+
    diracTripletPair a D1 (diracRawCovariantBase mu)
  | 2 => diracTripletPair a D0 (diracRawCovariantSecond jet mu)+
    diracTripletPair a D1 (diracRawCovariantFirst jet mu)
  | _ => diracTripletPair a D1 (diracRawCovariantSecond jet mu)

theorem diracPairCoefficient_flat (jet : NativeFirstJet) (mu a : Fin 4) (degree : Fin 4) :
    diracPairCoefficient jet mu a degree=diracRawPairCoefficient jet mu a degree := by
  simp only [diracPairCoefficient, diracRawPairCoefficient]
  fin_cases degree <;> norm_num only [Fin.coe_ofNat_eq_mod]
  all_goals simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    diracPairZero_read, diracPairOne_read, diracCovariantBase_flat,
    diracCovariantFirst_flat, diracCovariantSecond_flat]

def diracRawQuadratic (jet : NativeFirstJet) : ℝ :=
  ∑ mu : Fin 4, ∑ a : Fin 4, (
    diracAdjugateCoefficient (fieldCoframe jet.1) 0 mu a*(diracRawPairCoefficient jet mu a 2).re+
    diracAdjugateCoefficient (fieldCoframe jet.1) 1 mu a*(diracRawPairCoefficient jet mu a 1).re+
    diracAdjugateCoefficient (fieldCoframe jet.1) 2 mu a*(diracRawPairCoefficient jet mu a 0).re)

theorem nativeDiracQuadratic_flat (jet : NativeFirstJet) :
    nativeDiracQuadratic jet=diracRawQuadratic jet := by
  simp only [nativeDiracQuadratic, diracRawQuadratic, diracPairCoefficient_flat]



def diracSpinRawFlat (w : Fin 6 → ℝ) : DiracMatrix :=
  !![(1/2:ℂ)*(w 2:ℂ)+(1/2:ℂ)*Complex.I*(w 5:ℂ),(1/2:ℂ)*(w 0:ℂ)+(-1/2:ℂ)*Complex.I*(w 1:ℂ)+(1/2:ℂ)*Complex.I*(w 3:ℂ)+(1/2:ℂ)*(w 4:ℂ),0,0;
     (1/2:ℂ)*(w 0:ℂ)+(1/2:ℂ)*Complex.I*(w 1:ℂ)+(1/2:ℂ)*Complex.I*(w 3:ℂ)+(-1/2:ℂ)*(w 4:ℂ),(-1/2:ℂ)*(w 2:ℂ)+(-1/2:ℂ)*Complex.I*(w 5:ℂ),0,0;
     0,0,(-1/2:ℂ)*(w 2:ℂ)+(1/2:ℂ)*Complex.I*(w 5:ℂ),(-1/2:ℂ)*(w 0:ℂ)+(1/2:ℂ)*Complex.I*(w 1:ℂ)+(1/2:ℂ)*Complex.I*(w 3:ℂ)+(1/2:ℂ)*(w 4:ℂ);
     0,0,(-1/2:ℂ)*(w 0:ℂ)+(-1/2:ℂ)*Complex.I*(w 1:ℂ)+(1/2:ℂ)*Complex.I*(w 3:ℂ)+(-1/2:ℂ)*(w 4:ℂ),(1/2:ℂ)*(w 2:ℂ)+(-1/2:ℂ)*Complex.I*(w 5:ℂ)]

private theorem diracCons_mk_zero {α : Type*} {n : ℕ} (h : 0<n+1) (x : α) (v : Fin n → α) :
    Fin.cons (α := fun _ => α) x v ⟨0,h⟩ = x := rfl
private theorem diracCons_mk_succ {α : Type*} {n k : ℕ} (h : k+1<n+1) (x : α) (v : Fin n → α) :
    Fin.cons (α := fun _ => α) x v ⟨k+1,h⟩ = v ⟨k,Nat.lt_of_succ_lt_succ h⟩ := rfl

private theorem diracCons_two {α : Type*} {n : ℕ} (x : α) (v : Fin (n+2) → α) :
    Fin.cons (α := fun _ => α) x v (2 : Fin (n+3)) = v (1 : Fin (n+2)) := by
  rfl

private theorem diracCons_three {α : Type*} {n : ℕ} (x : α) (v : Fin (n+3) → α) :
    Fin.cons (α := fun _ => α) x v (3 : Fin (n+4)) = v (2 : Fin (n+3)) := by
  rfl

private theorem diracCons_four {α : Type*} {n : ℕ} (x : α) (v : Fin (n+4) → α) :
    Fin.cons (α := fun _ => α) x v (4 : Fin (n+5)) = v (3 : Fin (n+4)) := by
  rfl

private theorem diracCons_five {α : Type*} {n : ℕ} (x : α) (v : Fin (n+5) → α) :
    Fin.cons (α := fun _ => α) x v (5 : Fin (n+6)) = v (4 : Fin (n+5)) := by
  rfl

private theorem diracCons_six {α : Type*} {n : ℕ} (x : α) (v : Fin (n+6) → α) :
    Fin.cons (α := fun _ => α) x v (6 : Fin (n+7)) = v (5 : Fin (n+6)) := by
  rfl

theorem diracSpinRaw_flat (w : Fin 6 → ℝ) (i j : Fin 4) :
    diracSpinRaw w i j=diracSpinRawFlat w i j := by
  fin_cases i <;> fin_cases j
  all_goals try simp only [diracSpinRaw, diracSpinRawFlat, Finset.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
    lorentzBivectorFirst, lorentzBivectorSecond]
  all_goals try dsimp only [Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons,
    Fin.cases, Fin.induction, Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast, cast_eq]
  all_goals try dsimp only [Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons,
    Fin.cases, Fin.induction, Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast, cast_eq]
  all_goals try simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals try dsimp only [Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons,
    Fin.cases, Fin.induction, Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast, cast_eq]
  all_goals norm_num only [Fin.coe_ofNat_eq_mod, smul_eq_mul, mul_zero, zero_mul,
    one_mul, mul_one, add_zero, zero_add, Complex.I_mul_I]
  all_goals try simp only [Fin.cons_zero, Fin.cons_one, diracCons_mk_zero, diracCons_mk_succ, diracCons_two, diracCons_three, diracCons_four,
    diracCons_five, diracCons_six, Complex.I_mul_I]
  all_goals norm_num only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
  all_goals try simp only [eq_mpr_eq_cast, cast_eq, Rat.cast_zero, Rat.cast_one, Rat.cast_neg,
    diracCons_mk_zero, diracCons_mk_succ, Fin.cons_zero, Fin.cons_one, diracCons_two, diracCons_three]
  all_goals norm_num only [mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add]
  all_goals ring_nf!

def diracRawGaugeFlat (x : Fin 12 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.I*((x 6:ℂ)+(x 11:ℂ)),(x 0:ℂ)+Complex.I*(x 1:ℂ),(x 2:ℂ)+Complex.I*(x 3:ℂ);
     -(x 0:ℂ)+Complex.I*(x 1:ℂ),Complex.I*((x 7:ℂ)+(x 11:ℂ)),(x 4:ℂ)+Complex.I*(x 5:ℂ);
     -(x 2:ℂ)+Complex.I*(x 3:ℂ),-(x 4:ℂ)+Complex.I*(x 5:ℂ),Complex.I*(-(x 6:ℂ)-(x 7:ℂ)+(x 11:ℂ))]

theorem diracRawGauge_flat (x : Fin 12 → ℝ) (i j : Fin 3) :
    diracRawGauge x i j=diracRawGaugeFlat x i j := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [diracRawGauge, diracGaugeUnit, diracRawGaugeFlat, rawMotherReal, rawMotherImag,
    Fin.sum_univ_succ, Pi.single_apply, Fin.castLE, Fin.val_ofNat, Fin.val_zero, Fin.val_natCast, Fin.coe_ofNat_eq_mod]
  all_goals try simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false,
    eq_mpr_eq_cast, cast_eq]
  all_goals try dsimp only [Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons,
    Fin.cases, Fin.induction, Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast, cast_eq]
  all_goals norm_num only [Fin.coe_ofNat_eq_mod, mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add]
  all_goals try simp only [eq_mpr_eq_cast, cast_eq, Rat.cast_zero, Rat.cast_one, Rat.cast_neg,
    diracCons_mk_zero, diracCons_mk_succ, Fin.cons_zero, Fin.cons_one, diracCons_two, diracCons_three]
  all_goals norm_num only [mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add]
  all_goals norm_num only [Fin.castLE, Fin.val_ofNat, Fin.val_zero, Fin.val_natCast, Fin.coe_ofNat_eq_mod]
  all_goals try dsimp only [Fin.induction, Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast, cast_eq, Rat.cast_zero, Rat.cast_one, Rat.cast_neg]
  all_goals ring_nf!

open Lean Meta Elab Tactic in
elab "diracPolynomialNF" close?:(&"close")? : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).eq? |
    throwError "expected the actual quadratic equality"
  let (left, right) ← Mathlib.Tactic.AtomM.run (if close?.isSome then .reducible else .default) do
    let left ← Mathlib.Tactic.RingNF.evalExpr lhs
    let right ← Mathlib.Tactic.RingNF.evalExpr rhs
    pure (left, right)
  let lp := left.proof?.getD (← mkEqRefl lhs)
  let rp := right.proof?.getD (← mkEqRefl rhs)
  if close?.isSome then
    unless ← withReducible <| isDefEq left.expr right.expr do
      let mut a := left.expr
      let mut b := right.expr
      for _ in [:512] do
        unless a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs do break
        let xs := a.getAppArgs
        let ys := b.getAppArgs
        let mut descended := false
        for i in [:xs.size] do
          if xs[i]! != ys[i]! then
            a := xs[i]!
            b := ys[i]!
            descended := true
            break
        unless descended do break
      throwError "actual polynomial first unequal subterms:\n{a}\n{b}"
    goal.assign (← mkEqTrans lp (← mkEqSymm rp))
    replaceMainGoal []
  else
    let normalized ← mkFreshExprMVar (← mkEq left.expr right.expr)
    goal.assign (← mkEqTrans lp (← mkEqTrans normalized (← mkEqSymm rp)))
    replaceMainGoal [normalized.mvarId!]

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 65536 in
 theorem nativeDiracQuadratic_literal (jet : NativeFirstJet) :
    nativeDiracQuadratic jet = literalDiracQuadratic jet := by
  rw [nativeDiracQuadratic_flat]
  simp only [diracRawQuadratic, diracRawPairCoefficient]
  norm_num only [Fin.coe_ofNat_eq_mod]
  simp only [diracTripletPair, diracRawCovariantBase, diracRawCovariantFirst, diracRawCovariantSecond]
  simp_rw [diracSpinRaw_flat, diracRawGauge_flat]
  norm_num (config := { maxSteps := 1000000 }) [diracSpinRawFlat, diracRawGaugeFlat,
    diracPrepared, phaseComponentVelocity, homogeneousContorsion,
    diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
    lorentzBivectorFirst, lorentzBivectorSecond, Matrix.mul_apply, Matrix.smul_apply,
    Fin.sum_univ_succ, fieldCoframe, diracAdjugateCoefficient, fieldPrimalComplex, fieldPrimal,
    fieldDualComplex, fieldDual, primalSlot, dualSlot, coframeSlot, lorentzSlot, gaugeSlot,
    literalDiracQuadratic, literalDiracTerms, decodeNativeRealRecords, nativeDiracRecordCodes,
    nativeRecordRealAtoms, nativeRecordJet, nativeJetCoefficient, List.sum_cons,
    gaugeBackgroundRaw, gaugeColorRaw, frequency, gaugeScale, Complex.mul_re, Complex.mul_im]
  simp only [Fin.reduceSucc, Fin.reduceEq, Fin.isValue, Fin.reduceFinMk, if_true, if_false,
    eq_mpr_eq_cast, cast_eq]
  dsimp only [Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons,
    Fin.cases, Fin.induction, Fin.induction.go]
  simp only [eq_mpr_eq_cast, cast_eq, Fin.cons_zero, Fin.cons_one, diracCons_mk_zero, diracCons_mk_succ,
    diracCons_two, diracCons_three, diracCons_four, diracCons_five, diracCons_six]
  norm_num only [Fin.coe_ofNat_eq_mod, Pi.single_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im, smul_eq_mul, mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add]
  try simp only [Fin.reduceFinMk, Fin.reduceSucc, Fin.reduceEq, Fin.isValue, if_true, if_false, dite_true, dite_false]
  diracPolynomialNF
  try simp only [Mathlib.Tactic.RingNF.nat_rawCast_0, Mathlib.Tactic.RingNF.nat_rawCast_1, Mathlib.Tactic.RingNF.nat_rawCast_2, Mathlib.Tactic.RingNF.int_rawCast_neg, Mathlib.Tactic.RingNF.nnrat_rawCast, Mathlib.Tactic.RingNF.rat_rawCast_neg, pow_one, spinScale_sq, lapse_sq, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im]
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some (_, lhs, rhs) := (← Lean.instantiateMVars (← goal.getType)).eq? |
      throwError "expected the actual quadratic equality"
    let difference ← Lean.Meta.mkSub lhs rhs
    let (normal, atoms) ← Mathlib.Tactic.AtomM.run .default do
      let normal ← Mathlib.Tactic.RingNF.evalExpr difference
      let state : Mathlib.Tactic.AtomM.State ← get
      pure (normal, state.atoms)
    let zero ← Lean.Meta.mkNumeral (← Lean.Meta.inferType lhs) 0
    if ← Lean.Meta.isDefEq normal.expr zero then
      let proof := normal.proof?.getD (← Lean.Meta.mkEqRefl difference)
      let zeroProof ← Lean.Meta.mkEqTrans proof (← Lean.Meta.mkEqRefl zero)
      goal.assign (← Lean.Meta.mkAppM ``eq_of_sub_eq_zero #[zeroProof])
      Lean.Elab.Tactic.replaceMainGoal []
    else
      for atom in atoms do
        unless atom.hasFVar do Lean.logInfo m!"remaining actual constant atom: {atom}"
      let mut tail := normal.expr
      for _ in [:8] do
        if tail.getAppFn.isConstOf ``HAdd.hAdd then
          let args := tail.getAppArgs
          Lean.logInfo m!"remaining actual delta monomial: {args[args.size-2]!}"
          tail := args.back!
        else
          Lean.logInfo m!"remaining actual delta monomial: {tail}"
          break
      throwError "actual polynomial reduction has a nonzero residual"



private theorem diracLiteralHessian_value (terms : List (NativeJetIndex × NativeJetIndex × ℝ))
    (a b : NativeFirstJet) : nativeLiteralHessian terms a b =
      (terms.map fun term => term.2.2*(nativeJetCoefficient a term.1*nativeJetCoefficient b term.2.1+
        nativeJetCoefficient a term.2.1*nativeJetCoefficient b term.1)).sum := by
  unfold nativeLiteralHessian
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp only [List.map_cons, List.sum_cons, add_apply, ih, smul_apply, smul_eq_mul]
    simp only [nativeOrderedTermHessian, ContinuousLinearMap.smulRight_apply]
    rfl

private theorem diracLiteralHessian_diagonal (jet : NativeFirstJet) :
    literalDiracHessian jet jet=2*literalDiracQuadratic jet := by
  rw [literalDiracHessian, diracLiteralHessian_value]
  unfold literalDiracQuadratic
  rw [←List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro term _
  ring

private theorem diracLiteralHessian_symmetric (a b : NativeFirstJet) :
    literalDiracHessian a b=literalDiracHessian b a := by
  simp only [literalDiracHessian, diracLiteralHessian_value]
  congr 1
  apply List.map_congr_left
  intro term _
  ring

theorem nativeDiracHessian_literal (a b : NativeFirstJet) :
    nativeBlockHessian 3 a b=literalDiracHessian a b := by
  change nativeDiracHessian a b=literalDiracHessian a b
  have diagonal (jet : NativeFirstJet) : nativeDiracHessian jet jet=literalDiracHessian jet jet := by
    rw [nativeDiracHessian_quadratic, diracLiteralHessian_diagonal, nativeDiracQuadratic_literal]
  have total := diagonal (a+b)
  simp only [map_add, add_apply] at total
  rw [nativeDiracHessian_symmetric b a, diracLiteralHessian_symmetric b a,
    diagonal a, diagonal b] at total
  linarith

theorem nativeDiracFourier_literal (p : Fin 4 → ℂ) :
    nativeFourierHessian (nativeBlockHessian 3) p=nativeLiteralFourier literalDiracTerms p := by
  have source : nativeBlockHessian 3=literalDiracHessian := by
    apply ContinuousLinearMap.ext; intro a
    apply ContinuousLinearMap.ext; intro b
    exact nativeDiracHessian_literal a b
  rw [source]
  exact nativeLiteralFourier_sound literalDiracTerms p

end LowEnergy.SourcePropagationNativeActionHessian
