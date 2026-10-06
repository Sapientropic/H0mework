import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceChargeSpectrum
import Mathlib.LinearAlgebra.Matrix.Integer

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
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open scoped BigOperators Matrix InnerProductSpace

abbrev RestPoleIndex := Fin 2 × Fin 2

def sourceRestSign (side : Fin 2) : ℂ := if side=0 then -1 else 1
def sourceRestSymmetry (symmetry : Fin 2) : ℂ := if symmetry=0 then -1 else 1

def sourceRestExchange : Matrix Source.Index Source.Index ℂ := fun row column=>
  if row.1.val/2=column.1.val/2 ∧ row.1.val%2=column.2.val ∧ row.2.val=column.1.val%2 then 1 else 0

def sourceRestSide (side : Fin 2) : Matrix Source.Index Source.Index ℂ := fun row column=>
  if row=column ∧ row.1.val/2=side.val then 1 else 0

def sourceRestHamiltonian : Matrix Source.Index Source.Index ℂ := fun row column=>
  (if row.1.val<2 then -(frequency : ℂ) else (frequency : ℂ))*
    (2*(if row=column then 1 else 0)+sourceRestExchange row column)

def sourceRestPoleEnergy (pole : RestPoleIndex) : ℂ :=
  sourceRestSign pole.1*(frequency : ℂ)*(2+sourceRestSymmetry pole.2)

/-- Each projector retains the original chirality block and its spin-color exchange symmetry. -/
def sourceRestPoleProjection (pole : RestPoleIndex) : Matrix Source.Index Source.Index ℂ :=
  (1/2 : ℂ) • (sourceRestSide pole.1+sourceRestSymmetry pole.2 •
    (sourceRestSide pole.1*sourceRestExchange))

theorem sourceRestHamiltonian_generated (point : BasePoint) (values : Source.Index→ℂ) :
    FullQuantum.hamiltonian Runtime.configuration point 0 (embed values)=
      embed (sourceRestHamiltonian *ᵥ values) := by
  rw [Runtime.configuration_eq,physical_hamiltonian_embed,physical_free_embed]
  congr 1
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [principalValues,spinValues,gaugeValues,sourceRestHamiltonian,sourceRestExchange,
      Matrix.mulVec,dotProduct,Fintype.sum_prod_type,sourceColorPauli,
      DiracCliffordRepresentation.diracGamma,DiracCliffordRepresentation.diracGammaZero,
      DiracCliffordRepresentation.diracGammaOne,DiracCliffordRepresentation.diracGammaTwo,
      DiracCliffordRepresentation.diracGammaThree,DiracCliffordRepresentation.diracGammaFive,
      Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_three,Fin.sum_univ_two,frequency,gaugeScale]
  all_goals ring_nf; simp only [Complex.I_sq]; ring

private theorem sourceRestPoleProjection_entry (pole : RestPoleIndex) (row column : Source.Index) :
    sourceRestPoleProjection pole row column=
      (1/2 : ℂ)*((if row=column ∧ row.1.val/2=pole.1.val then 1 else 0)+
        sourceRestSymmetry pole.2*(if row.1.val/2=pole.1.val then sourceRestExchange row column else 0)) := by
  have diagonal : sourceRestSide pole.1=Matrix.diagonal (fun index : Source.Index=>
      if index.1.val/2=pole.1.val then (1 : ℂ) else 0) := by
    ext i j
    by_cases same : i=j
    · subst j
      simp [sourceRestSide]
    · simp [sourceRestSide,same]
  simp only [sourceRestPoleProjection,diagonal,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply,
    Matrix.diagonal_apply]
  by_cases same : row=column <;> by_cases side : row.1.val/2=pole.1.val <;> simp [same,side]

theorem sourceRestPoleProjection_hermitian (pole : RestPoleIndex) :
    (sourceRestPoleProjection pole).conjTranspose=sourceRestPoleProjection pole := by
  rcases pole with ⟨side,symmetry⟩
  ext row column
  rcases row with ⟨spin,color⟩
  rcases column with ⟨spin',color'⟩
  fin_cases side <;> fin_cases symmetry <;> fin_cases spin <;> fin_cases spin' <;>
    fin_cases color <;> fin_cases color' <;>
    norm_num [sourceRestPoleProjection_entry,sourceRestExchange,sourceRestSymmetry,
      Matrix.conjTranspose_apply,Matrix.mul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_four,Fin.sum_univ_two,Matrix.smul_apply,Matrix.add_apply]

private def sourceRestPoleNumerator (pole : RestPoleIndex) : Matrix Source.Index Source.Index ℤ :=
  fun row column=>if row.1.val/2=pole.1.val then
    (if row=column then 1 else 0)+(if pole.2=0 then -1 else 1)*
      (if row.1.val/2=column.1.val/2 ∧ row.1.val%2=column.2.val ∧ row.2.val=column.1.val%2 then 1 else 0)
  else 0

private theorem sourceRestPoleNumerator_multiply : ∀ left right : RestPoleIndex,
    sourceRestPoleNumerator left*sourceRestPoleNumerator right=
      if left=right then sourceRestPoleNumerator left+sourceRestPoleNumerator left else 0 := by
  decide +kernel

private theorem sourceRestPoleProjection_cast (pole : RestPoleIndex) :
    sourceRestPoleProjection pole=(1/2 : ℂ) • (sourceRestPoleNumerator pole).map ((↑) : ℤ→ℂ) := by
  ext row column
  rw [sourceRestPoleProjection_entry]
  simp only [Matrix.smul_apply,Matrix.map_apply,sourceRestPoleNumerator,sourceRestSymmetry,sourceRestExchange,smul_eq_mul]
  split_ifs <;> simp_all
  all_goals norm_num

theorem sourceRestPoleProjection_multiply (left right : RestPoleIndex) :
    sourceRestPoleProjection left*sourceRestPoleProjection right=
      if left=right then sourceRestPoleProjection left else 0 := by
  rw [sourceRestPoleProjection_cast,sourceRestPoleProjection_cast,smul_mul_assoc,mul_smul_comm,smul_smul,
    ←Matrix.map_mul_intCast,sourceRestPoleNumerator_multiply]
  by_cases same : left=right
  · subst right
    rw [if_pos rfl,if_pos rfl,
      Matrix.map_add (fun z : ℤ=>(z : ℂ)) (fun x y=>Int.cast_add x y)]
    module
  · simp [same]

private theorem sourceRestPoleNumerator_partition : ∀ row column : Source.Index,
    (∑ pole : RestPoleIndex,sourceRestPoleNumerator pole row column)=if row=column then 2 else 0 := by
  decide +kernel

theorem sourceRestPoleProjection_partition :
    (∑ pole : RestPoleIndex,sourceRestPoleProjection pole)=1 := by
  ext row column
  simp only [Matrix.sum_apply,sourceRestPoleProjection_cast,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul]
  rw [←Finset.mul_sum,←Int.cast_sum,sourceRestPoleNumerator_partition]
  by_cases same : row=column <;> simp [same,Matrix.one_apply]

private def sourceRestHamiltonianNumerator : Matrix Source.Index Source.Index ℤ := fun row column=>
  (if row.1.val<2 then -1 else 1)*
    (2*(if row=column then 1 else 0)+
      if row.1.val/2=column.1.val/2 ∧ row.1.val%2=column.2.val ∧ row.2.val=column.1.val%2 then 1 else 0)

private def sourceRestEnergyNumerator (pole : RestPoleIndex) : ℤ :=
  (if pole.1=0 then -1 else 1)*(2+if pole.2=0 then -1 else 1)

private theorem sourceRestHamiltonianNumerator_eigen : ∀ pole : RestPoleIndex,
    sourceRestHamiltonianNumerator*sourceRestPoleNumerator pole=
      sourceRestEnergyNumerator pole • sourceRestPoleNumerator pole := by
  decide +kernel

private theorem sourceRestHamiltonian_cast :
    sourceRestHamiltonian=(frequency : ℂ) • sourceRestHamiltonianNumerator.map ((↑) : ℤ→ℂ) := by
  ext row column
  simp only [sourceRestHamiltonian,sourceRestHamiltonianNumerator,Matrix.smul_apply,Matrix.map_apply,
    smul_eq_mul,sourceRestExchange]
  split_ifs <;> norm_num

theorem sourceRestPoleProjection_eigen (pole : RestPoleIndex) :
    sourceRestHamiltonian*sourceRestPoleProjection pole=
      sourceRestPoleEnergy pole • sourceRestPoleProjection pole := by
  rw [sourceRestHamiltonian_cast,sourceRestPoleProjection_cast,smul_mul_assoc,mul_smul_comm,smul_smul,
    ←Matrix.map_mul_intCast,sourceRestHamiltonianNumerator_eigen]
  ext row column
  simp only [Matrix.smul_apply,Matrix.map_apply,smul_eq_mul,Int.cast_mul,
    sourceRestPoleEnergy,sourceRestSign,sourceRestSymmetry,sourceRestEnergyNumerator]
  split_ifs <;> norm_num <;> ring

theorem sourceRestHamiltonian_spectral :
    sourceRestHamiltonian=∑ pole : RestPoleIndex,sourceRestPoleEnergy pole • sourceRestPoleProjection pole := by
  calc
    sourceRestHamiltonian=sourceRestHamiltonian*∑ pole : RestPoleIndex,sourceRestPoleProjection pole := by
      rw [sourceRestPoleProjection_partition,Matrix.mul_one]
    _=∑ pole : RestPoleIndex,sourceRestHamiltonian*sourceRestPoleProjection pole := by rw [Matrix.mul_sum]
    _=_ := by simp only [sourceRestPoleProjection_eigen]

/-- The four spectral sectors act on the original full mother Hamiltonian, on its invariant source carrier. -/
theorem sourceRestPoleProjection_physical (pole : RestPoleIndex) (point : BasePoint) (values : Source.Index→ℂ) :
    FullQuantum.hamiltonian Runtime.configuration point 0
        (embed (sourceRestPoleProjection pole *ᵥ values))=
      sourceRestPoleEnergy pole • embed (sourceRestPoleProjection pole *ᵥ values) := by
  rw [sourceRestHamiltonian_generated,Matrix.mulVec_mulVec,sourceRestPoleProjection_eigen,
    Matrix.smul_mulVec,map_smul]

abbrev RestStateIndex := Fin 2 × Fin 4

def actualRestAmplitude (point : BasePoint) : ℂ :=
  (ChargedPreparation.CanonicalParticle.normalization 0 : ℂ)*
    ChargedPreparation.CanonicalParticle.amplitude point*(2*(frequency : ℂ))

def sourceRestStateCoefficients (state : Fin 4) : Fin 4→ℂ :=
  ![![0,1,-1,0],![(spinScale : ℂ),0,0,0],![0,1,1,0],![0,0,0,(spinScale : ℂ)]] state

def sourceRestStateValues (state : RestStateIndex) : Source.Index→ℂ :=
  if state.1=0 then ChargedPreparation.CanonicalParticle.upperValues (sourceRestStateCoefficients state.2)
  else lowerValues (sourceRestStateCoefficients state.2)

private theorem sourceRestStateValues_entry (state : RestStateIndex) (index : Source.Index) :
    sourceRestStateValues state index=
      if state.1=0 then
        if index.1=0 then (if index.2=0 then sourceRestStateCoefficients state.2 0 else sourceRestStateCoefficients state.2 1)
        else if index.1=1 then (if index.2=0 then sourceRestStateCoefficients state.2 2 else sourceRestStateCoefficients state.2 3) else 0
      else
        if index.1=2 then (if index.2=0 then sourceRestStateCoefficients state.2 0 else sourceRestStateCoefficients state.2 1)
        else if index.1=3 then (if index.2=0 then sourceRestStateCoefficients state.2 2 else sourceRestStateCoefficients state.2 3) else 0 := by
  rcases state with ⟨side,state⟩
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases state <;> fin_cases spin <;> fin_cases color <;> rfl

private theorem sourceRestStateCoefficients_entry (state index : Fin 4) :
    sourceRestStateCoefficients state index=
      if state=0 then (if index=1 then 1 else if index=2 then -1 else 0)
      else if state=1 then (if index=0 then (spinScale : ℂ) else 0)
      else if state=2 then (if index=1 ∨ index=2 then 1 else 0)
      else (if index=3 then (spinScale : ℂ) else 0) := by
  fin_cases state <;> fin_cases index <;> rfl

def actualRestStateCoordinates (point : BasePoint) (state : RestStateIndex) : Source.Index→ℂ :=
  actualRestAmplitude point • sourceRestStateValues state

def sourceRestStateAction (state : Fin 4) : Mother :=
  ![(1 : Mother),
    -(spinScale : ℂ) • (Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 0)+
      Complex.I • Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 1)),
    (2 : ℂ) • Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 2),
    (spinScale : ℂ) • (Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 0)-
      Complex.I • Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 1))] state

def actualRestStatePreparation (state : RestStateIndex) : Mother :=
  let prepared := (sourceRestStateAction state.2).comp (actualPolePreparation 0)
  if state.1=0 then prepared
  else (-diracMatrixMatterAction DiracCliffordRepresentation.diracGammaZero).comp prepared

private theorem actualPoleCoordinates_zero (point : BasePoint) :
    actualPoleCoordinates point 0=actualRestStateCoordinates point (0,0) := by
  have rateZero : ChargedPreparation.SpatialSpectrum.rate 0=frequency := by
    simp [ChargedPreparation.SpatialSpectrum.rate,spatialSquare,
      Real.sqrt_sq_eq_abs,abs_of_pos ChargedPreparation.Dispersion.frequency_pos]
  ext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [actualPoleCoordinates,ChargedPreparation.CanonicalParticle.normalizedValues,
      ChargedPreparation.CanonicalParticle.values,ChargedPreparation.CanonicalParticle.coefficients,
      ChargedPreparation.CanonicalParticle.upperValues,actualRestStateCoordinates,actualRestAmplitude,
      sourceRestStateValues,sourceRestStateCoefficients,rateZero]
  all_goals ring

private theorem actualRestAmplitude_square (point : BasePoint) :
    star (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ) := by
  have unit:=ChargedPreparation.CanonicalParticle.normalized_values_square point 0
  change (∑ index : Source.Index,star (actualPoleCoordinates point 0 index)*actualPoleCoordinates point 0 index)=1 at unit
  rw [actualPoleCoordinates_zero] at unit
  simp [actualRestStateCoordinates,sourceRestStateValues,sourceRestStateCoefficients,
    ChargedPreparation.CanonicalParticle.upperValues,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] at unit
  change (starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ)
  linear_combination unit/2

private theorem sourceRestStateAction_generated (state : Fin 4) (point : BasePoint) :
    sourceRestStateAction state (embed (actualPoleCoordinates point 0))=
      embed (actualRestStateCoordinates point (0,state)) := by
  rw [actualPoleCoordinates_zero]
  fin_cases state
  all_goals first
  | rfl
  | change (-(spinScale : ℂ) • (Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 0)+
      Complex.I • Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 1)))
        (embed (actualRestStateCoordinates point (0,0)))=_
  | change ((2 : ℂ) • Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 2))
        (embed (actualRestStateCoordinates point (0,0)))=_
  | change ((spinScale : ℂ) • (Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 0)-
      Complex.I • Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 1)))
        (embed (actualRestStateCoordinates point (0,0)))=_
  all_goals simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    sourceCharge_embedding,←map_smul,←map_add,←map_sub]
  all_goals apply congrArg embed; ext index; rcases index with ⟨spin,color⟩
  all_goals fin_cases spin <;> fin_cases color <;>
    simp [actualRestStateCoordinates,sourceRestStateValues,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,sourceChargeCoordinates,
      sourceColorPauli,Fin.sum_univ_two]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

private theorem sourceRestState_rotate (values : Fin 4→ℂ) :
    (-diracMatrixMatterAction DiracCliffordRepresentation.diracGammaZero)
      (embed (ChargedPreparation.CanonicalParticle.upperValues values))=embed (lowerValues values) := by
  simp only [LinearMap.neg_apply,spin_embed]
  rw [←map_neg]
  congr 1
  ext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [ChargedPreparation.CanonicalParticle.upperValues,lowerValues,
      DiracCliffordRepresentation.diracGammaZero,Fin.sum_univ_four]

 theorem actualRestState_source (point : BasePoint) (state : RestStateIndex) :
    actualRestStatePreparation state (embed (Source.vector point))=embed (actualRestStateCoordinates point state) := by
  rcases state with ⟨side,state⟩
  fin_cases side
  · change sourceRestStateAction state (ChargedPreparation.CanonicalParticle.normalizedPreparation 0 (embed (Source.vector point)))=_
    rw [ChargedPreparation.CanonicalParticle.normalized_source]
    exact sourceRestStateAction_generated state point
  · change (-diracMatrixMatterAction DiracCliffordRepresentation.diracGammaZero)
      (sourceRestStateAction state (ChargedPreparation.CanonicalParticle.normalizedPreparation 0 (embed (Source.vector point))))=_
    rw [ChargedPreparation.CanonicalParticle.normalized_source]
    change (-diracMatrixMatterAction DiracCliffordRepresentation.diracGammaZero)
      (sourceRestStateAction state (embed (actualPoleCoordinates point 0)))=_
    rw [sourceRestStateAction_generated]
    change (-diracMatrixMatterAction DiracCliffordRepresentation.diracGammaZero)
      (embed (actualRestAmplitude point • ChargedPreparation.CanonicalParticle.upperValues (sourceRestStateCoefficients state)))=_
    rw [←ChargedPreparation.CanonicalParticle.upperValues_smul,sourceRestState_rotate,lowerValues_smul]
    rfl

 theorem actualRestState_full_prepared (point : BasePoint) (state : RestStateIndex) :
    operator (actualRestStatePreparation state) (YangMills.FullPairing.prepared point)=
      naturalCoordinates (embed (actualRestStateCoordinates point state)) := by
  rw [YangMills.FullPairing.prepared,operator_coordinates,actualRestState_source]

def sourceRestStatePole (state : RestStateIndex) : RestPoleIndex :=
  (state.1,if state.2=0 then 0 else 1)

theorem sourceRestState_projection (state : RestStateIndex) :
    sourceRestPoleProjection (sourceRestStatePole state) *ᵥ sourceRestStateValues state=sourceRestStateValues state := by
  rcases state with ⟨side,state⟩
  ext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases state <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceRestPoleProjection_entry,sourceRestExchange,sourceRestSymmetry,
      sourceRestStatePole,sourceRestStateValues,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,lowerValues,Matrix.mulVec,dotProduct,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two,
      Matrix.smul_apply,Matrix.add_apply]
  all_goals dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals simp only [Fin.reduceEq,Fin.isValue,Fin.reduceFinMk,if_true,if_false]
  all_goals norm_num

theorem actualRestState_hamiltonian (point : BasePoint) (state : RestStateIndex) :
    FullQuantum.hamiltonian Runtime.configuration point 0
      (actualRestStatePreparation state (actual.matter point))=
        sourceRestPoleEnergy (sourceRestStatePole state) •
          actualRestStatePreparation state (actual.matter point) := by
  have material : actual.matter point=(2 : ℂ) • embed (Source.vector point) := by
    apply naturalCoordinates.injective
    simpa only [map_smul,YangMills.FullPairing.prepared] using actual_eq_twice_prepared point
  rw [material,map_smul,map_smul,actualRestState_source]
  have projected : sourceRestPoleProjection (sourceRestStatePole state) *ᵥ actualRestStateCoordinates point state=
      actualRestStateCoordinates point state := by
    rw [actualRestStateCoordinates,Matrix.mulVec_smul,sourceRestState_projection]
  have eigen:=sourceRestPoleProjection_physical (sourceRestStatePole state) point (actualRestStateCoordinates point state)
  rw [projected] at eigen
  rw [eigen]
  exact smul_comm _ _ _

private theorem sourceRestState_values_gram (left right : RestStateIndex) :
    (∑ index : Source.Index,star (sourceRestStateValues left index)*sourceRestStateValues right index)=
      if left=right then 2 else 0 := by
  have scale : (spinScale : ℂ)^2=2 := by exact_mod_cast spinScale_sq
  rcases left with ⟨side,state⟩
  rcases right with ⟨side',state'⟩
  fin_cases side <;> fin_cases side' <;> fin_cases state <;> fin_cases state' <;>
    norm_num [sourceRestStateValues,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,lowerValues,
      Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals norm_num
  all_goals linear_combination scale

theorem actualRestState_orthonormal (point : BasePoint) (left right : RestStateIndex) :
    inner ℂ (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared point))
      (operator (actualRestStatePreparation right) (YangMills.FullPairing.prepared point))=
        if left=right then 1 else 0 := by
  rw [actualRestState_full_prepared,actualRestState_full_prepared,inner_embed]
  simp only [coordinates_embed,actualRestStateCoordinates,Pi.smul_apply,smul_eq_mul,star_mul]
  have factor : (∑ index : Source.Index,
      (star (sourceRestStateValues left index)*star (actualRestAmplitude point))*
        (actualRestAmplitude point*sourceRestStateValues right index))=
      (star (actualRestAmplitude point)*actualRestAmplitude point)*
        ∑ index : Source.Index,star (sourceRestStateValues left index)*sourceRestStateValues right index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [factor,actualRestAmplitude_square,sourceRestState_values_gram]
  split_ifs <;> norm_num

def sourceRestChargeMixing (direction : Fin 3) : Matrix RestStateIndex RestStateIndex ℂ := fun left right=>
  (1/2 : ℂ)*(∑ index : Source.Index,star (sourceRestStateValues left index)*
    sourceChargeCoordinates direction (sourceRestStateValues right) index)

def sourceRestChargeMixingBlock (direction : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  let s := (spinScale : ℂ)/4
  ![!![0,-s,0,s;-s,0,-s,0;0,-s,0,-s;s,0,-s,0],
    !![0,-Complex.I*s,0,-Complex.I*s;Complex.I*s,0,Complex.I*s,0;
      0,-Complex.I*s,0,Complex.I*s;Complex.I*s,0,-Complex.I*s,0],
    !![0,0,1/2,0;0,-1/2,0,0;1/2,0,0,0;0,0,0,1/2]] direction

theorem sourceRestChargeMixing_generated (direction : Fin 3) (left right : RestStateIndex) :
    sourceRestChargeMixing direction left right=
      if left.1=right.1 then sourceRestChargeMixingBlock direction left.2 right.2 else 0 := by
  have scale : (spinScale : ℂ)^2=2 := by exact_mod_cast spinScale_sq
  rcases left with ⟨side,state⟩
  rcases right with ⟨side',state'⟩
  fin_cases direction <;> fin_cases side <;> fin_cases side' <;> fin_cases state <;> fin_cases state' <;>
    norm_num [sourceRestChargeMixing,sourceRestChargeMixingBlock,sourceRestStateValues,
      sourceRestStateCoefficients,ChargedPreparation.CanonicalParticle.upperValues,lowerValues,
      sourceChargeCoordinates,sourceColorPauli,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals norm_num
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals ring_nf
  all_goals norm_num [scale]

/-- The same repaired independent dual reads every spectral-sector transition with the original action phase. -/
theorem actualRestState_current_mixing (direction : Fin 3) (point : BasePoint) (left right : RestStateIndex) :
    actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation left)
        (currentAction 0 (sourceColorP286Generator direction)
          (actualRestStatePreparation right (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*sourceRestChargeMixing direction left right := by
  rw [Electromagnetic.ExternalState.original_prepared_vertex]
  change 4*(spinScale : ℂ)*inner ℂ
    (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared point))
    (operator ((Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction)).comp
      (actualRestStatePreparation right)) (YangMills.FullPairing.prepared point))=_
  have composed : operator ((Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction)).comp
      (actualRestStatePreparation right)) (YangMills.FullPairing.prepared point)=
    operator (Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction))
      (operator (actualRestStatePreparation right) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared,operator_coordinates]
  rw [composed,actualRestState_full_prepared,actualRestState_full_prepared,
    operator_coordinates,inner_embed]
  simp only [sourceCharge_coordinates,actualRestStateCoordinates,Pi.smul_apply,smul_eq_mul,star_mul]
  have chargeScale : ∀ index,sourceChargeCoordinates direction
      (actualRestAmplitude point • sourceRestStateValues right) index=
      actualRestAmplitude point*sourceChargeCoordinates direction (sourceRestStateValues right) index := by
    intro index
    exact congrFun (sourceChargeCoordinates_smul direction (actualRestAmplitude point) (sourceRestStateValues right)) index
  simp only [chargeScale]
  have factor : (∑ index : Source.Index,
      (star (sourceRestStateValues left index)*star (actualRestAmplitude point))*
        (actualRestAmplitude point*sourceChargeCoordinates direction (sourceRestStateValues right) index))=
      (star (actualRestAmplitude point)*actualRestAmplitude point)*
        ∑ index : Source.Index,star (sourceRestStateValues left index)*sourceChargeCoordinates direction (sourceRestStateValues right) index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [factor,actualRestAmplitude_square,Stage10.ActionNormalization.phaseMomentum_source]
  simp only [sourceRestChargeMixing]
  push_cast
  rfl

theorem actualRestState_current_diagonal (direction : Fin 3) (point : BasePoint) (state : RestStateIndex) :
    actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation state)
        (currentAction 0 (sourceColorP286Generator direction)
          (actualRestStatePreparation state (actual.matter point))))=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*
        (if direction=2 then (if state.2=1 then -(1/2 : ℂ) else if state.2=3 then 1/2 else 0) else 0) := by
  rcases state with ⟨side,state⟩
  rw [actualRestState_current_mixing,sourceRestChargeMixing_generated]
  congr 1
  fin_cases direction <;> fin_cases state <;> norm_num [sourceRestChargeMixingBlock]
  all_goals simp only [Fin.reduceEq,Fin.isValue,Fin.reduceFinMk,if_true]
  all_goals norm_num

 theorem sourceRestState_charge_ends (side : Fin 2) (edge : Fin 2) :
    sourceChargeCoordinates 2 (sourceRestStateValues (side,if edge=0 then 1 else 3))=
      (if edge=0 then -(1/2 : ℂ) else 1/2) • sourceRestStateValues (side,if edge=0 then 1 else 3) := by
  ext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases edge <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceRestStateValues_entry,sourceRestStateCoefficients_entry,
      sourceChargeCoordinates,sourceColorPauli,Fin.sum_univ_two,Fin.reduceEq,Fin.isValue,Fin.reduceFinMk]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

 theorem actualRestState_charge_ends (point : BasePoint) (side : Fin 2) (edge : Fin 2) :
    Electromagnetic.Action.canonicalDirection (sourceColorP286Generator 2)
      (actualRestStatePreparation (side,if edge=0 then 1 else 3) (actual.matter point))=
      (if edge=0 then -(1/2 : ℂ) else 1/2) •
        actualRestStatePreparation (side,if edge=0 then 1 else 3) (actual.matter point) := by
  have material : actual.matter point=(2 : ℂ) • embed (Source.vector point) := by
    apply naturalCoordinates.injective
    simpa only [map_smul,YangMills.FullPairing.prepared] using actual_eq_twice_prepared point
  rw [material,map_smul,map_smul,actualRestState_source,sourceCharge_embedding,actualRestStateCoordinates,
    sourceChargeCoordinates_smul,sourceRestState_charge_ends]
  simp only [map_smul]
  module

 theorem actualRestState_prepared_nonzero (point : BasePoint) (state : RestStateIndex) :
    operator (actualRestStatePreparation state) (YangMills.FullPairing.prepared point)≠0 := by
  intro zero
  have unit:=actualRestState_orthonormal point state state
  rw [zero,inner_zero_left,if_pos rfl] at unit
  exact zero_ne_one unit

theorem actualRestState_matter_nonzero (point : BasePoint) (state : RestStateIndex) :
    actualRestStatePreparation state (actual.matter point)≠0 := by
  have material : actual.matter point=(2 : ℂ) • embed (Source.vector point) := by
    apply naturalCoordinates.injective
    simpa only [map_smul,YangMills.FullPairing.prepared] using actual_eq_twice_prepared point
  intro zero
  rw [material,map_smul,actualRestState_source] at zero
  have original : embed (actualRestStateCoordinates point state)=0 :=
    (smul_eq_zero.mp zero).resolve_left (by norm_num)
  apply actualRestState_prepared_nonzero point state
  rw [actualRestState_full_prepared,original,map_zero]

/-- Every source spectral branch has a nonzero external state produced from the original preparation and currents. -/
theorem actualRestPole_generated (point : BasePoint) (pole : RestPoleIndex) :
    ∃ state : RestStateIndex,
      actualRestStatePreparation state (actual.matter point)≠0 ∧
      FullQuantum.hamiltonian Runtime.configuration point 0
        (actualRestStatePreparation state (actual.matter point))=
          sourceRestPoleEnergy pole • actualRestStatePreparation state (actual.matter point) := by
  let state : RestStateIndex := (pole.1,if pole.2=0 then 0 else 1)
  refine ⟨state,actualRestState_matter_nonzero point state,?_⟩
  have selected : sourceRestStatePole state=pole := by
    rcases pole with ⟨side,symmetry⟩
    fin_cases symmetry <;> rfl
  rw [←selected]
  exact actualRestState_hamiltonian point state

theorem actualRestState_timeMomentum (point : BasePoint) (state : RestStateIndex) :
    FullQuantum.normalizedMomentum actual point
      ((actual.conjugateMatter point).comp (canonicalDual (actualRestStatePreparation state)))
      (actualRestStatePreparation state (actual.matter point))=
        (Stage10.ActionNormalization.phaseMomentum : ℂ) := by
  rw [canonical_time_gram,actualRestState_orthonormal,if_pos rfl,mul_one,
    Stage10.ActionNormalization.phaseMomentum_source]
  push_cast
  rfl

/-- This remains the original hypercharge channel on the full rest-pole pool. -/
theorem actualRestState_hypercharge_current (point : BasePoint) (state : RestStateIndex) :
    actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation state)
        (currentAction 0 HyperchargeResponse.chargeDirection
          (actualRestStatePreparation state (actual.matter point))))=
      -(Stage10.ActionNormalization.phaseMomentum : ℂ) := by
  rw [canonical_current_gram]
  have composed : operator (canonicalCharge.comp (actualRestStatePreparation state))
      (YangMills.FullPairing.prepared point)=
      operator canonicalCharge (operator (actualRestStatePreparation state) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared,operator_coordinates]
  rw [composed,actualRestState_full_prepared,operator_coordinates,inner_embed]
  simp_rw [canonical_charge_coordinates,mul_neg]
  rw [Finset.sum_neg_distrib]
  have unit : (∑ index : Source.Index,star (actualRestStateCoordinates point state index)*
      actualRestStateCoordinates point state index)=1 := by
    have pair:=actualRestState_orthonormal point state state
    rw [if_pos rfl,actualRestState_full_prepared,inner_embed] at pair
    simpa only [coordinates_embed] using pair
  rw [unit,mul_neg_one,Stage10.ActionNormalization.phaseMomentum_source]
  push_cast
  rfl

end LowEnergy.PreparationVacuumElectromagneticIdentity
