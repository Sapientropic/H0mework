import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeSpinConnection
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceConstrainedCurrentResponse
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalCurrentWave

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open SourcePropagationNativeActionHessian PreparationVacuumOriginalGreenFeedback PreparationVacuumLowerClassical
open PreparationVacuumMixedFieldReturn Stage9DEF Stage9DEF.Compatibility
open Stage10 Stage9C.Material.SpinPair
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open DiracCliffordRepresentation SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionActionVariation PreparationVacuumCoefficientBudget
open scoped Matrix BigOperators InnerProductSpace

abbrev sourceMovingExchangeMomentum (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) : Fin 4→ℂ :=
  PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalFourier leftMomentum rightMomentum left right

private def movingGaugeNullSelect (term : SourceTerm) : Bool :=
  decide (9≤term.row.val ∧ term.row.val<57 ∧ 112≤term.column.val ∧ term.column.val<121)

private def movingGaugeNullLiteral : List SourceTerm := [
  ⟨9,113,⟨1,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨10,112,⟨1,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨15,114,⟨1,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨16,114,⟨1,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨21,113,⟨0,1,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨21,114,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨22,112,⟨0,1,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨27,113,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨27,114,⟨0,1,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨28,113,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨28,114,⟨0,1,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨33,113,⟨0,0,1,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨34,112,⟨0,0,1,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨34,114,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨39,112,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨39,114,⟨0,0,1,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨40,112,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨40,114,⟨0,0,1,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨45,112,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨45,113,⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨46,112,⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨46,113,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨51,114,⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨52,114,⟨0,0,0,1⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩]

private theorem movingGaugeNullLiteral_source :
    originalChangeTerms.filter movingGaugeNullSelect=movingGaugeNullLiteral := by
  decide +kernel

private theorem movingGaugeNull_entry (terms : List SourceTerm) (p : Fin 4→ℂ)
    (mu : Fin 4) (a : Fin 12) (constraint : Fin 9) :
    PreparationVacuumOriginalGreenFeedback.sourceMatrix (terms.filter movingGaugeNullSelect) p (gaugeSlot mu a) (sourceRestGaugeConstraintSlot constraint)=
      PreparationVacuumOriginalGreenFeedback.sourceMatrix terms p (gaugeSlot mu a) (sourceRestGaugeConstraintSlot constraint) := by
  induction terms with
  | nil=>rfl
  | cons term rest ih=>
    by_cases keep : movingGaugeNullSelect term=true
    · simp [keep,sourceMatrix_cons,ih]
    · have zero : term.matrix p (gaugeSlot mu a) (sourceRestGaugeConstraintSlot constraint)=0 := by
        by_cases row : term.row=gaugeSlot mu a
        · by_cases column : term.column=sourceRestGaugeConstraintSlot constraint
          · apply False.elim
            apply keep
            simp only [movingGaugeNullSelect,row,column,gaugeSlot,sourceRestGaugeConstraintSlot,Fin.val_mk,
              decide_eq_true_eq]
            omega
          · simp [SourceTerm.matrix,Matrix.single,column]
        · simp [SourceTerm.matrix,Matrix.single,row]
      simp [keep,sourceMatrix_cons,zero,ih]

theorem sourceMovingGaugeReadback_literal (p : Fin 4→ℂ) (constraint : Fin 9) (mu : Fin 4) (a : Fin 12) :
    originalReadback p (sourceRestGaugeConstraintSlot constraint) (gaugeSlot mu a)=
      PreparationVacuumOriginalGreenFeedback.sourceMatrix movingGaugeNullLiteral (-p) (gaugeSlot mu a) (sourceRestGaugeConstraintSlot constraint) := by
  change PreparationVacuumOriginalGreenFeedback.sourceMatrix originalChangeTerms (-p) (gaugeSlot mu a) (sourceRestGaugeConstraintSlot constraint)=_
  rw [←movingGaugeNull_entry originalChangeTerms (-p) mu a constraint,movingGaugeNullLiteral_source]

private def movingFourIndex (index : Source.Index) : Fin 4 :=
  ⟨2*(index.1.val%2)+index.2.val,by omega⟩

private def movingBlockMatrix (K : Fin 4→Fin 4→ℂ) : Matrix Source.Index Source.Index ℂ :=
  fun row column=>if row.1.val/2=column.1.val/2 then
    (if row.1.val<2 then -1 else 1)*K (movingFourIndex row) (movingFourIndex column) else 0

def sourceMovingFullHamiltonian (momentum : Fin 3→ℝ) : Matrix Source.Index Source.Index ℂ :=
  movingBlockMatrix (ChargedPreparation.SpatialSpectrum.sourceMatrix momentum)

private theorem movingBlock_hermitian (K : Fin 4→Fin 4→ℂ) (hermitian : Matrix.IsHermitian K) :
    (movingBlockMatrix K).IsHermitian := by
  ext row column
  have entry : star (K (movingFourIndex column) (movingFourIndex row))=
      K (movingFourIndex row) (movingFourIndex column) :=
    congrFun (congrFun hermitian (movingFourIndex row)) (movingFourIndex column)
  rcases row with ⟨spin,color⟩
  rcases column with ⟨other,colour⟩
  fin_cases spin <;> fin_cases other <;>
    simp [movingBlockMatrix,Matrix.conjTranspose_apply]
  all_goals convert entry using 1 <;> rfl

theorem sourceMovingFullHamiltonian_hermitian (momentum : Fin 3→ℝ) :
    (sourceMovingFullHamiltonian momentum).IsHermitian :=
  movingBlock_hermitian _ (sourceMovingHamiltonian_hermitian momentum)

private theorem movingBlock_upper (K : Fin 4→Fin 4→ℂ) (values : Fin 4→ℂ) :
    movingBlockMatrix K *ᵥ ChargedPreparation.CanonicalParticle.upperValues values=
      ChargedPreparation.CanonicalParticle.upperValues (-(K *ᵥ values)) := by
  funext row
  rcases row with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    norm_num [movingBlockMatrix,movingFourIndex,ChargedPreparation.CanonicalParticle.upperValues,
      Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals try dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast,cast_eq]
  all_goals first | rfl | ring!

private theorem movingBlock_lower (K : Fin 4→Fin 4→ℂ) (values : Fin 4→ℂ) :
    movingBlockMatrix K *ᵥ lowerValues values=lowerValues (K *ᵥ values) := by
  funext row
  rcases row with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    norm_num [movingBlockMatrix,movingFourIndex,lowerValues,
      Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals try dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast,cast_eq]
  all_goals first | rfl | ring!

theorem sourceMovingFullHamiltonian_eigen (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    sourceMovingFullHamiltonian momentum *ᵥ sourceMovingPoleValues momentum state=
      (sourceMovingPoleEnergy momentum state:ℂ) • sourceMovingPoleValues momentum state := by
  have eigen := (sourceMovingHamiltonian_hermitian momentum).mulVec_eigenvectorBasis state.2
  change ChargedPreparation.SpatialSpectrum.sourceMatrix momentum *ᵥ
    (fun i=>sourceMovingPoleBasis momentum state.2 i)=
      ((sourceMovingHamiltonian_hermitian momentum).eigenvalues state.2) •
        (fun i=>sourceMovingPoleBasis momentum state.2 i) at eigen
  have complexEigen : ChargedPreparation.SpatialSpectrum.sourceMatrix momentum *ᵥ
      (fun i=>sourceMovingPoleBasis momentum state.2 i)=
      ((sourceMovingHamiltonian_hermitian momentum).eigenvalues state.2:ℂ) •
        (fun i=>sourceMovingPoleBasis momentum state.2 i) := by
    rw [eigen]
    funext i
    simp only [Pi.smul_apply,Complex.real_smul,smul_eq_mul]
  by_cases upper : state.1=0
  · rw [sourceMovingFullHamiltonian,sourceMovingPoleValues,if_pos upper,movingBlock_upper,complexEigen]
    simp only [sourceMovingPoleEnergy,upper,if_true,neg_one_mul,Complex.ofReal_neg]
    ext row
    rcases row with ⟨spin,color⟩
    fin_cases spin <;> fin_cases color <;> simp [ChargedPreparation.CanonicalParticle.upperValues]
  · rw [sourceMovingFullHamiltonian,sourceMovingPoleValues,if_neg upper,movingBlock_lower,complexEigen,lowerValues_smul]
    simp [sourceMovingPoleEnergy,upper]

private theorem movingHermitian_pair (H : Matrix Source.Index Source.Index ℂ)
    (hermitian : H.IsHermitian) (u v : Source.Index→ℂ) (energy : ℝ)
    (eigen : H *ᵥ u=(energy:ℂ) • u) :
    star u ⬝ᵥ (H *ᵥ v)=(energy:ℂ)*(star u ⬝ᵥ v) := by
  have left := congrArg star eigen
  rw [Matrix.star_mulVec,hermitian] at left
  simp only [star_smul,Complex.star_def,Complex.conj_ofReal] at left
  rw [Matrix.dotProduct_mulVec,left]
  simp only [smul_dotProduct,smul_eq_mul]

private theorem movingWard_pair_zero (leftH rightH G : Matrix Source.Index Source.Index ℂ)
    (leftHermitian : leftH.IsHermitian) (u v : Source.Index→ℂ) (leftEnergy rightEnergy : ℝ)
    (leftEigen : leftH *ᵥ u=(leftEnergy:ℂ) • u) (rightEigen : rightH *ᵥ v=(rightEnergy:ℂ) • v) :
    star u ⬝ᵥ ((((rightEnergy-leftEnergy:ℝ):ℂ) • G+leftH*G-G*rightH) *ᵥ v)=0 := by
  rw [Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,
    ←Matrix.mulVec_mulVec,rightEigen,Matrix.mulVec_smul,dotProduct_sub,dotProduct_add,
    dotProduct_smul,dotProduct_smul,movingHermitian_pair leftH leftHermitian u _ leftEnergy leftEigen]
  push_cast
  ring

def sourceMovingGaugeMatrix (mu : Fin 4) (a : Fin 12) : Matrix Source.Index Source.Index ℂ :=
  sourceGaugeVertexMatrix mu (p286CoordinateEquiv.symm (originalUnit a))

private theorem movingGaugeMatrix_unit (mu : Fin 4) (a : Fin 12) (row column : Source.Index) :
    sourceMovingGaugeMatrix mu a row column=
      sourceGaugeDensityWeight mu*(-((diracGammaZero*diracGamma mu) row.1 column.1))*Complex.I*
        diracGaugeUnit a (row.2.castLE (by decide)) (column.2.castLE (by decide)) := by
  have equality : (row.2.castLE (by decide):Fin 3)=(column.2.castLE (by decide):Fin 3) ↔ row.2=column.2 := by
    constructor
    · intro same
      apply Fin.ext
      have value:=congrArg (fun x : Fin 3=>x.val) same
      exact value
    · intro same
      simp [same]
  rw [←diracGaugeUnit_source]
  simp only [sourceMovingGaugeMatrix,sourceGaugeVertexMatrix,diracTripletGauge,equality]

private def movingSpinMatrix (mu : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],
    !![0,-1,0,0;-1,0,0,0;0,0,0,1;0,0,1,0],
    !![0,Complex.I,0,0;-Complex.I,0,0,0;0,0,0,-Complex.I;0,0,Complex.I,0],
    !![-1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,-1]] mu

private theorem movingSpinMatrix_source (mu row column : Fin 4) :
    -((diracGammaZero*diracGamma mu) row column)=movingSpinMatrix mu row column := by
  fin_cases mu <;> fin_cases row <;> fin_cases column <;>
    norm_num [movingSpinMatrix,diracGammaZero,diracGamma,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four]

  all_goals dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast,cast_eq]
  all_goals norm_num

private def movingColorMatrix (a : Fin 12) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a=0 then !![0,Complex.I;-Complex.I,0]
  else if a=1 then !![0,-1;-1,0]
  else if a=6 then !![-1,0;0,0]
  else if a=7 then !![0,0;0,-1]
  else if a=11 then !![-1,0;0,-1]
  else 0

private theorem movingColorMatrix_source (a : Fin 12) (row column : Fin 2) :
    Complex.I*diracGaugeUnit a (row.castLE (by decide)) (column.castLE (by decide))=
      movingColorMatrix a row column := by
  fin_cases a <;> fin_cases row <;> fin_cases column <;>
    norm_num [movingColorMatrix,diracGaugeUnit,rawMotherReal,rawMotherImag,Pi.single_apply,Fin.ext_iff]
  all_goals dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.castLE]
  all_goals try simp only [eq_mpr_eq_cast,cast_eq]
  all_goals norm_num

private theorem movingGaugeMatrix_flat (mu : Fin 4) (a : Fin 12) (row column : Source.Index) :
    sourceMovingGaugeMatrix mu a row column=
      sourceGaugeDensityWeight mu*movingSpinMatrix mu row.1 column.1*movingColorMatrix a row.2 column.2 := by
  rw [movingGaugeMatrix_unit,movingSpinMatrix_source]
  calc
    _=sourceGaugeDensityWeight mu*movingSpinMatrix mu row.1 column.1*
      (Complex.I*diracGaugeUnit a (row.2.castLE (by decide)) (column.2.castLE (by decide))) := by ring
    _=_ := by rw [movingColorMatrix_source]

private def movingReadbackCoefficient (p : Fin 4→ℂ) (constraint : Fin 9) (mu : Fin 4) (a : Fin 12) : ℂ :=
  if constraint=0 then
    (if a=1 then p mu/2 else 0)+
      if mu=2 then (if a=6 then -3*(spinScale:ℂ)/10 else if a=7 then 3*(spinScale:ℂ)/10 else 0)
      else if mu=3 ∧ a=0 then 3*(spinScale:ℂ)/10 else 0
  else if constraint=1 then
    (if a=0 then p mu/2 else 0)+
      if mu=1 then (if a=6 then 3*(spinScale:ℂ)/10 else if a=7 then -3*(spinScale:ℂ)/10 else 0)
      else if mu=3 ∧ a=1 then -3*(spinScale:ℂ)/10 else 0
  else if constraint=2 then
    (if a=6 then p mu/2 else if a=7 then -p mu/2 else 0)+
      if mu=1 ∧ a=0 then -3*(spinScale:ℂ)/10
      else if mu=2 ∧ a=1 then 3*(spinScale:ℂ)/10 else 0
  else 0

private def movingLinearPower (index : Fin 5) : Powers :=
  ![⟨0,0,0,0⟩,⟨1,0,0,0⟩,⟨0,1,0,0⟩,⟨0,0,1,0⟩,⟨0,0,0,1⟩] index

private def movingLinearBasis (p : Fin 4→ℂ) (index : Fin 5) : ℂ :=
  ![1,p 0,p 1,p 2,p 3] index

private def movingReflection (index : Fin 5) : SourceCoefficient := if index=0 then 1 else -1

private def movingLinearExtract (terms : List SourceTerm) (row column : Fin 289) (index : Fin 5) : SourceCoefficient :=
  terms.foldr (fun term value=>if term.row=row ∧ term.column=column ∧ term.powers=movingLinearPower index then
    movingReflection index*term.coefficient+value else value) 0

private def movingExpectedCoefficient (constraint : Fin 9) (mu : Fin 4) (a : Fin 12) (index : Fin 5) : SourceCoefficient :=
  if index=0 then
    if constraint=0 then
      if mu=2 ∧ a=6 then ⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩
      else if mu=2 ∧ a=7 ∨ mu=3 ∧ a=0 then ⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩ else 0
    else if constraint=1 then
      if mu=1 ∧ a=6 then ⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩
      else if mu=1 ∧ a=7 ∨ mu=3 ∧ a=1 then ⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩ else 0
    else if constraint=2 then
      if mu=1 ∧ a=0 then ⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩
      else if mu=2 ∧ a=1 then ⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩ else 0
    else 0
  else if index.val=mu.val+1 then
    if constraint=0 ∧ a=1 ∨ constraint=1 ∧ a=0 ∨ constraint=2 ∧ a=6 then ⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩
    else if constraint=2 ∧ a=7 then ⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩ else 0
  else 0

private theorem movingExpectedCoefficient_code : ∀ constraint : Fin 9,∀ mu : Fin 4,∀ a : Fin 12,∀ index : Fin 5,
    movingLinearExtract movingGaugeNullLiteral (gaugeSlot mu a) (sourceRestGaugeConstraintSlot constraint) index=
      movingExpectedCoefficient constraint mu a index := by
  decide +kernel

private theorem movingLinearPower_injective : Function.Injective movingLinearPower := by decide +kernel

private theorem movingLinearPower_reflected (p : Fin 4→ℂ) (index : Fin 5) :
    (movingLinearPower index).value (-p)=coefficientValue (movingReflection index)*movingLinearBasis p index := by
  have one : coefficientValue (1:SourceCoefficient)=1 := coefficientMap.map_one
  have negative : coefficientValue (-1:SourceCoefficient)=-1 := by
    change coefficientMap (-1)=-1
    rw [map_neg,map_one]
  fin_cases index <;> norm_num [movingLinearPower,Powers.value,movingReflection,movingLinearBasis,one,negative]

private theorem movingLinearLiteral_supported : ∀ term ∈ movingGaugeNullLiteral,
    ∃ index : Fin 5,term.powers=movingLinearPower index := by decide +kernel

private theorem movingSingleLinear_eval (term : SourceTerm) (p : Fin 4→ℂ) (row column : Fin 289)
    (supported : ∃ index : Fin 5,term.powers=movingLinearPower index) :
    term.matrix (-p) row column=
      ∑ index : Fin 5,coefficientValue (if term.row=row ∧ term.column=column ∧ term.powers=movingLinearPower index then
        movingReflection index*term.coefficient else 0)*movingLinearBasis p index := by
  obtain ⟨index,powers⟩:=supported
  by_cases rows : term.row=row
  · by_cases columns : term.column=column
    · rw [Finset.sum_eq_single index]
      · simp only [rows,columns,powers,and_self,if_true,SourceTerm.matrix,Matrix.single_apply,
          coefficient_mul,movingLinearPower_reflected]
        ring
      · intro other _ distinct
        have off : term.powers≠movingLinearPower other := by
          rw [powers]
          intro equal
          exact distinct (movingLinearPower_injective equal).symm
        simp [off,coefficient_zero]
      · simp
    · simp [SourceTerm.matrix,Matrix.single,columns,coefficient_zero]
  · simp [SourceTerm.matrix,Matrix.single,rows,coefficient_zero]

private theorem movingLinearTerms_eval (terms : List SourceTerm)
    (supported : ∀ term ∈ terms,∃ index : Fin 5,term.powers=movingLinearPower index)
    (p : Fin 4→ℂ) (row column : Fin 289) :
    PreparationVacuumOriginalGreenFeedback.sourceMatrix terms (-p) row column=
      ∑ index : Fin 5,coefficientValue (movingLinearExtract terms row column index)*movingLinearBasis p index := by
  induction terms with
  | nil=>simp [PreparationVacuumOriginalGreenFeedback.sourceMatrix,movingLinearExtract,coefficient_zero]
  | cons term rest ih=>
    have head:=movingSingleLinear_eval term p row column (supported term (by simp))
    have tail:=ih (fun term member=>supported term (by simp [member]))
    have step (index : Fin 5) : movingLinearExtract (term::rest) row column index=
        (if term.row=row ∧ term.column=column ∧ term.powers=movingLinearPower index then
          movingReflection index*term.coefficient else 0)+movingLinearExtract rest row column index := by
      by_cases same : term.row=row ∧ term.column=column ∧ term.powers=movingLinearPower index <;>
        simp [movingLinearExtract,same]
    rw [sourceMatrix_cons,Matrix.add_apply,head,tail]
    simp only [step,coefficient_add,add_mul,Finset.sum_add_distrib]

private theorem movingExpectedCoefficient_eval (p : Fin 4→ℂ) (constraint : Fin 9) (mu : Fin 4) (a : Fin 12) :
    (∑ index : Fin 5,coefficientValue (movingExpectedCoefficient constraint mu a index)*movingLinearBasis p index)=
      movingReadbackCoefficient p constraint mu a := by
  rw [Fin.sum_univ_succ]
  simp only [movingExpectedCoefficient,Fin.val_zero,if_true,movingLinearBasis,Matrix.cons_val_zero,mul_one]
  simp only [Fin.sum_univ_four]
  fin_cases mu <;> norm_num [movingExpectedCoefficient,movingLinearBasis,coefficientValue,
    movingReadbackCoefficient,rootTwo,spinScale]
  all_goals split_ifs <;> first
    | omega
    | (norm_num [QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] <;>
       (try dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
        norm_num; ring!))

private theorem movingReadbackCoefficient_source (p : Fin 4→ℂ) (constraint : Fin 9) (mu : Fin 4) (a : Fin 12) :
    originalReadback p (sourceRestGaugeConstraintSlot constraint) (gaugeSlot mu a)=
      movingReadbackCoefficient p constraint mu a := by
  rw [sourceMovingGaugeReadback_literal,movingLinearTerms_eval movingGaugeNullLiteral movingLinearLiteral_supported]
  simp only [movingExpectedCoefficient_code]
  exact movingExpectedCoefficient_eval p constraint mu a

def sourceMovingConstraintMatrix (p : Fin 4→ℂ) (constraint : Fin 9) : Matrix Source.Index Source.Index ℂ :=
  ∑ mu : Fin 4,∑ a : Fin 12,movingReadbackCoefficient p constraint mu a • sourceMovingGaugeMatrix mu a

private def movingConstraintReduced (p : Fin 4→ℂ) (constraint : Fin 9) : Matrix Source.Index Source.Index ℂ :=
  if constraint=0 then
    (∑ mu : Fin 4,(p mu/2) • sourceMovingGaugeMatrix mu 1)+
      (3*(spinScale:ℂ)/10) • (sourceMovingGaugeMatrix 2 7-sourceMovingGaugeMatrix 2 6+sourceMovingGaugeMatrix 3 0)
  else if constraint=1 then
    (∑ mu : Fin 4,(p mu/2) • sourceMovingGaugeMatrix mu 0)+
      (3*(spinScale:ℂ)/10) • (sourceMovingGaugeMatrix 1 6-sourceMovingGaugeMatrix 1 7-sourceMovingGaugeMatrix 3 1)
  else if constraint=2 then
    (∑ mu : Fin 4,(p mu/2) • (sourceMovingGaugeMatrix mu 6-sourceMovingGaugeMatrix mu 7))+
      (3*(spinScale:ℂ)/10) • (sourceMovingGaugeMatrix 2 1-sourceMovingGaugeMatrix 1 0)
  else 0

private theorem movingSum6_7 {V : Type} [AddCommMonoid V] (f g : Fin 12→V) :
    (∑ x : Fin 12,if x=6 then f x else if x=7 then g x else 0)=f 6+g 7 := by
  have split (x : Fin 12) : (if x=6 then f x else if x=7 then g x else 0)=
      (if x=6 then f x else 0)+(if x=7 then g x else 0) := by
    by_cases first : x=6
    · subst x
      simp [show (6:Fin 12)≠7 by decide]
    · simp [first]
  simp_rw [split]
  simp [Finset.sum_add_distrib]

private theorem movingConstraint_abstract {V : Type} [AddCommGroup V] [Module ℂ V]
    (M : Fin 4→Fin 12→V) (p : Fin 4→ℂ) (constraint : Fin 9) :
    (∑ mu : Fin 4,∑ a : Fin 12,movingReadbackCoefficient p constraint mu a • M mu a)=
      if constraint=0 then
        (∑ mu : Fin 4,(p mu/2) • M mu 1)+(3*(spinScale:ℂ)/10) • (M 2 7-M 2 6+M 3 0)
      else if constraint=1 then
        (∑ mu : Fin 4,(p mu/2) • M mu 0)+(3*(spinScale:ℂ)/10) • (M 1 6-M 1 7-M 3 1)
      else if constraint=2 then
        (∑ mu : Fin 4,(p mu/2) • (M mu 6-M mu 7))+(3*(spinScale:ℂ)/10) • (M 2 1-M 1 0)
      else 0 := by
  fin_cases constraint <;>
    simp [movingReadbackCoefficient,Fin.sum_univ_four,add_smul,ite_smul,Finset.sum_add_distrib]
  all_goals simp_rw [movingSum6_7]
  all_goals module

private theorem movingConstraint_reduced (p : Fin 4→ℂ) (constraint : Fin 9) :
    sourceMovingConstraintMatrix p constraint=movingConstraintReduced p constraint :=
  movingConstraint_abstract sourceMovingGaugeMatrix p constraint

def sourceMovingWardGenerator (index : Fin 3) : Matrix Source.Index Source.Index ℂ :=
  ![sourceMovingGaugeMatrix 0 1,sourceMovingGaugeMatrix 0 0,
    sourceMovingGaugeMatrix 0 6-sourceMovingGaugeMatrix 0 7] index

private def movingFlatGauge (n : ℂ) (mu : Fin 4) (a : Fin 12) : Matrix Source.Index Source.Index ℂ :=
  fun row column=>(if mu=0 then 1 else n)*movingSpinMatrix mu row.1 column.1*movingColorMatrix a row.2 column.2

private theorem movingFlatGauge_source (mu : Fin 4) (a : Fin 12) :
    sourceMovingGaugeMatrix mu a=movingFlatGauge (lapse:ℂ) mu a := by
  ext row column
  rw [movingGaugeMatrix_flat]
  rfl

private def movingFourHamiltonian (n s : ℂ) (p : Fin 3→ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let z:=n*p 2
  let a:=n*(p 0-Complex.I*p 1)
  let b:=n*(p 0+Complex.I*p 1)
  let w:=3*n*s/5
  !![3*w+z,0,a,0;0,2*w+z,w,a;b,w,2*w-z,0;0,b,0,3*w-z]

private theorem movingFrequency_source : (frequency:ℂ)=3*(lapse:ℂ)*(spinScale:ℂ)/5 := by
  unfold frequency gaugeScale
  push_cast
  ring

private theorem movingFullHamiltonian_source (p : Fin 3→ℝ) :
    sourceMovingFullHamiltonian p=movingBlockMatrix
      (movingFourHamiltonian (lapse:ℂ) (spinScale:ℂ) (fun mu=>(p mu:ℂ))) := by
  unfold sourceMovingFullHamiltonian ChargedPreparation.SpatialSpectrum.sourceMatrix
  rw [movingFrequency_source]
  rfl

private theorem movingConstraint_Ward0 (leftMomentum rightMomentum : Fin 3→ℝ)
    (leftEnergy rightEnergy : ℝ) :
    sourceMovingConstraintMatrix
      ![-Complex.I*((rightEnergy-leftEnergy:ℝ):ℂ),
        Complex.I*((rightMomentum 0-leftMomentum 0:ℝ):ℂ),
        Complex.I*((rightMomentum 1-leftMomentum 1:ℝ):ℂ),
        Complex.I*((rightMomentum 2-leftMomentum 2:ℝ):ℂ)] 0=
      (-Complex.I/2) • (((rightEnergy-leftEnergy:ℝ):ℂ) • sourceMovingWardGenerator 0+
        sourceMovingFullHamiltonian leftMomentum*sourceMovingWardGenerator 0-
        sourceMovingWardGenerator 0*sourceMovingFullHamiltonian rightMomentum) := by
  rw [movingConstraint_reduced]
  simp only [movingConstraintReduced,sourceMovingWardGenerator,movingFlatGauge_source,movingFullHamiltonian_source]
  generalize (lapse:ℂ)=n
  generalize (spinScale:ℂ)=s
  ext row column
  rcases row with ⟨spin,color⟩
  rcases column with ⟨other,colour⟩
  fin_cases spin <;> fin_cases other <;> fin_cases color <;> fin_cases colour <;>
    norm_num [movingFourHamiltonian,movingBlockMatrix,movingFourIndex,
      Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_four,Fin.sum_univ_two,movingFlatGauge,movingSpinMatrix,movingColorMatrix,Fin.ext_iff]
  all_goals try dsimp only [Matrix.of_apply,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast,cast_eq]
  all_goals try dsimp only [Matrix.of_apply,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals ring_nf!

private theorem movingConstraint_Ward1 (leftMomentum rightMomentum : Fin 3→ℝ)
    (leftEnergy rightEnergy : ℝ) :
    sourceMovingConstraintMatrix
      ![-Complex.I*((rightEnergy-leftEnergy:ℝ):ℂ),
        Complex.I*((rightMomentum 0-leftMomentum 0:ℝ):ℂ),
        Complex.I*((rightMomentum 1-leftMomentum 1:ℝ):ℂ),
        Complex.I*((rightMomentum 2-leftMomentum 2:ℝ):ℂ)] 1=
      (-Complex.I/2) • (((rightEnergy-leftEnergy:ℝ):ℂ) • sourceMovingWardGenerator 1+
        sourceMovingFullHamiltonian leftMomentum*sourceMovingWardGenerator 1-
        sourceMovingWardGenerator 1*sourceMovingFullHamiltonian rightMomentum) := by
  rw [movingConstraint_reduced]
  simp only [movingConstraintReduced,sourceMovingWardGenerator,movingFlatGauge_source,movingFullHamiltonian_source]
  generalize (lapse:ℂ)=n
  generalize (spinScale:ℂ)=s
  ext row column
  rcases row with ⟨spin,color⟩
  rcases column with ⟨other,colour⟩
  fin_cases spin <;> fin_cases other <;> fin_cases color <;> fin_cases colour <;>
    norm_num [movingFourHamiltonian,movingBlockMatrix,movingFourIndex,
      Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_four,Fin.sum_univ_two,movingFlatGauge,movingSpinMatrix,movingColorMatrix,Fin.ext_iff]
  all_goals try dsimp only [Matrix.of_apply,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast,cast_eq]
  all_goals try dsimp only [Matrix.of_apply,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals ring_nf!
  all_goals try simp only [Complex.I_sq]
  all_goals ring!

private theorem movingConstraint_Ward2 (leftMomentum rightMomentum : Fin 3→ℝ)
    (leftEnergy rightEnergy : ℝ) :
    sourceMovingConstraintMatrix
      ![-Complex.I*((rightEnergy-leftEnergy:ℝ):ℂ),
        Complex.I*((rightMomentum 0-leftMomentum 0:ℝ):ℂ),
        Complex.I*((rightMomentum 1-leftMomentum 1:ℝ):ℂ),
        Complex.I*((rightMomentum 2-leftMomentum 2:ℝ):ℂ)] 2=
      (-Complex.I/2) • (((rightEnergy-leftEnergy:ℝ):ℂ) • sourceMovingWardGenerator 2+
        sourceMovingFullHamiltonian leftMomentum*sourceMovingWardGenerator 2-
        sourceMovingWardGenerator 2*sourceMovingFullHamiltonian rightMomentum) := by
  rw [movingConstraint_reduced]
  simp only [movingConstraintReduced,sourceMovingWardGenerator,movingFlatGauge_source,movingFullHamiltonian_source]
  generalize (lapse:ℂ)=n
  generalize (spinScale:ℂ)=s
  ext row column
  rcases row with ⟨spin,color⟩
  rcases column with ⟨other,colour⟩
  fin_cases spin <;> fin_cases other <;> fin_cases color <;> fin_cases colour <;>
    norm_num [movingFourHamiltonian,movingBlockMatrix,movingFourIndex,
      Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_four,Fin.sum_univ_two,movingFlatGauge,movingSpinMatrix,movingColorMatrix,Fin.ext_iff]
  all_goals try dsimp only [Matrix.of_apply,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals try simp only [eq_mpr_eq_cast,cast_eq]
  all_goals try dsimp only [Matrix.of_apply,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num [movingFlatGauge,movingSpinMatrix,movingColorMatrix,Matrix.of_apply,Fin.ext_iff]
  all_goals push_cast
  all_goals ring_nf!
  all_goals simp only [true_or,or_true]

private theorem movingConstraint_Ward_algebra (leftMomentum rightMomentum : Fin 3→ℝ)
    (leftEnergy rightEnergy : ℝ) (index : Fin 3) :
    sourceMovingConstraintMatrix
      ![-Complex.I*((rightEnergy-leftEnergy:ℝ):ℂ),
        Complex.I*((rightMomentum 0-leftMomentum 0:ℝ):ℂ),
        Complex.I*((rightMomentum 1-leftMomentum 1:ℝ):ℂ),
        Complex.I*((rightMomentum 2-leftMomentum 2:ℝ):ℂ)] ⟨index.val,by omega⟩=
      (-Complex.I/2) • (((rightEnergy-leftEnergy:ℝ):ℂ) • sourceMovingWardGenerator index+
        sourceMovingFullHamiltonian leftMomentum*sourceMovingWardGenerator index-
        sourceMovingWardGenerator index*sourceMovingFullHamiltonian rightMomentum) := by
  fin_cases index
  · exact movingConstraint_Ward0 leftMomentum rightMomentum leftEnergy rightEnergy
  · exact movingConstraint_Ward1 leftMomentum rightMomentum leftEnergy rightEnergy
  · exact movingConstraint_Ward2 leftMomentum rightMomentum leftEnergy rightEnergy

private theorem movingMatrixContraction_sum (M : Fin 4→Fin 12→Matrix Source.Index Source.Index ℂ)
    (c : Fin 4→Fin 12→ℂ) (u v : Source.Index→ℂ) :
    (∑ mu : Fin 4,∑ a : Fin 12,c mu a*(star u ⬝ᵥ (M mu a *ᵥ v)))=
      star u ⬝ᵥ ((∑ mu : Fin 4,∑ a : Fin 12,c mu a • M mu a) *ᵥ v) := by
  symm
  rw [Matrix.sum_mulVec,dotProduct_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [Matrix.sum_mulVec,dotProduct_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.smul_mulVec,dotProduct_smul]
  rfl

theorem sourceMovingConstraintTensor_matrix (p : Fin 4→ℂ) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) :
    sourceMovingConstraintTensor p leftMomentum rightMomentum left right constraint=
      (ActionNormalization.phaseMomentum:ℂ)*
        (star (sourceMovingPoleValues leftMomentum left) ⬝ᵥ
          (sourceMovingConstraintMatrix p constraint *ᵥ sourceMovingPoleValues rightMomentum right)) := by
  change (ActionNormalization.phaseMomentum:ℂ)*
      (∑ mu : Fin 4,∑ a : Fin 12,
        originalReadback p (sourceRestGaugeConstraintSlot constraint) (gaugeSlot mu a)*
          (star (sourceMovingPoleValues leftMomentum left) ⬝ᵥ
            (sourceMovingGaugeMatrix mu a *ᵥ sourceMovingPoleValues rightMomentum right)))=_
  simp only [movingReadbackCoefficient_source]
  congr 1
  exact movingMatrixContraction_sum sourceMovingGaugeMatrix (movingReadbackCoefficient p constraint) _ _

private theorem movingExchange_coordinates (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) : sourceMovingExchangeMomentum leftMomentum rightMomentum left right=
      ![-Complex.I*((sourceMovingPoleEnergy rightMomentum right-sourceMovingPoleEnergy leftMomentum left:ℝ):ℂ),
        Complex.I*((rightMomentum 0-leftMomentum 0:ℝ):ℂ),
        Complex.I*((rightMomentum 1-leftMomentum 1:ℝ):ℂ),
        Complex.I*((rightMomentum 2-leftMomentum 2:ℝ):ℂ)] := by
  funext mu
  fin_cases mu <;> rfl

theorem sourceMovingConstraintTensor_onShell (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) :
    sourceMovingConstraintTensor (sourceMovingExchangeMomentum leftMomentum rightMomentum left right)
      leftMomentum rightMomentum left right constraint=0 := by
  rw [sourceMovingConstraintTensor_matrix]
  by_cases active : constraint.val<3
  · let index : Fin 3:=⟨constraint.val,active⟩
    have same : (⟨index.val,by omega⟩:Fin 9)=constraint:=Fin.ext rfl
    rw [movingExchange_coordinates,←same,movingConstraint_Ward_algebra,
      Matrix.smul_mulVec,dotProduct_smul]
    rw [movingWard_pair_zero _ _ _ (sourceMovingFullHamiltonian_hermitian leftMomentum) _ _
      (sourceMovingPoleEnergy leftMomentum left) (sourceMovingPoleEnergy rightMomentum right)
      (sourceMovingFullHamiltonian_eigen leftMomentum left)
      (sourceMovingFullHamiltonian_eigen rightMomentum right)]
    simp
  · have inactive : sourceMovingConstraintMatrix
        (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) constraint=0 := by
      rw [movingConstraint_reduced]
      have a : constraint≠0:=by intro h; subst constraint; simp at active
      have b : constraint≠1:=by intro h; subst constraint; simp at active
      have c : constraint≠2:=by intro h; subst constraint; simp at active
      simp [movingConstraintReduced,a,b,c]
    simp [inactive]

private theorem movingCompatibility_fromNine (p : Fin 4→ℂ) (forcing : Fin 289→ℂ)
    (nine : ∀ constraint : Fin 9,
      sourceCompatibility p forcing (sourceRestGaugeConstraintSlot constraint)=0) :
    sourceCompatibility p forcing=0 := by
  funext field
  by_cases inside : 112 ≤ field.val ∧ field.val<121
  · let index : Fin 9:=⟨field.val-112,by omega⟩
    have same : sourceRestGaugeConstraintSlot index=field := by
      apply Fin.ext
      simp only [sourceRestGaugeConstraintSlot,Fin.val_mk]
      dsimp [index]
      omega
    simpa only [same,Pi.zero_apply] using nine index
  · unfold sourceCompatibility nullProjection projectionMatrix
    rw [Matrix.mulVec_diagonal]
    have flag : nullFlag field=false := by
      simp only [nullFlag,decide_eq_false_iff_not]
      exact inside
    simp only [flag,Bool.false_eq_true,if_false,zero_mul,Pi.zero_apply]

theorem actualMovingNativeForcing_compatible (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) :
    sourceCompatibility (sourceMovingExchangeMomentum leftMomentum rightMomentum left right)
      (actualMovingNativeForcing point leftMomentum rightMomentum left right)=0 := by
  apply movingCompatibility_fromNine
  intro constraint
  rw [actualMovingConstraintCurrent_generated,sourceMovingConstraintTensor_onShell]

theorem sourceMovingWaveForcing_compatible (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) :
    sourceCompatibility (sourceMovingExchangeMomentum leftMomentum rightMomentum left right)
      (sourceMovingWaveForcing point leftMomentum rightMomentum left right)=0 := by
  apply movingCompatibility_fromNine
  intro constraint
  rw [sourceMovingWaveForcing_constraints,sourceMovingConstraintTensor_onShell,mul_zero]

theorem sourceMovingWaveField_native (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex)
    (regular : sourceMovingExchangeMomentum leftMomentum rightMomentum left right∈regularSource) :
    nativeFourierHessian nativeHessian (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) *ᵥ
      PreparationVacuumOriginalGreenFeedback.sourceField
        ⟨sourceMovingExchangeMomentum leftMomentum rightMomentum left right,regular⟩
        (sourceMovingWaveForcing point leftMomentum rightMomentum left right)=
      sourceMovingWaveForcing point leftMomentum rightMomentum left right := by
  have generated:=nativeAction_sourceField
    (⟨sourceMovingExchangeMomentum leftMomentum rightMomentum left right,regular⟩:regularSource)
    (sourceMovingWaveForcing point leftMomentum rightMomentum left right)
  simpa only [sourceMovingWaveForcing_compatible,Matrix.mulVec_zero,sub_zero] using generated

theorem sourceMovingWaveField_native36 (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex)
    (regular : sourceMovingExchangeMomentum leftMomentum rightMomentum left right∈regularSource) :
    PreparationVacuumFieldConstraintResponse.originalReader36 (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) *ᵥ
      (nativeFourierHessian nativeHessian (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) *ᵥ
        PreparationVacuumOriginalGreenFeedback.sourceField
          ⟨sourceMovingExchangeMomentum leftMomentum rightMomentum left right,regular⟩
          (sourceMovingWaveForcing point leftMomentum rightMomentum left right))=
      PreparationVacuumFieldConstraintResponse.originalReader36 (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) *ᵥ
        sourceMovingWaveForcing point leftMomentum rightMomentum left right := by
  rw [sourceMovingWaveField_native]

end LowEnergy.PreparationVacuumElectromagneticIdentity
