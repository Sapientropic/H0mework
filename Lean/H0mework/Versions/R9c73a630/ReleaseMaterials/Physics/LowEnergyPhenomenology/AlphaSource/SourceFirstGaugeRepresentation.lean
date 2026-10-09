import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeField

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstPoleGaugeVertex
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaugeProjection.ConcreteBlockDiagonal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumLowerClassical PreparationVacuumCoefficientBudget
open PreparationVacuumSourceMatrixInverse PreparationCoordinates SourceQuantumScalarChart SourceQuantumNativeDimensions
open PreparationPhysicalNormalizedFullField PreparationPhysicalActualPhaseChargeReturn
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalNativePhaseChargeInventory
open PreparationPhysicalNativeOriginPhaseWard
open DiracExteriorMatterAction DiracCliffordRepresentation SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa
open StageNineExteriorMotherLieRepresentation StageNineP286GaugeConnectionVariation
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineResidualLimitScalarBalanceClosure
open Stage9C.Material.SpinPair YangMills.FullPairing
open scoped Matrix BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Quantum.InternalIndex:=Classical.decEq _

/-- The same original gauge connection, before any representation restriction. -/
def sourceFirstTemporalLie : NativeLie := sourceFirstGaugeConnection 0 0

private def temporalRaw : Fin 12→ℚ :=
  Pi.single 6 (6/11)+Pi.single 7 (-5/11)+Pi.single 10 (3/11)+Pi.single 11 (5/11)

theorem sourceFirstGauge_raw (k mu : Fin 4) :
    rawCoordinates (sourceFirstGaugeConnection k mu)=sourceFirstGaugeCoefficients k mu := by
  ext i
  simp [sourceFirstGaugeConnection,originalUnit,Pi.single_apply]

private theorem temporal_native :
    sourceFirstTemporalLie=rawCoordinates.symm (fun i=>(temporalRaw i:ℝ)) := by
  apply rawCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  change rawCoordinates (sourceFirstGaugeConnection 0 0)=_
  rw [sourceFirstGauge_raw]
  ext i
  simp only [sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,sourceFirstSpatialCoefficients,
    sourceFirstLongitudinalCoefficients,temporalRaw,Pi.add_apply,Pi.single_apply,ite_apply,Pi.zero_apply,
    Fin.ext_iff]
  norm_num
  split_ifs <;> norm_num

private def gaugeRational (k mu : Fin 4) : Fin 12→ℚ :=
  (if k=0 ∧ mu=0 then temporalRaw else 0)+
  (if k=1 ∧ mu=1 then Pi.single 6 (39/67)+Pi.single 7 (-34/67)+Pi.single 10 (15/67)+Pi.single 11 (25/67) else 0)+
  (if k=2 ∧ mu=2 then Pi.single 6 (39/67)+Pi.single 7 (-34/67)+Pi.single 10 (15/67)+Pi.single 11 (25/67) else 0)+
  (if k=3 ∧ mu=3 then Pi.single 6 (36/67)+Pi.single 7 (-31/67)+Pi.single 10 (15/67)+Pi.single 11 (25/67) else 0)+
  (if k=1 ∧ mu=3 then Pi.single 1 (-3/67) else 0)+
  (if k=2 ∧ mu=3 then Pi.single 0 (-3/67) else 0)

private theorem gauge_cast (k mu : Fin 4) (a : Fin 12) :
    (gaugeRational k mu a:ℝ)=sourceFirstGaugeCoefficients k mu a := by
  fin_cases k <;> fin_cases mu <;> fin_cases a <;>
    norm_num only [gaugeRational,temporalRaw,sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,
      sourceFirstSpatialCoefficients,sourceFirstLongitudinalCoefficients,Pi.add_apply,Pi.single_apply,
      ite_apply,Pi.zero_apply,Fin.ext_iff] <;> norm_num

private theorem gauge_native (k mu : Fin 4) :
    sourceFirstGaugeConnection k mu=rawCoordinates.symm (fun i=>(gaugeRational k mu i:ℝ)) := by
  apply rawCoordinates.injective
  rw [LinearEquiv.apply_symm_apply,sourceFirstGauge_raw]
  ext i
  exact (gauge_cast k mu i).symm

/-- The actual native connection returns its color/hyper block on the source doublet. -/
def sourceFirstGaugeDoublet (k mu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I*((sourceFirstGaugeCoefficients k mu 6:ℂ)+(sourceFirstGaugeCoefficients k mu 11:ℂ)),
       (sourceFirstGaugeCoefficients k mu 0:ℂ)+Complex.I*(sourceFirstGaugeCoefficients k mu 1:ℂ);
     -(sourceFirstGaugeCoefficients k mu 0:ℂ)+Complex.I*(sourceFirstGaugeCoefficients k mu 1:ℂ),
       Complex.I*((sourceFirstGaugeCoefficients k mu 7:ℂ)+(sourceFirstGaugeCoefficients k mu 11:ℂ))]

private theorem raw_doublet (x : Fin 12→ℚ) (row column : Fin 2) :
    ((p286CoordinateEquiv.symm (rawCoordinates.symm (fun i=>(x i:ℝ)))).1:Matrix (Fin 3) (Fin 3) ℂ)
      (row.castLE (by decide)) (column.castLE (by decide))+
      (if row=column then (p286CoordinateEquiv.symm (rawCoordinates.symm (fun i=>(x i:ℝ)))).2.2.val else 0)=
      (!![Complex.I*((x 6:ℂ)+(x 11:ℂ)),(x 0:ℂ)+Complex.I*(x 1:ℂ);
          -(x 0:ℂ)+Complex.I*(x 1:ℂ),Complex.I*((x 7:ℂ)+(x 11:ℂ))]) row column := by
  have colorMap (e : Fin 2) : smBlockIndexEquivFin7.symm (e.castLE (by decide))=
      Sum.inl (e.castLE (by decide)) := by fin_cases e <;> rfl
  have hyperMap : smBlockIndexEquivFin7.symm (5:Fin 7)=hyperPlusIndex := rfl
  have color:=rawMother_entry x (row.castLE (by decide)) (column.castLE (by decide))
  have hyper:=rawMother_entry x (5:Fin 7) (5:Fin 7)
  simp only [colorMap] at color
  simp only [hyperMap] at hyper
  change ((p286CoordinateEquiv.symm (rawCoordinates.symm (fun i=>(x i:ℝ)))).1:Matrix (Fin 3) (Fin 3) ℂ)
      (row.castLE (by decide)) (column.castLE (by decide))=_ at color
  change (p286CoordinateEquiv.symm (rawCoordinates.symm (fun i=>(x i:ℝ)))).2.2.val=_ at hyper
  rw [color,hyper]
  have reHyper : rawMotherReal x (5:Fin 7) 5=0 := rfl
  have imHyper : rawMotherImag x (5:Fin 7) 5=x 11 := rfl
  rw [reHyper,imHyper]
  fin_cases row <;> fin_cases column <;>
    norm_num [rawMotherReal,rawMotherImag,Matrix.cons_val,Fin.castLE]
  all_goals ring

theorem sourceFirstGaugeDoublet_generated (k mu : Fin 4) (row column : Fin 2) :
    ((p286CoordinateEquiv.symm (sourceFirstGaugeConnection k mu)).1:Matrix (Fin 3) (Fin 3) ℂ)
      (row.castLE (by decide)) (column.castLE (by decide))+
      (if row=column then (p286CoordinateEquiv.symm (sourceFirstGaugeConnection k mu)).2.2.val else 0)=
      sourceFirstGaugeDoublet k mu row column := by
  rw [gauge_native,raw_doublet]
  have cast (i : Fin 12) : (gaugeRational k mu i:ℂ)=(sourceFirstGaugeCoefficients k mu i:ℂ) := by
    exact_mod_cast gauge_cast k mu i
  simp only [cast,sourceFirstGaugeDoublet]

/-- The complete seven-dimensional native spectrum remains in the full exterior action. -/
def sourceFirstTemporalWeight : SU7MotherIndex→ℚ
  | .inl c=>if c=0 then 6/11 else if c=1 then -5/11 else -1/11
  | .inr (.inl w)=>if w=0 then 3/11 else -3/11
  | .inr (.inr (.inl _))=>5/11
  | .inr (.inr (.inr _))=>-5/11

def sourceFirstTemporalMother : SU7MotherLieMatrix :=
  p286LieBlockEmbed (p286CoordinateEquiv.symm sourceFirstTemporalLie)

private def temporalNumericWeight : Fin 7→ℚ := ![6/11,-5/11,-1/11,3/11,-3/11,5/11,-5/11]

private theorem temporal_numeric_real : ∀i j : Fin 7,rawMotherReal temporalRaw i j=0 := by decide +kernel

private theorem temporal_numeric_imag : ∀i j : Fin 7,
    rawMotherImag temporalRaw i j=if i=j then temporalNumericWeight i else 0 := by decide +kernel

private theorem temporal_numeric_weight : ∀i : Fin 7,
    sourceFirstTemporalWeight (smBlockIndexEquivFin7.symm i)=temporalNumericWeight i := by decide +kernel

theorem sourceFirstTemporalMother_matrix :
    sourceFirstTemporalMother.val=Matrix.diagonal (fun i=>(sourceFirstTemporalWeight i:ℂ)*Complex.I) := by
  ext i j
  obtain ⟨r,rfl⟩:=smBlockIndexEquivFin7.symm.surjective i
  obtain ⟨c,rfl⟩:=smBlockIndexEquivFin7.symm.surjective j
  rw [sourceFirstTemporalMother,temporal_native,rawMother_entry]
  by_cases same : r=c
  · subst c
    simp [temporal_numeric_real,temporal_numeric_imag,temporal_numeric_weight]
  · simp [temporal_numeric_real,temporal_numeric_imag,same]

private theorem temporal_fundamental (i : SU7MotherIndex) :
    fundamentalMotherLieAction sourceFirstTemporalMother (su7FundamentalBasis i)=
      ((sourceFirstTemporalWeight i:ℂ)*Complex.I) • su7FundamentalBasis i := by
  change sourceFirstTemporalMother.val*ᵥsu7FundamentalBasis i=_
  rw [sourceFirstTemporalMother_matrix]
  ext j
  rw [Matrix.mulVec_diagonal]
  simp [su7FundamentalBasis,Pi.single_apply]
  split_ifs <;> simp_all

def sourceFirstExteriorWeight {degree : ℕ} (i : ExteriorBasisIndex degree) : ℚ :=
  ∑j∈i.1,sourceFirstTemporalWeight j

/-- All exterior sectors are priced by the original native generator, not replaced by the actual-eight restriction. -/
theorem sourceFirstTemporal_exterior (degree : ℕ) (i : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree sourceFirstTemporalMother (su7ExteriorBasis degree i)=
      ((sourceFirstExteriorWeight i:ℂ)*Complex.I) • su7ExteriorBasis degree i := by
  classical
  rw [exteriorMotherLieAction_basis]
  have term (position : Fin degree) :
      (exteriorPower.ιMulti ℂ degree) (exteriorBasisLieActionInput degree sourceFirstTemporalMother i position)=
      ((sourceFirstTemporalWeight (exteriorPositionEquiv i position).1:ℂ)*Complex.I) • su7ExteriorBasis degree i := by
    rw [exteriorBasisLieActionTerm_eq_update]
    have eigen:=temporal_fundamental (exteriorPositionEquiv i position).1
    change fundamentalMotherLieAction sourceFirstTemporalMother (exteriorBasisInput degree i position)=
      ((sourceFirstTemporalWeight (exteriorPositionEquiv i position).1:ℂ)*Complex.I) • exteriorBasisInput degree i position at eigen
    rw [eigen,(exteriorPower.ιMulti ℂ degree).map_update_smul,Function.update_eq_self,exteriorBasisInput_wedge_eq_basis]
  change (∑position : Fin degree,(exteriorPower.ιMulti ℂ degree)
    (exteriorBasisLieActionInput degree sourceFirstTemporalMother i position))=_
  simp_rw [term]
  rw [←Finset.sum_smul,←Finset.sum_mul,←Rat.cast_sum]
  congr 3
  exact ((exteriorPositionEquiv i).sum_comp (fun j=>sourceFirstTemporalWeight j)).trans
    (Finset.sum_subtype i.1 (by simp) sourceFirstTemporalWeight).symm

def sourceFirstInternalWeight : Quantum.InternalIndex→ℚ
  | .inl i=>sourceFirstExteriorWeight i
  | .inr (.inl i)=>sourceFirstExteriorWeight i
  | .inr (.inr i)=>sourceFirstExteriorWeight i

def sourceFirstWholeWeight (i : Quantum.Index) : ℚ := sourceFirstInternalWeight i.2

def sourceFirstTemporalGenerator : Mother := diracExteriorMotherLieAction sourceFirstTemporalMother

theorem sourceFirstTemporal_basis (i : Quantum.Index) :
    sourceFirstTemporalGenerator (Quantum.wholeBasis i)=
      ((sourceFirstWholeWeight i:ℂ)*Complex.I) • Quantum.wholeBasis i := by
  rcases i with ⟨spin,i|i|i⟩
  all_goals
    funext s
    simp only [sourceFirstTemporalGenerator,diracExteriorMotherLieAction,internalMatterLinearAction,
      Quantum.wholeBasis,Pi.basis_apply,Pi.smul_apply]
    by_cases h:s=spin
    · subst s
      simp [Quantum.internalBasis,Module.Basis.prod_apply,exteriorSpinorMotherLieAction,
        sourceFirstTemporal_exterior,sourceFirstWholeWeight,sourceFirstInternalWeight]
    · simp [h,exteriorSpinorMotherLieAction]

/-- Full252 matrix identity, including all fractional weights. -/
theorem sourceFirstTemporal_matrix :
    Quantum.operatorMatrix sourceFirstTemporalGenerator=
      Matrix.diagonal (fun i=>(sourceFirstWholeWeight i:ℂ)*Complex.I) := by
  ext i j
  rw [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply]
  rw [sourceFirstTemporal_basis,map_smul,Module.Basis.repr_self]
  simp [Matrix.diagonal_apply,Finsupp.single_apply]
  split_ifs <;> simp_all

theorem sourceFirstTemporal_native :
    Quantum.operatorMatrix sourceFirstTemporalGenerator=GaussNativeMatter.nativePrimal sourceFirstTemporalLie := rfl

def sourceFirstEightIndex (i : Stage9DEF.Source.Index) : Quantum.Index :=
  ⟨i.1,Sum.inr (Sum.inl (sourceColorDoubletIndex i.2))⟩

theorem sourceFirstEightBasis (i : Stage9DEF.Source.Index) :
    Quantum.wholeBasis (sourceFirstEightIndex i)=Stage9DEF.Compatibility.embed (Pi.single i 1) := by
  rcases i with ⟨base,edge⟩
  fin_cases edge
  all_goals
    unfold Quantum.wholeBasis sourceFirstEightIndex
    rw [Pi.basis_apply]
    funext spin
    by_cases same : spin=base
    · rw [same]
      simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Pi.single_apply,Prod.mk.injEq]
    · simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Prod.mk.injEq,same]

private theorem eight_weight (i : Stage9DEF.Source.Index) :
    (sourceFirstWholeWeight (sourceFirstEightIndex i):ℂ)=(sourceActualPhaseCharge i.2:ℂ) := by
  have weight : ∀edge : Fin 2,sourceFirstExteriorWeight (sourceColorDoubletIndex edge)=
      (if edge=0 then 1 else 0:ℚ) := by decide +kernel
  change (sourceFirstExteriorWeight (sourceColorDoubletIndex i.2):ℂ)=_
  rw [weight]
  rcases i with ⟨spin,edge⟩
  fin_cases edge <;> norm_num [sourceActualPhaseCharge]

private theorem eight_phase_weight (i : Stage9DEF.Source.Index) :
    (sourceWholeWeight (sourceFirstEightIndex i):ℂ)= -(sourceActualPhaseCharge i.2:ℂ) := by
  have weight : ∀edge : Fin 2,sourcePhaseWeight (sourceColorDoubletIndex edge)=
      (if edge=0 then -1 else 0:ℚ) := by decide +kernel
  change (sourcePhaseWeight (sourceColorDoubletIndex i.2):ℂ)=_
  rw [weight]
  rcases i with ⟨spin,edge⟩
  fin_cases edge <;> norm_num [sourceActualPhaseCharge]

/-- The complete native difference is retained before the actual-eight restriction. -/
def sourceFirstTemporalDifference : Mother := sourceFirstTemporalGenerator+sourcePhaseGaugeGenerator

theorem sourceFirstTemporal_full :
    sourceFirstTemporalGenerator= -sourcePhaseGaugeGenerator+sourceFirstTemporalDifference := by
  unfold sourceFirstTemporalDifference
  abel

/-- The temporal energy generator carries the complete gauge difference before external restriction. -/
def sourceFirstTemporalCharge : Mother := (-Complex.I) • sourceFirstTemporalGenerator

theorem sourceFirstTemporalCharge_full :
    sourceFirstTemporalCharge=sourcePhaseGaugeCharge+(-Complex.I) • sourceFirstTemporalDifference := by
  unfold sourceFirstTemporalCharge sourcePhaseGaugeCharge sourceFirstTemporalDifference
  module

/-- The original phase-current generator retains its further full252 difference as well. -/
theorem sourceFirstTemporalCharge_phase :
    sourceFirstTemporalCharge=Complex.I • sourceNativeOriginGenerator+
      (-Complex.I) • (sourceFirstTemporalDifference+sourcePhaseGaugeDifference) := by
  rw [sourcePhaseGaugeGenerator_full]
  unfold sourceFirstTemporalCharge sourceFirstTemporalDifference
  module

/-- The actual embedding pays the temporal identity; it is not an equality of full252 generators. -/
theorem sourceFirstTemporalDifference_embed (values : Stage9DEF.Source.Index→ℂ) :
    sourceFirstTemporalDifference (Stage9DEF.Compatibility.embed values)=0 := by
  have zero : sourceFirstTemporalDifference.comp Stage9DEF.Compatibility.embed=0 := by
    apply (Pi.basisFun ℂ Stage9DEF.Source.Index).ext
    intro i
    rw [Pi.basisFun_apply]
    change sourceFirstTemporalGenerator (Stage9DEF.Compatibility.embed (Pi.single i 1))+
      sourcePhaseGaugeGenerator (Stage9DEF.Compatibility.embed (Pi.single i 1))=0
    rw [sourcePhaseGaugeGenerator_embed,←sourceFirstEightBasis,sourceFirstTemporal_basis,sourcePhaseGenerator_basis,
      eight_weight,eight_phase_weight]
    module
  exact congrArg (fun L : (Stage9DEF.Source.Index→ℂ)→ₗ[ℂ]DiracExteriorMatterCarrier=>L values) zero

theorem sourceFirstTemporal_embed (values : Stage9DEF.Source.Index→ℂ) :
    sourceFirstTemporalGenerator (Stage9DEF.Compatibility.embed values)=
      -sourcePhaseGaugeGenerator (Stage9DEF.Compatibility.embed values) := by
  have generated:=sourceFirstTemporalDifference_embed values
  change sourceFirstTemporalGenerator _+sourcePhaseGaugeGenerator _=0 at generated
  exact eq_neg_of_add_eq_zero_left generated

/-- The same original four columns acquire the source-generated unit/neutral temporal action. -/
theorem sourceFirstTemporal_actualColumn (side edge : Fin 2) :
    sourceFirstTemporalGenerator (sourceChargedRestriction side edge)=
      ((sourceActualPhaseCharge edge:ℂ)*Complex.I) • sourceChargedRestriction side edge := by
  have relation : sourceFirstTemporalGenerator (sourceChargedRestriction side edge)=
      -sourcePhaseGaugeGenerator (sourceChargedRestriction side edge) := by
    rw [sourceChargedRestriction_basis,map_smul,map_smul,sourceFirstTemporal_embed,smul_neg]
  rw [relation,sourcePhaseGauge_actualColumn]
  module

theorem sourceFirstTemporalCharge_actualColumn (side edge : Fin 2) :
    sourceFirstTemporalCharge (sourceChargedRestriction side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedRestriction side edge := by
  rw [sourceFirstTemporalCharge,LinearMap.smul_apply,sourceFirstTemporal_actualColumn,smul_smul]
  congr 1
  calc
    (-Complex.I)*((sourceActualPhaseCharge edge:ℂ)*Complex.I)=
      -(sourceActualPhaseCharge edge:ℂ)*(Complex.I*Complex.I) := by ring
    _=_ := by rw [Complex.I_mul_I];ring

end LowEnergy.PreparationPhysicalFirstPoleGaugeVertex
