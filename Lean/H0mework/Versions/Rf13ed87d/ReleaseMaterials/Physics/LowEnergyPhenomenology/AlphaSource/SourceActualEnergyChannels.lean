import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFieldEnergyAxes
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyChannelFrame
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNormalizedEnergyJet
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelTwoSpinPort
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedPropagatingRead
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.BosonCausal.Metric
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Lapse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNormalizedFullField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse PreparationVacuumMixedControl
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumChargedLongRangeRead
open PreparationVacuumNativeSlowCoupling PreparationVacuumSourceFieldFamily
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumNonlinearFieldCurve PreparationVacuumNativeFieldInjection
open PreparationVacuumPhysicalQuantumLockedCharge PreparationPhysicalActionUnits
open PreparationVacuumCausalPoleResponse PreparationVacuumActualFieldQuantization
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedSpatialResponse
open PreparationVacuumFullSlowFieldResponse PreparationVacuumChargedPacketGreen
open PreparationVacuumQuantumSlowResidue
open PreparationVacuumGaugeSourceInjection GaussQuantumMultiplier GaussFockLift
open GaussCoreHilbert SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open CanonicalGradedCharge GaussHistoryHilbert PreparationVacuumMovingPoleGaussReturn
open FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open Stage10.CanonicalMatter PreparationVacuumElectromagneticIdentity
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _

/-- These are the four actual charged source columns, not a choice inside a degenerate eigenspace. -/
def sourceChargedBasisIndex (side edge : Fin 2) : Source.Index :=
  (⟨2*side.val+edge.val,by omega⟩,edge)

theorem sourceChargedRestValues_basis (side edge : Fin 2) :
    sourceRestStateValues (sourceChargedRestIndex side edge)=
      (spinScale:ℂ) • Pi.single (sourceChargedBasisIndex side edge) 1 := by
  ext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases edge <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceChargedRestIndex,sourceChargedBasisIndex,sourceRestStateValues,
      sourceRestStateCoefficients,Stage10.ChargedPreparation.CanonicalParticle.upperValues,
      Stage10.ChargedPreparation.SpatialSpectrum.lowerValues,Pi.single_apply,Prod.mk.injEq,
      Matrix.of_apply,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals rfl

theorem sourceChargedRestriction_basis (side edge : Fin 2) :
    sourceChargedRestriction side edge=
      (actualRestAmplitude 0*(spinScale:ℂ)) •
        Stage9DEF.Compatibility.embed (Pi.single (sourceChargedBasisIndex side edge) 1) := by
  rw [sourceChargedRestriction,actualRestState_source,actualRestStateCoordinates,
    sourceChargedRestValues_basis,smul_smul,map_smul]

def sourceChargedQuantumIndex (side edge : Fin 2) : Quantum.Index :=
  ⟨(sourceChargedBasisIndex side edge).1,Sum.inr (Sum.inl (sourceColorDoubletIndex edge))⟩

private theorem sourceChargedWholeBasis (side edge : Fin 2) :
    Quantum.wholeBasis (sourceChargedQuantumIndex side edge)=
      Stage9DEF.Compatibility.embed (Pi.single (sourceChargedBasisIndex side edge) 1) := by
  unfold Quantum.wholeBasis sourceChargedQuantumIndex
  rw [Pi.basis_apply]
  funext spin
  by_cases same : spin=(sourceChargedBasisIndex side edge).1
  · rw [same]
    fin_cases edge <;>
      simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Pi.single_apply,Prod.mk.injEq,
        sourceChargedBasisIndex]
  · fin_cases edge <;>
      simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Pi.single_apply,Prod.mk.injEq,
        sourceChargedBasisIndex] at same ⊢

theorem sourceChargedCoordinates_basis (side edge : Fin 2) :
    sourceChargedCoordinates side edge=(actualRestAmplitude 0*(spinScale:ℂ)) •
      Pi.single (Sum.inl (sourceChargedQuantumIndex side edge)) 1 := by
  rw [sourceChargedCoordinates,sourceChargedRestriction_basis,←sourceChargedWholeBasis,map_smul]
  ext index
  cases index with
  | inl j=>simp [Quantum.coordinates,Pi.single_apply,Finsupp.single_apply,eq_comm]
  | inr j=>simp

/-- The complete regular/contact matrix keeps the original native inverse and current support. -/
theorem sourceEnergyRegularMatrix_original :
    sourceRegularMatrix 0=originalChange 0*(contactInverse 0+fullInverse*activeProjection)*
      (originalChange 0).transpose := by
  have green : unrestrictedGreen 0=fullInverse:=complementGreen_origin
  rw [sourceRegularMatrix,green]
  unfold originalReadback
  simp only [neg_zero]
  noncomm_ring

/-- The actual unit Gauss preparation returns the complete one-particle matrix pairing. -/
theorem sourceChargedEnergyRead_matrix (epsilon : ℝ) (precision : 0<epsilon)
    (A : FullMatrix) (side edge other opposite : Fin 2) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
      (lift (quantized A) (sourceChargedGaussPrepared epsilon precision other opposite))=
        ∑j : Mode,star (sourceChargedCoordinates side edge j)*
          (A*ᵥsourceChargedCoordinates other opposite) j := by
  have base : inner ℂ (sourcePoleBase epsilon precision) (sourcePoleBase epsilon precision)=1 := by
    rw [inner_self_eq_norm_sq_to_K,sourcePoleBase_unit]
    norm_num
  rw [←GaussHalfDensity.fockHalfDensityEquiv.inner_map_map,PiLp.inner_apply]
  simp only [sourceChargedGaussPrepared_coordinates,sourceChargedGauss_action_coordinates,
    inner_smul_left,inner_smul_right,base,mul_one]
  change inner ℂ (sourceChargedFiber side edge) (quantized A (sourceChargedFiber other opposite))=_
  rw [sourceChargedFiber,sourceChargedFiber,quantized_oneParticle,SourceQuantumFockGauge.fiber_pairing]
  simp only [oneParticleFiber,LinearEquiv.apply_symm_apply]
  exact QuantizationCheck.Fermion.pairing_oneParticle _ _

theorem sourceChargedCommonPhase_unit :
    star (actualRestAmplitude 0*(spinScale:ℂ))*(actualRestAmplitude 0*(spinScale:ℂ))=1 := by
  have base : inner ℂ (sourcePoleBase 1 (by norm_num)) (sourcePoleBase 1 (by norm_num))=1 := by
    rw [inner_self_eq_norm_sq_to_K,sourcePoleBase_unit]
    norm_num
  have gram:=sourceChargedGauss_gram 1 (by norm_num) 0 0 0 0
  rw [←GaussHalfDensity.fockHalfDensityEquiv.inner_map_map,PiLp.inner_apply] at gram
  simp only [sourceChargedGaussPrepared_coordinates,inner_smul_left,inner_smul_right,
    base,mul_one,ite_true] at gram
  change inner ℂ (sourceChargedFiber 0 0) (sourceChargedFiber 0 0)=1 at gram
  rw [SourceQuantumFockGauge.fiber_pairing] at gram
  simp only [sourceChargedFiber,oneParticleFiber,LinearEquiv.apply_symm_apply,
    QuantizationCheck.Fermion.pairing_oneParticle,sourceChargedCoordinates_basis] at gram
  simpa [Pi.single_apply,Pi.smul_apply,smul_eq_mul] using gram

/-- The full CAR/Gauss read returns the actual two independent source columns with their source-generated normalization. -/
theorem sourceChargedEnergyRead_entry (epsilon : ℝ) (precision : 0<epsilon)
    (A : FullMatrix) (side edge other opposite : Fin 2) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
      (lift (quantized A) (sourceChargedGaussPrepared epsilon precision other opposite))=
        A (Sum.inl (sourceChargedQuantumIndex side edge))
          (Sum.inl (sourceChargedQuantumIndex other opposite)) := by
  rw [sourceChargedEnergyRead_matrix]
  simp only [sourceChargedCoordinates_basis,Matrix.mulVec_smul,Matrix.mulVec_single_one,
    Pi.smul_apply,smul_eq_mul,star_mul,Pi.single_apply,apply_ite,star_one,star_zero]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Matrix.col_apply]
  rw [←star_mul,←mul_assoc,sourceChargedCommonPhase_unit,one_mul]

/-- Complexification uses the real source energy probes; it never identifies the two matter legs. -/
def sourceFullEnergyMatrix (p : PhysicalMomentum) (s : ActionState) (V : Fin 289→ℂ) : FullMatrix :=
  ∑j : Fin 289,V j • sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit j))

theorem sourceFullEnergyMatrix_real (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (f : Field289) :
    sourceFullEnergyMatrix p s (fun j=>(f j:ℂ))=
      sourceNormalizedEnergySymbol p s (fieldDirection f) := by
  unfold sourceFullEnergyMatrix
  simp only [sourceNormalizedEnergySymbol_original p s _ valid]
  conv_rhs=>rw [symbolFirst,fieldDirection_coordinates f,map_sum]
  simp only [symbolFirst,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rfl

private theorem energyMatrix_zero (p : PhysicalMomentum) (s : ActionState) :
    sourceFullEnergyMatrix p s 0=0 := by
  simp [sourceFullEnergyMatrix]

private theorem energyMatrix_add (p : PhysicalMomentum) (s : ActionState) (V W : Fin 289→ℂ) :
    sourceFullEnergyMatrix p s (V+W)=sourceFullEnergyMatrix p s V+sourceFullEnergyMatrix p s W := by
  simp only [sourceFullEnergyMatrix,Pi.add_apply,add_smul,Finset.sum_add_distrib]

private theorem energyMatrix_single (p : PhysicalMomentum) (s : ActionState)
    (j : Fin 289) (c : ℂ) :
    sourceFullEnergyMatrix p s (Pi.single j c)=
      c • sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit j)) := by
  simp [sourceFullEnergyMatrix,Pi.single_apply]

private theorem energyMatrix_single_column (p : PhysicalMomentum) (s : ActionState)
    (row column target : Fin 289) (c : ℂ) :
    sourceFullEnergyMatrix p s (fun j=>Matrix.single row column c j target)=
      if column=target then c • sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit row)) else 0 := by
  by_cases h : column=target
  · subst target
    have field : (fun j=>Matrix.single row column c j column)=Pi.single row c := by
      funext j
      simp [Matrix.single_apply,Pi.single_apply,eq_comm]
    rw [field,energyMatrix_single,if_pos rfl]
  · have field : (fun j=>Matrix.single row column c j target)=0 := by
      funext j
      simp [h]
    rw [field,energyMatrix_zero,if_neg h]

private theorem energyMatrix_sourceTerms (p : PhysicalMomentum) (s : ActionState)
    (terms : List SourceTerm) (v : Fin 4→ℂ) (column : Fin 289) :
    sourceFullEnergyMatrix p s (fun j=>sourceMatrix terms v j column)=
      terms.foldr (fun t A=>if t.column=column then
        (coefficientValue t.coefficient*t.powers.value v) •
          sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit t.row))+A else A) 0 := by
  induction terms with
  | nil=>exact energyMatrix_zero p s
  | cons t rest ih=>
    have field : (fun j=>sourceMatrix (t::rest) v j column)=
        (fun j=>t.matrix v j column)+(fun j=>sourceMatrix rest v j column) := by
      funext j
      rw [sourceMatrix_cons]
      rfl
    rw [field,energyMatrix_add,ih]
    unfold SourceTerm.matrix
    rw [energyMatrix_single_column]
    simp only [List.foldr_cons]
    split_ifs <;> simp only [zero_add]

private theorem energyMatrix_smul (p : PhysicalMomentum) (s : ActionState)
    (c : ℂ) (V : Fin 289→ℂ) :
    sourceFullEnergyMatrix p s (c • V)=c • sourceFullEnergyMatrix p s V := by
  simp only [sourceFullEnergyMatrix,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]

private theorem energyMatrix_sum (p : PhysicalMomentum) (s : ActionState) (V : Fin 3→Fin 289→ℂ) :
    sourceFullEnergyMatrix p s (∑i : Fin 3,V i)=∑i : Fin 3,sourceFullEnergyMatrix p s (V i) := by
  simp only [sourceFullEnergyMatrix,Finset.sum_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Each coefficient is the actual normalized energy matrix of its original field coordinate. -/
def sourceLiteralEnergyWeight (p : PhysicalMomentum) (s : ActionState) (v : Fin 4→ℂ)
    (i : Fin 3) : FullMatrix :=
  (sourceEnergyChannelTerms.filter (fun t=>decide (t.column.val=i.val))).foldr
    (fun t A=> (coefficientValue t.coefficient*t.powers.value v) •
      sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit t.row))+A) 0

theorem sourceLiteralEnergyWeight_generated (p : PhysicalMomentum) (s : ActionState)
    (v : Fin 4→ℂ) (i : Fin 3) :
    sourceLiteralEnergyWeight p s v i=sourceFullEnergyMatrix p s
      (fun j=>sourceChargedNativeFrameJet v j ⟨i.val,by omega⟩) := by
  have column : (fun j=>sourceMatrix sourceEnergyChannelTerms v j ⟨i.val,by omega⟩)=
      (fun j=>sourceChargedNativeFrameJet v j ⟨i.val,by omega⟩) := by
    funext j
    rw [sourceEnergyChannelMatrix_entry]
  rw [←column,energyMatrix_sourceTerms]
  unfold sourceLiteralEnergyWeight
  have fold (terms : List SourceTerm) :
      (terms.filter (fun t=>decide (t.column.val=i.val))).foldr
        (fun t A=>(coefficientValue t.coefficient*t.powers.value v) •
          sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit t.row))+A) 0=
      terms.foldr (fun t A=>if t.column=(⟨i.val,by omega⟩:Fin 289) then
        (coefficientValue t.coefficient*t.powers.value v) •
          sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit t.row))+A else A) 0 := by
    induction terms with
    | nil=>rfl
    | cons t rest ih=>
      by_cases same : t.column.val=i.val
      · simp [same,Fin.ext_iff,ih]
      · simp [same,Fin.ext_iff,ih]
  exact fold sourceEnergyChannelTerms

theorem sourceLiteralEnergyWeight_axis (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (i : Fin 3) (k : Fin 4) :
    sourceLiteralEnergyWeight p s (Pi.single k 1) i=
      sourceNormalizedEnergySymbol p s (fieldDirection (sourceEnergyAxisField i k)) := by
  rw [sourceLiteralEnergyWeight_generated]
  have column : (fun j=>sourceChargedNativeFrameJet (Pi.single k 1) j ⟨i.val,by omega⟩)=
      (fun j=>(sourceEnergyAxisField i k j:ℂ)) := by
    rw [sourceEnergyAxisField_cast]
    funext j
    rw [sourceEnergyChannelMatrix_entry]
  rw [column,sourceFullEnergyMatrix_real p s valid]

private theorem sourcePower_linear (a : Powers) (degree : a.total=1) (v : Fin 4→ℂ) :
    a.value v=∑k : Fin 4,v k*a.value (Pi.single k 1) := by
  have cases :
      (a.temporal=1 ∧ a.first=0 ∧ a.second=0 ∧ a.third=0) ∨
      (a.temporal=0 ∧ a.first=1 ∧ a.second=0 ∧ a.third=0) ∨
      (a.temporal=0 ∧ a.first=0 ∧ a.second=1 ∧ a.third=0) ∨
      (a.temporal=0 ∧ a.first=0 ∧ a.second=0 ∧ a.third=1) := by
    unfold Powers.total at degree
    omega
  rcases cases with h|h|h|h
  all_goals rcases h with ⟨h0,h1,h2,h3⟩
  all_goals simp [Powers.value,h0,h1,h2,h3,Pi.single_apply]

/-- Original real-axis energy responses are complexified linearly, without conjugating field momentum on the independent dual block. -/
theorem sourceLiteralEnergyWeight_axes (p : PhysicalMomentum) (s : ActionState)
    (v : Fin 4→ℂ) (i : Fin 3) :
    sourceLiteralEnergyWeight p s v i=
      ∑k : Fin 4,v k • sourceLiteralEnergyWeight p s (Pi.single k 1) i := by
  have sourceDegrees : sourceEnergyChannelTerms.all (fun t=>decide (t.powers.total=1))=true := by
    decide +kernel
  have fold (terms : List SourceTerm) (degrees : ∀t∈terms,t.powers.total=1) :
      terms.foldr (fun t A=>(coefficientValue t.coefficient*t.powers.value v) •
        sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit t.row))+A) 0=
      ∑k : Fin 4,v k • terms.foldr (fun t A=>(coefficientValue t.coefficient*t.powers.value (Pi.single k 1)) •
        sourceNormalizedEnergySymbol p s (fieldDirection (fieldUnit t.row))+A) 0 := by
    induction terms with
    | nil=>simp
    | cons t rest ih=>
      have first:=degrees t List.mem_cons_self
      have remaining:=ih (fun a ha=>degrees a (List.mem_cons_of_mem _ ha))
      simp only [List.foldr_cons,smul_add,Finset.sum_add_distrib]
      rw [remaining,sourcePower_linear t.powers first,Finset.mul_sum,Finset.sum_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_smul]
      congr 1
      ring
  unfold sourceLiteralEnergyWeight
  apply fold
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp sourceDegrees t (List.mem_of_mem_filter ht))

/-- Whole 504-CAR response keeps the real-axis branch order before complex field-momentum continuation. -/
theorem sourceLiteralChannelTwoEnergy (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 2=
      ∑k : Fin 4,v k • SourceRealScalarFock.branches (spinCoordinates
        ((Complex.I*((Pi.single k (1:ℝ):Fin 4→ℝ) 0:ℂ)) • (1:DiracMatrix)-
          (Complex.I*(Real.sqrt 30:ℂ)/5) •
            (∑j : Fin 3,((Pi.single k (1:ℝ):Fin 4→ℝ) j.succ:ℂ) •
              (diracGammaZero*diracGamma j.succ)))) := by
  rw [sourceLiteralEnergyWeight_axes]
  apply Finset.sum_congr rfl
  intro k _
  rw [sourceLiteralEnergyWeight_axis p _
    (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint),sourceChannelTwoAxisEnergy]

private theorem five_single (i : Fin 3) :
    fiveVector (Pi.single (⟨i.val,by omega⟩:Fin 5) (1:ℂ))=
      Pi.single (⟨i.val,by omega⟩:Fin 289) (1:ℂ) := by
  funext j
  by_cases inside : j.val<5
  · simp [fiveVector,inside,Pi.single_apply,Fin.ext_iff]
  · have different : i.val≠j.val:=by omega
    simp [fiveVector,inside,Fin.ext_iff,different]

theorem sourceLiteralEnergyWeight_channel (p : PhysicalMomentum) (s : ActionState)
    (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3) :
    sourceLiteralEnergyWeight p s (fixedMomentum n zeta) i=
      sourceFullEnergyMatrix p s (sourceChargedChannel n zeta i) := by
  rw [sourceChargedChannel,five_single,Matrix.mulVec_single_one,
    sourceLiteralEnergyWeight_generated]
  rfl

/-- The original complete second field enters its normalized energy matrix with all three actual denominators and regular current. -/
theorem sourceFullEnergyMatrix_channels (p : PhysicalMomentum) (s : ActionState)
    (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (left right : RestStateIndex) :
    sourceFullEnergyMatrix p s (sourceChargedSecondField q n zeta.val left right)=
      (∑i : Fin 3,((sourceChargedDenominator n zeta.val i)⁻¹*
        sourceSlowRead (sourceActualNativeResidue q n zeta.val left right) ⟨i.val,by omega⟩) •
          sourceLiteralEnergyWeight p s (fixedMomentum n zeta.val) i)+
      sourceFullEnergyMatrix p s (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n zeta.val left right) := by
  rw [sourceChargedSecondField_channels q n zeta,energyMatrix_add,energyMatrix_sum]
  simp only [energyMatrix_smul,←sourceLiteralEnergyWeight_channel]

/-- Both external states are the original independent charged preparations. -/
def sourceFullEnergyRead (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (s : ActionState) (side edge other opposite : Fin 2) (V : Fin 289→ℂ) : ℂ :=
  inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
    (lift (quantized (sourceFullEnergyMatrix p s V))
      (sourceChargedGaussPrepared epsilon precision other opposite))

def sourceLiteralEnergyCoefficient (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (s : ActionState) (v : Fin 4→ℂ) (i : Fin 3) (side edge other opposite : Fin 2) : ℂ :=
  inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
    (lift (quantized (sourceLiteralEnergyWeight p s v i))
      (sourceChargedGaussPrepared epsilon precision other opposite))

theorem sourceFullEnergyRead_coefficients (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (side edge other opposite : Fin 2)
    (V : Fin 289→ℂ) :
    sourceFullEnergyRead epsilon precision p s side edge other opposite V=
      ∑j : Mode,star (sourceChargedCoordinates side edge j)*
        (sourceFullEnergyMatrix p s V*ᵥsourceChargedCoordinates other opposite) j :=
  sourceChargedEnergyRead_matrix epsilon precision _ side edge other opposite

/-- The actual two-leg energy read retains all three source denominators and the entire regular current. -/
theorem sourceFullEnergyRead_channels (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (side edge other opposite : Fin 2)
    (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (left right : RestStateIndex) :
    sourceFullEnergyRead epsilon precision p s side edge other opposite
      (sourceChargedSecondField q n zeta.val left right)=
      (∑i : Fin 3,((sourceChargedDenominator n zeta.val i)⁻¹*
        sourceSlowRead (sourceActualNativeResidue q n zeta.val left right) ⟨i.val,by omega⟩)*
          sourceLiteralEnergyCoefficient epsilon precision p s (fixedMomentum n zeta.val) i
            side edge other opposite)+
      sourceFullEnergyRead epsilon precision p s side edge other opposite
        (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n zeta.val left right) := by
  simp only [sourceFullEnergyRead,sourceLiteralEnergyCoefficient,sourceChargedEnergyRead_entry]
  rw [sourceFullEnergyMatrix_channels]
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]

/-- The finite coefficients consume the actual full source inverse-variation formula. -/
theorem sourceFullEnergyMatrix_generated (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (V : Fin 289→ℂ) :
    sourceFullEnergyMatrix p s V=
      ∑j : Fin 289,V j • fourierLinear p (sourceHamiltonianJetMatrix s (fieldDirection (fieldUnit j))) := by
  unfold sourceFullEnergyMatrix
  simp only [sourceNormalizedEnergySymbol_matrix p s _ valid]

end LowEnergy.PreparationPhysicalNormalizedFullField
