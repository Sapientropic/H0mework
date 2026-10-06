import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationActionFieldLift

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumActionFieldLift
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussFockWeights GaussQuantumMultiplier
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionDecomposition PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearFieldCurve
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open CanonicalGradedLocalCurrent Filter Set
abbrev Localizer:=CanonicalGradedLocalCurrent.Localizer
abbrev FiberMap:=CanonicalGradedLocalCurrent.FiberMap
open GaussUnitaryHistory (Index)
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators Distributions InnerProductSpace Interval
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FieldOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def direction (f : Field289) (remaining : Bool) (z : SourceCoordinateSlice) : ActionState :=
  if remaining then complement f z else sliceState (fieldVector f z)

theorem direction_sum (f : Field289) (z : SourceCoordinateSlice) :
    direction f true z+direction f false z=fieldDirection f :=by
  change (fieldDirection f-sliceState (fieldVector f z))+sliceState (fieldVector f z)=fieldDirection f
  abel

theorem direction_smooth (f : Field289) (remaining : Bool) (z : physicalChart) : ContDiffAt ℝ ∞ (direction f remaining) z.val :=by
  cases remaining
  · exact sliceStateCLM.contDiff.contDiffAt.comp z.val (fieldVector_smooth f z)
  · exact complement_smooth f z

def currentSymbol (p : PhysicalMomentum) (s v : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight s*symbolFirst p s v)
def contactSymbol (p : PhysicalMomentum) (s v w : ActionState) : FullMatrix :=
  -(4:ℂ) • (actionWeightFirst s w*symbolFirst p s v+sourceActionWeight s*symbolSecond p s v w)

theorem currentSymbol_add (p : PhysicalMomentum) (s u v : ActionState) :
    currentSymbol p s (u+v)=currentSymbol p s u+currentSymbol p s v :=by
  simp only [currentSymbol,symbolFirst,map_add,mul_add,smul_add]

theorem contactSymbol_add_left (p : PhysicalMomentum) (s u v w : ActionState) :
    contactSymbol p s (u+v) w=contactSymbol p s u w+contactSymbol p s v w :=by
  simp only [contactSymbol,symbolFirst,symbolSecond,map_add,mul_add,smul_add]
  abel

theorem contactSymbol_add_right (p : PhysicalMomentum) (s u v w : ActionState) :
    contactSymbol p s u (v+w)=contactSymbol p s u v+contactSymbol p s u w :=by
  simp only [contactSymbol,symbolFirst,symbolSecond,actionWeightFirst,map_add,add_apply,mul_add,add_mul,smul_add]
  abel

def currentPiece (f : Field289) (p : PhysicalMomentum) (a : Bool) (z : SourceCoordinateSlice) : FullMatrix :=
  currentSymbol p (sourceState z) (direction f a z)
def contactPiece (f g : Field289) (p : PhysicalMomentum) (a b : Bool) (z : SourceCoordinateSlice) : FullMatrix :=
  contactSymbol p (sourceState z) (direction f a z) (direction g b z)

theorem currentPiece_sum (f : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    (∑a : Bool,currentPiece f p a z.val)=rawActionSymbol f p (sourceState z.val) :=by
  rw [Fintype.sum_bool,currentPiece,currentPiece,←currentSymbol_add,direction_sum]
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  exact (rawActionSymbol_source f p (sourceState z.val) valid).symm

theorem contactPiece_sum (f g : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    (∑a : Bool,∑b : Bool,contactPiece f g p a b z.val)=rawActionContact f p (sourceState z.val) (fieldDirection g) :=by
  simp only [Fintype.sum_bool,contactPiece]
  rw [←contactSymbol_add_right,←contactSymbol_add_right,direction_sum,←contactSymbol_add_left,direction_sum]
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  exact (rawActionContact_generated f p (sourceState z.val) (fieldDirection g) valid).symm

theorem currentPiece_smooth (f : Field289) (p : PhysicalMomentum) (a : Bool) (z : physicalChart) :
    ContDiffAt ℝ ∞ (currentPiece f p a) z.val :=by
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  have first:=((sourceSymbol_smooth p (sourceState z.val) valid).fderiv_right (m:=∞) (by simp)).comp z.val sourceState_smooth.contDiffAt
  have firstValue:=first.clm_apply (direction_smooth f a z)
  have W:=(sourceActionWeight_smooth (sourceState z.val) valid).comp z.val sourceState_smooth.contDiffAt
  exact (W.mul firstValue).const_smul (-(4:ℂ))

theorem contactPiece_smooth (f g : Field289) (p : PhysicalMomentum) (a b : Bool) (z : physicalChart) :
    ContDiffAt ℝ ∞ (contactPiece f g p a b) z.val :=by
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  have first:=((sourceSymbol_smooth p (sourceState z.val) valid).fderiv_right (m:=∞) (by simp)).comp z.val sourceState_smooth.contDiffAt
  have firstValue:=first.clm_apply (direction_smooth f a z)
  have second:=(((sourceSymbol_smooth p (sourceState z.val) valid).fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).comp z.val sourceState_smooth.contDiffAt
  have secondValue:=(second.clm_apply (direction_smooth g b z)).clm_apply (direction_smooth f a z)
  have W:=(sourceActionWeight_smooth (sourceState z.val) valid).comp z.val sourceState_smooth.contDiffAt
  have DW:=((sourceActionWeight_smooth (sourceState z.val) valid).fderiv_right (m:=∞) (by simp)).comp z.val sourceState_smooth.contDiffAt
  exact (((DW.clm_apply (direction_smooth g b z)).mul firstValue).add (W.mul secondValue)).const_smul (-(4:ℂ))

def branchMatrix (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (a b : Bool) (z : SourceCoordinateSlice) : FullMatrix :=
  if contact then contactPiece f g p a b z else currentPiece f p a z

theorem branchMatrix_smooth (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (a b : Bool) (z : physicalChart) :
    ContDiffAt ℝ ∞ (branchMatrix contact f g p a b) z.val :=by
  cases contact
  · exact currentPiece_smooth f p a z
  · exact contactPiece_smooth f g p a b z

def branchCoefficient (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (a b : Bool) (z : SourceCoordinateSlice) : FiberMap :=(phi z:ℂ) • quantizer (branchMatrix contact f g p a b z)

theorem branchCoefficient_zero (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (a b : Bool) (z : SourceCoordinateSlice) (outside : z∉tsupport phi) : branchCoefficient contact f g p phi a b z=0 :=by
  rw [branchCoefficient,image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
  exact zero_smul ℂ (quantizer (branchMatrix contact f g p a b z))

theorem branchCoefficient_smooth (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (a b : Bool) : ContDiff ℝ ∞ (branchCoefficient contact f g p phi a b) :=by
  apply contDiff_iff_contDiffAt.mpr;intro z
  by_cases inside : z∈tsupport phi
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z phi.contDiff.contDiffAt).smul
      ((quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z
        (branchMatrix_smooth contact f g p a b ⟨z,phi.tsupport_subset inside⟩))
  · apply (contDiffAt_const (c:=(0:FiberMap))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport phi).isOpen_compl.mem_nhds inside] with y hy
    exact branchCoefficient_zero contact f g p phi a b y hy

def branchTest (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) (a b : Bool) :
    𝓓(physicalChart,FiberMap) where
  toFun:=branchCoefficient contact f g p phi a b
  contDiff':=branchCoefficient_smooth contact f g p phi a b
  hasCompactSupport':=by
    apply phi.hasCompactSupport.of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_tsupport phi)
    intro z hz;by_contra outside;exact hz (branchCoefficient_zero contact f g p phi a b z outside)
  tsupport_subset':=by
    apply Set.Subset.trans _ phi.tsupport_subset
    apply closure_minimal _ (isClosed_tsupport phi)
    intro z hz;by_contra outside;exact hz (branchCoefficient_zero contact f g p phi a b z outside)

def branchPrice (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) (a b : Bool) : ℝ :=
  ‖(branchTest contact f g p phi a b : BoundedContinuousFunction SourceCoordinateSlice FiberMap)‖

theorem branchCoefficient_weights (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (a b : Bool) (z : SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (weight w) (branchCoefficient contact f g p phi a b z) :=(weight_commute w _).smul_right (phi z:ℂ)

def branchGauss (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) (a b : Bool) : FieldOp :=
  GaussBoundedMultiplier.extension (branchCoefficient contact f g p phi a b)
    (fun _=>(branchCoefficient_smooth contact f g p phi a b).contDiffAt)
    (fun z w=>branchCoefficient_weights contact f g p phi a b z.val w) (branchPrice contact f g p phi a b)
    (by exact norm_nonneg (branchTest contact f g p phi a b : BoundedContinuousFunction SourceCoordinateSlice FiberMap))
    (fun z v=>((branchCoefficient contact f g p phi a b z.val).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((branchTest contact f g p phi a b : BoundedContinuousFunction SourceCoordinateSlice FiberMap).norm_coe_le_norm z.val) (norm_nonneg v)))

theorem branchGauss_core (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) (a b : Bool) (u : QuantumTest) :
    branchGauss contact f g p phi a b (embed u)=embed (localMultiplier (branchCoefficient contact f g p phi a b)
      (fun _=>(branchCoefficient_smooth contact f g p phi a b).contDiffAt) u) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ u

theorem branchGauss_price (contact : Bool) (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) (a b : Bool) :
    ‖branchGauss contact f g p phi a b‖≤ branchPrice contact f g p phi a b :=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

theorem rawGauss_current_split (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    rawGauss false f g p phi=∑a : Bool,branchGauss false f g p phi a false :=by
  apply GaussYukawaGrade.core_ext;intro u
  simp only [sum_apply,rawGauss_core,branchGauss_core,←map_sum]
  apply congrArg embed;apply DFunLike.ext;intro z
  by_cases inside : z∈physicalChart
  · change (phi z:ℂ) • rawStateFiber f p (sourceState z) (u z)=
      ∑a : Bool,((phi z:ℂ) • quantizer (currentPiece f p a z)) (u z)
    rw [←rawActionSymbol_actual f p z,←currentPiece_sum f p ⟨z,inside⟩,map_sum]
    simp only [Finset.smul_sum,sum_apply,smul_apply]
  · have zero : u z=0:=image_eq_zero_of_notMem_tsupport (fun h=>inside (u.tsupport_subset h))
    change rawLocalized false f g p phi z (u z)=∑a : Bool,branchCoefficient false f g p phi a false z (u z)
    simp only [zero,map_zero,Finset.sum_const_zero]

theorem rawGauss_contact_split (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    rawGauss true f g p phi=∑a : Bool,∑b : Bool,branchGauss true f g p phi a b :=by
  apply GaussYukawaGrade.core_ext;intro u
  simp only [sum_apply,rawGauss_core,branchGauss_core,←map_sum]
  apply congrArg embed;apply DFunLike.ext;intro z
  by_cases inside : z∈physicalChart
  · change (phi z:ℂ) • rawContactFiber f g p z (u z)=
      ∑a : Bool,∑b : Bool,((phi z:ℂ) • quantizer (contactPiece f g p a b z)) (u z)
    rw [←rawActionContact_actual f g p ⟨z,inside⟩,←contactPiece_sum f g p ⟨z,inside⟩]
    simp only [map_sum,Finset.smul_sum,sum_apply,smul_apply]
  · have zero : u z=0:=image_eq_zero_of_notMem_tsupport (fun h=>inside (u.tsupport_subset h))
    change rawLocalized true f g p phi z (u z)=∑a : Bool,∑b : Bool,branchCoefficient true f g p phi a b z (u z)
    simp only [zero,map_zero,Finset.sum_const_zero]

def sumJet {ι E : Type*} [Fintype ι] [AddCommMonoid E] (j : ι→SourceJet E) : SourceJet E :=
  ⟨∑i,(j i).value,∑i,(j i).first,∑i,(j i).second⟩

theorem sourceJet_ext {E : Type*} (a b : SourceJet E) (hv : a.value=b.value) (h1 : a.first=b.first) (h2 : a.second=b.second) : a=b :=by
  cases a;cases b;cases hv;cases h1;cases h2;rfl

theorem wordJet_left_sum {ι : Type*} [Fintype ι] (Co Cm Ci B : FieldOp) (A : ι→FieldOp)
    (ao bo am bm ai bi r : ℝ) :
    wordJet Co Cm Ci (∑i,A i) B ao bo am bm ai bi r=
      sumJet (fun i=>wordJet Co Cm Ci (A i) B ao bo am bm ai bi r) :=by
  apply sourceJet_ext <;>
    simp only [wordJet,jetMul,jetConst,sumJet,Finset.sum_mul,Finset.mul_sum,Finset.sum_add_distrib,
      mul_zero,zero_mul,add_zero,zero_add,Finset.sum_const_zero,add_mul,mul_add]

theorem wordJet_right_sum {ι : Type*} [Fintype ι] (Co Cm Ci A : FieldOp) (B : ι→FieldOp)
    (ao bo am bm ai bi r : ℝ) :
    wordJet Co Cm Ci A (∑i,B i) ao bo am bm ai bi r=
      sumJet (fun i=>wordJet Co Cm Ci A (B i) ao bo am bm ai bi r) :=by
  apply sourceJet_ext <;>
    simp only [wordJet,jetMul,jetConst,sumJet,Finset.sum_mul,Finset.mul_sum,Finset.sum_add_distrib,
      mul_zero,zero_mul,add_zero,zero_add,Finset.sum_const_zero,add_mul,mul_add]

theorem contactJet_sum {ι : Type*} [Fintype ι] (Co Ci : FieldOp) (A : ι→FieldOp)
    (ao bo ai bi r : ℝ) :
    jetMul (jetMul (timeJet Co ao bo r) (jetConst (∑i,A i))) (timeJet Ci ai bi r)=
      sumJet (fun i=>jetMul (jetMul (timeJet Co ao bo r) (jetConst (A i))) (timeJet Ci ai bi r)) :=by
  apply sourceJet_ext <;>
    simp only [jetMul,jetConst,sumJet,Finset.sum_mul,Finset.mul_sum,Finset.sum_add_distrib,
      mul_zero,zero_mul,add_zero,zero_add,Finset.sum_const_zero,add_mul,mul_add]

def currentPieceJet (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (piece : Bool) (r : ℝ) : SourceJet FieldOp :=
  let f:=sourceFieldUnit a
  let g:=sourceFieldUnit b
  let forward:=wordJet (generator q F (q.p+q.k+q.ell)) (generator q F (q.p+q.ell)) (generator q F q.p)
    (branchGauss false f g (q.p+q.ell) q.phi piece false) (localizedGauss g q.p q.psi) (-1) (-q.age) 1 0 0 q.age r
  let reverse:=wordJet (generator q F (q.p+q.k+q.ell)) (generator q F (q.p+q.k)) (generator q F q.p)
    (localizedGauss g (q.p+q.k) q.psi) (branchGauss false f g q.p q.phi piece false) 0 (-q.age) (-1) 0 1 q.age r
  jetScale (-Complex.I) (jetSub reverse forward)

def contactPieceJet (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (i j : Bool) (r : ℝ) : SourceJet FieldOp :=
  jetMul (jetMul (timeJet (generator q F (q.p+q.k+q.ell)) (-1) (-q.age) r)
    (jetConst (branchGauss true (sourceFieldUnit a) (sourceFieldUnit b) q.p (contactLocalizer q.phi q.psi) i j)))
      (timeJet (generator q F q.p) 1 q.age r)

theorem rawKernelJet_split (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (r : ℝ) :
    rawKernelJet q F a b r=sumJet (fun i : Bool=>currentPieceJet q F a b i r) :=by
  dsimp only [rawKernelJet]
  rw [rawGauss_current_split,rawGauss_current_split,wordJet_left_sum,wordJet_right_sum]
  apply sourceJet_ext <;>
    simp only [sumJet,currentPieceJet,jetScale,jetSub,Finset.sum_sub_distrib,Finset.smul_sum,smul_sub]

theorem rawContactJet_split (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (r : ℝ) :
    rawContactJet q F a b r=sumJet (fun i : Bool=>sumJet (fun j : Bool=>contactPieceJet q F a b i j r)) :=by
  unfold rawContactJet
  rw [rawGauss_contact_split,contactJet_sum]
  apply sourceJet_ext <;> simp only [sumJet,contactJet_sum,contactPieceJet]

lemma jetMul_source (a b : ℝ→SourceJet FieldOp) (r : ℝ) (ha : HasSourceJets a r) (hb : HasSourceJets b r) :
    HasSourceJets (fun t=>jetMul (a t) (b t)) r :=
  ⟨ha.1.mul hb.1,(ha.2.mul hb.1).add (ha.1.mul hb.2)⟩

lemma jetConst_source (A : FieldOp) (r : ℝ) : HasSourceJets (fun _=>jetConst A) r :=
  ⟨hasDerivAt_const r A,hasDerivAt_const r 0⟩

lemma timeJet_source (C : FieldOp) (rate shift r : ℝ) : HasSourceJets (timeJet C rate shift) r :=by
  have path : HasDerivAt (fun t : ℝ=>rate*t+shift) rate r :=by
    convert! ((hasDerivAt_id r).const_mul rate).add_const shift using 1
    simp
  have source : HasDerivAt (SourceFiniteUnitary.time C)
      (SourceFiniteUnitary.time C (rate*r+shift)*((-Complex.I) • C)) (rate*r+shift) :=
    hasDerivAt_exp_smul_const ((-Complex.I) • C) (rate*r+shift)
  have first:=source.scomp r path
  exact ⟨first,(first.mul_const ((-Complex.I) • C)).const_smul rate⟩

lemma wordJet_source (Co Cm Ci A B : FieldOp) (ao bo am bm ai bi r : ℝ) :
    HasSourceJets (wordJet Co Cm Ci A B ao bo am bm ai bi) r :=
  jetMul_source _ _ r (jetMul_source _ _ r (jetMul_source _ _ r
    (jetMul_source _ _ r (timeJet_source Co ao bo r) (jetConst_source A r)) (timeJet_source Cm am bm r))
      (jetConst_source B r)) (timeJet_source Ci ai bi r)

theorem currentPieceJet_generated (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (i : Bool) (r : ℝ) :
    HasSourceJets (currentPieceJet q F a b i) r :=by
  have forward:=wordJet_source (generator q F (q.p+q.k+q.ell)) (generator q F (q.p+q.ell)) (generator q F q.p)
    (branchGauss false (sourceFieldUnit a) (sourceFieldUnit b) (q.p+q.ell) q.phi i false)
    (localizedGauss (sourceFieldUnit b) q.p q.psi) (-1) (-q.age) 1 0 0 q.age r
  have reverse:=wordJet_source (generator q F (q.p+q.k+q.ell)) (generator q F (q.p+q.k)) (generator q F q.p)
    (localizedGauss (sourceFieldUnit b) (q.p+q.k) q.psi)
    (branchGauss false (sourceFieldUnit a) (sourceFieldUnit b) q.p q.phi i false) 0 (-q.age) (-1) 0 1 q.age r
  constructor
  · convert! (reverse.1.sub forward.1).const_smul (-Complex.I) using 1
  · convert! (reverse.2.sub forward.2).const_smul (-Complex.I) using 1

theorem contactPieceJet_generated (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (i j : Bool) (r : ℝ) :
    HasSourceJets (contactPieceJet q F a b i j) r :=
  jetMul_source _ _ r (jetMul_source _ _ r (timeJet_source _ _ _ _) (jetConst_source _ _)) (timeJet_source _ _ _ _)

def currentActionPiece (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (i : Bool) (r : ℝ) : SourceJet ℂ :=
  readJet q (currentPieceJet q F a b i r)
def contactActionPiece (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (i j : Bool) (r : ℝ) : SourceJet ℂ :=
  readJet q (contactPieceJet q F a b i j r)

theorem currentActionPiece_generated (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (i : Bool) (r : ℝ) :
    HasSourceJets (currentActionPiece q F a b i) r :=by
  have h:=currentPieceJet_generated q F a b i r
  exact ⟨(sourcePairRead q).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt r h.1,
    (sourcePairRead q).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt r h.2⟩

theorem contactActionPiece_generated (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (i j : Bool) (r : ℝ) :
    HasSourceJets (contactActionPiece q F a b i j) r :=by
  have h:=contactPieceJet_generated q F a b i j r
  exact ⟨(sourcePairRead q).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt r h.1,
    (sourcePairRead q).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt r h.2⟩

theorem currentActionPiece_sum (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (r : ℝ) :
    actionJet q F false a b r=sumJet (fun i : Bool=>currentActionPiece q F a b i r) :=by
  change readJet q (rawKernelJet q F a b r)=_
  rw [rawKernelJet_split]
  apply sourceJet_ext <;> simp only [sumJet,readJet,currentActionPiece,map_sum]

theorem contactActionPiece_sum (q : SourceResponsePoint) (F : Index) (a b : Fin 97) (r : ℝ) :
    actionJet q F true a b r=sumJet (fun i : Bool=>sumJet (fun j : Bool=>contactActionPiece q F a b i j r)) :=by
  change readJet q (rawContactJet q F a b r)=_
  rw [rawContactJet_split]
  apply sourceJet_ext <;> simp only [sumJet,readJet,contactActionPiece,map_sum]

theorem jetEntry_sum {ι : Type*} [Fintype ι] (j : ι→SourceJet ℂ) (k : Fin 3) :
    jetEntry (sumJet j) k=∑i,jetEntry (j i) k :=by
  fin_cases k <;> rfl

theorem injectSource_sum {ι : Type*} [Fintype ι] (j : ι→Fin 97→ℂ) :
    injectSource (fun a=>∑i,j i a)=∑i,injectSource (j i) :=by
  funext row
  simp only [injectSource,Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro a _
  split_ifs <;> simp

/-- Euler moves the original raw action current to the right-hand side. -/
def eulerSourceJet (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97) (r : ℝ) (k : Fin 3) : Fin 289→ℂ :=
  -injectSource (fun a=>jetEntry (actionJet q F contact a b r) k)

def currentEulerPiece (q : SourceResponsePoint) (F : Index) (b : Fin 97) (i : Bool) (r : ℝ) (k : Fin 3) : Fin 289→ℂ :=
  -injectSource (fun a=>jetEntry (currentActionPiece q F a b i r) k)

def contactEulerPiece (q : SourceResponsePoint) (F : Index) (b : Fin 97) (i j : Bool) (r : ℝ) (k : Fin 3) : Fin 289→ℂ :=
  -injectSource (fun a=>jetEntry (contactActionPiece q F a b i j r) k)

theorem eulerSource_current_split (q : SourceResponsePoint) (F : Index) (b : Fin 97) (r : ℝ) (k : Fin 3) :
    eulerSourceJet q F false b r k=∑i : Bool,currentEulerPiece q F b i r k :=by
  simp only [eulerSourceJet,currentActionPiece_sum,jetEntry_sum,injectSource_sum,currentEulerPiece,Finset.sum_neg_distrib]

theorem eulerSource_contact_split (q : SourceResponsePoint) (F : Index) (b : Fin 97) (r : ℝ) (k : Fin 3) :
    eulerSourceJet q F true b r k=∑i : Bool,∑j : Bool,contactEulerPiece q F b i j r k :=by
  simp only [eulerSourceJet,contactActionPiece_sum,jetEntry_sum,injectSource_sum,contactEulerPiece,Finset.sum_neg_distrib]

theorem eulerSource_pairing (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97) (r : ℝ) (k : Fin 3) (f : Field289) :
    (∑row : Fin 289,(f row:ℂ)*eulerSourceJet q F contact b r k row)=
      -(∑a : Fin 97,(f (sourceSlot a):ℂ)*jetEntry (actionJet q F contact a b r) k) :=by
  simp only [eulerSourceJet,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
  rw [actual_source_pairing]

end LowEnergy.PreparationVacuumActionFieldLift
