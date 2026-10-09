import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPoleFrameReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePoleChargeReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumWholeOrigin
open PreparationVacuumSoftPoleSelection PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open FullQuantum.StateGreen GaussNativeMatter PreparationVacuumLowerClassical
open PreparationVacuumSourceChartBudget SourceQuantumResidualGaugeSlice SourceQuantumNativeDimensions
open Stage9C.Material.SpinPair StageNineHolonomicField PreparationCoordinates SourceQuantumScalarChart
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalChange fullKernelFrame slowFastFrame fullNativeOrigin

private def branchSelectorTerms : List SourceTerm :=
  [⟨1,0,⟨0,0,0,0⟩,1⟩,⟨2,1,⟨0,0,0,0⟩,1⟩]

/-- Literal complete endpoint columns, including their matter, independent dual and auxiliary entries. -/
def sourceNativeOriginActionTerms : List SourceTerm := [
  ⟨21,0,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨34,0,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨88,0,⟨0,0,0,0⟩,1⟩,⟨94,0,⟨0,0,0,0⟩,1⟩,
  ⟨112,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨118,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨217,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩⟩,
  ⟨230,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩⟩,
  ⟨74,1,⟨0,0,0,0⟩,1⟩,⟨76,1,⟨0,0,0,0⟩,-1⟩,
  ⟨80,1,⟨0,0,0,0⟩,1⟩,⟨82,1,⟨0,0,0,0⟩,-1⟩,
  ⟨98,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨100,1,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨104,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨106,1,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩]

private theorem endpoint_certificate :
    fastNormalizeTerms (productTerms (productTerms fullNativeOriginTerms slowFastFrameTerms) branchSelectorTerms++
      negativeTerms sourceNativeOriginActionTerms)=[] := by decide +kernel

/-- Both endpoints are read from the original O0N frame, rather than the distinct first frame derivative. -/
theorem sourceNativeOriginAction_generated (branch : Fin 2) :
    nativeBranchVector branch=fun i=>sourceMatrix sourceNativeOriginActionTerms 0 i ⟨branch.val,by omega⟩ := by
  have generated:=normalization_equal _ _ endpoint_certificate (0:Fin 4→ℂ)
  simp only [productTerms_value,←fullNativeOrigin_generated,slowFastFrame_constant] at generated
  have vector : sourceMatrix branchSelectorTerms 0*ᵥ(Pi.single (⟨branch.val,by omega⟩:Fin 289) 1)=
      fiveVector (Pi.single (residueIndex branch) 1) := by
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases branch <;>
      norm_num [branchSelectorTerms,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue,
        Matrix.col_apply,Matrix.single_apply,residueIndex,fiveVector,Pi.single_apply,Fin.ext_iff,
        QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]
    all_goals (split_ifs <;> simp_all; omega)
  have returned:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥPi.single (⟨branch.val,by omega⟩:Fin 289) 1) generated
  rw [←Matrix.mulVec_mulVec,vector,Matrix.mulVec_single_one] at returned
  funext i
  simpa only [nativeBranchVector,fullNativeOrigin,Matrix.mulVec_mulVec,mul_assoc,Matrix.col_apply] using congrFun returned i

/-- The full endpoint is kept as a complex source field; only its action components are read below. -/
def sourceNativeOriginReal (branch : Fin 2) : Field289 := fun i=>(nativeBranchVector branch i).re

def sourceNativeOriginImag (branch : Fin 2) : Field289 := fun i=>(nativeBranchVector branch i).im

def sourceNativeOriginGaugeWeight : ℝ := (3/10)*Real.sqrt 2

private theorem matrix_row_zero (terms : List SourceTerm) (i j : Fin 289)
    (rows : ∀t∈terms,t.row≠i) : sourceMatrix terms 0 i j=0 := by
  induction terms with
  | nil=>rfl
  | cons t rest ih=>
    rw [sourceMatrix_cons,Matrix.add_apply]
    have first : t.matrix 0 i j=0 := by
      simp only [SourceTerm.matrix,Matrix.single_apply]
      exact if_neg (fun h=>rows t List.mem_cons_self h.1)
    rw [first,ih (fun a ha=>rows a (List.mem_cons_of_mem _ ha)),zero_add]

private theorem endpoint_rows : sourceNativeOriginActionTerms.all
    (fun t=>decide (t.row.val=21 ∨ t.row.val=34 ∨ (73≤t.row.val ∧ t.row.val<121) ∨ 217≤t.row.val))=true := by
  decide +kernel

private theorem real_absent_slot (branch : Fin 2) (i : Fin 289)
    (absent : i.val≠21 ∧ i.val≠34 ∧ ((i.val < 73) ∨ (121 ≤ i.val)) ∧ i.val<217) :
    sourceNativeOriginReal branch i=0 := by
  unfold sourceNativeOriginReal
  rw [sourceNativeOriginAction_generated]
  dsimp only []
  have zero : sourceMatrix sourceNativeOriginActionTerms 0 i ⟨branch.val,by omega⟩=0 := by
    apply matrix_row_zero
    intro t member equal
    have support:=of_decide_eq_true (List.all_eq_true.mp endpoint_rows t member)
    have value:=congrArg Fin.val equal
    omega
  rw [zero,Complex.zero_re]

private theorem real_scalar_slot (branch : Fin 2) (j : Fin 9) :
    sourceNativeOriginReal branch (scalarSlot j)=0 := by
  apply real_absent_slot
  simp only [scalarSlot,Fin.val_mk]
  omega

private theorem real_coframe_slot (branch : Fin 2) (a mu : Fin 4) :
    sourceNativeOriginReal branch (coframeSlot a mu)=0 := by
  apply real_absent_slot
  simp only [coframeSlot,Fin.val_mk]
  omega

private theorem real_lorentz_slot (branch : Fin 2) (mu : Fin 4) (a : Fin 6) :
    sourceNativeOriginReal branch (lorentzSlot mu a)=0 := by
  apply real_absent_slot
  simp only [lorentzSlot,Fin.val_mk]
  omega

private theorem real_gauge_slot (branch : Fin 2) (mu : Fin 4) (a : Fin 12) :
    sourceNativeOriginReal branch (gaugeSlot mu a)=
      if branch=0 then (if mu=1 ∧ a=0 then sourceNativeOriginGaugeWeight else 0)-
        (if mu=2 ∧ a=1 then sourceNativeOriginGaugeWeight else 0) else 0 := by
  have rows : (sourceNativeOriginActionTerms.drop 2).all (fun t=>decide (73≤t.row.val))=true := by decide +kernel
  have remaining : sourceMatrix (sourceNativeOriginActionTerms.drop 2) 0 (gaugeSlot mu a) ⟨branch.val,by omega⟩=0 := by
    apply matrix_row_zero
    intro t member equal
    have support:=of_decide_eq_true (List.all_eq_true.mp rows t member)
    have value:=congrArg Fin.val equal
    simp only [gaugeSlot,Fin.val_mk] at value
    omega
  unfold sourceNativeOriginReal
  rw [sourceNativeOriginAction_generated]
  dsimp only []
  have split : sourceNativeOriginActionTerms=sourceNativeOriginActionTerms.take 2++sourceNativeOriginActionTerms.drop 2 :=
    (List.take_append_drop 2 sourceNativeOriginActionTerms).symm
  rw [split,sourceMatrix_append,Matrix.add_apply,remaining,add_zero]
  have first : (21:ℕ)=9+12*mu.val+a.val ↔ mu.val=1 ∧ a.val=0 := by omega
  have second : (34:ℕ)=9+12*mu.val+a.val ↔ mu.val=2 ∧ a.val=1 := by omega
  have head : sourceMatrix (sourceNativeOriginActionTerms.take 2) 0=
      Matrix.single 21 0 ((3/10:ℂ)*rootTwo)+Matrix.single 34 0 (-((3/10:ℂ)*rootTwo)) := by
    norm_num [sourceNativeOriginActionTerms,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue]
  rw [head,Matrix.add_apply]
  norm_num only [Matrix.single_apply,Fin.ext_iff,gaugeSlot]
  norm_num [Fin.val_ofNat]
  simp only [first,second]
  have coefficient : ((3/10:ℂ)*rootTwo).re=sourceNativeOriginGaugeWeight := by
    norm_num [rootTwo,sourceNativeOriginGaugeWeight]
  simp only [apply_ite,Complex.zero_re,Complex.neg_re,coefficient]
  have aZero : a=0 ↔ a.val=0 := Fin.ext_iff
  have bZero : branch=0 ↔ branch.val=0 := Fin.ext_iff
  have reversed : 0=branch.val ↔ branch.val=0 := eq_comm
  simp only [aZero,bZero,reversed]
  by_cases active : branch.val=0 <;> by_cases firstSlot : mu.val=1 ∧ a.val=0 <;>
    by_cases secondSlot : mu.val=2 ∧ a.val=1 <;>
    simp only [active,firstSlot,secondSlot,and_true,and_false,if_true,if_false] <;> norm_num

/-- The two spatial gauge components are read in the original physical basis; no temporal hypercharge direction is substituted. -/
theorem sourceNativeOriginReal_gauge (branch : Fin 2) (mu : Fin 4) :
    fieldGauge (sourceNativeOriginReal branch) mu=
      if branch=0 then sourceNativeOriginGaugeWeight •
        ((if mu=1 then PreparationVacuumLowerClassical.originalUnit 0 else 0)-
          (if mu=2 then PreparationVacuumLowerClassical.originalUnit 1 else 0)) else 0 := by
  unfold fieldGauge
  simp_rw [real_gauge_slot]
  by_cases branchZero : branch=0
  · simp only [if_pos branchZero,sub_smul,Finset.sum_sub_distrib,ite_smul,zero_smul]
    fin_cases mu <;> simp
  · simp [branchZero]

theorem sourceNativeOriginReal_remaining (branch : Fin 2) :
    fieldScalar (sourceNativeOriginReal branch)=0 ∧ fieldCoframe (sourceNativeOriginReal branch)=0 ∧
      fieldLorentz (sourceNativeOriginReal branch)=0 := by
  refine ⟨?_,?_,?_⟩
  · simp only [fieldScalar,real_scalar_slot,zero_smul,Finset.sum_const_zero]
  · funext a mu
    exact real_coframe_slot branch a mu
  · funext mu a
    exact real_lorentz_slot branch mu a

private theorem source_matrix_im_zero (terms : List SourceTerm) (i j : Fin 289) :
    (sourceMatrix terms 0 i j).im=0 := by
  induction terms with
  | nil=>rfl
  | cons t rest ih=>
    rw [sourceMatrix_cons,Matrix.add_apply,Complex.add_im,ih,add_zero]
    simp only [SourceTerm.matrix,Matrix.single_apply]
    split_ifs
    · have factor : (t.powers.value (0 : Fin 4→ℂ)).im=0 := by
        simp only [Powers.value,Pi.zero_apply]
        rw [←Complex.ofReal_zero]
        simp only [←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_im]
      have coefficient : (coefficientValue t.coefficient).im=0 := by simp [coefficientValue,rootTwo,rootFifteen]
      simp only [Complex.mul_im,factor,coefficient,mul_zero,zero_mul,add_zero]
    · rfl

theorem sourceNativeOriginImag_zero (branch : Fin 2) : sourceNativeOriginImag branch=0 := by
  funext i
  simp only [sourceNativeOriginImag,sourceNativeOriginAction_generated,source_matrix_im_zero,Pi.zero_apply]

/-- These are the original two spatial stabilizer connections, with their source coefficient. -/
def sourceNativeOriginConnection (branch : Fin 2) (mu : Fin 4) : SourceMatrix :=
  if branch=0 then sourceNativeOriginGaugeWeight •
    ((if mu=1 then nativePrimal (originalUnit 0) else 0)-
      (if mu=2 then nativePrimal (originalUnit 1) else 0)) else 0

/-- The full endpoint action keeps exactly its generated physical gauge connection; the non-action matter/dual/auxiliary fields remain in the whole vector. -/
theorem sourceNativeOriginAction_state (branch : Fin 2) :
    fieldDirection (sourceNativeOriginReal branch)=(0,sourceNativeOriginConnection branch,0) := by
  rw [←stateDirection_source]
  change (fieldCoframe (sourceNativeOriginReal branch),
    (fun mu=>spinLinear mu (fieldLorentz (sourceNativeOriginReal branch))+
      nativePrimal (fieldGauge (sourceNativeOriginReal branch) mu)),
    scalarLinear (fieldScalar (sourceNativeOriginReal branch)))=_
  rw [(sourceNativeOriginReal_remaining branch).1,(sourceNativeOriginReal_remaining branch).2.1,
    (sourceNativeOriginReal_remaining branch).2.2]
  simp only [map_zero,zero_add]
  refine Prod.ext rfl ?_
  refine Prod.ext ?_ rfl
  funext mu
  dsimp only []
  rw [sourceNativeOriginReal_gauge]
  unfold sourceNativeOriginConnection
  split_ifs <;> simp only [map_zero,map_smul,map_sub]

theorem sourceNativeOriginAction_connection (branch : Fin 2) (mu : Fin 4) :
    sourceModeConnection mu (nativeBranchVector branch)=sourceNativeOriginConnection branch mu := by
  have real : (fun i=>(sourceNativeOriginReal branch i:ℂ))=nativeBranchVector branch := by
    funext i
    have imaginary:=congrFun (sourceNativeOriginImag_zero branch) i
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im,sourceNativeOriginImag,Pi.zero_apply] using imaginary.symm
  rw [←real,sourceModeConnection_real]
  exact congrArg (fun state : ActionState=>state.2.1 mu) (sourceNativeOriginAction_state branch)

/-- The spatial directions are the original doubled color Pauli generators, generated from the native coordinate equivalence. -/
theorem sourceNativeOrigin_unit_zero :
    p286CoordinateEquiv.symm (originalUnit 0)=(2:ℝ) • sourceColorP286Generator 1 := by
  have same : originalUnit 0=(sourceStabilizer 0).val := by
    apply rawCoordinates.injective
    rw [originalUnit,LinearEquiv.apply_symm_apply,sourceStabilizer_raw]
    rfl
  rw [same]
  change p286CoordinateEquiv.symm (∑i : Fin 3,(![0,2,0] i:ℝ) • colorGenerator i)=_
  simp [Fin.sum_univ_three,colorGenerator]

theorem sourceNativeOrigin_unit_one :
    p286CoordinateEquiv.symm (originalUnit 1)=(2:ℝ) • sourceColorP286Generator 0 := by
  have same : originalUnit 1=(sourceStabilizer 1).val := by
    apply rawCoordinates.injective
    rw [originalUnit,LinearEquiv.apply_symm_apply,sourceStabilizer_raw]
    rfl
  rw [same]
  change p286CoordinateEquiv.symm (∑i : Fin 3,(![2,0,0] i:ℝ) • colorGenerator i)=_
  simp [Fin.sum_univ_three,colorGenerator]

end LowEnergy.PreparationPhysicalNativePoleChargeReturn
