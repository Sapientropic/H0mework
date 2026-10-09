import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeColumn

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNullNative
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift StageNineP286GaugeAuxiliaryVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumOriginalGreenFeedback
open PreparationVacuumNativeSourceRestriction PreparationVacuumNativeLocalWard PreparationVacuumSourceFieldFamily
open PreparationVacuumNativeFieldInjection PreparationVacuumLorentzFieldInjection PreparationVacuumGaugeSourceInjection
open SourcePropagationNativeActionHessian PreparationVacuumLowerClassical PreparationCoordinates GaussHistoryHilbert
open ActualEMDressedSchur
open scoped Matrix BigOperators
attribute [local irreducible] originalChange Stage9C.Material.SpinPair.actual
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

@[local simp] private theorem cases_one {A : Type*} (a : A) (f : Fin 3→A) : Fin.cases a f (1 : Fin 4)=f 0:=rfl
@[local simp] private theorem cases_two {A : Type*} (a : A) (f : Fin 3→A) : Fin.cases a f (2 : Fin 4)=f 1:=rfl
@[local simp] private theorem cases_three {A : Type*} (a : A) (f : Fin 3→A) : Fin.cases a f (3 : Fin 4)=f 2:=rfl

private theorem source_matrix_row_zero (terms : List SourceTerm) (p : Fin 4→ℂ) (row col : Fin 289)
    (support : ∀t∈terms,t.row≠row) : sourceMatrix terms p row col=0 := by
  induction terms with
  | nil=>rfl
  | cons t rest ih=>
    have first:=support t (by simp)
    have tail:=ih (fun u hu=>support u (by simp [hu]))
    rw [sourceMatrix_cons,Matrix.add_apply,tail]
    simp [SourceTerm.matrix,first]

private theorem source_matrix_entry (terms : List SourceTerm) (p : Fin 4→ℂ) (i j : Fin 289) :
    sourceMatrix terms p i j=(terms.map (fun t=>if t.row=i ∧ t.column=j then
      coefficientValue t.coefficient*t.powers.value p else 0)).sum := by
  induction terms with
  | nil=>rfl
  | cons t rest ih=>
    rw [sourceMatrix_cons,Matrix.add_apply,ih]
    simp [SourceTerm.matrix,Matrix.single_apply]

private theorem source_null_scalar_slots (p : Fin 4→ℝ) (n : Fin 9) (j : Fin 9) :
    originalNullReal p n (scalarSlot j)=0 := by
  have certificate : ∀n : Fin 9,(nullColumnTerms n).all (fun t=>decide (9 ≤ t.row.val))=true := by decide +kernel
  rw [originalNullReal,original_null_column_literal]
  have zero:=source_matrix_row_zero (nullColumnTerms n) (fun mu=>(p mu:ℂ)) (scalarSlot j) (nullColumnIndex n) (by
    intro t member same
    have bound : 9 ≤ t.row.val:=of_decide_eq_true (List.all_eq_true.mp (certificate n) t member)
    have values:=congrArg Fin.val same
    simp only [scalarSlot] at values
    omega)
  rw [zero,Complex.zero_re]

theorem original_null_scalar (p : Fin 4→ℝ) (n : Fin 9) : fieldScalar (originalNullReal p n)=0 := by
  simp only [fieldScalar,source_null_scalar_slots,zero_smul,Finset.sum_const_zero]

private theorem source_null_color_coframe (p : Fin 4→ℝ) (g : Fin 3) (a mu : Fin 4) :
    fieldCoframe (originalNullReal p (Fin.castAdd 6 g)) a mu=0 := by
  have certificate : ∀g : Fin 3,(nullColumnTerms (Fin.castAdd 6 g)).all
      (fun t=>decide (t.row.val<57 ∨ 73 ≤ t.row.val))=true := by decide +kernel
  unfold fieldCoframe
  rw [originalNullReal,original_null_column_literal]
  have zero:=source_matrix_row_zero (nullColumnTerms (Fin.castAdd 6 g)) (fun nu=>(p nu:ℂ))
    (coframeSlot a mu) (nullColumnIndex (Fin.castAdd 6 g)) (by
      intro t member same
      have bound : t.row.val<57 ∨ 73 ≤ t.row.val:=of_decide_eq_true (List.all_eq_true.mp (certificate g) t member)
      have values:=congrArg Fin.val same
      simp only [coframeSlot] at values
      omega)
  rw [zero,Complex.zero_re]

private theorem source_null_color_lorentz (p : Fin 4→ℝ) (g : Fin 3) (mu : Fin 4) (a : Fin 6) :
    fieldLorentz (originalNullReal p (Fin.castAdd 6 g)) mu a=0 := by
  have certificate : ∀g : Fin 3,(nullColumnTerms (Fin.castAdd 6 g)).all
      (fun t=>decide (t.row.val<121 ∨ 145 ≤ t.row.val))=true := by decide +kernel
  unfold fieldLorentz
  rw [originalNullReal,original_null_column_literal]
  have zero:=source_matrix_row_zero (nullColumnTerms (Fin.castAdd 6 g)) (fun nu=>(p nu:ℂ))
    (lorentzSlot mu a) (nullColumnIndex (Fin.castAdd 6 g)) (by
      intro t member same
      have bound : t.row.val<121 ∨ 145 ≤ t.row.val:=of_decide_eq_true (List.all_eq_true.mp (certificate g) t member)
      have values:=congrArg Fin.val same
      simp only [lorentzSlot] at values
      omega)
  rw [zero,Complex.zero_re]

private theorem source_null_lorentz_gauge (p : Fin 4→ℝ) (n : Fin 6) (mu : Fin 4) (a : Fin 12) :
    originalNullReal p (Fin.natAdd 3 n) (gaugeSlot mu a)=0 := by
  have certificate : ∀n : Fin 6,(nullColumnTerms (Fin.natAdd 3 n)).all
      (fun t=>decide (t.row.val<9 ∨ 57 ≤ t.row.val))=true := by decide +kernel
  rw [originalNullReal,original_null_column_literal]
  have zero:=source_matrix_row_zero (nullColumnTerms (Fin.natAdd 3 n)) (fun nu=>(p nu:ℂ))
    (gaugeSlot mu a) (nullColumnIndex (Fin.natAdd 3 n)) (by
      intro t member same
      have bound : t.row.val<9 ∨ 57 ≤ t.row.val:=of_decide_eq_true (List.all_eq_true.mp (certificate n) t member)
      have values:=congrArg Fin.val same
      simp only [gaugeSlot] at values
      omega)
  rw [zero,Complex.zero_re]

private theorem bracket_zero_right (a : P286LieBlockData) : p286LieBracket a 0=0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket,suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket,suLieBracket]
    · simp [p286LieBracket]

private def colorCrossRaw (g j : Fin 3) : Fin 12→ℝ :=
  (!![0,-gaugeColorRaw 2,gaugeColorRaw 1;gaugeColorRaw 2,0,-gaugeColorRaw 0;
    -gaugeColorRaw 1,gaugeColorRaw 0,0] : Matrix (Fin 3) (Fin 3) (Fin 12→ℝ)) g j

private theorem color_cross_raw (g j : Fin 3) :
    rawCoordinates (p286CoordinateEquiv (p286LieBracket (sourceColorP286Generator g) (sourceColorP286Generator j)))=
      colorCrossRaw g j := by
  rw [sourceColorP286Generator_bracket]
  fin_cases g <;> fin_cases j
  all_goals simp [colorCrossRaw,map_neg,gaugeColor_source]

private def nativeColorGaugeRaw (p : Fin 4→ℝ) (g : Fin 3) (mu : Fin 4) : Fin 12→ℝ :=
  Fin.cases 0 (fun j=>gaugeScale • colorCrossRaw g j) mu-p mu • gaugeColorRaw g

private theorem native_color_gauge_raw (p : Fin 4→ℝ) (g : Fin 3) (mu : Fin 4) :
    rawCoordinates (gaugeDirection g 1 p (fun nu=>p286CoordinateEquiv (actual.gaugeConnection 0 nu)) mu)=
      nativeColorGaugeRaw p g mu := by
  unfold gaugeDirection colorLie
  simp only [one_smul,map_sub,map_smul,StageNineP286GaugeAuxiliaryVariation.p286CoordinateLieBracket,LinearEquiv.symm_apply_apply]
  change rawCoordinates (p286CoordinateEquiv (p286LieBracket (sourceColorP286Generator g) (actual.gaugeConnection 0 mu)))-
    p mu • rawCoordinates (p286CoordinateEquiv (sourceColorP286Generator g))=_
  rw [gaugeColor_source]
  have background (j : Fin 3) : actual.gaugeConnection 0 j.succ=gaugeScale • sourceColorP286Generator j := by
    rw [actual_gaugeConnection]
    fin_cases j <;> rfl
  refine Fin.cases ?_ (fun j=>?_) mu
  · have time : actual.gaugeConnection 0 0=0:=by rw [actual_gaugeConnection]; rfl
    rw [time,bracket_zero_right,map_zero,map_zero]
    rfl
  · rw [background,p286LieBracket_smul_right,map_smul,map_smul,color_cross_raw]
    rfl

private theorem original_color_gauge_raw (p : Fin 4→ℝ) (g : Fin 3) (mu : Fin 4) (a : Fin 12) :
    originalNullReal p (Fin.castAdd 6 g) (gaugeSlot mu a)=nativeColorGaugeRaw p g mu a := by
  rw [originalNullReal,original_null_column_literal,source_matrix_entry]
  fin_cases g <;> fin_cases mu <;> fin_cases a
  all_goals norm_num [nullColumnTerms,nullColumnIndex,gaugeSlot,Fin.castAdd,Fin.castLE,Fin.natAdd,Fin.ext_iff]
  all_goals norm_num [Powers.value,coefficientValue,rootTwo,rootFifteen,Fin.ext_iff,
    nativeColorGaugeRaw,colorCrossRaw,gaugeColorRaw,Pi.single_apply,gaugeScale,spinScale]
  all_goals ring_nf
  all_goals congr 2

private theorem color_gauge_source (p : Fin 4→ℝ) (g : Fin 3) (mu : Fin 4) :
    fieldGauge (originalNullReal p (Fin.castAdd 6 g)) mu=
      gaugeDirection g 1 p (fun nu=>p286CoordinateEquiv (actual.gaugeConnection 0 nu)) mu := by
  apply rawCoordinates.injective
  rw [gaugeFieldRaw_source,native_color_gauge_raw]
  funext a
  exact original_color_gauge_raw p g mu a

private theorem lapse_native : lapse=(3/25:ℝ)*Real.sqrt 2*Real.sqrt 15 := by
  have two : (Real.sqrt 2)^2=2:=Real.sq_sqrt (by norm_num)
  have fifteen : (Real.sqrt 15)^2=15:=Real.sq_sqrt (by norm_num)
  have positive : 0 ≤ (3/25:ℝ)*Real.sqrt 2*Real.sqrt 15:=by positivity
  nlinarith [lapse_sq,lapse_pos,mul_self_nonneg ((3/25:ℝ)*Real.sqrt 2*Real.sqrt 15-lapse)]

private theorem frame_entry (a : Fin 6) (i j : Fin 4) :
    frameGenerator a i j=minkowskiInternalSign i*orientedLorentzBivectorBasisCoefficient a i j := by
  simp only [frameGenerator,lorentzGenerator,lorentzSkewConnectionOfBivectorOneForm,
    Pi.single_eq_same,loweredLorentzBivectorMatrix,Pi.single_apply,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]

private theorem lorentz_coframe_source (p : Fin 4→ℝ) (a : Fin 6) (i mu : Fin 4) :
    fieldCoframe (originalNullReal p (Fin.natAdd 3 a)) i mu=(frameGenerator a*actual.coframe 0) i mu := by
  unfold fieldCoframe
  rw [originalNullReal,original_null_column_literal,source_matrix_entry,actual_coframe]
  change _=(frameGenerator a*homogeneousCoframe lapse) i mu
  rw [homogeneousCoframe,Matrix.mul_diagonal,frame_entry,lapse_native]
  fin_cases a <;> fin_cases i <;> fin_cases mu
  all_goals norm_num [nullColumnTerms,nullColumnIndex,coframeSlot,Fin.castAdd,Fin.castLE,Fin.natAdd,Fin.ext_iff]
  all_goals norm_num [Powers.value,coefficientValue,rootTwo,rootFifteen,
    orientedLorentzBivectorBasisCoefficient,pairFirst,pairSecond,minkowskiInternalSign,Fin.ext_iff]

private theorem lorentz_matrix_smul (r : ℝ) (w : Fin 6→ℝ) : lorentzMatrix (r • w)=r • lorentzMatrix w := by
  funext i j
  simp only [lorentzMatrix,lorentzSkewConnectionOfBivectorOneForm,Pi.single_eq_same,
    loweredLorentzBivectorMatrix,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum]
  ring

private theorem lorentz_bracket_smul (r : ℝ) (v w : Fin 6→ℝ) (b : Fin 6) :
    lorentzBracketCoordinates v (r • w) b=r*lorentzBracketCoordinates v w b := by
  simp only [lorentzBracketCoordinates,lorentz_matrix_smul,Matrix.mul_smul,Matrix.smul_mul,
    ←smul_sub,Matrix.smul_apply,smul_eq_mul]
  ring

private theorem lorentz_bracket_zero (v : Fin 6→ℝ) (b : Fin 6) : lorentzBracketCoordinates v 0 b=0 := by
  have zero : lorentzMatrix 0=0 := by
    funext i j
    simp [lorentzMatrix,lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix]
  simp only [lorentzBracketCoordinates,zero,mul_zero,zero_mul,sub_self,Matrix.zero_apply,mul_zero]

private def nativeLorentzRaw (p : Fin 4→ℝ) (a : Fin 6) (mu : Fin 4) : Fin 6→ℝ :=
  Fin.cases 0 (fun j=>(-spinScale) • (fun b=>bivectorGenerator a (Fin.natAdd 3 j) b)) mu-p mu • Pi.single a 1

private theorem native_lorentz_raw (p : Fin 4→ℝ) (a : Fin 6) (mu : Fin 4) (b : Fin 6) :
    connectionBivectorDirection a 1 p (homogeneousContorsion spinScale) mu b=nativeLorentzRaw p a mu b := by
  have background (j : Fin 3) : homogeneousContorsion spinScale j.succ=spinScale • Pi.single (Fin.natAdd 3 j) 1 := by
    funext k
    fin_cases j <;> fin_cases k <;> norm_num [homogeneousContorsion,Fin.natAdd,Pi.single_apply,Fin.ext_iff]
  refine Fin.cases ?_ (fun j=>?_) mu
  · simp only [connectionBivectorDirection,one_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    change lorentzBracketCoordinates (Pi.single a 1) 0 b-p 0*((Pi.single a (1:ℝ) : Fin 6→ℝ) b)=_
    rw [lorentz_bracket_zero]
    rfl
  · simp only [connectionBivectorDirection,one_smul,background,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [lorentz_bracket_smul,bivectorGenerator_originalAdjoint]
    change spinScale*(-bivectorGenerator a (Fin.natAdd 3 j) b)-p j.succ*((Pi.single a (1:ℝ) : Fin 6→ℝ) b)=
      (-spinScale)*bivectorGenerator a (Fin.natAdd 3 j) b-p j.succ*((Pi.single a (1:ℝ) : Fin 6→ℝ) b)
    ring

private def lorentzBackgroundTable : Fin 6→Fin 3→Fin 6→ℝ :=
  ![![![0,0,0,0,0,0],![0,0,1,0,0,0],![0,-1,0,0,0,0]],![![0,0,-1,0,0,0],![0,0,0,0,0,0],![1,0,0,0,0,0]],![![0,1,0,0,0,0],![-1,0,0,0,0,0],![0,0,0,0,0,0]],![![0,0,0,0,0,0],![0,0,0,0,0,1],![0,0,0,0,-1,0]],![![0,0,0,0,0,-1],![0,0,0,0,0,0],![0,0,0,1,0,0]],![![0,0,0,0,1,0],![0,0,0,-1,0,0],![0,0,0,0,0,0]]]

private theorem lorentz_background_table (a : Fin 6) (j : Fin 3) (b : Fin 6) :
    bivectorGenerator a (Fin.natAdd 3 j) b=lorentzBackgroundTable a j b :=by
  simp only [bivectorGenerator,frame_entry]
  fin_cases a <;> fin_cases j <;> fin_cases b
  all_goals norm_num [lorentzBackgroundTable,orientedLorentzBivectorBasisCoefficient,
    pairFirst,pairSecond,minkowskiInternalSign,Fin.natAdd,Fin.ext_iff]

private theorem lorentz_connection_source (p : Fin 4→ℝ) (a b : Fin 6) (mu : Fin 4) :
    fieldLorentz (originalNullReal p (Fin.natAdd 3 a)) mu b=
      connectionBivectorDirection a 1 p (homogeneousContorsion spinScale) mu b := by
  rw [native_lorentz_raw]
  unfold fieldLorentz
  rw [originalNullReal,original_null_column_literal,source_matrix_entry]
  simp only [nativeLorentzRaw,lorentz_background_table]
  fin_cases a <;> fin_cases b <;> fin_cases mu
  all_goals norm_num [nullColumnTerms,nullColumnIndex,lorentzSlot,Fin.castAdd,Fin.castLE,Fin.natAdd,Fin.ext_iff]
  all_goals norm_num [Powers.value,coefficientValue,rootTwo,rootFifteen,Fin.ext_iff,
    lorentzBackgroundTable,Pi.single_apply,spinScale,Fin.natAdd,Fin.castLE]
  all_goals congr 2

private theorem native_scalar_zero (n : Fin 9) (p : Fin 4→ℝ) : fieldScalar (nativeSourceColumn n 1 p)=0 := by
  rw [nativeSourceColumn,nonscalarRestriction_fieldScalar]

private theorem original_source_lorentz : originalSourceData.2.2.2=homogeneousContorsion spinScale := by
  funext mu a
  change loweredLorentzConnectionCoefficient (actual.gravityConnection 0) mu a=_
  rw [actual_gravityConnection]
  exact loweredLorentzConnectionCoefficient_ofBivectorOneForm _ mu a

private theorem color_source_data (p : Fin 4→ℝ) (g : Fin 3) :
    sourceData (originalNullReal p (Fin.castAdd 6 g))=sourceData (nativeSourceColumn (Fin.castAdd 6 g) 1 p) := by
  apply Prod.ext
  · change fieldScalar _=fieldScalar _
    rw [original_null_scalar,native_scalar_zero]
  apply Prod.ext
  · funext mu
    change fieldGauge _ mu=fieldGauge _ mu
    rw [nativeSourceColumn,nonscalarRestriction_fieldGauge]
    simp only [nativeSourcePrimitive,Fin.addCases_left,colorPrimitiveDirection,LinearEquiv.apply_symm_apply]
    exact color_gauge_source p g mu
  apply Prod.ext
  · funext a mu
    change fieldCoframe (originalNullReal p (Fin.castAdd 6 g)) a mu=(nativeSourceColumn (Fin.castAdd 6 g) 1 p) (coframeSlot a mu)
    rw [source_null_color_coframe,nativeSourceColumn,nonscalarRestriction_coframe]
    simp only [nativeSourcePrimitive,Fin.addCases_left,colorPrimitiveDirection,Pi.zero_apply]
    rfl
  · funext mu a
    change fieldLorentz (originalNullReal p (Fin.castAdd 6 g)) mu a=(nativeSourceColumn (Fin.castAdd 6 g) 1 p) (lorentzSlot mu a)
    rw [source_null_color_lorentz,nativeSourceColumn,nonscalarRestriction_lorentz]
    simp [nativeSourcePrimitive,colorPrimitiveDirection,loweredLorentzConnectionCoefficient]

private theorem lorentz_source_data (p : Fin 4→ℝ) (a : Fin 6) :
    sourceData (originalNullReal p (Fin.natAdd 3 a))=sourceData (nativeSourceColumn (Fin.natAdd 3 a) 1 p) := by
  apply Prod.ext
  · change fieldScalar _=fieldScalar _
    rw [original_null_scalar,native_scalar_zero]
  apply Prod.ext
  · funext mu
    change fieldGauge _ mu=fieldGauge _ mu
    rw [nativeSourceColumn,nonscalarRestriction_fieldGauge]
    simp only [nativeSourcePrimitive,Fin.addCases_right,lorentzPrimitiveDirection,Pi.zero_apply,map_zero]
    simp only [fieldGauge,source_null_lorentz_gauge,zero_smul,Finset.sum_const_zero]
  apply Prod.ext
  · funext i mu
    change fieldCoframe (originalNullReal p (Fin.natAdd 3 a)) i mu=(nativeSourceColumn (Fin.natAdd 3 a) 1 p) (coframeSlot i mu)
    rw [lorentz_coframe_source,nativeSourceColumn,nonscalarRestriction_coframe]
    simp only [nativeSourcePrimitive,Fin.addCases_right,lorentzPrimitiveDirection,one_smul]
    rfl
  · funext mu b
    change fieldLorentz (originalNullReal p (Fin.natAdd 3 a)) mu b=(nativeSourceColumn (Fin.natAdd 3 a) 1 p) (lorentzSlot mu b)
    rw [lorentz_connection_source,nativeSourceColumn,nonscalarRestriction_lorentz]
    simp only [nativeSourcePrimitive,Fin.addCases_right,lorentzPrimitiveDirection,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,original_source_lorentz]

/-- All primary fields are restrictions of the same actual-reference primitive; the complete original column remains retained. -/
theorem original_null_sourceData (p : Fin 4→ℝ) (n : Fin 9) :
    sourceData (originalNullReal p n)=sourceData (nativeSourceColumn n 1 p) := by
  refine Fin.addCases (motive:=fun k : Fin 9=>
    sourceData (originalNullReal p k)=sourceData (nativeSourceColumn k 1 p))
    (fun g : Fin 3=>?_) (fun a : Fin 6=>?_) n
  · exact color_source_data p g
  · exact lorentz_source_data p a

/-- This is the original ActionState occurrence consumed by the full Noether reader and its contact. -/
theorem original_null_native_state (p : Fin 4→ℝ) (n : Fin 9) :
    fieldDirection (originalNullReal p n)=stateVariation n 1 p (sourceState sourcePoint.val) := by
  rw [←stateDirection_source,original_null_sourceData,stateDirection_source,nativeSourceColumn_state]

end LowEnergy.GaussComposite.ActualDressedNullNative
