import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoefficientWedgeActions
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrimitiveArrays

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCoefficientBudget
open SaturationMonoid.PhysicsCore
open PreparationVacuumPrimitiveMatrix PreparationVacuumSourceMatrixInverse PreparationVacuumSourceChartBudget
open PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineExteriorMotherLieRepresentation
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
open scoped BigOperators RealInnerProductSpace

private abbrev sourceMotherOrder : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective
local instance : LinearOrder SU7MotherIndex := sourceMotherOrder
local instance : LE SU7MotherIndex := sourceMotherOrder.toLE
local instance : LT SU7MotherIndex := sourceMotherOrder.toLT

open Lean Elab Term in
elab "scalar_lex_position%" : term => do
  let ns := Lean.Name.str (Lean.Name.str (Lean.Name.num `_private.H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarCoordinates 0) "LowEnergy") "PreparationScalarCoordinates"
  Lean.Meta.mkConstWithFreshMVarLevels (Lean.Name.str ns "lex_position")

theorem source_occupancy (i : Fin 35) (s : Fin 4) :
    occupancy (lexIndex i) s=smBlockIndexEquivFin7.symm (lexOrder i s) :=
  (scalar_lex_position%) i s

def numericSign (a : Fin 4→Fin 7) : ℤˣ :=
  ∏ p∈Equiv.Perm.finPairsLT 4,if a p.1≤a p.2 then -1 else 1

def numericWedgeCode (a : Fin 4→Fin 7) (output : Fin 35) : ℤ :=
  if Function.Injective a then
    if Finset.univ.image a=Finset.univ.image (lexOrder output) then (numericSign a : ℤ) else 0
  else 0

def fastWedgeCode (a : Fin 4→Fin 7) (output : Fin 35) : ℤ :=
  if Finset.univ.image a=Finset.univ.image (lexOrder output) then
    if Function.Injective a then (numericSign a : ℤ) else 0
  else 0

theorem fastWedgeCode_eq (a : Fin 4→Fin 7) (output : Fin 35) :
    fastWedgeCode a output=numericWedgeCode a output := by
  by_cases h : Function.Injective a <;>
    by_cases e : Finset.univ.image a=Finset.univ.image (lexOrder output) <;>
    simp only [fastWedgeCode,numericWedgeCode,h,e,if_true,if_false]

theorem sign_aux (p : Equiv.Perm (Fin 4)) : p.sign=Equiv.Perm.signAux p := by
  let hom : Equiv.Perm (Fin 4) →* ℤˣ := MonoidHom.mk' Equiv.Perm.signAux Equiv.Perm.signAux_mul
  have onto : Function.Surjective hom := by
    intro u
    rcases Int.units_eq_one_or u with h|h
    · subst u; exact ⟨1,Equiv.Perm.signAux_one 4⟩
    · subst u; exact ⟨Equiv.swap 0 1,Equiv.Perm.signAux_swap (x:=(0 : Fin 4)) (y:=1) (by decide)⟩
  have equal := Equiv.Perm.eq_sign_of_surjective_hom onto
  exact (congrArg (fun f : Equiv.Perm (Fin 4) →* ℤˣ => f p) equal).symm

theorem occupiedRank_order (a : Occupancy) (h : Function.Injective a) (i j : Fin 4) :
    occupiedRank a h i≤occupiedRank a h j ↔
      smBlockIndexEquivFin7 (a i)≤ smBlockIndexEquivFin7 (a j) := by
  exact ((occupiedIndex a h).val.orderIsoOfFin (occupiedIndex a h).prop).symm.le_iff_le

theorem occupiedSign_numeric (a : Fin 4→Fin 7) (h : Function.Injective (smBlockIndexEquivFin7.symm ∘ a)) :
    (occupiedPermutation (smBlockIndexEquivFin7.symm ∘ a) h).sign=numericSign a := by
  rw [sign_aux]
  unfold Equiv.Perm.signAux numericSign
  apply Finset.prod_congr rfl
  intro p hp
  change (if occupiedRank (smBlockIndexEquivFin7.symm ∘ a) h p.1≤
      occupiedRank (smBlockIndexEquivFin7.symm ∘ a) h p.2 then (-1 : ℤˣ) else 1)=_
  simp only [occupiedRank_order,Function.comp_apply,Equiv.apply_symm_apply]

theorem source_lex_image (i : Fin 35) :
    (lexIndex i).val=Finset.univ.image (smBlockIndexEquivFin7.symm ∘ lexOrder i) := by
  fin_cases i <;> decide +kernel

theorem occupiedIndex_numeric (a : Fin 4→Fin 7) (h : Function.Injective (smBlockIndexEquivFin7.symm ∘ a))
    (output : Fin 35) :
    occupiedIndex (smBlockIndexEquivFin7.symm ∘ a) h=lexIndex output ↔
      Finset.univ.image a=Finset.univ.image (lexOrder output) := by
  rw [Subtype.ext_iff,source_lex_image]
  change Finset.univ.image (smBlockIndexEquivFin7.symm ∘ a)=
    Finset.univ.image (smBlockIndexEquivFin7.symm ∘ lexOrder output) ↔ _
  rw [←Finset.image_image,←Finset.image_image]
  exact (Finset.image_injective smBlockIndexEquivFin7.symm.injective).eq_iff

/-- The native sorting/sign occurrence is read by six Fin7 comparisons; no sorting recursor is evaluated. -/
theorem numericWedgeCode_source (a : Fin 4→Fin 7) (output : Fin 35) :
    wedgeInteger (smBlockIndexEquivFin7.symm ∘ a) (lexIndex output)=numericWedgeCode a output := by
  by_cases h : Function.Injective a
  · have native := smBlockIndexEquivFin7.symm.injective.comp h
    simp only [wedgeInteger,dif_pos native,numericWedgeCode,if_pos h]
    simp only [occupiedIndex_numeric,occupiedSign_numeric]
  · have native : ¬Function.Injective (smBlockIndexEquivFin7.symm ∘ a) := by
      intro H
      apply h
      intro i j hij
      exact H (congrArg smBlockIndexEquivFin7.symm hij)
    simp only [wedgeInteger,dif_neg native,numericWedgeCode,if_neg h]

-- The first nine are the original broken columns, followed by the original stabilizer columns.
def nativeGenerator : Fin 12→NativeLie :=
  ![(sourceBroken 0).val,(sourceBroken 1).val,(sourceBroken 2).val,(sourceBroken 3).val,
    (sourceBroken 4).val,(sourceBroken 5).val,(sourceBroken 6).val,(sourceBroken 7).val,(sourceBroken 8).val,
    (sourceStabilizer 0).val,(sourceStabilizer 1).val,(sourceStabilizer 2).val]

def rawGenerator : Fin 12→Fin 12→ℚ :=
  ![Pi.single 2 1,Pi.single 3 1,Pi.single 4 1,Pi.single 5 1,
    Pi.single 6 (1/2)+Pi.single 7 (1/2),Pi.single 8 1,Pi.single 9 1,Pi.single 10 1,Pi.single 11 1,
    Pi.single 0 1,Pi.single 1 1,-Pi.single 6 1+Pi.single 7 1]

theorem nativeGenerator_raw (b : Fin 12) : rawCoordinates (nativeGenerator b)=(fun i => (rawGenerator b i : ℝ)) := by
  fin_cases b
  · change rawCoordinates (sourceBroken 0).val=_
    exact (sourceBroken_raw 0).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 1).val=_
    exact (sourceBroken_raw 1).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 2).val=_
    exact (sourceBroken_raw 2).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 3).val=_
    exact (sourceBroken_raw 3).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 4).val=_
    exact (sourceBroken_raw 4).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 5).val=_
    exact (sourceBroken_raw 5).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 6).val=_
    exact (sourceBroken_raw 6).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 7).val=_
    exact (sourceBroken_raw 7).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceBroken 8).val=_
    exact (sourceBroken_raw 8).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceStabilizer 0).val=_
    exact (sourceStabilizer_raw 0).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceStabilizer 1).val=_
    exact (sourceStabilizer_raw 1).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)
  · change rawCoordinates (sourceStabilizer 2).val=_
    exact (sourceStabilizer_raw 2).trans (by
      ext i
      fin_cases i <;> norm_num [rawBrokenColumn,rawGenerator,Pi.single_apply,Fin.ext_iff]
      all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
      all_goals norm_num)

def rawMotherReal (x : Fin 12→ℚ) : Matrix (Fin 7) (Fin 7) ℚ :=
  !![0,x 0,x 2,0,0,0,0;
     -x 0,0,x 4,0,0,0,0;
     -x 2,-x 4,0,0,0,0,0;
     0,0,0,0,x 8,0,0;
     0,0,0,-x 8,0,0,0;
     0,0,0,0,0,0,0;
     0,0,0,0,0,0,0]

def rawMotherImag (x : Fin 12→ℚ) : Matrix (Fin 7) (Fin 7) ℚ :=
  !![x 6,x 1,x 3,0,0,0,0;
     x 1,x 7,x 5,0,0,0,0;
     x 3,x 5,-(x 6+x 7),0,0,0,0;
     0,0,0,x 10,x 9,0,0;
     0,0,0,x 9,-x 10,0,0;
     0,0,0,0,0,x 11,0;
     0,0,0,0,0,0,-x 11]

def motherReal (b : Fin 12) : Matrix (Fin 7) (Fin 7) ℚ := rawMotherReal (rawGenerator b)
def motherImag (b : Fin 12) : Matrix (Fin 7) (Fin 7) ℚ := rawMotherImag (rawGenerator b)

def nativeMother (b : Fin 12) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (p286CoordinateEquiv.symm (nativeGenerator b))

theorem rawMother_entry (x : Fin 12→ℚ) (i j : Fin 7) :
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (rawCoordinates.symm (fun k => (x k : ℝ))))).val
      (smBlockIndexEquivFin7.symm i) (smBlockIndexEquivFin7.symm j)=
        (rawMotherReal x i j : ℂ)+(rawMotherImag x i j : ℂ)*Complex.I := by
  change rawP286LieBlock (p286CoordinateEquiv.symm (rawBuild (fun k => (x k : ℝ)))) _ _=_
  unfold rawBuild
  rw [scalar_source_const% "native_symm"]
  trans literalFundamental
    ![(x 0 : ℝ),(x 1 : ℝ),(x 2 : ℝ),(x 3 : ℝ),
      (x 4 : ℝ),(x 5 : ℝ),(x 6 : ℝ),
      (x 6 : ℝ)+(x 7 : ℝ)]
    ![(x 8 : ℝ),(x 9 : ℝ),(x 10 : ℝ)] (x 11 : ℝ) i j
  · exact (scalar_source_const% "native_entry") _ _ _ i j
  · fin_cases i <;> fin_cases j <;>
      norm_num [literalFundamental,rawMotherReal,rawMotherImag,Rat.cast_add,Rat.cast_neg]
    all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
    all_goals push_cast
    all_goals ring

theorem nativeMother_entry (b : Fin 12) (i j : Fin 7) :
    (nativeMother b).val (smBlockIndexEquivFin7.symm i) (smBlockIndexEquivFin7.symm j)=
      (motherReal b i j : ℂ)+(motherImag b i j : ℂ)*Complex.I := by
  have gen : nativeGenerator b=rawCoordinates.symm (fun k => (rawGenerator b k : ℝ)) := by
    apply rawCoordinates.injective
    simpa only [LinearEquiv.apply_symm_apply] using nativeGenerator_raw b
  unfold nativeMother
  rw [gen]
  exact rawMother_entry (rawGenerator b) i j

def sparseProduct (c : ℚ) (w : ℤ) : ℚ := if c=0 then 0 else c*(w : ℚ)

theorem sparseProduct_eq (c : ℚ) (w : ℤ) : sparseProduct c w=c*(w : ℚ) := by
  by_cases h : c=0 <;> simp [sparseProduct,h]

def denseExterior (imaginary : Bool) (b : Fin 12) (output input : Fin 35) : ℚ :=
  ∑ s : Fin 4,∑ j : Fin 7,
    sparseProduct (if imaginary then motherImag b j (lexOrder input s) else motherReal b j (lexOrder input s))
      (numericWedgeCode (Function.update (lexOrder input) s j) output)


def motherStep : Fin 12→Fin 7→Option (Fin 7×ℚ×ℚ) :=
  ![![some (2,-1,0),none,some (0,1,0),none,none,none,none],
    ![some (2,0,1),none,some (0,0,1),none,none,none,none],
    ![none,some (2,-1,0),some (1,1,0),none,none,none,none],
    ![none,some (2,0,1),some (1,0,1),none,none,none,none],
    ![some (0,0,1/2),some (1,0,1/2),some (2,0,-1),none,none,none,none],
    ![none,none,none,some (4,-1,0),some (3,1,0),none,none],
    ![none,none,none,some (4,0,1),some (3,0,1),none,none],
    ![none,none,none,some (3,0,1),some (4,0,-1),none,none],
    ![none,none,none,none,none,some (5,0,1),some (6,0,-1)],
    ![some (1,-1,0),some (0,1,0),none,none,none,none,none],
    ![some (1,0,1),some (0,0,1),none,none,none,none,none],
    ![some (0,0,-1),some (1,0,1),none,none,none,none,none]]

theorem motherStep_source : ∀ (b : Fin 12) (i j : Fin 7),
    motherReal b i j=(match motherStep b j with | none=>0 | some t=>if i=t.1 then t.2.1 else 0) ∧
    motherImag b i j=(match motherStep b j with | none=>0 | some t=>if i=t.1 then t.2.2 else 0) := by
  intro b i j
  fin_cases b <;>
    norm_num [motherReal,motherImag,rawMotherReal,rawMotherImag,rawGenerator,Pi.single_apply,Fin.ext_iff]
  all_goals fin_cases i <;> fin_cases j <;> norm_num [motherStep]


def rationalExterior (imaginary : Bool) (b : Fin 12) (output input : Fin 35) : ℚ :=
  ∑ s : Fin 4,match motherStep b (lexOrder input s) with
    | none=>0
    | some t=>sparseProduct (if imaginary then t.2.2 else t.2.1)
        (fastWedgeCode (Function.update (lexOrder input) s t.1) output)

theorem rationalExterior_dense (imaginary : Bool) (b : Fin 12) (output input : Fin 35) :
    rationalExterior imaginary b output input=denseExterior imaginary b output input := by
  unfold rationalExterior denseExterior
  simp_rw [fastWedgeCode_eq]
  apply Finset.sum_congr rfl
  intro s hs
  simp_rw [(motherStep_source b _ _).1,(motherStep_source b _ _).2]
  cases h : motherStep b (lexOrder input s) with
  | none=>simp [h,sparseProduct]
  | some t=>
    cases imaginary <;> simp [h,sparseProduct_eq,ite_mul]

def rationalRho (b : Fin 12) (i j : Fin 70) : ℚ :=
  Fin.addCases (m:=35) (n:=35) (motive:=fun _=>ℚ)
    (fun r => Fin.addCases (m:=35) (n:=35) (motive:=fun _=>ℚ)
      (fun c => rationalExterior false b r c) (fun c => -rationalExterior true b r c) j)
    (fun r => Fin.addCases (m:=35) (n:=35) (motive:=fun _=>ℚ)
      (fun c => rationalExterior true b r c) (fun c => rationalExterior false b r c) j) i

theorem exteriorEntry_rational (b : Fin 12) (i j : Fin 35) :
    exteriorEntry (nativeMother b).val (lexIndex i) (lexIndex j)=
      (rationalExterior false b i j : ℂ)+(rationalExterior true b i j : ℂ)*Complex.I := by
  have wedge (s : Fin 4) (t : Fin 7) :
      wedgeInteger (Function.update (occupancy (lexIndex j)) s (smBlockIndexEquivFin7.symm t)) (lexIndex i)=
        numericWedgeCode (Function.update (lexOrder j) s t) i := by
    have family : Function.update (occupancy (lexIndex j)) s (smBlockIndexEquivFin7.symm t)=
        smBlockIndexEquivFin7.symm ∘ Function.update (lexOrder j) s t := by
      funext k
      by_cases hk : k=s <;> simp [hk,Function.update,source_occupancy]
    rw [family,numericWedgeCode_source]
  rw [rationalExterior_dense,rationalExterior_dense]
  unfold exteriorEntry denseExterior
  simp only [Bool.false_eq_true,ite_false,ite_true,sparseProduct_eq]
  simp_rw [← smBlockIndexEquivFin7.symm.sum_comp]
  have entry (s : Fin 4) (t : Fin 7) :
      (nativeMother b).val (smBlockIndexEquivFin7.symm t) (occupancy (lexIndex j) s)=
        (motherReal b t (smBlockIndexEquivFin7 (occupancy (lexIndex j) s)) : ℂ)+
        (motherImag b t (smBlockIndexEquivFin7 (occupancy (lexIndex j) s)) : ℂ)*Complex.I := by
    simpa only [Equiv.symm_apply_apply] using nativeMother_entry b t (smBlockIndexEquivFin7 (occupancy (lexIndex j) s))
  simp_rw [entry,wedge,source_occupancy]
  simp only [Equiv.apply_symm_apply]
  push_cast
  simp only [add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro s hs <;> apply Finset.sum_congr rfl <;> intro t ht <;> ring


theorem scalarUnit_real_lex (j k : Fin 35) :
    scalarUnit (realSlot j) (lexIndex k)=if k=j then 1 else 0 := by
  have cross : imagSlot k≠realSlot j := by
    intro h
    have hv:=congrArg Fin.val h
    dsimp [imagSlot,realSlot] at hv
    omega
  have same : realSlot k=realSlot j ↔ k=j := by simp [realSlot,Fin.ext_iff]
  change scalarBuild (Pi.single (realSlot j) 1) (lexIndex k)=_
  rw [scalar_build_lex]
  by_cases h : k=j
  · subst k; simp [Pi.single_apply,cross]
  · simp [Pi.single_apply,cross,same,h]

theorem scalarUnit_imag_lex (j k : Fin 35) :
    scalarUnit (imagSlot j) (lexIndex k)=if k=j then Complex.I else 0 := by
  have cross : realSlot k≠imagSlot j := by
    intro h
    have hv:=congrArg Fin.val h
    dsimp [imagSlot,realSlot] at hv
    omega
  have same : imagSlot k=imagSlot j ↔ k=j := by simp [imagSlot,Fin.ext_iff]
  change scalarBuild (Pi.single (imagSlot j) 1) (lexIndex k)=_
  rw [scalar_build_lex]
  by_cases h : k=j
  · subst k; simp [Pi.single_apply,cross]
  · simp [Pi.single_apply,cross,same,h]

theorem action_unit_real (b : Fin 12) (i j : Fin 35) :
    action (scalarUnit (realSlot j)) (nativeGenerator b) (lexIndex i)=
      exteriorEntry (nativeMother b).val (lexIndex i) (lexIndex j) := by
  change scalarMotherLieAction (nativeMother b) (scalarUnit (realSlot j)) (lexIndex i)=_
  rw [scalarMotherLieAction_source,←lex_bijective.sum_comp]
  simp_rw [scalarUnit_real_lex]
  simp

theorem action_unit_imag (b : Fin 12) (i j : Fin 35) :
    action (scalarUnit (imagSlot j)) (nativeGenerator b) (lexIndex i)=
      exteriorEntry (nativeMother b).val (lexIndex i) (lexIndex j)*Complex.I := by
  change scalarMotherLieAction (nativeMother b) (scalarUnit (imagSlot j)) (lexIndex i)=_
  rw [scalarMotherLieAction_source,←lex_bijective.sum_comp]
  simp_rw [scalarUnit_imag_lex]
  simp

def nativeRho (b : Fin 12) (i j : Fin 70) : ℝ :=
  scalarRealify (action (scalarUnit j) (nativeGenerator b)) i

theorem rationalRho_source (b : Fin 12) (i j : Fin 70) : (rationalRho b i j : ℝ)=nativeRho b i j := by
  refine Fin.addCases (m:=35) (n:=35) (fun r => ?_) (fun r => ?_) i
  · refine Fin.addCases (m:=35) (n:=35) (fun c => ?_) (fun c => ?_) j
    · simp only [rationalRho,Fin.addCases_left]
      change (rationalExterior false b r c : ℝ)=scalarRead (action (scalarUnit (realSlot c)) (nativeGenerator b)) (realSlot r)
      rw [scalar_read_real,action_unit_real,exteriorEntry_rational]
      simp
    · simp only [rationalRho,Fin.addCases_left,Fin.addCases_right]
      change ((-rationalExterior true b r c : ℚ) : ℝ)=scalarRead (action (scalarUnit (imagSlot c)) (nativeGenerator b)) (realSlot r)
      rw [scalar_read_real,action_unit_imag,exteriorEntry_rational]
      simp
  · refine Fin.addCases (m:=35) (n:=35) (fun c => ?_) (fun c => ?_) j
    · simp only [rationalRho,Fin.addCases_right,Fin.addCases_left]
      change (rationalExterior true b r c : ℝ)=scalarRead (action (scalarUnit (realSlot c)) (nativeGenerator b)) (imagSlot r)
      rw [scalar_read_imag,action_unit_real,exteriorEntry_rational]
      simp
    · simp only [rationalRho,Fin.addCases_right]
      change (rationalExterior false b r c : ℝ)=scalarRead (action (scalarUnit (imagSlot c)) (nativeGenerator b)) (imagSlot r)
      rw [scalar_read_imag,action_unit_imag,exteriorEntry_rational]
      simp

def scalarColumns : Fin 61→List (Fin 70×ℚ) :=
  ![[(0,(1/2 : ℚ)),(5,(-1/2 : ℚ))],
    [(1,(1 : ℚ))],
    [(2,(1 : ℚ))],
    [(3,(1 : ℚ))],
    [(4,(1 : ℚ))],
    [(6,(1 : ℚ))],
    [(7,(1 : ℚ))],
    [(8,(1 : ℚ))],
    [(9,(1 : ℚ))],
    [(10,(1 : ℚ))],
    [(11,(1 : ℚ))],
    [(12,(1 : ℚ))],
    [(13,(1/2 : ℚ)),(15,(-1/2 : ℚ))],
    [(14,(1 : ℚ))],
    [(16,(1 : ℚ))],
    [(17,(1 : ℚ))],
    [(18,(1 : ℚ))],
    [(19,(1 : ℚ))],
    [(20,(1 : ℚ))],
    [(21,(1 : ℚ))],
    [(22,(1 : ℚ))],
    [(23,(1/2 : ℚ)),(25,(-1/2 : ℚ))],
    [(24,(1 : ℚ))],
    [(26,(1 : ℚ))],
    [(27,(1 : ℚ))],
    [(28,(1 : ℚ))],
    [(29,(1 : ℚ))],
    [(30,(1 : ℚ))],
    [(31,(1 : ℚ))],
    [(32,(1 : ℚ))],
    [(33,(1 : ℚ))],
    [(34,(1 : ℚ))],
    [(35,(1/2 : ℚ)),(40,(-1/2 : ℚ))],
    [(36,(1/4 : ℚ)),(38,(-1/4 : ℚ)),(42,(-1/4 : ℚ)),(44,(1/4 : ℚ))],
    [(37,(1 : ℚ))],
    [(39,(1 : ℚ))],
    [(41,(1 : ℚ))],
    [(43,(1 : ℚ))],
    [(45,(1 : ℚ))],
    [(46,(1 : ℚ))],
    [(47,(1 : ℚ))],
    [(48,(1/2 : ℚ)),(50,(-1/2 : ℚ))],
    [(49,(1 : ℚ))],
    [(51,(1 : ℚ))],
    [(52,(1 : ℚ))],
    [(53,(1 : ℚ))],
    [(54,(1 : ℚ))],
    [(55,(1 : ℚ))],
    [(56,(1 : ℚ))],
    [(57,(1 : ℚ))],
    [(58,(1/2 : ℚ)),(60,(-1/2 : ℚ))],
    [(59,(1 : ℚ))],
    [(61,(1 : ℚ))],
    [(62,(1 : ℚ))],
    [(63,(1 : ℚ))],
    [(64,(1 : ℚ))],
    [(65,(1 : ℚ))],
    [(66,(1 : ℚ))],
    [(67,(1 : ℚ))],
    [(68,(1 : ℚ))],
    [(69,(1 : ℚ))]]

def dualColumns : Fin 61→List (Fin 70×ℚ) :=
  ![[(0,(1 : ℚ)),(5,(-1 : ℚ))],
    [(1,(1 : ℚ))],
    [(2,(1 : ℚ))],
    [(3,(1 : ℚ))],
    [(4,(1 : ℚ))],
    [(6,(1 : ℚ))],
    [(7,(1 : ℚ))],
    [(8,(1 : ℚ))],
    [(9,(1 : ℚ))],
    [(10,(1 : ℚ))],
    [(11,(1 : ℚ))],
    [(12,(1 : ℚ))],
    [(13,(1 : ℚ)),(15,(-1 : ℚ))],
    [(14,(1 : ℚ))],
    [(16,(1 : ℚ))],
    [(17,(1 : ℚ))],
    [(18,(1 : ℚ))],
    [(19,(1 : ℚ))],
    [(20,(1 : ℚ))],
    [(21,(1 : ℚ))],
    [(22,(1 : ℚ))],
    [(23,(1 : ℚ)),(25,(-1 : ℚ))],
    [(24,(1 : ℚ))],
    [(26,(1 : ℚ))],
    [(27,(1 : ℚ))],
    [(28,(1 : ℚ))],
    [(29,(1 : ℚ))],
    [(30,(1 : ℚ))],
    [(31,(1 : ℚ))],
    [(32,(1 : ℚ))],
    [(33,(1 : ℚ))],
    [(34,(1 : ℚ))],
    [(35,(1 : ℚ)),(40,(-1 : ℚ))],
    [(36,(1 : ℚ)),(38,(-1 : ℚ)),(42,(-1 : ℚ)),(44,(1 : ℚ))],
    [(37,(1 : ℚ))],
    [(39,(1 : ℚ))],
    [(41,(1 : ℚ))],
    [(43,(1 : ℚ))],
    [(45,(1 : ℚ))],
    [(46,(1 : ℚ))],
    [(47,(1 : ℚ))],
    [(48,(1 : ℚ)),(50,(-1 : ℚ))],
    [(49,(1 : ℚ))],
    [(51,(1 : ℚ))],
    [(52,(1 : ℚ))],
    [(53,(1 : ℚ))],
    [(54,(1 : ℚ))],
    [(55,(1 : ℚ))],
    [(56,(1 : ℚ))],
    [(57,(1 : ℚ))],
    [(58,(1 : ℚ)),(60,(-1 : ℚ))],
    [(59,(1 : ℚ))],
    [(61,(1 : ℚ))],
    [(62,(1 : ℚ))],
    [(63,(1 : ℚ))],
    [(64,(1 : ℚ))],
    [(65,(1 : ℚ))],
    [(66,(1 : ℚ))],
    [(67,(1 : ℚ))],
    [(68,(1 : ℚ))],
    [(69,(1 : ℚ))]]

def columnEntry (column : List (Fin 70×ℚ)) (i : Fin 70) : ℚ :=
  (column.map (fun p => if p.1=i then p.2 else 0)).sum

def columnValue (column : List (Fin 70×ℚ)) (v : Fin 70→ℝ) : ℝ :=
  (column.map (fun p => (p.2 : ℝ)*v p.1)).sum

theorem scalarColumns_code (i : Fin 70) (j : Fin 61) :
    rationalR i j=columnEntry (scalarColumns j) i := by
  revert i j
  decide +kernel

theorem dualColumns_read (v : Fin 70→ℝ) (j : Fin 61) :
    read61 v j=columnValue (dualColumns j) v := by
  fin_cases j <;> norm_num [read61,dualColumns,columnValue]
  all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

theorem columnValue_unit (column : List (Fin 70×ℚ)) (i : Fin 70) :
    columnValue column (Pi.single i 1)=(columnEntry column i : ℝ) := by
  induction column with
  | nil => simp [columnValue,columnEntry]
  | cons a column ih =>
    simp only [columnValue,columnEntry,List.map_cons,List.sum_cons,Rat.cast_add]
    change (a.2 : ℝ)*(Pi.single i 1 : Fin 70→ℝ) a.1+columnValue column (Pi.single i 1)=
      ((if a.1=i then a.2 else 0 : ℚ) : ℝ)+(columnEntry column i : ℝ)
    rw [ih]
    by_cases h : a.1=i <;> simp [Pi.single_apply,h]

def rationalCompressed (b : Fin 12) (i j : Fin 61) : ℚ :=
  ((dualColumns i).map (fun u => ((scalarColumns j).map (fun v =>
    u.2*rationalRho b u.1 v.1*v.2)).sum)).sum

-- These match the original matrix_norm_upper arrays; all statements still require source readback below.
def brokenNorms : Fin 9→ℚ := ![3,3,3,3,2,2,2,2,2]
def stabilizerNorms : Fin 3→ℚ := ![4,4,2]


theorem scalarRealify_list_sum (vs : List Scalar) (i : Fin 70) :
    scalarRealify vs.sum i=(vs.map (fun v => scalarRealify v i)).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simpa only [List.sum_cons,List.map_cons,map_add,Pi.add_apply] using congrArg (scalarRealify v i+·) ih

theorem scalarFree_unit_expansion (j : Fin 61) :
    (scalarFree.symm (Pi.single j 1)).val=
      ((scalarColumns j).map (fun p => (p.2 : ℝ) • scalarUnit p.1)).sum := by
  apply scalarRealify.injective
  ext i
  rw [decode_original_scalar,scalarRealify_list_sum]
  change sourceR i j=_
  rw [←rationalR_cast,scalarColumns_code,←columnValue_unit]
  simp only [columnValue,List.map_map,map_smul,Pi.smul_apply,smul_eq_mul,scalarUnit_read]
  congr 1
  apply List.map_congr_left
  intro p hp
  change (p.2 : ℝ)*(Pi.single i 1 : Fin 70→ℝ) p.1=scalarRealify ((p.2 : ℝ) • scalarUnit p.1) i
  have scaled := congrFun (scalarRealify.map_smul (p.2 : ℝ) (scalarUnit p.1)) i
  change scalarRealify ((p.2 : ℝ) • scalarUnit p.1) i=(p.2 : ℝ)*scalarRealify (scalarUnit p.1) i at scaled
  rw [scaled,congrFun (scalarUnit_read p.1) i]
  simp [Pi.single_apply,eq_comm]

def scalarReader (b : Fin 12) (i : Fin 70) : Scalar →ₗ[ℝ] ℝ :=
  ((LinearMap.proj i).comp scalarRealify.toLinearMap).comp
    (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (nativeGenerator b))

theorem scalarReader_unit (b : Fin 12) (i j : Fin 70) :
    scalarReader b i (scalarUnit j)=nativeRho b i j := rfl

theorem action_scalarFree_unit (b : Fin 12) (i : Fin 70) (j : Fin 61) :
    scalarRealify (action (scalarFree.symm (Pi.single j 1)).val (nativeGenerator b)) i=
      ((scalarColumns j).map (fun v => (v.2 : ℝ)*nativeRho b i v.1)).sum := by
  change scalarReader b i (scalarFree.symm (Pi.single j 1)).val=_
  rw [scalarFree_unit_expansion,map_list_sum]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  change scalarReader b i ((v.2 : ℝ) • scalarUnit v.1)=(v.2 : ℝ)*nativeRho b i v.1
  rw [map_smul]
  rfl

def nativeCompressed (b : Fin 12) (i j : Fin 61) : ℝ :=
  read61 (scalarRealify (action (scalarFree.symm (Pi.single j 1)).val (nativeGenerator b))) i

theorem rationalCompressed_source (b : Fin 12) (i j : Fin 61) :
    (rationalCompressed b i j : ℝ)=nativeCompressed b i j := by
  unfold nativeCompressed
  rw [dualColumns_read]
  unfold columnValue rationalCompressed
  simp_rw [action_scalarFree_unit]
  push_cast
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro u hu
  dsimp only [Function.comp_apply]
  push_cast
  rw [←List.sum_map_mul_left]
  simp only [List.map_map,Function.comp_apply]
  congr 1
  apply List.map_congr_left
  intro v hv
  change ((u.2*rationalRho b u.1 v.1*v.2 : ℚ) : ℝ)=
    (u.2 : ℝ)*((v.2 : ℝ)*nativeRho b u.1 v.1)
  push_cast
  rw [rationalRho_source]
  ring


open SU7MotherGaugeTheory StageNineCoframeGravityGaugeRegularity

def nativeMatrix (a : NativeLie) : Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  (p286LieBlockEmbed (p286CoordinateEquiv.symm a)).val

def rawOfMatrix (M : Matrix SU7MotherIndex SU7MotherIndex ℂ) : Fin 12→ℝ :=
  let read (i j : Fin 7):=M (smBlockIndexEquivFin7.symm i) (smBlockIndexEquivFin7.symm j)
  ![(read 0 1).re,(read 0 1).im,(read 0 2).re,(read 0 2).im,
    (read 1 2).re,(read 1 2).im,(read 0 0).im,-(read 2 2).im-(read 0 0).im,
    (read 3 4).re,(read 3 4).im,(read 3 3).im,(read 5 5).im]

theorem nativeMatrix_raw (a : NativeLie) : rawCoordinates a=rawOfMatrix (nativeMatrix a) := by
  have coordinates:=nativeCoordinates_apply (p286CoordinateEquiv.symm a)
  rw [p286CoordinateEquiv.apply_symm_apply] at coordinates
  change rawRead a=_
  unfold rawRead
  rw [coordinates]
  ext i
  fin_cases i <;> rfl

theorem nativeMatrix_bracket (a b : NativeLie) :
    nativeMatrix (jointP286CoordinateLieBracket a b)=nativeMatrix a*nativeMatrix b-nativeMatrix b*nativeMatrix a := by
  unfold nativeMatrix jointP286CoordinateLieBracket
  rw [p286CoordinateEquiv.symm_apply_apply,p286LieBlockEmbed_bracket]
  rfl

theorem raw_bracket_matrix (a b : NativeLie) :
    rawCoordinates (jointP286CoordinateLieBracket a b)=
      rawOfMatrix (nativeMatrix a*nativeMatrix b-nativeMatrix b*nativeMatrix a) := by
  rw [nativeMatrix_raw,nativeMatrix_bracket]

def bracketReal (b : Fin 12) (k i j : Fin 7) (x : Fin 12→ℚ) : ℚ :=
  motherReal b i k*rawMotherReal x k j-motherImag b i k*rawMotherImag x k j-
    rawMotherReal x i k*motherReal b k j+rawMotherImag x i k*motherImag b k j

def bracketImag (b : Fin 12) (k i j : Fin 7) (x : Fin 12→ℚ) : ℚ :=
  motherReal b i k*rawMotherImag x k j+motherImag b i k*rawMotherReal x k j-
    rawMotherReal x i k*motherImag b k j-rawMotherImag x i k*motherReal b k j

def rationalRawRead (re im : Matrix (Fin 7) (Fin 7) ℚ) : Fin 12→ℚ :=
  ![re 0 1,im 0 1,re 0 2,im 0 2,re 1 2,im 1 2,im 0 0,-im 2 2-im 0 0,
    re 3 4,im 3 4,im 3 3,im 5 5]

def denseAd (b : Fin 12) (i j : Fin 12) : ℚ :=
  rationalRawRead (fun r c=>∑ k,bracketReal b k r c (Pi.single j 1))
    (fun r c=>∑ k,bracketImag b k r c (Pi.single j 1)) i

def nativeAd (b : Fin 12) (i j : Fin 12) : ℝ :=
  rawCoordinates (jointP286CoordinateLieBracket (nativeGenerator b)
    (rawCoordinates.symm (Pi.single j 1))) i

theorem raw_commutator_entry (b : Fin 12) (x : Fin 12→ℚ) (i j : Fin 7) :
    (nativeMatrix (nativeGenerator b)*nativeMatrix (rawCoordinates.symm (fun k=>(x k : ℝ)))-
      nativeMatrix (rawCoordinates.symm (fun k=>(x k : ℝ)))*nativeMatrix (nativeGenerator b))
      (smBlockIndexEquivFin7.symm i) (smBlockIndexEquivFin7.symm j)=
      ((∑ k,bracketReal b k i j x : ℚ) : ℂ)+((∑ k,bracketImag b k i j x : ℚ) : ℂ)*Complex.I := by
  simp only [Matrix.sub_apply,Matrix.mul_apply]
  rw [← Finset.sum_sub_distrib]
  rw [←smBlockIndexEquivFin7.symm.sum_comp]
  have nentry (r c : Fin 7) :
      nativeMatrix (nativeGenerator b) (smBlockIndexEquivFin7.symm r) (smBlockIndexEquivFin7.symm c)=
        (motherReal b r c : ℂ)+(motherImag b r c : ℂ)*Complex.I := nativeMother_entry b r c
  simp_rw [nentry]
  simp only [nativeMatrix,rawMother_entry]
  push_cast
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [bracketReal,bracketImag]
  push_cast
  ring_nf
  simp
  ring

theorem denseAd_source (b : Fin 12) (i j : Fin 12) :
    (denseAd b i j : ℝ)=nativeAd b i j := by
  have unit : (Pi.single j 1 : Fin 12→ℝ)=fun k=>((Pi.single j 1 : Fin 12→ℚ) k : ℝ) := by
    ext k
    by_cases h : k=j <;> simp [Pi.single_apply,h]
  unfold nativeAd
  rw [raw_bracket_matrix,unit]
  unfold rawOfMatrix
  simp only [raw_commutator_entry]
  fin_cases i <;>
    norm_num [denseAd,rationalRawRead,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]



def rawUnitStep : Fin 12→Fin 7→Option (Fin 7×ℚ×ℚ) :=
  ![![some (1,-1,0),some (0,1,0),none,none,none,none,none],
    ![some (1,0,1),some (0,0,1),none,none,none,none,none],
    ![some (2,-1,0),none,some (0,1,0),none,none,none,none],
    ![some (2,0,1),none,some (0,0,1),none,none,none,none],
    ![none,some (2,-1,0),some (1,1,0),none,none,none,none],
    ![none,some (2,0,1),some (1,0,1),none,none,none,none],
    ![some (0,0,1),none,some (2,0,-1),none,none,none,none],
    ![none,some (1,0,1),some (2,0,-1),none,none,none,none],
    ![none,none,none,some (4,-1,0),some (3,1,0),none,none],
    ![none,none,none,some (4,0,1),some (3,0,1),none,none],
    ![none,none,none,some (3,0,1),some (4,0,-1),none,none],
    ![none,none,none,none,none,some (5,0,1),some (6,0,-1)]]

def stepReal (a : Fin 7→Option (Fin 7×ℚ×ℚ)) (i j : Fin 7) : ℚ :=
  match a j with
  | none => 0
  | some t => if i=t.1 then t.2.1 else 0
def stepImag (a : Fin 7→Option (Fin 7×ℚ×ℚ)) (i j : Fin 7) : ℚ :=
  match a j with
  | none => 0
  | some t => if i=t.1 then t.2.2 else 0

theorem rawUnitStep_source : ∀ (b : Fin 12) (i j : Fin 7),
    rawMotherReal (Pi.single b 1) i j=stepReal (rawUnitStep b) i j ∧
    rawMotherImag (Pi.single b 1) i j=stepImag (rawUnitStep b) i j := by
  intro b i j
  fin_cases b <;>
    norm_num [rawMotherReal,rawMotherImag,Pi.single_apply,Fin.ext_iff]
  all_goals fin_cases i <;> fin_cases j <;> norm_num [rawUnitStep,stepReal,stepImag,Fin.ext_iff]

def stepProduct (a c : Fin 7→Option (Fin 7×ℚ×ℚ)) (i j : Fin 7) : ℚ×ℚ :=
  match c j with
  |none=>(0,0)
  |some t=>match a t.1 with
    |none=>(0,0)
    |some u=>if i=u.1 then (u.2.1*t.2.1-u.2.2*t.2.2,u.2.1*t.2.2+u.2.2*t.2.1) else (0,0)

theorem stepProduct_real (a c : Fin 7→Option (Fin 7×ℚ×ℚ)) (i j : Fin 7) :
    (stepProduct a c i j).1=∑ k,(stepReal a i k*stepReal c k j-stepImag a i k*stepImag c k j) := by
  cases hc:c j with
  |none=>simp [stepProduct,stepReal,stepImag,hc]
  |some t=>
    simp only [stepProduct,hc,stepReal,stepImag]
    simp only [mul_ite,mul_zero,ite_sub_ite,sub_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    cases ha:a t.1 with
    |none=>simp [ha]
    |some u=>by_cases h : i=u.1 <;> simp [ha,h]

theorem stepProduct_imag (a c : Fin 7→Option (Fin 7×ℚ×ℚ)) (i j : Fin 7) :
    (stepProduct a c i j).2=∑ k,(stepReal a i k*stepImag c k j+stepImag a i k*stepReal c k j) := by
  cases hc:c j with
  |none=>simp [stepProduct,stepReal,stepImag,hc]
  |some t=>
    simp only [stepProduct,hc,stepReal,stepImag]
    simp only [mul_ite,mul_zero,ite_add_ite,add_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    cases ha:a t.1 with
    |none=>simp [ha]
    |some u=>by_cases h : i=u.1 <;> simp [ha,h]

def rationalAd (b : Fin 12) (i j : Fin 12) : ℚ :=
  rationalRawRead
    (fun r c=>(stepProduct (motherStep b) (rawUnitStep j) r c).1-
      (stepProduct (rawUnitStep j) (motherStep b) r c).1)
    (fun r c=>(stepProduct (motherStep b) (rawUnitStep j) r c).2-
      (stepProduct (rawUnitStep j) (motherStep b) r c).2) i

theorem rationalAd_dense (b : Fin 12) (i j : Fin 12) : rationalAd b i j=denseAd b i j := by
  have realEq (r c : Fin 7) :
      (stepProduct (motherStep b) (rawUnitStep j) r c).1-
        (stepProduct (rawUnitStep j) (motherStep b) r c).1=
      ∑ k,bracketReal b k r c (Pi.single j 1) := by
    rw [stepProduct_real,stepProduct_real,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [bracketReal,(rawUnitStep_source j _ _).1,(rawUnitStep_source j _ _).2,
      (motherStep_source b _ _).1,(motherStep_source b _ _).2,stepReal,stepImag]
    ring
  have imagEq (r c : Fin 7) :
      (stepProduct (motherStep b) (rawUnitStep j) r c).2-
        (stepProduct (rawUnitStep j) (motherStep b) r c).2=
      ∑ k,bracketImag b k r c (Pi.single j 1) := by
    rw [stepProduct_imag,stepProduct_imag,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [bracketImag,(rawUnitStep_source j _ _).1,(rawUnitStep_source j _ _).2,
      (motherStep_source b _ _).1,(motherStep_source b _ _).2,stepReal,stepImag]
    ring
  simp only [rationalAd,denseAd,realEq,imagEq]

theorem rationalAd_source (b : Fin 12) (i j : Fin 12) : (rationalAd b i j : ℝ)=nativeAd b i j := by
  rw [rationalAd_dense]
  exact denseAd_source b i j


def generatorNorms : Fin 12→ℚ := ![3,3,3,3,2,2,2,2,2,4,4,2]

theorem rationalAd_bounds : ∀ (b : Fin 12) (j : Fin 12),
    (∑ i,|rationalAd b i j|)≤generatorNorms b := by
  intro b j
  fin_cases b <;> fin_cases j <;> decide +kernel



theorem rationalCompressed_bounds : ∀ (b : Fin 12) (j : Fin 61),
    (∑ i,|rationalCompressed b i j|)≤generatorNorms b := by
  intro b j
  fin_cases b <;> fin_cases j <;> decide +kernel



theorem nativeAd_column_bound (b j : Fin 12) :
    (∑ i,|nativeAd b i j|)≤(generatorNorms b : ℝ) := by
  simp_rw [←rationalAd_source]
  exact_mod_cast rationalAd_bounds b j

theorem nativeCompressed_column_bound (b : Fin 12) (j : Fin 61) :
    (∑ i,|nativeCompressed b i j|)≤(generatorNorms b : ℝ) := by
  simp_rw [←rationalCompressed_source]
  exact_mod_cast rationalCompressed_bounds b j

end LowEnergy.PreparationVacuumCoefficientBudget
