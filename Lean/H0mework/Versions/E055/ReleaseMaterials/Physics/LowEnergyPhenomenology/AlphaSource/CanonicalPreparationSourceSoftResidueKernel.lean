import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualNativePole

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumSoftPoleSelection
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open CanonicalGradedSpatialSource Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

/-- These coefficients are obtained from the source time-kinetic derivatives on the two actual sheets. -/
def softCoefficient (branch : Fin 2) : ℝ:=
  if branch=0 then -(99/(10*sourceRoot)) else -(27/(20*sourceRoot))

def leadingResidue (branch : Fin 2) (n : PhysicalMomentum) : Matrix (Fin 5) (Fin 5) ℂ:=
  (physicalSlope 0 (sourceSpeed branch) n:ℂ)⁻¹ • (characteristicTensor (sourceSpeed branch) n).adjugate

theorem sourceResidue_soft_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>sourceResidue e.val (sourceSheet branch n unit e.val) n)
      scaleApproach (𝓝 (leadingResidue branch n)):=by
  have trajectory : Tendsto (fun e : scaleDomain=>(e.val,sourceSheet branch n unit e.val)) scaleApproach (𝓝 (0,sourceSpeed branch)):=
    scaleVal_tendsto.prodMk_nhds ((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto)
  have slope := (physicalSlope_continuous_origin (sourceSpeed branch) n).tendsto.comp trajectory
  have scalar := (Complex.continuous_ofReal.tendsto (physicalSlope 0 (sourceSpeed branch) n)).comp slope
  have inverse:=scalar.inv₀ (Complex.ofReal_ne_zero.mpr (sourceSpeed_simple branch n unit))
  have matrix := (extendedTensor_smooth (sourceSpeed branch) n).continuousAt.tendsto.comp trajectory
  have adjugate := continuous_id.matrix_adjugate.continuousAt.tendsto.comp matrix
  simpa only [Function.comp_apply,extendedTensor_origin,id_eq,sourceResidue,leadingResidue] using inverse.smul adjugate

private def sourceA (s : ℝ) (n : PhysicalMomentum) :=sourceRoot*((25/18:ℝ)*s^2+(25/54:ℝ)*spatialSquare n)
private def sourceB (s : ℝ) (n : PhysicalMomentum) :=sourceRoot*(-(10/99:ℝ)*s^2+(12/335:ℝ)*spatialSquare n)
private def sourceC (s : ℝ) (n : PhysicalMomentum) :=sourceRoot*(-(20/27:ℝ)*s^2+(8/15:ℝ)*spatialSquare n)

private def sourceDerivative (s : ℝ) (n : PhysicalMomentum) : ℝ:=
  (((-256*s)*sourceA s n+(-128*s^2)*(sourceRoot*((25/9:ℝ)*s)))*sourceB s n+
    (-128*s^2)*sourceA s n*(sourceRoot*(-(20/99:ℝ)*s)))*sourceC s n+
      (-128*s^2)*sourceA s n*sourceB s n*(sourceRoot*(-(40/27:ℝ)*s))

private theorem quadratic_derivative (a b s : ℝ) :
    HasDerivAt (fun x : ℝ=>sourceRoot*(a*x^2+b)) (sourceRoot*(2*a*s)) s:=by
  have h:=(hasDerivAt_const s sourceRoot).mul
    (((hasDerivAt_const s a).mul ((hasDerivAt_id s).pow 2)).add (hasDerivAt_const s b))
  exact h.congr_deriv (by dsimp;ring)

private theorem sourceDet_derivative (s : ℝ) (n : PhysicalMomentum) :
    HasDerivAt (fun x=>characteristicDeterminant x n) (sourceDerivative s n) s:=by
  have a : HasDerivAt (fun x=>sourceA x n) (sourceRoot*((25/9:ℝ)*s)) s:=by
    simpa only [sourceA,show (2:ℝ)*(25/18)=25/9 by norm_num] using quadratic_derivative (25/18) ((25/54)*spatialSquare n) s
  have b : HasDerivAt (fun x=>sourceB x n) (sourceRoot*(-(20/99:ℝ)*s)) s:=by
    simpa only [sourceB,show (2:ℝ)*(-(10/99))=-(20/99) by norm_num] using quadratic_derivative (-(10/99)) ((12/335)*spatialSquare n) s
  have c : HasDerivAt (fun x=>sourceC x n) (sourceRoot*(-(40/27:ℝ)*s)) s:=by
    simpa only [sourceC,show (2:ℝ)*(-(20/27))=-(40/27) by norm_num] using quadratic_derivative (-(20/27)) ((8/15)*spatialSquare n) s
  have h:=(((hasDerivAt_const s (-128:ℝ)).mul ((hasDerivAt_id s).pow 2)).mul a).mul b |>.mul c
  exact h.congr_deriv (by dsimp;unfold sourceDerivative;ring)

private theorem sparse_five_det (a b c d : ℂ) :
    (Matrix.diagonal (![a,b,c,0,0] : Fin 5→ℂ)+Matrix.single 3 4 d+Matrix.single 4 3 (-d)).det=a*b*c*d^2:=by
  let M : Matrix (Fin 5) (Fin 5) ℂ:=Matrix.diagonal ![a,b,c,0,0]+Matrix.single 3 4 d+Matrix.single 4 3 (-d)
  have diagonal : M.submatrix id (Equiv.swap (3:Fin 5) 4)=Matrix.diagonal ![a,b,c,d,-d]:=by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M,Matrix.submatrix_apply,Matrix.diagonal_apply,Matrix.single_apply,Matrix.add_apply,Equiv.swap_apply_def,Fin.ext_iff]
  have h:=Matrix.det_permute' (Equiv.swap (3:Fin 5) 4) M
  rw [diagonal,Matrix.det_diagonal] at h
  norm_num [Fin.prod_univ_succ,Fin.ext_iff] at h
  change M.det=a*b*c*d^2
  calc
    M.det=a*(b*(c*(d*d))):=h.symm
    _=a*b*c*d^2:=by ring

private theorem adjugate_source_entry (branch : Fin 2) (s : ℝ) (n : PhysicalMomentum) :
    (characteristicTensor s n).adjugate (residueIndex branch) (residueIndex branch)=
      ((-128*s^2*sourceA s n*(if branch=0 then sourceC s n else sourceB s n):ℝ):ℂ):=by
  have updated : (characteristicTensor s n).updateRow (residueIndex branch) (Pi.single (residueIndex branch) 1)=
      Matrix.diagonal ![(sourceA s n:ℂ),(if branch=0 then 1 else (sourceB s n:ℂ)),
        (if branch=0 then (sourceC s n:ℂ) else 1),0,0]+
        Matrix.single 3 4 (8*Complex.I*rootTwo*(s:ℂ))+Matrix.single 4 3 (-(8*Complex.I*rootTwo*(s:ℂ))):=by
    fin_cases branch <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [characteristicTensor,residueIndex,sourceA,sourceB,sourceC,sourceRoot,rootTwo,rootFifteen,
        Matrix.updateRow_apply,Pi.single_apply,Fin.ext_iff,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
  rw [Matrix.adjugate_apply,updated,sparse_five_det]
  have root : rootTwo^2=(2:ℂ):=by norm_num [rootTwo,←Complex.ofReal_pow,Real.sq_sqrt]
  split_ifs <;> push_cast <;> simp only [mul_pow,Complex.I_sq,root] <;> ring


private theorem characteristic_zero_row (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀j,(characteristicTensor (sourceSpeed branch) n) (residueIndex branch) j=0:=by
  intro j
  fin_cases branch <;> fin_cases j <;>
    norm_num [characteristicTensor,residueIndex,Matrix.diagonal_apply,Fin.ext_iff,←Complex.ofReal_pow,sourceSpeed_square,unit]
  all_goals rfl

private theorem characteristic_zero_column (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀i,(characteristicTensor (sourceSpeed branch) n) i (residueIndex branch)=0:=by
  intro i
  fin_cases branch <;> fin_cases i <;>
    norm_num [characteristicTensor,residueIndex,Matrix.diagonal_apply,Fin.ext_iff,←Complex.ofReal_pow,sourceSpeed_square,unit]

private theorem adjugate_supported (M : Matrix (Fin 5) (Fin 5) ℂ) (k : Fin 5)
    (row : ∀j,M k j=0) (column : ∀i,M i k=0) :
    M.adjugate=Matrix.single k k (M.adjugate k k):=by
  ext i j
  by_cases hi : i=k
  · subst i
    by_cases hj : j=k
    · subst j;simp
    · rw [Matrix.adjugate_apply]
      have zero : (M.updateRow j (Pi.single k 1)).det=0:=by
        apply Matrix.det_eq_zero_of_row_eq_zero k
        intro q
        simpa only [Matrix.updateRow_ne (Ne.symm hj)] using row q
      simp [zero,Ne.symm hj]
  · have zero : M.adjugate i j=0:=by
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_column_eq_zero k
      intro q
      by_cases same : q=j
      · subst q
        simp [Matrix.updateRow_self,Ne.symm hi]
      · simpa only [Matrix.updateRow_ne same] using column q
    simp [zero,Ne.symm hi]

theorem leadingResidue_support (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    leadingResidue branch n=
      Matrix.single (residueIndex branch) (residueIndex branch)
        ((physicalSlope 0 (sourceSpeed branch) n:ℂ)⁻¹*
          (characteristicTensor (sourceSpeed branch) n).adjugate (residueIndex branch) (residueIndex branch)):=by
  rw [leadingResidue,adjugate_supported _ _ (characteristic_zero_row branch n unit) (characteristic_zero_column branch n unit),Matrix.smul_single]
  simp only [Matrix.single_apply_same,smul_eq_mul]

private theorem source_kinetic_cofactor (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    physicalSlope 0 (sourceSpeed branch) n*softCoefficient branch=
      2*sourceSpeed branch*(-128*(sourceSpeed branch)^2*sourceA (sourceSpeed branch) n*
        (if branch=0 then sourceC (sourceSpeed branch) n else sourceB (sourceSpeed branch) n)):=by
  rw [physicalSlope_origin,(sourceDet_derivative (sourceSpeed branch) n).deriv]
  have root : sourceRoot≠0:=ne_of_gt (by unfold sourceRoot;positivity)
  unfold sourceDerivative softCoefficient sourceA sourceB sourceC
  rw [sourceSpeed_square,unit]
  split_ifs <;> field_simp [root] <;> ring

/-- The complete source frequency derivative fixes the soft coefficient of each branch. -/
theorem leadingResidue_normalization (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    (2*(sourceSpeed branch:ℂ)) • leadingResidue branch n=
      Matrix.single (residueIndex branch) (residueIndex branch) (softCoefficient branch:ℂ):=by
  rw [leadingResidue_support branch n unit,Matrix.smul_single,smul_eq_mul,adjugate_source_entry]
  apply congrArg (Matrix.single (residueIndex branch) (residueIndex branch))
  have nonzero : (physicalSlope 0 (sourceSpeed branch) n:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (sourceSpeed_simple branch n unit)
  have cofactor : (physicalSlope 0 (sourceSpeed branch) n:ℂ)*(softCoefficient branch:ℂ)=
      (2*(sourceSpeed branch:ℂ))*
        ((-128*(sourceSpeed branch)^2*sourceA (sourceSpeed branch) n*
          (if branch=0 then sourceC (sourceSpeed branch) n else sourceB (sourceSpeed branch) n):ℝ):ℂ):=by
    exact_mod_cast source_kinetic_cofactor branch n unit
  apply (mul_left_cancel₀ nonzero)
  calc
    _=(2*(sourceSpeed branch:ℂ))*
        ((-128*(sourceSpeed branch)^2*sourceA (sourceSpeed branch) n*
          (if branch=0 then sourceC (sourceSpeed branch) n else sourceB (sourceSpeed branch) n):ℝ):ℂ):=by
      field_simp
    _= _ :=cofactor.symm

/-- Source normalization retains both generated branches and their distinct single-slot limits. -/
theorem sourceResidue_normalized_soft_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ)) •
      sourceResidue e.val (sourceSheet branch n unit e.val) n) scaleApproach
      (𝓝 (Matrix.single (residueIndex branch) (residueIndex branch) (softCoefficient branch:ℂ))):=by
  have speed:=((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto)
  have complexSpeed:=(Complex.continuous_ofReal.tendsto (sourceSpeed branch)).comp speed
  have scalar : Tendsto (fun e : scaleDomain=>2*(sourceSheet branch n unit e.val:ℂ)) scaleApproach
      (𝓝 (2*(sourceSpeed branch:ℂ))):=tendsto_const_nhds.mul complexSpeed
  have result:=scalar.smul (sourceResidue_soft_limit branch n unit)
  rw [leadingResidue_normalization branch n unit] at result
  exact result

theorem softCoefficient_nonzero (branch : Fin 2) : softCoefficient branch≠0:=by
  have root : sourceRoot≠0:=ne_of_gt (by unfold sourceRoot;positivity)
  unfold softCoefficient
  split_ifs <;> simp [root]

end LowEnergy.PreparationVacuumSoftPoleSelection
