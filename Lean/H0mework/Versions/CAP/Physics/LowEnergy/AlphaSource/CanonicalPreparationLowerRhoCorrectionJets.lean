import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerRaw94Recognition

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerCorrections
open PreparationVacuumPrincipalBudget PreparationVacuumRationalW PreparationVacuumDensityBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open PreparationVacuumCentralBudget PreparationVacuumEngineBudget PreparationVacuumEngineSmooth
open PreparationVacuumClockSymbol PreparationVacuumWeylOrdering PreparationVacuumLowerLeaves
open PreparationScalarCoordinates GaussHistoryHilbert
open scoped BigOperators ContDiff Topology Matrix

abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

def rhoColumn : RectSymbol 94 1 := fun x i _ => rawAmbient (Fin.natAdd 6 i) x

def dq (i : Fin 94) (f : Symbol) : Symbol := fun x => fderiv ℝ f x (qDirection (Fin.natAdd 6 i))

def densityQuadratic (P : RectSymbol 94 94) : Symbol := fun x => ((rhoColumn x)ᵀ*P x*rhoColumn x) 0 0

def densityDrift (P : RectSymbol 94 94) : Symbol := fun x =>
  ∑ i : Fin 94,∑ k : Fin 94,dq i (fun y => P y i k) x*rawAmbient (Fin.natAdd 6 k) x

def densityHessian (P : RectSymbol 94 94) : Symbol := fun x =>
  ∑ i : Fin 94,∑ k : Fin 94,P x i k*rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k) x

def densityCorrection (P : RectSymbol 94 94) : Symbol := fun x =>
  densityQuadratic P x+densityDrift P x+densityHessian P x

def weylCorrection (P : RectSymbol 94 94) : Symbol := fun x =>
  (1/4 : ℝ)*∑ i : Fin 94,∑ k : Fin 94,dq i (dq k (fun y => P y i k)) x

def densityArray (B : ArrayBound) (m : ℕ) : ℝ := productArray B (powerArray ellArray 2) m+
  94^2*productArray (fun r => B (r+1)) ellArray m+94^2*productArray B logHArray m

def weylArray (B : ArrayBound) (m : ℕ) : ℝ := (94^2/4 : ℝ)*B (m+2)

theorem rho_smooth (i : Fin 94) : SmoothSymbol (rawAmbient (Fin.natAdd 6 i)) := by
  intro x hx
  exact ((rawHalfLog_smooth _ ⟨_,hx.1.1⟩).comp x
    (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).contDiffWithinAt

theorem rhoHessian_smooth (i k : Fin 94) : SmoothSymbol (rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k)) := by
  intro x hx
  exact ((DR_smooth _ (rawHalfLog_smooth _ ⟨_,hx.1.1⟩)).comp x
    (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).contDiffWithinAt

theorem dq_smooth (i : Fin 94) (f : Symbol) (smooth : SmoothSymbol f) : SmoothSymbol (dq i f) := by
  intro x hx
  exact ((((smooth x hx).contDiffAt (poleDomain_open.mem_nhds hx)).fderiv_right (m:=∞) (by simp)).clm_apply
    contDiffAt_const).contDiffWithinAt

theorem dq_jet (i : Fin 94) (f : Symbol) (smooth : SmoothSymbol f) (m : ℕ) (w : Word m)
    (x : Phase) (hx : x∈poleDomain) :
    jet m (dq i f) w x=jet (m+1) f (Fin.snoc w (Fin.natAdd 6 i,false)) x := by
  let v : Word (m+1) := Fin.snoc w (Fin.natAdd 6 i,false)
  have read : jet (m+1) f v x=jet m (fun y => fderiv ℝ f y (slotDirection (v (Fin.last m)))) (Fin.init v) x :=
    PreparationVacuumCoframeBudget.jet_succ_right f m v x ((smooth x hx).contDiffAt (poleDomain_open.mem_nhds hx))
  simp only [v,Fin.snoc_last,Fin.init_snoc,slotDirection,Bool.false_eq_true,if_false] at read
  exact read.symm

theorem finite_dq (i : Fin 94) (f : Symbol) (smooth : SmoothSymbol f) (B : ArrayBound) (M : ℕ)
    (x : Phase) (hx : x∈poleDomain) (bound : FiniteBound f (M+1) B x) :
    FiniteBound (dq i f) M (fun m => B (m+1)) x := by
  intro m hm w
  rw [dq_jet i f smooth m w x hx]
  exact bound (m+1) (by omega) _

theorem finite_restrict (f : Symbol) (B : ArrayBound) {M L : ℕ} (le : M ≤ L) (x : Phase)
    (bound : FiniteBound f L B x) : FiniteBound f M B x := fun m hm w => bound m (hm.trans le) w

theorem rhoColumn_smooth : RectSmooth rhoColumn := fun i _ => rho_smooth i

theorem rhoColumn_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) (M : ℕ) :
    MatrixBound rhoColumn M ellArray x := by
  intro m _ w
  have total : (∑ i : Fin 94,|jet m (rawAmbient (Fin.natAdd 6 i)) w x|) ≤ ellArray m := actual_rho94_budget x box m w
  constructor
  · intro i
    simpa only [rhoColumn,Fin.sum_univ_one] using
      (Finset.single_le_sum (fun k _ => abs_nonneg (jet m (rawAmbient (Fin.natAdd 6 k)) w x))
        (Finset.mem_univ i)).trans total
  · intro k
    exact total

theorem rho_entry_budget (k : Fin 94) (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) (M : ℕ) :
    FiniteBound (rawAmbient (Fin.natAdd 6 k)) M ellArray x := by
  intro m hm w
  exact rect_entry (rhoColumn_budget x box M m hm w) k 0

theorem rho_hessian_entry_budget (i k : Fin 94) (x : Phase)
    (box : PreparationVacuumCoframeBudget.sourceBox x) (M : ℕ) :
    FiniteBound (rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k)) M logHArray x := by
  intro m _ w
  have total : (∑ i : Fin 94,∑ k : Fin 94,|jet m (rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k)) w x|) ≤ logHArray m :=
    actual_rho94_logH_budget x box m w
  exact ((Finset.single_le_sum (fun j _ => abs_nonneg (jet m (rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 j)) w x))
    (Finset.mem_univ k)).trans (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun r _ => abs_nonneg
      (jet m (rawHessianAmbient (Fin.natAdd 6 j) (Fin.natAdd 6 r)) w x))) (Finset.mem_univ i))).trans total

theorem finite_double_sum (f : Fin 94 → Fin 94 → Symbol) (smooth : ∀ i k,SmoothSymbol (f i k))
    (B : ArrayBound) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (bounds : ∀ i k,FiniteBound (f i k) M B x) :
    FiniteBound (fun y => ∑ i : Fin 94,∑ k : Fin 94,f i k y) M (fun m => 94^2*B m) x := by
  have inner (i : Fin 94) := finite_sum Finset.univ (f i) (fun k _ => smooth i k)
    (fun _ => B) M x hx (fun k _ => bounds i k)
  have ss (i : Fin 94) : SmoothSymbol (fun y => ∑ k : Fin 94,f i k y) := by
    apply ContDiffOn.sum
    intro k _
    exact smooth i k
  have result := finite_sum Finset.univ (fun i y => ∑ k : Fin 94,f i k y) (fun i _ => ss i)
    (fun _ m => ∑ _ : Fin 94,B m) M x hx (fun i _ => inner i)
  simpa [pow_two,mul_assoc] using result

theorem densityQuadratic_smooth (P : RectSymbol 94 94) (ps : RectSmooth P) : SmoothSymbol (densityQuadratic P) :=
  matrix_product_smooth _ _ (matrix_product_smooth _ _ (fun i k => rhoColumn_smooth k i) ps) rhoColumn_smooth 0 0

theorem densityDrift_smooth (P : RectSymbol 94 94) (ps : RectSmooth P) : SmoothSymbol (densityDrift P) := by
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro k _
  exact (dq_smooth i _ (ps i k)).mul (rho_smooth k)

theorem densityHessian_smooth (P : RectSymbol 94 94) (ps : RectSmooth P) : SmoothSymbol (densityHessian P) := by
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro k _
  exact (ps i k).mul (rhoHessian_smooth i k)

theorem densityCorrection_smooth (P : RectSymbol 94 94) (ps : RectSmooth P) : SmoothSymbol (densityCorrection P) :=
  ((densityQuadratic_smooth P ps).add (densityDrift_smooth P ps)).add (densityHessian_smooth P ps)

theorem weylCorrection_smooth (P : RectSymbol 94 94) (ps : RectSmooth P) : SmoothSymbol (weylCorrection P) := by
  apply ContDiffOn.mul contDiffOn_const
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro k _
  exact dq_smooth i _ (dq_smooth k _ (ps i k))

theorem density_quadratic_budget (P : RectSymbol 94 94) (ps : RectSmooth P) (B : ArrayBound)
    (bp : ∀ m,0 ≤ B m) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x) (bound : MatrixBound P M B x) :
    FiniteBound (densityQuadratic P) M (productArray B (powerArray ellArray 2)) x := by
  have ep : ∀ m,0 ≤ ellArray m := fun m => by unfold ellArray; positivity
  have eb := rhoColumn_budget x box M
  have first := finite_matrix_product (fun y => (rhoColumn y)ᵀ) P
    (fun i k => rhoColumn_smooth k i) ps M ellArray B ep bp x hx (finite_matrix_transpose _ M _ x eb) bound
  have second := finite_matrix_product (fun y => (rhoColumn y)ᵀ*P y) rhoColumn
    (matrix_product_smooth _ _ (fun i k => rhoColumn_smooth k i) ps) rhoColumn_smooth M
    (productArray ellArray B) ellArray (productArray_nonnegative ellArray B ep bp) ep x hx first eb
  have arr : productArray (productArray ellArray B) ellArray=productArray B (powerArray ellArray 2) := by
    rw [powerArray_two,productArray_comm ellArray B,productArray_assoc]
  rw [arr] at second
  intro m hm w
  exact rect_entry (second m hm w) 0 0

theorem density_correction_budget (P : RectSymbol 94 94) (ps : RectSmooth P) (B : ArrayBound)
    (bp : ∀ m,0 ≤ B m) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x) (bound : MatrixBound P (M+2) B x) :
    FiniteBound (densityCorrection P) M (densityArray B) x := by
  have entry (i k : Fin 94) : FiniteBound (fun y => P y i k) (M+2) B x :=
    fun m hm w => rect_entry (bound m hm w) i k
  have qb := density_quadratic_budget P ps B bp M x hx box (fun m hm w => bound m (by omega) w)
  have db := finite_double_sum (fun i k y => dq i (fun z => P z i k) y*rawAmbient (Fin.natAdd 6 k) y)
    (fun i k => (dq_smooth i _ (ps i k)).mul (rho_smooth k)) (productArray (fun r => B (r+1)) ellArray) M x hx (by
      intro i k
      exact finite_product _ _ (dq_smooth i _ (ps i k)) (rho_smooth k) _ ellArray (fun r => bp (r+1)) M x hx
        (finite_dq i _ (ps i k) B M x hx (finite_restrict _ B (by omega) x (entry i k))) (rho_entry_budget k x box M))
  have hb := finite_double_sum (fun i k y => P y i k*rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k) y)
    (fun i k => (ps i k).mul (rhoHessian_smooth i k)) (productArray B logHArray) M x hx (by
      intro i k
      exact finite_product _ _ (ps i k) (rhoHessian_smooth i k) B logHArray bp M x hx
        (finite_restrict _ B (by omega) x (entry i k)) (rho_hessian_entry_budget i k x box M))
  exact finite_add _ _ ((densityQuadratic_smooth P ps).add (densityDrift_smooth P ps)) (densityHessian_smooth P ps)
    _ _ M x hx (finite_add _ _ (densityQuadratic_smooth P ps) (densityDrift_smooth P ps) _ _ M x hx qb db) hb

theorem weyl_correction_budget (P : RectSymbol 94 94) (ps : RectSmooth P) (B : ArrayBound)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (bound : MatrixBound P (M+2) B x) :
    FiniteBound (weylCorrection P) M (weylArray B) x := by
  have sum := finite_double_sum (fun i k => dq i (dq k (fun y => P y i k)))
    (fun i k => dq_smooth i _ (dq_smooth k _ (ps i k))) (fun m => B (m+2)) M x hx (by
      intro i k
      have entry : FiniteBound (fun y => P y i k) (M+2) B x := fun m hm w => rect_entry (bound m hm w) i k
      have first := finite_dq k _ (ps i k) B (M+1) x hx entry
      have second := finite_dq i _ (dq_smooth k _ (ps i k)) (fun m => B (m+1)) M x hx first
      exact second)
  have smooth : SmoothSymbol (fun y => ∑ i : Fin 94,∑ k : Fin 94,dq i (dq k (fun z => P z i k)) y) := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro k _
    exact dq_smooth i _ (dq_smooth k _ (ps i k))
  have scaled := finite_scale (1/4 : ℝ) _ smooth _ M x hx sum
  intro m hm w
  change |jet m (fun y => (1/4 : ℝ)*∑ i : Fin 94,∑ k : Fin 94,dq i (dq k (fun z => P z i k)) y) w x| ≤ _
  refine (scaled m hm w).trans_eq ?_
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)]
  unfold weylArray
  ring

end LowEnergy.PreparationVacuumLowerCorrections
