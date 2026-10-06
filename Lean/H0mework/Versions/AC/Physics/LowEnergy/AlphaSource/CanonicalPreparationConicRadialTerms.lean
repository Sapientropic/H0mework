import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCutoffBox
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumConicBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget
open scoped BigOperators ContDiff Topology RealInnerProductSpace

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

def punctured : Set Phase := {x | x.2≠0}
def rho (x : Phase) : ℝ := ‖x.2‖
def radialPower (a : ℝ) : Symbol := fun x => (rho x)^a

def momentumCoordinate (i : Fin 100) : Phase →L[ℝ] ℝ :=
  (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 100 => ℝ) i).comp (ContinuousLinearMap.snd ℝ _ _)

def radialGradient (x : Phase) : Phase →L[ℝ] ℝ :=
  (innerSL ℝ x.2).comp (ContinuousLinearMap.snd ℝ _ _)

structure RadialTerm where
  coefficient : ℝ
  contractions : ℕ
  coordinates : List (Fin 100)

def termValue (a : ℝ) (t : RadialTerm) : Symbol := fun x =>
  t.coefficient*radialPower (a-2*t.contractions) x*
    (t.coordinates.map (fun i => momentumCoordinate i x)).prod

def termNext (a : ℝ) (s : Slot) (t : RadialTerm) : List RadialTerm :=
  if s.2 then
    ⟨t.coefficient*(a-2*t.contractions),t.contractions+1,s.1::t.coordinates⟩ ::
      List.ofFn (fun i : Fin t.coordinates.length =>
        ⟨if s.1=t.coordinates.get i then t.coefficient else 0,t.contractions,
          t.coordinates.take i.val++t.coordinates.drop (i.val+1)⟩)
  else []

theorem punctured_open : IsOpen punctured := by
  exact (isClosed_singleton.preimage continuous_snd).isOpen_compl

theorem radialPower_smooth (a : ℝ) : ContDiffOn ℝ ∞ (radialPower a) punctured := by
  intro x hx
  have normSmooth : ContDiffAt ℝ ∞ rho x := contDiff_snd.contDiffAt.norm ℝ hx
  exact (normSmooth.rpow_const_of_ne (norm_pos_iff.mpr hx).ne').contDiffWithinAt

private theorem norm_power_differential (a : ℝ) (p : PhysicalMomentum) (nonzero : p≠0) :
    HasFDerivAt (fun p : PhysicalMomentum => ‖p‖^a) ((a*‖p‖^(a-2)) • innerSL ℝ p) p := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq p).rpow_const (p:=a/2) (by simp [nonzero]) using 0
  simp_rw [←Real.rpow_natCast_mul (norm_nonneg _),←Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  ring_nf

theorem radialPower_differential (a : ℝ) (x : Phase) (hx : x∈punctured) :
    HasFDerivAt (radialPower a) ((a*radialPower (a-2) x) • radialGradient x) x := by
  have hd := (norm_power_differential a x.2 hx).comp x (hasFDerivAt_snd (𝕜:=ℝ) (p:=x))
  simpa only [radialPower,rho,radialGradient,ContinuousLinearMap.smul_comp] using! hd

theorem momentumCoordinate_direction (i : Fin 100) (s : Slot) :
    momentumCoordinate i (slotDirection s)=if s.2 then (if i=s.1 then 1 else 0) else 0 := by
  rcases s with ⟨j,b⟩
  cases b <;> simp [momentumCoordinate,slotDirection,qDirection,pDirection]

theorem radialGradient_direction (x : Phase) (s : Slot) :
    radialGradient x (slotDirection s)=if s.2 then momentumCoordinate s.1 x else 0 := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [radialGradient,slotDirection,qDirection,pDirection,momentumCoordinate,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct]

theorem termValue_smooth (a : ℝ) (t : RadialTerm) : ContDiffOn ℝ ∞ (termValue a t) punctured := by
  have polynomial : ContDiff ℝ ∞ (fun x : Phase => (t.coordinates.map (fun i => momentumCoordinate i x)).prod) :=
    by
      have all (xs : List (Fin 100)) : ContDiff ℝ ∞ (fun y : Phase => (xs.map (fun i => momentumCoordinate i y)).prod) := by
        induction xs with
        | nil => exact contDiff_const
        | cons i xs ih => simpa only [List.map_cons,List.prod_cons] using! (momentumCoordinate i).contDiff.mul ih
      exact all t.coordinates
  exact (contDiffOn_const.mul (radialPower_smooth _)).mul polynomial.contDiffOn

theorem termValue_differential (a : ℝ) (s : Slot) (t : RadialTerm) (x : Phase) (hx : x∈punctured) :
    fderiv ℝ (termValue a t) x (slotDirection s)=((termNext a s t).map (fun u => termValue a u x)).sum := by
  classical
  have monomial := HasFDerivAt.list_prod' (l:=t.coordinates) (x:=x) (fun i _ => (momentumCoordinate i).hasFDerivAt)
  have actual := ((radialPower_differential (a-2*t.contractions) x hx).const_mul t.coefficient).mul monomial
  change HasFDerivAt (termValue a t) _ x at actual
  rw [actual.fderiv]
  simp only [add_apply,smul_apply,op_smul_eq_smul,radialGradient_direction,
    sum_apply,momentumCoordinate_direction,smul_eq_mul]
  cases h : s.2
  · simp [termNext,h]
  · simp only [h,if_true,termNext,List.map_cons,List.sum_cons,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    unfold termValue
    simp only [List.map_cons,List.prod_cons,List.map_append,List.prod_append,List.map_take,List.map_drop]
    have exponents : a-2*↑(t.contractions+1)=a-2*t.contractions-2 := by push_cast; ring
    rw [exponents]
    simp only [Finset.mul_sum]
    conv_lhs => rw [add_comm]
    apply congrArg₂ (fun u v : ℝ => u+v)
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      simp only [List.get_eq_getElem,Fin.getElem_fin]
      by_cases same : s.1=t.coordinates[i.val]
      · simp [same,mul_assoc]
      · simp [same,Ne.symm same]

end LowEnergy.PreparationVacuumConicBudget
