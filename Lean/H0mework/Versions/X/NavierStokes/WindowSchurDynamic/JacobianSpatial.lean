import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianControl
import H0mework.Versions.X.NavierStokes.WindowHistory.SpatialWords

set_option autoImplicit false
open scoped BigOperators Topology ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianSpatial
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_inner restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistorySpatialWords (fiber operator)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowAugmentedGradient (derivative derivative_apply)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowHistoryJacobianControl (form heat)
noncomputable section

def spatial (M : ℕ) (j : Coordinate) : H →L[ℝ] H := operator M [j]

theorem fiber_original (M : ℕ) (j : Coordinate) (v : wholePhysical) :
    fiber M [j] v=includeCLM (modes M) (modes_closed M)
      (derivative (modes M) (modes_zero M) (modes_closed M) j
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)) := rfl

private theorem imaginary_skew (z a b : ℂ) (zero : z.re=0) :
    (z*a).re*b.re+(z*a).im*b.im= -(a.re*(z*b).re+a.im*(z*b).im) := by
  simp only [Complex.mul_re,Complex.mul_im,zero,zero_mul,zero_add,zero_sub]
  ring

theorem finite_skew (M : ℕ) (j : Coordinate) (u v : physicalSpace (modes M)) :
    pairing (modes M) (derivative (modes M) (modes_zero M) (modes_closed M) j u) v=
      -pairing (modes M) u (derivative (modes M) (modes_zero M) (modes_closed M) j v) := by
  simp only [pairing_eq,derivative_apply,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [complexCoordinateRealInner,← Finset.sum_neg_distrib,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact imaginary_skew (NativePhysicalGradient.multiplier k j) (u.1 k i) (v.1 k i)
    (by simp [NativePhysicalGradient.multiplier,complexWavevector])

theorem finite_square (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) :
    (∑j : Coordinate,derivative (modes M) (modes_zero M) (modes_closed M) j
      (derivative (modes M) (modes_zero M) (modes_closed M) j v))=
        -NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v := by
  apply Subtype.ext
  apply lp.ext
  funext k
  simp only [Submodule.coe_sum,lp.coeFn_sum,Finset.sum_apply,derivative_apply,Submodule.coe_neg,lp.coeFn_neg,
    Pi.neg_apply,NativeWindowOperatorGreen.laplacian_row,smul_smul,← Finset.sum_smul,← pow_two,
    NativeWindowHighTransportHeat.multiplier_square_sum,neg_smul]
  congr 1

theorem finite_commute (nu : Viscosity) (M : ℕ) (j : Coordinate) (v : physicalSpace (modes M)) :
    derivative (modes M) (modes_zero M) (modes_closed M) j
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)=
        NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
          (derivative (modes M) (modes_zero M) (modes_closed M) j v) := by
  apply Subtype.ext
  apply lp.ext
  funext k
  simp only [derivative_apply,NativeWindowOperatorGreen.laplacian_row]
  exact smul_comm _ _ _

theorem fiber_skew (M : ℕ) (j : Coordinate) (u v : wholePhysical) :
    inner ℝ (fiber M [j] u) v= -inner ℝ u (fiber M [j] v) := by
  rw [fiber_original,fiber_original,include_inner _ (modes_zero M),real_inner_comm (includeCLM _ _ _) u,
    include_inner _ (modes_zero M)]
  exact (finite_skew M j _ _).trans (congrArg Neg.neg (pairing_symmetric (modes M) _ _))

private theorem lift_skew {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : E →L[ℝ] E) (skew : ∀ u v,inner ℝ (D u) v= -inner ℝ u (D v)) (u v : Lp E 2 averageMeasure) :
    inner ℝ (D.compLpL 2 averageMeasure u) v= -inner ℝ u (D.compLpL 2 averageMeasure v) := by
  rw [L2.inner_def,L2.inner_def,← integral_neg]
  apply integral_congr_ae
  filter_upwards [D.coeFn_compLpL u,D.coeFn_compLpL v] with lag first last
  rw [first,last,skew]

theorem spatial_skew (M : ℕ) (j : Coordinate) (u v : H) :
    inner ℝ (spatial M j u) v= -inner ℝ u (spatial M j v) :=
  lift_skew (E := wholePhysical) (fiber M [j]) (fiber_skew M j) u v

theorem fiber_square (nu : Viscosity) (M : ℕ) (v : wholePhysical) :
    (∑j : Coordinate,fiber M [j] (fiber M [j] v))= -laplacianFiber nu M v := by
  simp only [fiber_original,restrict_include]
  exact (map_sum (includeCLM (modes M) (modes_closed M)) _ _).symm.trans
    ((congrArg (includeCLM (modes M) (modes_closed M)) (finite_square nu M
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))).trans
      ((includeCLM (modes M) (modes_closed M)).map_neg _))

theorem fiber_commute (nu : Viscosity) (M : ℕ) (j : Coordinate) (v : wholePhysical) :
    fiber M [j] (laplacianFiber nu M v)=laplacianFiber nu M (fiber M [j] v) := by
  change includeCLM (modes M) (modes_closed M) (derivative (modes M) (modes_zero M) (modes_closed M) j
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) (includeCLM (modes M) (modes_closed M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)))))=_
  rw [restrict_include,fiber_original]
  change _=includeCLM (modes M) (modes_closed M) (NativeWindowOperatorGreen.laplacian (modes M)
    (modes_zero M) (modes_closed M) nu (restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (includeCLM (modes M) (modes_closed M) _)))
  rw [restrict_include,finite_commute]

private theorem lift_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Coordinate → E →L[ℝ] E) (L : E →L[ℝ] E) (same : ∀v,(∑j,D j (D j v))= -L v)
    (v : Lp E 2 averageMeasure) :
    (∑j,(D j).compLpL 2 averageMeasure ((D j).compLpL 2 averageMeasure v))= -L.compLpL 2 averageMeasure v := by
  apply Lp.ext
  have all : ∀ᵐ lag ∂averageMeasure,∀j,
      (D j).compLpL 2 averageMeasure ((D j).compLpL 2 averageMeasure v) lag=D j (D j (v lag)) := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(D j).coeFn_compLpL ((D j).compLpL 2 averageMeasure v),(D j).coeFn_compLpL v] with lag first last
    rw [first,last]
  filter_upwards [all,Lp.coeFn_finsetSum Finset.univ (fun j => (D j).compLpL 2 averageMeasure ((D j).compLpL 2 averageMeasure v)),
    Lp.coeFn_neg (L.compLpL 2 averageMeasure v),L.coeFn_compLpL v] with lag source summed negative actual
  rw [summed,negative,Pi.neg_apply,actual]
  simpa only [Finset.sum_apply,source] using same (v lag)

theorem spatial_square (nu : Viscosity) (M : ℕ) (v : H) :
    (∑j : Coordinate,spatial M j (spatial M j v))= -laplacianAction nu M v :=
  lift_square (E := wholePhysical) (fun j => fiber M [j]) (laplacianFiber nu M) (fiber_square nu M) v

private theorem lift_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D L : E →L[ℝ] E) (same : ∀v,D (L v)=L (D v)) (v : Lp E 2 averageMeasure) :
    D.compLpL 2 averageMeasure (L.compLpL 2 averageMeasure v)=L.compLpL 2 averageMeasure (D.compLpL 2 averageMeasure v) := by
  apply Lp.ext
  filter_upwards [D.coeFn_compLpL (L.compLpL 2 averageMeasure v),L.coeFn_compLpL v,
    L.coeFn_compLpL (D.compLpL 2 averageMeasure v),D.coeFn_compLpL v] with lag first second third fourth
  rw [first,second,third,fourth,same]

theorem spatial_commute (nu : Viscosity) (M : ℕ) (j : Coordinate) (v : H) :
    spatial M j (laplacianAction nu M v)=laplacianAction nu M (spatial M j v) :=
  lift_commute (E := wholePhysical) (fiber M [j]) (laplacianFiber nu M) (fiber_commute nu M j) v

private theorem sum_commute {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D L : E →L[ℝ] E) (same : ∀v,D (L v)=L (D v)) (a : ℝ) (v : E) :
    D ((ContinuousLinearMap.id ℝ E+a • L) v)=(ContinuousLinearMap.id ℝ E+a • L) (D v) := by
  simp only [add_apply,ContinuousLinearMap.id_apply,smul_apply,map_add,map_smul,same]

theorem heat_commute (nu : Viscosity) (M : ℕ) (j : Coordinate) (v : H) :
    spatial M j (heat nu M v)=heat nu M (spatial M j v) := by
  simpa only [heat] using! sum_commute (E := H) (spatial M j) (laplacianAction nu M) (spatial_commute nu M j) nu.coeff v

private theorem paired_skew {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D G : E →L[ℝ] E) (skew : ∀u v,inner ℝ (D u) v= -inner ℝ u (D v))
    (commute : ∀v,D (G v)=G (D v)) (u v : E) :
    inner ℝ u (G (D v))= -inner ℝ (D u) (G v) := by
  rw [← commute,skew,neg_neg]

theorem form_skew (nu : Viscosity) (M : ℕ) (j : Coordinate) (u v : H) :
    form nu M u (spatial M j v)= -form nu M (spatial M j u) v := by
  simpa only [form] using!
    paired_skew (E := H) (spatial M j) (heat nu M) (spatial_skew M j) (heat_commute nu M j) u v

private theorem sum_green {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G L : E →L[ℝ] E) (D : Coordinate → E →L[ℝ] E)
    (skew : ∀j u v,inner ℝ u (G (D j v))= -inner ℝ (D j u) (G v))
    (square : ∀v,(∑j,D j (D j v))= -L v) (u v : E) :
    (∑j,inner ℝ (D j u) (G (D j v)))=inner ℝ u (G (L v)) := by
  have each (j : Coordinate) : inner ℝ (D j u) (G (D j v))= -inner ℝ u (G (D j (D j v))) := by
    linarith only [skew j u (D j v)]
  simp_rw [each]
  rw [Finset.sum_neg_distrib,← inner_sum,← map_sum,square,map_neg,inner_neg_right,neg_neg]

theorem form_gradient (nu : Viscosity) (M : ℕ) (u v : H) :
    (∑j : Coordinate,form nu M (spatial M j u) (spatial M j v))=form nu M u (laplacianAction nu M v) := by
  simpa only [form] using! sum_green (E := H) (heat nu M) (laplacianAction nu M) (spatial M)
    (form_skew nu M) (spatial_square nu M) u v

theorem energy_gradient (nu : Viscosity) (M : ℕ) (v : H) :
    (∑j : Coordinate,NativeWindowHistorySchurTemporalControl.energy nu M (spatial M j v))=
      NativeWindowTraceWholeHistory.gradient M v+nu.coeff*‖laplacianAction nu M v‖^2 := by
  have symmetric:=NativeWindowHistoryJacobianControl.form_symmetric nu M v (laplacianAction nu M v)
  have split:=NativeWindowHistoryJacobianControl.form_split nu M (laplacianAction nu M v) v
  have middle:form nu M v (laplacianAction nu M v)=
      NativeWindowTraceWholeHistory.gradient M v+nu.coeff*‖laplacianAction nu M v‖^2 :=
    symmetric.trans (split.trans (congrArg₂ (fun a b : ℝ => a+nu.coeff*b)
      ((real_inner_comm v (laplacianAction nu M v)).trans (NativeWindowMetricGraphHistory.history_gradient nu M v))
      (real_inner_self_eq_norm_sq (laplacianAction nu M v))))
  exact ((Finset.sum_congr rfl fun j _ => NativeWindowHistoryJacobianControl.form_self nu M (spatial M j v))).symm.trans
    ((form_gradient nu M v v).trans middle)

theorem mass_gradient (nu : Viscosity) (M : ℕ) (v : H) :
    (∑j : Coordinate,‖spatial M j v‖^2)=NativeWindowTraceWholeHistory.gradient M v := by
  have source:=sum_green (E := H) (ContinuousLinearMap.id ℝ H) (laplacianAction nu M) (spatial M)
    (fun j u w => by simpa only [ContinuousLinearMap.id_apply,neg_neg] using!
      (congrArg Neg.neg (spatial_skew M j u w)).symm)
    (spatial_square nu M) v v
  simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,NativeWindowMetricGraphHistory.history_gradient] using! source

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianSpatial
