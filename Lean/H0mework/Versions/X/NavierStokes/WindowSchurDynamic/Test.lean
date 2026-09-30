import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.Kernel
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorFiber
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Mean

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicTest
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_inner restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (forwardFiber velocityPath)
open NativeWindowHistorySchurAdvectorFiber (family)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open NativeWindowHistoryFrozenInverse (kernel)
open NativeWindowTraceWholeHistory (projection)
noncomputable section
variable {nu : Viscosity}

def heat (nu : Viscosity) (M : ℕ) : wholePhysical →L[ℝ] wholePhysical :=
  projection M+nu.coeff • laplacianFiber nu M

def advection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    wholePhysical →L[ℝ] wholePhysical := family nu M (velocityPath seed M time)

theorem forward_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    forwardFiber seed M time v=(-nu.coeff) • laplacianFiber nu M v+advection seed M time v := by
  rw [← NativeWindowHistorySchurAdvectorFiber.family_source,
    NativeWindowMetricGraphMean.diffusion_laplacian]
  rfl

theorem projection_symmetric (M : ℕ) (x y : wholePhysical) :
    inner ℝ (projection M x) y=inner ℝ x (projection M y) := by
  rw [projection,ContinuousLinearMap.comp_apply,include_inner _ (modes_zero M),
    real_inner_comm _ x,ContinuousLinearMap.comp_apply,include_inner _ (modes_zero M),pairing_symmetric]

theorem laplacian_symmetric (nu : Viscosity) (M : ℕ) (x y : wholePhysical) :
    inner ℝ (laplacianFiber nu M x) y=inner ℝ x (laplacianFiber nu M y) := by
  change inner ℝ (includeCLM (modes M) (modes_closed M)
    (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) x))) y=
    inner ℝ x (includeCLM (modes M) (modes_closed M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) y)))
  rw [include_inner _ (modes_zero M),real_inner_comm _ x,
    include_inner _ (modes_zero M),pairing_symmetric]
  exact (NativeWindowAugmentedGreen.laplacian_adjoint (nu := nu) (modes M) (modes_zero M) (modes_closed M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) y)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) x)).symm

theorem heat_symmetric (nu : Viscosity) (M : ℕ) (x y : wholePhysical) :
    inner ℝ (heat nu M x) y=inner ℝ x (heat nu M y) := by
  simp only [heat,add_apply,smul_apply,
    inner_add_left,inner_add_right,real_inner_smul_left (F := wholePhysical),real_inner_smul_right (F := wholePhysical),
    projection_symmetric,laplacian_symmetric]

private theorem skew_of_diagonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (diagonal : ∀ v,inner ℝ v (A v)=0) (x y : E) :
    inner ℝ (A x) y= -inner ℝ x (A y) := by
  have mixed:=diagonal (x+y)
  simp only [map_add,inner_add_left,inner_add_right,diagonal,zero_add,add_zero] at mixed
  rw [real_inner_comm (A x) y] at mixed
  linarith only [mixed]

theorem advection_diagonal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    inner ℝ v (advection seed M time v)=0 := by
  have paid:=NativeWindowHistoryOseenGap.fiber_energy seed M time v
  rw [forward_split,inner_add_right,real_inner_smul_right (F := wholePhysical),
    NativeWindowMetricGraphHistory.fiber_gradient] at paid
  linarith only [paid]

theorem advection_skew (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x y : wholePhysical) :
    inner ℝ (advection seed M time x) y= -inner ℝ x (advection seed M time y) :=
  skew_of_diagonal (advection seed M time) (advection_diagonal seed M time) x y

theorem heat_kernel (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    heat nu M (kernel seed M time v)=projection M v+advection seed M time (kernel seed M time v) := by
  have actual:=NativeWindowHistoryFrozenInverse.kernel_write seed M time v
  rw [forward_split,neg_smul] at actual
  simp only [heat,add_apply,smul_apply,
    NativeWindowHistoryFrozenInverse.kernel_projected]
  calc
    kernel seed M time v+nu.coeff • laplacianFiber nu M (kernel seed M time v)=
        (kernel seed M time v-(-(nu.coeff • laplacianFiber nu M (kernel seed M time v))+
          advection seed M time (kernel seed M time v)))+advection seed M time (kernel seed M time v) := by abel
    _=projection M v+advection seed M time (kernel seed M time v) := congrArg (fun x => x+_) actual

theorem adjoint_heat (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    (kernel seed M time).adjoint (heat nu M v)=
      projection M v-(kernel seed M time).adjoint (advection seed M time v) := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right,inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right,← heat_symmetric,heat_kernel,
    inner_add_left,projection_symmetric,advection_skew]
  rfl

def transpose (nu : Viscosity) (M : ℕ) (X : wholePhysical) : wholePhysical →L[ℝ] wholePhysical :=
  (family nu M).flip X

def test (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (X v : wholePhysical) : wholePhysical :=
  heat nu M v-(transpose nu M X).adjoint ((kernel seed M time).adjoint (heat nu M v))

private theorem subtract_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (q x y : E) : q-T (x-y)=q-T x+T y := by
  rw [map_sub]
  abel

theorem test_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (X v : wholePhysical) :
    test seed M time X v=heat nu M v-(transpose nu M X).adjoint (projection M v)+
      (transpose nu M X).adjoint ((kernel seed M time).adjoint (advection seed M time v)) := by
  exact (congrArg (fun x => heat nu M v-(transpose nu M X).adjoint x)
    (adjoint_heat seed M time v)).trans
      (subtract_image (transpose nu M X).adjoint (heat nu M v) (projection M v)
        ((kernel seed M time).adjoint (advection seed M time v)))

private theorem derivative_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K T : E →L[ℝ] E) (q a d : E) :
    2*inner ℝ q (a-K (T a+d))=
      2*inner ℝ a (q-T.adjoint (K.adjoint q))-2*inner ℝ d (K.adjoint q) := by
  rw [map_add,inner_sub_right,inner_add_right,inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right,real_inner_comm q a,
    real_inner_comm q (K (T a)),real_inner_comm q (K d)]
  ring

theorem test_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (X v a d : wholePhysical) :
    2*inner ℝ (heat nu M v) (a-kernel seed M time (family nu M a X+d))=
      2*inner ℝ a (test seed M time X v)-
        2*inner ℝ d ((kernel seed M time).adjoint (heat nu M v)) :=
  derivative_pairing (kernel seed M time) (transpose nu M X) (heat nu M v) a d

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicTest
