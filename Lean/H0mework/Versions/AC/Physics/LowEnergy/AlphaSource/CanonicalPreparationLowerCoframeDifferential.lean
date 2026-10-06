import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationDensityOriginalArrays
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCorrection
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalTimePairTensor

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerTensorBudget
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy PreparationScalarCoordinates
open PreparationVacuumLowerLeaves CanonicalPreparationMomentum
open scoped BigOperators ContDiff Topology Matrix

abbrev Configuration := SourceCoordinateSlice
local notation "D" => GaussCoframeCore.coframeDirection

def qRead (i : Fin 6) : Configuration →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin 6 => ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _)

theorem qRead_apply (i : Fin 6) (z : Configuration) : qRead i z=z.1 i := rfl

theorem qRead_direction (i j : Fin 6) : qRead i (D j)=if i=j then 1 else 0 := by
  simp [qRead,GaussCoframeCore.coframeDirection,EuclideanSpace.single,PiLp.single_apply]

def K (i j : Fin 6) (z : Configuration) : ℝ :=
  GaussCoframeKinetic.polynomial z.1 i j/(4*volume z)

theorem K_original (i j : Fin 6) (z : Configuration) :
    K i j z=GaussCoframeKinetic.coefficient i j z/sourceTime 0 := by
  unfold K GaussCoframeKinetic.coefficient
  field_simp [source_time_nonzero]

theorem K_smooth (i j : Fin 6) (z : physicalChart) : ContDiffAt ℝ ∞ (K i j) z.val := by
  have same : K i j=(fun w => GaussCoframeKinetic.coefficient i j w/sourceTime 0) := funext (K_original i j)
  rw [same]
  exact (GaussCoframeKinetic.coefficient_smooth i j z).div_const _

def polynomialSlope (q d : Coframe) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-2*q 0*d 0, d 0*q 1+q 0*d 1, d 0*q 2+q 0*d 2, d 0*q 3+q 0*d 3, d 0*q 4+q 0*d 4, d 0*q 5+q 0*d 5;
    d 0*q 1+q 0*d 1, -8*q 0*d 0-2*q 1*d 1, -(d 1*q 2+q 1*d 2), d 1*q 3+q 1*d 3, d 1*q 4+q 1*d 4, d 1*q 5+q 1*d 5;
    d 0*q 2+q 0*d 2, -(d 1*q 2+q 1*d 2), -2*q 2*d 2, d 2*q 3+q 2*d 3, d 2*q 4+q 2*d 4, d 2*q 5+q 2*d 5;
    d 0*q 3+q 0*d 3, d 1*q 3+q 1*d 3, d 2*q 3+q 2*d 3, -8*q 0*d 0-8*q 1*d 1-2*q 3*d 3, -4*(d 1*q 2+q 1*d 2)-(d 3*q 4+q 3*d 4), -(d 3*q 5+q 3*d 5);
    d 0*q 4+q 0*d 4, d 1*q 4+q 1*d 4, d 2*q 4+q 2*d 4, -4*(d 1*q 2+q 1*d 2)-(d 3*q 4+q 3*d 4), -8*q 2*d 2-2*q 4*d 4, -(d 4*q 5+q 4*d 5);
    d 0*q 5+q 0*d 5, d 1*q 5+q 1*d 5, d 2*q 5+q 2*d 5, -(d 3*q 5+q 3*d 5), -(d 4*q 5+q 4*d 5), -2*q 5*d 5]

theorem polynomial_derivative (i j : Fin 6) (z d : Configuration) :
    fderiv ℝ (fun w : Configuration => GaussCoframeKinetic.polynomial w.1 i j) z d=
      polynomialSlope z.1 d.1 i j := by
  have h (r : Fin 6) := (qRead r).hasFDerivAt (x := z)
  fin_cases i <;> fin_cases j
  · have hd := (((h 0).pow 2).neg)
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]
  · have hd := ((h 0).mul (h 1))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 2))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 3))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 4))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 1))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((((hasFDerivAt_const (4 : ℝ) z).neg).mul ((h 0).pow 2)).sub ((h 1).pow 2))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 1).neg).mul (h 2))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 1).mul (h 3))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 1).mul (h 4))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 1).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 2))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 1).neg).mul (h 2))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 2).pow 2).neg)
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]
  · have hd := ((h 2).mul (h 3))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 2).mul (h 4))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 2).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 3))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 1).mul (h 3))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 2).mul (h 3))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((((hasFDerivAt_const (4 : ℝ) z).neg).mul ((h 0).pow 2)).sub ((hasFDerivAt_const (4 : ℝ) z).mul ((h 1).pow 2))).sub ((h 3).pow 2))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((((hasFDerivAt_const (4 : ℝ) z).neg).mul (h 1)).mul (h 2)).sub ((h 3).mul (h 4)))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 3).neg).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 4))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 1).mul (h 4))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 2).mul (h 4))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((((hasFDerivAt_const (4 : ℝ) z).neg).mul (h 1)).mul (h 2)).sub ((h 3).mul (h 4)))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((((hasFDerivAt_const (4 : ℝ) z).neg).mul ((h 2).pow 2)).sub ((h 4).pow 2))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 4).neg).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 0).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 1).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := ((h 2).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 3).neg).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 4).neg).mul (h 5))
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]; ring
  · have hd := (((h 5).pow 2).neg)
    calc
      _ = _ := congrArg (fun L : Configuration →L[ℝ] ℝ => L d) hd.fderiv
      _ = _ := by norm_num [polynomialSlope,qRead]

end LowEnergy.PreparationVacuumLowerTensorBudget
