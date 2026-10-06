import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationDensityLog
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoframeOriginal
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalSourceSmooth
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaugeInverse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDensityBudget
open PreparationVacuumDensityTrace PreparationVacuumLowerLeaves PreparationScalarCoordinates
open PreparationCoordinates PreparationActualFactor PreparationPhaseScalar
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy
open scoped BigOperators ContDiff Topology

abbrev Configuration := SourceCoordinateSlice

def coordinate (i : Fin 100) : Configuration →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp fullCoordinates.toContinuousLinearMap

theorem coordinate_volume : volume=(fun z => coordinate 0 z*coordinate 2 z*coordinate 5 z) := rfl

theorem coordinate_rho : rho3OnConfiguration=(fun z => 8*(coordinate 67 z)^2*coordinate 77 z) := rfl

theorem coordinate_rawDirection (i j : Fin 100) :
    coordinate i (rawDirection j)=if j=i then 1 else 0 := by
  simp [coordinate,rawDirection,Pi.single_apply,eq_comm]

def logDerivative (f : Configuration → ℝ) (z D : Configuration) : ℝ :=
  (f z)⁻¹*fderiv ℝ f z D

private theorem log_mul (f g : Configuration → ℝ) (z D : Configuration)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (fn : f z≠0) (gn : g z≠0) :
    logDerivative (fun y => f y*g y) z D=logDerivative f z D+logDerivative g z D := by
  unfold logDerivative
  change (f z*g z)⁻¹*fderiv ℝ (f*g) z D=_
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  field_simp
  ring

private theorem log_square (f : Configuration → ℝ) (z D : Configuration)
    (hf : DifferentiableAt ℝ f z) (fn : f z≠0) :
    logDerivative (fun y => f y^2) z D=2*logDerivative f z D := by
  rw [show (fun y => f y^2)=(fun y => f y*f y) by funext y; ring,log_mul f f z D hf hf fn fn]
  ring

private theorem log_sqrt (f : Configuration → ℝ) (z D : Configuration)
    (hf : DifferentiableAt ℝ f z) (positive : 0<f z) :
    logDerivative (fun y => Real.sqrt (f y)) z D=(1/2 : ℝ)*logDerivative f z D := by
  have root : Real.sqrt (f z)≠0 := (Real.sqrt_pos.mpr positive).ne'
  unfold logDerivative
  rw [(hf.hasFDerivAt.sqrt positive.ne').fderiv]
  simp only [smul_apply,smul_eq_mul]
  calc
    _ = fderiv ℝ f z D/(2*(Real.sqrt (f z))^2) := by field_simp
    _ = fderiv ℝ f z D/(2*f z) := by rw [Real.sq_sqrt positive.le]
    _ = _ := by field_simp

private theorem coordinate_log (i : Fin 100) (z D : Configuration) :
    logDerivative (coordinate i) z D=(coordinate i z)⁻¹*coordinate i D := by
  simp only [logDerivative,ContinuousLinearMap.fderiv]

private theorem volume_log (z : physicalChart) (D : Configuration) :
    logDerivative volume z.val D=
      (coordinate 0 z.val)⁻¹*coordinate 0 D+(coordinate 2 z.val)⁻¹*coordinate 2 D+
        (coordinate 5 z.val)⁻¹*coordinate 5 D := by
  have p0 : coordinate 0 z.val≠0 := z.property.1.ne'
  have p2 : coordinate 2 z.val≠0 := z.property.2.1.ne'
  have p5 : coordinate 5 z.val≠0 := z.property.2.2.1.ne'
  rw [coordinate_volume]
  rw [log_mul (fun y => coordinate 0 y*coordinate 2 y) (coordinate 5) z.val D
    ((coordinate 0).differentiableAt.mul (coordinate 2).differentiableAt)
    (coordinate 5).differentiableAt (mul_ne_zero p0 p2) p5,
    log_mul (coordinate 0) (coordinate 2) z.val D (coordinate 0).differentiableAt
      (coordinate 2).differentiableAt p0 p2,coordinate_log,coordinate_log,coordinate_log]

private theorem rho_log (z : physicalChart) (D : Configuration) :
    logDerivative rho3OnConfiguration z.val D=
      2*(coordinate 67 z.val)⁻¹*coordinate 67 D+(coordinate 77 z.val)⁻¹*coordinate 77 D := by
  have first : coordinate 67 z.val≠0 := z.property.2.2.2.2.1.ne'
  have second : coordinate 77 z.val≠0 := z.property.2.2.2.2.2.1.ne'
  have sq : DifferentiableAt ℝ (fun y => (coordinate 67 y)^2) z.val := (coordinate 67).differentiableAt.pow 2
  rw [coordinate_rho]
  rw [log_mul (fun y => 8*(coordinate 67 y)^2) (coordinate 77) z.val D (sq.const_mul 8)
    (coordinate 77).differentiableAt (mul_ne_zero (by norm_num) (pow_ne_zero 2 first)) second,
    log_mul (fun _ => 8) (fun y => (coordinate 67 y)^2) z.val D (by fun_prop) sq
      (by norm_num) (pow_ne_zero 2 first),log_square _ _ _ (coordinate 67).differentiableAt first]
  simp only [logDerivative,ContinuousLinearMap.fderiv,fderiv_const_apply,zero_apply,mul_zero,zero_add]
  ring

def coframeLog (i : Fin 100) (z : Configuration) : ℝ :=
  (if i=0 then 1 else 0)*(coordinate 0 z)⁻¹+
  (if i=2 then 1 else 0)*(coordinate 2 z)⁻¹+
  (if i=5 then 1 else 0)*(coordinate 5 z)⁻¹

def rhoLog (i : Fin 100) (z : Configuration) : ℝ :=
  (if i=67 then 1 else 0)*(coordinate 67 z)⁻¹+
  (if i=77 then 1 else 0)*(1/2 : ℝ)*(coordinate 77 z)⁻¹

/-- The original volume part and the original rho3 part have disjoint coordinate support. -/
theorem actual_rawHalfLog_split (i : Fin 100) (z : physicalChart) :
    rawHalfLog i z.val=coframeLog i z.val+rhoLog i z.val := by
  rw [original_rawHalfLog_feed]
  change logDerivative literalHalf z.val (rawDirection i)=_
  change logDerivative (fun y => volume y*Real.sqrt (rho3OnConfiguration y)) z.val (rawDirection i)=_
  have hv : DifferentiableAt ℝ volume z.val := volume_smooth.differentiable (by simp) |>.differentiableAt
  have hr : DifferentiableAt ℝ rho3OnConfiguration z.val := rho3OnConfiguration_smooth.differentiable (by simp) |>.differentiableAt
  rw [log_mul volume (fun y => Real.sqrt (rho3OnConfiguration y)) z.val (rawDirection i) hv
    (hr.sqrt (rho3OnConfiguration_positive z).ne')
    (volume_pos z).ne' (Real.sqrt_pos.mpr (rho3OnConfiguration_positive z)).ne',
    log_sqrt rho3OnConfiguration z.val (rawDirection i) hr (rho3OnConfiguration_positive z),volume_log,rho_log]
  simp only [coordinate_rawDirection]
  unfold coframeLog rhoLog
  ring

theorem coframeLog_other (i : Fin 100) (h0 : i≠0) (h2 : i≠2) (h5 : i≠5) : coframeLog i=fun _ => 0 := by
  funext z
  simp [coframeLog,h0,h2,h5]

theorem rhoLog_other (i : Fin 100) (h67 : i≠67) (h77 : i≠77) : rhoLog i=fun _ => 0 := by
  funext z
  simp [rhoLog,h67,h77]

theorem actual_rawHalfLog_coframe (i : Fin 6) (z : physicalChart) :
    rawHalfLog (Fin.castAdd 94 i) z.val=coframeLog (Fin.castAdd 94 i) z.val := by
  rw [actual_rawHalfLog_split,rhoLog_other _ (by intro h; have hh := congrArg Fin.val h; change i.val=67 at hh; omega)
    (by intro h; have hh := congrArg Fin.val h; change i.val=77 at hh; omega),add_zero]

theorem actual_rawHalfLog_rho (i : Fin 94) (z : physicalChart) :
    rawHalfLog (Fin.natAdd 6 i) z.val=rhoLog (Fin.natAdd 6 i) z.val := by
  rw [actual_rawHalfLog_split,coframeLog_other _
    (by intro h; have hh := congrArg Fin.val h; change 6+i.val=0 at hh; omega)
    (by intro h; have hh := congrArg Fin.val h; change 6+i.val=2 at hh; omega)
    (by intro h; have hh := congrArg Fin.val h; change 6+i.val=5 at hh; omega),zero_add]

end LowEnergy.PreparationVacuumDensityBudget
