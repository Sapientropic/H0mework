import H0mework.Physics.LowEnergy.Quantum.GaussCoframeKinetic
import H0mework.Physics.LowEnergy.Quantum.GaussCoframeSpin

/-! Original coframe kinetic/current/contact/volume action on the same Gauss100 core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussCoframeForm
open GaussNativeEnergy GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussFockPair
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq

abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
def Paired (A B : End) : Prop := ∀ f g, sourcePair f (A g) = sourcePair (B f) g

private theorem paired_add {A B C D : End} (hA : Paired A B) (hC : Paired C D) :
    Paired (A+C) (B+D) := by
  intro f g
  simp only [LinearMap.add_apply, sourcePair, map_add, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) (hA f g) (hC f g)

private theorem paired_real {A B : End} (r : ℝ) (h : Paired A B) :
    Paired ((r : ℂ) • A) ((r : ℂ) • B) := by
  intro f g
  simp only [LinearMap.smul_apply, sourcePair, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  exact congrArg ((r : ℂ) * ·) (h f g)

private theorem paired_comp {A B C D : End} (hA : Paired A B) (hC : Paired C D) :
    Paired (A.comp C) (D.comp B) := fun f g => (hA f (C g)).trans (hC (B f) g)

private theorem paired_sum {ι : Type*} [Fintype ι] {A B : ι → End}
    (h : ∀ i, Paired (A i) (B i)) : Paired (∑ i, A i) (∑ i, B i) := by
  intro f g
  simp only [LinearMap.sum_apply, sourcePair, map_sum, inner_sum, sum_inner]
  exact Finset.sum_congr rfl (fun i _ => h i f g)

private theorem paired_symmetrize {A B : End} (hA : Paired A B) (hB : Paired B A) :
    Paired ((1/2 : ℂ) • (A+B)) ((1/2 : ℂ) • (A+B)) := by
  have h : Paired (A+B) (B+A) := paired_add hA hB
  rw [add_comm B A] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using paired_real (1/2) h

private theorem paired_sandwich {A M : End} (hA : Paired A A) (hM : Paired M M) :
    Paired (A.comp (M.comp A)) (A.comp (M.comp A)) := by
  have hMA : Paired (M.comp A) (A.comp M) := paired_comp hM hA
  have h : Paired (A.comp (M.comp A)) ((A.comp M).comp A) := paired_comp hA hMA
  simpa only [LinearMap.comp_assoc] using h

def mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : End :=
  (1/2 : ℂ) • ((GaussCoframeSpin.current a).comp
    ((GaussNativeForm.multiply c smooth).comp (GaussCoframeCore.momentum i)) +
    (GaussCoframeCore.adjoint i).comp
      ((GaussNativeForm.multiply c smooth).comp (GaussCoframeSpin.current a)))

theorem mixed_pair (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : Paired (mixed i a c smooth) (mixed i a c smooth) := by
  have hC : Paired (GaussCoframeSpin.current a) (GaussCoframeSpin.current a) := GaussCoframeSpin.current_pair a
  have hM : Paired (GaussNativeForm.multiply c smooth) (GaussNativeForm.multiply c smooth) :=
    GaussNativeForm.multiply_pair c smooth
  have hP : Paired (GaussCoframeCore.momentum i) (GaussCoframeCore.adjoint i) := GaussCoframeCore.momentum_pair i
  have hQ : Paired (GaussCoframeCore.adjoint i) (GaussCoframeCore.momentum i) := GaussCoframeKinetic.adjoint_pair i
  have hMP : Paired ((GaussNativeForm.multiply c smooth).comp (GaussCoframeCore.momentum i))
      ((GaussCoframeCore.adjoint i).comp (GaussNativeForm.multiply c smooth)) := paired_comp hM hP
  have hMC : Paired ((GaussNativeForm.multiply c smooth).comp (GaussCoframeSpin.current a))
      ((GaussCoframeSpin.current a).comp (GaussNativeForm.multiply c smooth)) := paired_comp hM hC
  have h1 := paired_comp hC hMP
  have h2 := paired_comp hQ hMC
  simp only [LinearMap.comp_assoc] at h1 h2
  exact paired_symmetrize h1 h2

def inverseVolume (z : SourceCoordinateSlice) : ℝ := sourceTime 0/volume z

theorem inverseVolume_smooth (z : physicalChart) : ContDiffAt ℝ ∞ inverseVolume z.val :=
  contDiffAt_const.div volume_smooth.contDiffAt (volume_pos z).ne'

def currentCoefficient (j : Fin 6) (z : SourceCoordinateSlice) : ℝ := inverseVolume z*z.1 j

theorem currentCoefficient_smooth (j : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (currentCoefficient j) z.val := (inverseVolume_smooth z).mul (by fun_prop)

def currentAction : End :=
  mixed 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0) +
  mixed 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1) +
  mixed 3 4 (fun z => -currentCoefficient 0 z) (fun z => (currentCoefficient_smooth 0 z).neg) +
  mixed 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2)

def spinWeight : Fin 7 → ℝ := ![-3/4,-3/4,-3/4,-1,-1,-1,3/4]

def spinSquare (a : Fin 7) : End :=
  (spinWeight a : ℂ) • (GaussCoframeSpin.current a).comp
    ((GaussNativeForm.multiply inverseVolume inverseVolume_smooth).comp (GaussCoframeSpin.current a))

def number : End :=
  GaussQuantumMultiplier.action (fun _ => Matrix.diagonal (fun _ : Mode => (1 : ℂ)))
    (fun _ => contDiffAt_const)

theorem number_apply (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    number f z word = (word.card : ℂ)*f z word := by
  change (SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize
    (Matrix.diagonal (fun _ : Mode => (1 : ℂ))) (fiberCoordinates (f z))) word = _
  have h := SaturationMonoid.PhysicsCore.LowEnergy.Fermion.occupationCharge_original_quantize
    (fun _ : Mode => (1 : ℂ))
  exact (congrFun (LinearMap.congr_fun h (fiberCoordinates (f z))) word).trans
    (SourceFockRaising.total_apply (fiberCoordinates (f z)) word)

theorem number_pair : Paired number number :=
  GaussQuantumMultiplier.action_pair _ _ (by intro z; simp)

def numberCoefficient (z : SourceCoordinateSlice) : ℝ := -(9/8 : ℝ)*inverseVolume z

theorem numberCoefficient_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ numberCoefficient z.val := contDiffAt_const.mul (inverseVolume_smooth z)

def numberShift : End := (1/2 : ℂ) •
  (number.comp (GaussNativeForm.multiply numberCoefficient numberCoefficient_smooth) +
    (GaussNativeForm.multiply numberCoefficient numberCoefficient_smooth).comp number)

def volumePotential (z : SourceCoordinateSlice) : ℝ := 3*sourceTime 0*volume z

theorem volumePotential_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ volumePotential z.val := contDiffAt_const.mul volume_smooth.contDiffAt

def coframeAction : End := GaussCoframeKinetic.kinetic + currentAction +
  (∑ a : Fin 7, spinSquare a) + numberShift + GaussNativeForm.multiply volumePotential volumePotential_smooth

theorem coframeAction_pair : Paired coframeAction coframeAction := by
  have hK : Paired GaussCoframeKinetic.kinetic GaussCoframeKinetic.kinetic := GaussCoframeKinetic.kinetic_pair
  have hC : Paired currentAction currentAction :=
    paired_add (paired_add (paired_add (mixed_pair _ _ _ _) (mixed_pair _ _ _ _))
      (mixed_pair _ _ _ _)) (mixed_pair _ _ _ _)
  have hS (a : Fin 7) : Paired (spinSquare a) (spinSquare a) :=
    paired_real (spinWeight a) (paired_sandwich (GaussCoframeSpin.current_pair a)
      (GaussNativeForm.multiply_pair inverseVolume inverseVolume_smooth))
  have hN : Paired numberShift numberShift :=
    paired_symmetrize
      (paired_comp number_pair (GaussNativeForm.multiply_pair numberCoefficient numberCoefficient_smooth))
      (paired_comp (GaussNativeForm.multiply_pair numberCoefficient numberCoefficient_smooth) number_pair)
  exact paired_add (paired_add (paired_add (paired_add hK hC) (paired_sum hS)) hN)
    (GaussNativeForm.multiply_pair _ _)

def coframeOperator : H →ₗ.[ℂ] H := realize coframeAction

#print axioms number_apply
#print axioms coframeAction
#print axioms coframeAction_pair
end LowEnergy.GaussCoframeForm
