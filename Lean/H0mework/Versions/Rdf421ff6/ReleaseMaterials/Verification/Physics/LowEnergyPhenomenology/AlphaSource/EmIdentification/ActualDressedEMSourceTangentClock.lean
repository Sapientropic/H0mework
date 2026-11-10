import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedEMCorrectedCouplingSourceOwn.ActualDressedEMCorrectedRootFluxConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularStaticCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMSourceTransport
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedAngularSourceCoefficients ActualDressedAngularSpherePrice
open ActualDressedZeroClockFrequency ActualDressedZeroClockVector ActualDressedEMQuantumThreshold
open ActualDressedEMClockDispersion ActualDressedUniformMaterialCoefficients
open scoped Matrix BigOperators Topology

/-- Inner variable is the spatial tangent, middle variable original frequency, outer variable damping. -/
abbrev TangentFrequency := (ℂ[X])[X]
abbrev TangentDamping := TangentFrequency[X]

def sourceTangentMomentum (n delta : PhysicalMomentum) (t : ℝ) : PhysicalMomentum := n+t • delta

def tangentClockSlice (eps : ℝ) (n delta : PhysicalMomentum) : AngularParameters→+*TangentDamping :=
  MvPolynomial.eval₂Hom (C.comp (C.comp C))
    (Fin.addCases (motive := fun _ => TangentDamping)
      (fun i : Fin 3 => if i=0 then C (C (C (eps : ℂ))) else if i=1 then X else C X)
      (fun j : Fin 3 => C (C (C (n j : ℂ)+X*C (delta j : ℂ)))))

def tangentSpecialize (t : ℝ) : TangentDamping→+*(ℂ[X])[X] :=
  mapRingHom (mapRingHom (evalRingHom (t : ℂ)))

theorem actual_tangent_clock_hom (eps t : ℝ) (n delta : PhysicalMomentum) :
    (tangentSpecialize t).comp (tangentClockSlice eps n delta)=
      (frequencyClockSlice eps).comp (angularSpecialize (sourceTangentMomentum n delta t)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [tangentSpecialize,tangentClockSlice,frequencyClockSlice,angularSpecialize]
  · intro i
    refine Fin.addCases (m:=3) (n:=3) (motive:=fun j =>
      ((tangentSpecialize t).comp (tangentClockSlice eps n delta)) (MvPolynomial.X j)=
        ((frequencyClockSlice eps).comp (angularSpecialize (sourceTangentMomentum n delta t))) (MvPolynomial.X j)) ?_ ?_ i
    · intro j
      simp [tangentSpecialize,tangentClockSlice,frequencyClockSlice,angularSpecialize]
      split_ifs <;> simp_all
    · intro j
      simp only [RingHom.comp_apply,tangentClockSlice,angularSpecialize,MvPolynomial.eval₂Hom_X',Fin.addCases_right]
      simp [tangentSpecialize,frequencyClockSlice,sourceTangentMomentum,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      exact mul_comm _ _

def sourceTangentClearing (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) : TangentDamping :=
  tangentClockSlice eps n delta (angularDenominator event)

def sourceTangentPencil (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) TangentDamping :=
  (angularClearedPencil event).map (tangentClockSlice eps n delta)

def sourceTangentQuantum (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) TangentDamping :=
  (angularNumerator event).map (tangentClockSlice eps n delta)

def sourceTangentOrder (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) : ℕ :=
  (sourceTangentClearing event eps n delta).natTrailingDegree

def sourceTangentThresholdClearing (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) : TangentFrequency :=
  (sourceTangentClearing event eps n delta).coeff (sourceTangentOrder event eps n delta)

def sourceTangentThresholdPencil (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) TangentFrequency :=
  fun i j => (sourceTangentPencil event eps n delta i j).coeff (sourceTangentOrder event eps n delta)

def sourceTangentThresholdQuantum (event : DressedEvent) (eps : ℝ) (n delta : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) TangentFrequency :=
  fun i j => (X*sourceTangentQuantum event eps n delta i j).coeff (sourceTangentOrder event eps n delta)

def tangentFrequencySpecialize (t : ℝ) : TangentFrequency→+*ℂ[X] := mapRingHom (evalRingHom (t : ℂ))

theorem actual_tangent_full_clearing (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum) :
    tangentSpecialize t (sourceTangentClearing event eps n delta)=
      fullClockClearing event eps (sourceTangentMomentum n delta t) := by
  change ((tangentSpecialize t).comp (tangentClockSlice eps n delta)) (angularDenominator event)=_
  rw [actual_tangent_clock_hom,RingHom.comp_apply,angular_denominator_specialize]
  rfl

theorem actual_tangent_full_pencil (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum) :
    (sourceTangentPencil event eps n delta).map (tangentSpecialize t)=
      fullClockPencil event eps (sourceTangentMomentum n delta t) := by
  rw [sourceTangentPencil,Matrix.map_map]
  change (angularClearedPencil event).map ((tangentSpecialize t).comp (tangentClockSlice eps n delta))=_
  rw [actual_tangent_clock_hom]
  change (angularClearedPencil event).map
    (⇑(frequencyClockSlice eps) ∘ ⇑(angularSpecialize (sourceTangentMomentum n delta t)))=_
  rw [←Matrix.map_map,angular_pencil_specialize]
  rfl

theorem actual_tangent_full_quantum (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum) :
    (sourceTangentQuantum event eps n delta).map (tangentSpecialize t)=
      fullClockQuantumNumerator event eps (sourceTangentMomentum n delta t) := by
  rw [sourceTangentQuantum,Matrix.map_map]
  change (angularNumerator event).map ((tangentSpecialize t).comp (tangentClockSlice eps n delta))=_
  rw [actual_tangent_clock_hom]
  change (angularNumerator event).map
    (⇑(frequencyClockSlice eps) ∘ ⇑(angularSpecialize (sourceTangentMomentum n delta t)))=_
  rw [←Matrix.map_map,angular_numerator_specialize]
  rfl

/-- The source leading coefficient itself selects a chart where the original damping order is fixed. -/
theorem actual_tangent_clock_order (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum)
    (regular : tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)≠0) :
    clearingClockOrder event eps (sourceTangentMomentum n delta t)=sourceTangentOrder event eps n delta := by
  let P := sourceTangentClearing event eps n delta
  let f := tangentFrequencySpecialize t
  have same : P.map f=fullClockClearing event eps (sourceTangentMomentum n delta t) :=
    actual_tangent_full_clearing event eps t n delta
  have lead : (P.map f).coeff P.natTrailingDegree≠0 := by
    simpa only [coeff_map,sourceTangentThresholdClearing,sourceTangentOrder,P,f] using regular
  have nonzero : P.map f≠0 := by intro h;rw [h,coeff_zero] at lead;exact lead rfl
  have lower : ∀m<P.natTrailingDegree,(P.map f).coeff m=0 := by
    intro m hm
    rw [coeff_map,coeff_eq_zero_of_lt_natTrailingDegree hm,map_zero]
  have equal := le_antisymm (natTrailingDegree_le_of_ne_zero lead) (le_natTrailingDegree nonzero lower)
  simpa only [same,clearingClockOrder,sourceTangentOrder,P] using equal

theorem actual_tangent_threshold_clearing (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum)
    (regular : tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)≠0) :
    tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)=
      zeroClockClearing event eps (sourceTangentMomentum n delta t) := by
  have order := actual_tangent_clock_order event eps t n delta regular
  have coefficient := congrArg (fun P : (ℂ[X])[X] => P.coeff (sourceTangentOrder event eps n delta))
    (actual_tangent_full_clearing event eps t n delta)
  simpa only [tangentSpecialize,Polynomial.coe_mapRingHom,coeff_map,zeroClockClearing,order,
    sourceTangentThresholdClearing,tangentFrequencySpecialize] using coefficient

theorem actual_tangent_threshold_pencil (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum)
    (regular : tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)≠0) :
    (sourceTangentThresholdPencil event eps n delta).map (tangentFrequencySpecialize t)=
      zeroClockPencil event eps (sourceTangentMomentum n delta t) := by
  have order := actual_tangent_clock_order event eps t n delta regular
  funext i j
  have coefficient := congrArg (fun M : Matrix (Fin 289) (Fin 289) (ℂ[X])[X] =>
    (M i j).coeff (sourceTangentOrder event eps n delta)) (actual_tangent_full_pencil event eps t n delta)
  simpa only [Matrix.map_apply,tangentSpecialize,Polynomial.coe_mapRingHom,coeff_map,
    sourceTangentThresholdPencil,tangentFrequencySpecialize,zeroClockPencil,order] using coefficient

theorem actual_tangent_threshold_quantum (event : DressedEvent) (eps t : ℝ) (n delta : PhysicalMomentum)
    (regular : tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)≠0) :
    (sourceTangentThresholdQuantum event eps n delta).map (tangentFrequencySpecialize t)=
      zeroClockQuantumNumerator event eps (sourceTangentMomentum n delta t) := by
  have order := actual_tangent_clock_order event eps t n delta regular
  funext i j
  have mapped := congrFun (congrFun (actual_tangent_full_quantum event eps t n delta) i) j
  have coefficient := congrArg (fun P : (ℂ[X])[X] => (X*P).coeff (sourceTangentOrder event eps n delta)) mapped
  simp only [Matrix.map_apply] at coefficient
  have natural : X*(tangentSpecialize t (sourceTangentQuantum event eps n delta i j))=
      tangentSpecialize t (X*sourceTangentQuantum event eps n delta i j) := by
    rw [map_mul]
    simp [tangentSpecialize]
  rw [natural] at coefficient
  simpa only [Matrix.map_apply,tangentSpecialize,Polynomial.coe_mapRingHom,coeff_map,
    sourceTangentThresholdQuantum,tangentFrequencySpecialize,zeroClockQuantumNumerator,order] using coefficient

end LowEnergy.GaussComposite.ActualDressedEMSourceTransport
