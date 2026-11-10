import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedOrderedSpatialReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open ActualDressedFullCoulomb ActualDressedAngularSourceCoefficients ActualDressedUniformMaterialCoefficients
open ActualDressedOrderedStatic ActualDressedEMTensorClock ActualCompositeFieldCurrent ActualEMCurrentSplit ActualEMCarrierOwn
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open scoped Matrix BigOperators

abbrev DirectionParameters := MvPolynomial (Fin 3) ℂ
abbrev DirectionStaticPolynomials := (DirectionParameters[X])[X]

def directionValues (n : PhysicalMomentum) : Fin 3→ℂ := fun j => (n j : ℂ)

def directionSpecialize (n : PhysicalMomentum) : DirectionStaticPolynomials→+*(ℂ[X])[X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.eval (directionValues n)))

/-- The outer variable is damping, the inner variable spatial IR; direction stays in the same source coefficients. -/
def angularStaticSlice : AngularParameters→+*DirectionStaticPolynomials :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (Polynomial.C.comp MvPolynomial.C))
    (Fin.addCases (motive := fun _ => DirectionStaticPolynomials)
      (fun i : Fin 3 => if i=0 then Polynomial.C Polynomial.X else if i=1 then Polynomial.X else 0)
      (fun j : Fin 3 => Polynomial.C (Polynomial.C (MvPolynomial.X j))))

theorem static_direction_hom (n : PhysicalMomentum) :
    (directionSpecialize n).comp angularStaticSlice=staticIRClockSlice.comp (angularSpecialize n) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [directionSpecialize,angularStaticSlice,staticIRClockSlice,angularSpecialize]
  · intro i
    refine Fin.addCases (m:=3) (n:=3) (motive := fun j =>
      ((directionSpecialize n).comp angularStaticSlice) (MvPolynomial.X j)=
      (staticIRClockSlice.comp (angularSpecialize n)) (MvPolynomial.X j)) ?_ ?_ i
    · intro j
      simp [directionSpecialize,angularStaticSlice,staticIRClockSlice,angularSpecialize]
      split_ifs <;> simp_all
    · intro j
      simp only [RingHom.comp_apply,angularStaticSlice,angularSpecialize,MvPolynomial.eval₂Hom_X',Fin.addCases_right]
      simp [directionSpecialize,staticIRClockSlice,directionValues]

def angularDeterminant (event : DressedEvent) : AngularParameters := (angularClearedPencil event).det

def angularProbeNumerator (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : AngularParameters :=
  angularDenominator event*dotProduct (fun i => MvPolynomial.C (ActualCompositeFieldCurrent.compositeCurrent pd dL dR i))
    ((angularClearedPencil event).adjugate*ᵥfun j => MvPolynomial.C (ActualCompositeFieldCurrent.compositeCurrent ps sL sR j))

def angularEMNumerator (event : DressedEvent) : Matrix (Fin 4) (Fin 4) AngularParameters :=
  fun mu nu => angularDenominator event*dotProduct (fun i => MvPolynomial.C (emInsertion i mu))
    ((angularClearedPencil event).adjugate*ᵥfun j => MvPolynomial.C (emInsertion j nu))

private theorem adjugate_read_map {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
    (f : R→+*S) (H : Matrix ι ι R) (d : R) (fd fs : ι→R) :
    f (d*dotProduct fd (H.adjugate*ᵥfs))=
      f d*dotProduct (fun i => f (fd i)) ((H.map f).adjugate*ᵥfun j => f (fs j)) := by
  have adj : H.adjugate.map f=(H.map f).adjugate := f.map_adjugate H
  rw [map_mul,←adj]
  simp only [dotProduct,Matrix.mulVec,Matrix.map_apply,map_sum,map_mul]

theorem angular_determinant_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    angularSpecialize n (angularDeterminant event)=commonDeterminant event n := by
  have matrix : (angularSpecialize n).mapMatrix (angularClearedPencil event)=
      (angularClearedPencil event).map (angularSpecialize n) := by
    ext i j
    rfl
  rw [angularDeterminant,(angularSpecialize n).map_det,matrix,angular_pencil_specialize]
  rfl

theorem angular_probe_numerator_specialize (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    angularSpecialize n (angularProbeNumerator event pd ps dL dR sL sR)=commonCurrentNumerator event n pd ps dL dR sL sR := by
  unfold angularProbeNumerator commonCurrentNumerator
  rw [adjugate_read_map,angular_denominator_specialize,angular_pencil_specialize]
  simp only [angularSpecialize,MvPolynomial.eval₂Hom_C]

theorem angular_em_numerator_specialize (event : DressedEvent) (n : PhysicalMomentum) (mu nu : Fin 4) :
    angularSpecialize n (angularEMNumerator event mu nu)=commonEMTensorNumerator event n mu nu := by
  unfold angularEMNumerator commonEMTensorNumerator
  rw [adjugate_read_map,angular_denominator_specialize,angular_pencil_specialize]
  simp only [angularSpecialize,MvPolynomial.eval₂Hom_C]

def directionClockDeterminant (event : DressedEvent) : DirectionStaticPolynomials :=
  angularStaticSlice (angularDeterminant event)
def directionClockProbeNumerator (event : DressedEvent) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : DirectionStaticPolynomials :=
  angularStaticSlice (angularProbeNumerator event pd ps dL dR sL sR)
def directionClockEMNumerator (event : DressedEvent) : Matrix (Fin 4) (Fin 4) DirectionStaticPolynomials :=
  fun mu nu => angularStaticSlice (angularEMNumerator event mu nu)

theorem actual_direction_clock_determinant (event : DressedEvent) (n : PhysicalMomentum) :
    directionSpecialize n (directionClockDeterminant event)=irClockDeterminant event n := by
  change ((directionSpecialize n).comp angularStaticSlice) (angularDeterminant event)=_
  rw [static_direction_hom,RingHom.comp_apply,angular_determinant_specialize]
  rfl

theorem actual_direction_clock_probe (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    directionSpecialize n (directionClockProbeNumerator event pd ps dL dR sL sR)=
      irClockProbeNumerator event n pd ps dL dR sL sR := by
  change ((directionSpecialize n).comp angularStaticSlice) (angularProbeNumerator event pd ps dL dR sL sR)=_
  rw [static_direction_hom,RingHom.comp_apply,angular_probe_numerator_specialize]
  rfl

theorem actual_direction_clock_em (event : DressedEvent) (n : PhysicalMomentum) (mu nu : Fin 4) :
    directionSpecialize n (directionClockEMNumerator event mu nu)=irClockEMNumerator event n mu nu := by
  change ((directionSpecialize n).comp angularStaticSlice) (angularEMNumerator event mu nu)=_
  rw [static_direction_hom,RingHom.comp_apply,angular_em_numerator_specialize]
  rfl

end LowEnergy.GaussComposite.ActualDressedAngularSpherePrice
