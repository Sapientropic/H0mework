import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Coulomb
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.EnergyDefs
import Mathlib.Analysis.Calculus.FDeriv.Star

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.Elementwise
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame}

theorem raw_nuclear_source (source : CPS1ElectronicSource.State frame)
    (p q : CPS1MolecularFrame.PrimitiveIndex source) (jetP jetQ : Fin 3 → Nat) (spin : Bool) (nuclear : Point) :
    rawNuclearIntegralAt source (sourcePositions source) p q jetP jetQ spin nuclear =
      CPS1MolecularFrame.rawNuclearIntegral source p q jetP jetQ spin nuclear := rfl

theorem raw_pair_source (source : CPS1ElectronicSource.State frame)
    (p q r s : CPS1MolecularFrame.PrimitiveIndex source) (spin secondSpin : Bool) :
    rawPairIntegralAt source (sourcePositions source) p q r s spin secondSpin =
      CPS1MolecularFrame.rawPairIntegral source p q r s spin secondSpin := rfl

theorem nuclear_integral_source (source : CPS1ElectronicSource.State frame)
    (i j : CPS1MolecularFrame.ActualIndex source) (nuclear : Point) :
    nuclearIntegralAt source (sourcePositions source) i j nuclear = CPS1MolecularFrame.nuclearIntegral source i j nuclear := by
  simp only [nuclearIntegralAt,raw_nuclear_source]
  exact (CPS1MolecularFrame.nuclear_integral_expansion source i j nuclear).symm

theorem pair_integral_source (source : CPS1ElectronicSource.State frame)
    (i j k l : CPS1MolecularFrame.ActualIndex source) (spin secondSpin : Bool) :
    pairIntegralAt source (sourcePositions source) i j k l spin secondSpin =
      CPS1MolecularFrame.pairIntegral source i j k l spin secondSpin := by
  simp only [pairIntegralAt,raw_pair_source]
  exact (CPS1MolecularFrame.pair_integral_expansion source i j k l spin secondSpin).symm

theorem two_body_source (source : CPS1ElectronicSource.State frame) (i j k l : CPS1MolecularFrame.ActualIndex source) :
    twoBodyAt source (sourcePositions source) i j k l = CPS1MolecularFrame.twoBody source i j k l := by
  simp only [twoBodyAt,pair_integral_source,CPS1MolecularFrame.twoBody]

theorem kinetic_source (source : CPS1ElectronicSource.State frame) (i j : CPS1MolecularFrame.ActualIndex source) :
    kineticAt source (sourcePositions source) i j = CPS1MolecularFrame.kinetic source i j := by
  simp only [kineticAt,basis_jet_source,CPS1MolecularFrame.kinetic]

theorem attraction_source (source : CPS1ElectronicSource.State frame) (i j : CPS1MolecularFrame.ActualIndex source) :
    attractionAt source (sourcePositions source) i j = CPS1MolecularFrame.attraction source i j := by
  simp only [attractionAt,nuclear_integral_source,CPS1MolecularFrame.attraction]
  apply congrArg List.sum
  have generated := congrArg (List.map (fun nucleus : CPS1AtomicDynamics.Body.Node =>
    -(nucleus.particle.charge : ℂ)*CPS1MolecularFrame.nuclearIntegral source i j (Geometry.nucleusPosition nucleus)))
      (CPS1MolecularFrame.actual_nuclei_complete source)
  simpa only [List.map_ofFn,sourcePositions,CPS1MolecularFrame.position,Function.comp_def] using generated

theorem core_source (source : CPS1ElectronicSource.State frame) :
    coreAt source (sourcePositions source) = CPS1MolecularFrame.core source := by
  funext i j
  simp only [coreAt,kinetic_source,attraction_source,CPS1MolecularFrame.core]

theorem energy_source (source : CPS1ElectronicSource.State frame) (occupied : OccupiedConfiguration source) :
    energyAt source (sourcePositions source) occupied =
      CPS1MolecularFrame.totalEnergy source (occupied*occupied.conjTranspose) := by
  simp only [energyAt,nuclear_energy_source,electronicEnergyAt,core_source,two_body_source,densityAt,
    CPS1MolecularFrame.totalEnergy,CPS1MolecularFrame.electronicEnergy,Geometry.nuclearEnergy]

theorem material_energy_source (state : CPS1MolecularFrame.Material frame) :
    energyAt state.reference (sourcePositions state.reference) state.occupied = state.energy :=
  energy_source state.reference state.occupied

theorem energy_with_momenta_source (source : CPS1ElectronicSource.State frame) (occupied : OccupiedConfiguration source) :
    energyWithMomenta source (sourcePositions source) (energySourceMomenta source) occupied =
      CPS1MolecularFrame.totalEnergy source (occupied*occupied.conjTranspose) := by
  exact energy_source source occupied

theorem physical_fock_source (source : CPS1ElectronicSource.State frame) (occupied : OccupiedConfiguration source) :
    physicalFockAt source (sourcePositions source) occupied =
      CPS1MolecularFrame.fock source (occupied*occupied.conjTranspose) := by
  funext i k
  simp only [physicalFockAt,core_source,two_body_source,densityAt,CPS1MolecularFrame.fock]

def selectedNuclearPositions (source : CPS1ElectronicSource.State frame)
    (p q : CPS1MolecularFrame.PrimitiveIndex source) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    NuclearConfiguration source →L[ℝ] (Fin 3 → Point) :=
  ContinuousLinearMap.pi ![
    (ContinuousLinearMap.proj p.1.1 : NuclearConfiguration source →L[ℝ] Point),
    (ContinuousLinearMap.proj q.1.1 : NuclearConfiguration source →L[ℝ] Point),
    (ContinuousLinearMap.proj nuclear : NuclearConfiguration source →L[ℝ] Point)]

def selectedPairPositions (source : CPS1ElectronicSource.State frame)
    (p q r s : CPS1MolecularFrame.PrimitiveIndex source) : NuclearConfiguration source →L[ℝ] (Fin 4 → Point) :=
  ContinuousLinearMap.pi ![
    (ContinuousLinearMap.proj p.1.1 : NuclearConfiguration source →L[ℝ] Point),
    (ContinuousLinearMap.proj q.1.1 : NuclearConfiguration source →L[ℝ] Point),
    (ContinuousLinearMap.proj r.1.1 : NuclearConfiguration source →L[ℝ] Point),
    (ContinuousLinearMap.proj s.1.1 : NuclearConfiguration source →L[ℝ] Point)]

theorem raw_nuclear_differentiable (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (p q : CPS1MolecularFrame.PrimitiveIndex source) (jetP jetQ : Fin 3 → Nat) (spin : Bool)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    DifferentiableAt ℝ (fun next => rawNuclearIntegralAt source next p q jetP jetQ spin (next nuclear)) positions := by
  by_cases matching : p.2 = spin ∧ q.2 = spin
  · simp only [rawNuclearIntegralAt,if_pos matching]
    have generated := (multicentre_nuclear_hasFDerivAt p.1.2.val q.1.2.val jetP jetQ
      (selectedNuclearPositions source p q nuclear positions)).comp positions
        (selectedNuclearPositions source p q nuclear).hasFDerivAt
    exact generated.differentiableAt
  · simp only [rawNuclearIntegralAt,if_neg matching]
    exact differentiableAt_const 0

theorem raw_pair_differentiable (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (p q r s : CPS1MolecularFrame.PrimitiveIndex source) (spin secondSpin : Bool) :
    DifferentiableAt ℝ (fun next => rawPairIntegralAt source next p q r s spin secondSpin) positions := by
  by_cases matching : p.2 = spin ∧ q.2 = spin ∧ r.2 = secondSpin ∧ s.2 = secondSpin
  · simp only [rawPairIntegralAt,if_pos matching]
    have generated := (multicentre_pair_hasFDerivAt ![p.1.2.val,q.1.2.val,r.1.2.val,s.1.2.val] (fun _ => 0)
      (selectedPairPositions source p q r s positions)).comp positions (selectedPairPositions source p q r s).hasFDerivAt
    exact generated.differentiableAt
  · simp only [rawPairIntegralAt,if_neg matching]
    exact differentiableAt_const 0

theorem nuclear_integral_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (i j : CPS1MolecularFrame.ActualIndex source)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    DifferentiableAt ℝ (fun next => nuclearIntegralAt source next i j (next nuclear)) positions := by
  exact DifferentiableAt.fun_sum (u := Finset.univ) (fun spin _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ =>
        (raw_nuclear_differentiable source positions p q 0 0 spin nuclear).const_mul
          (star (CPS1MolecularFrame.basisCoefficient source p i)*CPS1MolecularFrame.basisCoefficient source q j))))

theorem pair_integral_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (i j k l : CPS1MolecularFrame.ActualIndex source) (spin secondSpin : Bool) :
    DifferentiableAt ℝ (fun next => pairIntegralAt source next i j k l spin secondSpin) positions := by
  exact DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun r _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) (fun s _ =>
          (raw_pair_differentiable source positions p q r s spin secondSpin).const_mul
            (star (CPS1MolecularFrame.basisCoefficient source p i)*CPS1MolecularFrame.basisCoefficient source q j*
              star (CPS1MolecularFrame.basisCoefficient source r k)*CPS1MolecularFrame.basisCoefficient source s l)))))

theorem two_body_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (i j k l : CPS1MolecularFrame.ActualIndex source) :
    DifferentiableAt ℝ (fun next => twoBodyAt source next i j k l) positions :=
  DifferentiableAt.fun_sum (u := Finset.univ) (fun spin _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun secondSpin _ =>
      pair_integral_differentiable source positions i k j l spin secondSpin))

theorem kinetic_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (i j : CPS1MolecularFrame.ActualIndex source) :
    DifferentiableAt ℝ (fun next => kineticAt source next i j) positions := by
  exact (DifferentiableAt.fun_sum (u := Finset.univ) (fun axis _ =>
    ((basis_jet_hasFDerivAt source positions i (raise 0 axis)).inner ℂ
      (basis_jet_hasFDerivAt source positions j (raise 0 axis))).differentiableAt)).const_mul
        ((1/(2*source.geometry.electronInertia) : ℝ) : ℂ)

private theorem complex_list_differentiable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type*} (indices : List I) (values : I → X → ℂ) (current : X)
    (each : ∀ index ∈ indices, DifferentiableAt ℝ (values index) current) :
    DifferentiableAt ℝ (fun next => (indices.map (fun index => values index next)).sum) current := by
  induction indices with
  | nil => exact differentiableAt_const 0
  | cons index rest ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (each index (List.mem_cons_self)).add (ih (fun other member => each other (List.mem_cons_of_mem _ member)))

theorem attraction_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (i j : CPS1MolecularFrame.ActualIndex source) :
    DifferentiableAt ℝ (fun next => attractionAt source next i j) positions := by
  have each (nuclear : CPS1MolecularFrame.NuclearIndex source) :=
    (nuclear_integral_differentiable source positions i j nuclear).const_mul
      (-((CPS1MolecularFrame.nucleus source nuclear).particle.charge : ℂ))
  have generated := complex_list_differentiable (List.finRange source.geometry.nuclei.length)
    (fun nuclear next => -((CPS1MolecularFrame.nucleus source nuclear).particle.charge : ℂ)*
      nuclearIntegralAt source next i j (next nuclear)) positions (fun nuclear _ => each nuclear)
  simpa only [attractionAt,List.ofFn_eq_map] using generated

theorem core_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (i j : CPS1MolecularFrame.ActualIndex source) :
    DifferentiableAt ℝ (fun next => coreAt source next i j) positions :=
  (kinetic_differentiable source positions i j).add (attraction_differentiable source positions i j)

def occupiedCoordinate (source : CPS1ElectronicSource.State frame) (i : CPS1MolecularFrame.ActualIndex source)
    (electron : ElectronIndex source.geometry) : EnergyConfiguration source →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj electron : (ElectronIndex source.geometry → ℂ) →L[ℝ] ℂ).comp
    ((ContinuousLinearMap.proj i : OccupiedConfiguration source →L[ℝ] (ElectronIndex source.geometry → ℂ)).comp
      (ContinuousLinearMap.snd ℝ (NuclearConfiguration source) (OccupiedConfiguration source)))

theorem density_entry_differentiable (source : CPS1ElectronicSource.State frame)
    (current : EnergyConfiguration source) (i j : CPS1MolecularFrame.ActualIndex source) :
    DifferentiableAt ℝ (fun next : EnergyConfiguration source => densityAt source next.2 i j) current := by
  unfold densityAt
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
  have each (electron : ElectronIndex source.geometry) :
      DifferentiableAt ℝ (fun next : EnergyConfiguration source => next.2 i electron*star (next.2 j electron)) current := by
    have first : DifferentiableAt ℝ (fun next : EnergyConfiguration source => next.2 i electron) current :=
      (occupiedCoordinate source i electron).differentiableAt
    have second : DifferentiableAt ℝ (fun next : EnergyConfiguration source => next.2 j electron) current :=
      (occupiedCoordinate source j electron).differentiableAt
    have conjugate : DifferentiableAt ℝ (fun next : EnergyConfiguration source => star (next.2 j electron)) current :=
      DifferentiableAt.star (𝕜 := ℝ) second
    exact DifferentiableAt.mul (𝕜 := ℝ) (𝔸 := ℂ) first conjugate
  exact DifferentiableAt.fun_sum (𝕜 := ℝ) (E := EnergyConfiguration source) (F := ℂ)
    (u := Finset.univ) (A := fun electron next => next.2 i electron*star (next.2 j electron))
      (fun electron _ => each electron)

theorem electronic_energy_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source) :
    DifferentiableAt ℝ (fun next : EnergyConfiguration source => electronicEnergyAt source next.1 next.2)
      (positions,occupied) := by
  classical
  let current : EnergyConfiguration source := (positions,occupied)
  have positional : DifferentiableAt ℝ (Prod.fst : EnergyConfiguration source → NuclearConfiguration source) current :=
    differentiableAt_fst
  have coreEntry (i j : CPS1MolecularFrame.ActualIndex source) :
      DifferentiableAt ℝ (fun next : EnergyConfiguration source => coreAt source next.1 i j) current :=
    (core_differentiable source positions i j).comp
      (f := (Prod.fst : EnergyConfiguration source → NuclearConfiguration source))
      (g := fun next : NuclearConfiguration source => coreAt source next i j) current positional
  have pairEntry (i j k l : CPS1MolecularFrame.ActualIndex source) :
      DifferentiableAt ℝ (fun next : EnergyConfiguration source => twoBodyAt source next.1 i j k l) current :=
    (two_body_differentiable source positions i j k l).comp
      (f := (Prod.fst : EnergyConfiguration source → NuclearConfiguration source))
      (g := fun next : NuclearConfiguration source => twoBodyAt source next i j k l) current positional
  have densityEntry (i j : CPS1MolecularFrame.ActualIndex source) :
      DifferentiableAt ℝ (fun next : EnergyConfiguration source => densityAt source next.2 i j) current :=
    density_entry_differentiable source current i j
  have oneBody : DifferentiableAt ℝ (fun next : EnergyConfiguration source =>
      ∑ i, ∑ j, coreAt source next.1 i j*densityAt source next.2 j i) current :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun i _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => (coreEntry i j).mul (densityEntry j i)))
  have pairBody : DifferentiableAt ℝ (fun next : EnergyConfiguration source =>
      ∑ i, ∑ j, ∑ k, ∑ l, densityAt source next.2 k i*densityAt source next.2 l j*
        (twoBodyAt source next.1 i j k l-twoBodyAt source next.1 i j l k)) current :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun i _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun k _ =>
        DifferentiableAt.fun_sum (u := Finset.univ) (fun l _ =>
          ((densityEntry k i).mul (densityEntry l j)).mul ((pairEntry i j k l).sub (pairEntry i j l k))))))
  have oneReal := Complex.reCLM.differentiableAt.comp current oneBody
  have pairReal := (Complex.reCLM.differentiableAt.comp current pairBody).const_smul (1/2 : ℝ)
  change DifferentiableAt ℝ (fun next : EnergyConfiguration source => electronicEnergyAt source next.1 next.2) current
  apply (oneReal.add pairReal).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun next => by
    simp only [electronicEnergyAt,Matrix.trace,Matrix.diag,Matrix.mul_apply,smul_eq_mul,
      Function.comp_def,Complex.reCLM_apply,Pi.add_apply,Pi.smul_apply]

theorem energy_hasFDerivAt (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source)
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    HasFDerivAt (fun next : EnergyConfiguration source => energyAt source next.1 next.2)
      (energyDifferential source positions occupied) (positions,occupied) := by
  classical
  let lifted : EnergyConfiguration source →L[ℝ] (NuclearConfiguration source × NuclearConfiguration source) :=
    (ContinuousLinearMap.fst ℝ (NuclearConfiguration source) (OccupiedConfiguration source)).prod 0
  have coordinates : HasFDerivAt (fun next : EnergyConfiguration source => (next.1,energySourceMomenta source))
      lifted (positions,occupied) :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (positions,occupied))).prodMk
      (hasFDerivAt_const (energySourceMomenta source) (positions,occupied))
  have nuclear := (nuclear_energy_hasFDerivAt source positions (energySourceMomenta source) ready).comp
    (positions,occupied) coordinates
  exact (nuclear.differentiableAt.add (electronic_energy_differentiable source positions occupied)).hasFDerivAt

theorem energy_with_momenta_hasFDerivAt (source : CPS1ElectronicSource.State frame)
    (positions momenta : NuclearConfiguration source) (occupied : OccupiedConfiguration source)
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    HasFDerivAt (fun next : EnergyConfiguration source => energyWithMomenta source next.1 momenta next.2)
      (energyDifferential source positions occupied) (positions,occupied) := by
  classical
  have difference : (fun next : EnergyConfiguration source => energyWithMomenta source next.1 momenta next.2) =
      fun next => energyAt source next.1 next.2+
        (nuclearKineticAt source momenta-nuclearKineticAt source (energySourceMomenta source)) := by
    funext next
    unfold energyWithMomenta energyAt nuclearEnergyAt
    ring
  rw [difference]
  exact (energy_hasFDerivAt source positions occupied ready).add_const _

end
end CPS1Deformation
