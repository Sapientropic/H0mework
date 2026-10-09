import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateQuarticFinite
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorContactVertices
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorScalar61Exchange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.ActualCandidateVertexEntries
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open StageNineHolonomicField StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity DiracExteriorMatterAction
open StageNineResidualLimitScalarBalanceClosure StageNineExteriorMotherLieRepresentation
open StageNineP286LinkedActiveLieRepresentation
open SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open MixedSpectatorCandidate MixedSpectatorContactVertices
open DiracCliffordRepresentation Stage9C.Material.SpinPair
open GaugeProjection.ConcreteBlockDiagonal PointwiseDiracSpinConnectionLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open scoped BigOperators Matrix
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

abbrev Support := Fin 4 × Fin 3
def supportNamed (i : Support) : NamedMode := (i.1,i.2,if i.1 < 2 then 0 else 1)
def supportMode (dual : Bool) (i : Support) : Mode := rootMode dual (supportNamed i)

private theorem matter_enumeration (c : Fin 3) (h position : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm (internalBasis c h) position =
      if position = 0 then Sum.inl c else spectator h := by
  let family : Fin 2 → SU7MotherIndex := fun position => if position = 0 then Sum.inl c else spectator h
  have hm (position : Fin 2) : family position ∈ (internalBasis c h).val := by
    change family position ∈ {Sum.inl c,spectator h}
    by_cases hp : position = 0 <;> simp [family,hp]
  have he : family = (internalBasis c h).val.orderEmbOfFin (internalBasis c h).property := by
    apply Finset.orderEmbOfFin_unique _ hm
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try norm_num at hij
    change smBlockIndexEquivFin7 (Sum.inl c) < smBlockIndexEquivFin7 (spectator h)
    fin_cases c <;> fin_cases h <;> decide
  exact (congrFun he position).symm

/-- The actual exterior two-slot action, with neither a fitted table nor a compressed product. -/
def gaugeEntry (M : SU7MotherLieMatrix) (c : Fin 3) (h : Fin 2) (d : Fin 3) (k : Fin 2) : ℂ :=
  (if h = k then M.val (Sum.inl c) (Sum.inl d) else 0) +
  (if c = d then M.val (spectator h) (spectator k) else 0)

theorem actual_exterior_entry (M : SU7MotherLieMatrix) (c : Fin 3) (h : Fin 2) (d : Fin 3) (k : Fin 2) :
    (su7ExteriorBasis 2).repr (exteriorMotherLieAction 2 M
      (su7ExteriorBasis 2 (internalBasis d k))) (internalBasis c h) = gaugeEntry M c h d k := by
  rw [exteriorMotherLieAction_basis_current]
  unfold exteriorBasisLieAction
  rw [map_sum]
  change (∑ position : Fin 2, (su7ExteriorBasis 2).repr
    ((exteriorPower.ιMulti ℂ 2) (exteriorBasisLieActionInput 2 M (internalBasis d k) position))
      (internalBasis c h)) = _
  simp_rw [exteriorBasisLieActionTerm_eq_update]
  unfold su7ExteriorBasis
  simp_rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  fin_cases c <;> fin_cases h <;> fin_cases d <;> fin_cases k <;>
    simp [gaugeEntry, Matrix.det_fin_two, Fin.sum_univ_two, exteriorBasisInput,
      exteriorPositionEquiv, matter_enumeration, fundamentalMotherLieAction,
      Matrix.mulVecLin, su7FundamentalBasis, spectator, hyperPlusIndex]

private theorem named_value (i : NamedMode) :
    namedColumn i = Pi.single i.1 (0,su7ExteriorBasis 2 (internalBasis i.2.1 i.2.2),0) := by
  rw [namedColumn,Quantum.wholeBasis,Pi.basis_apply]
  congr 1
  apply Prod.ext
  · simp [Quantum.internalBasis,rootIndex]
  · apply Prod.ext <;> simp [Quantum.internalBasis,rootIndex]

private theorem matrix_entry (A : FullQuantum.Mother) (i j : NamedMode) :
    Quantum.operatorMatrix A (rootIndex i) (rootIndex j) =
      Quantum.coordinates (A (namedColumn j)) (rootIndex i) := by
  have h := congrFun (Quantum.matrix_action A (namedColumn j)) (rootIndex i)
  rw [actual_named_column_coordinates] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

private theorem coordinates_two (v : DiracExteriorMatterCarrier) (i : NamedMode) :
    Quantum.coordinates v (rootIndex i) =
      (su7ExteriorBasis 2).repr (v i.1).2.1 (internalBasis i.2.1 i.2.2) := rfl

private theorem yukawa_two (phi : ExteriorBreakingScalarCarrier) (v : DiracExteriorMatterCarrier)
    (i : NamedMode) : Quantum.coordinates (diracDualRightChiralYukawaAction phi v) (rootIndex i) = 0 := by
  rw [coordinates_two]
  simp [diracDualRightChiralYukawaAction,diracExteriorYukawaInternalAction,
    internalMatterLinearAction,exteriorYukawaInternalAction]



def basisEntry (i j : NamedMode) : ℂ := if i = j then 1 else 0

def spinEntry (S : DiracMatrix) (i j : NamedMode) : ℂ :=
  ∑ r : Fin 4, S i.1 r * basisEntry (r,i.2) j

def internalEntry (M : SU7MotherLieMatrix) (i j : NamedMode) : ℂ :=
  if i.1 = j.1 then gaugeEntry M i.2.1 i.2.2 j.2.1 j.2.2 else 0

private theorem basis_coordinates (i j : NamedMode) :
    Quantum.coordinates (namedColumn j) (rootIndex i) = basisEntry i j := by
  rw [actual_named_column_coordinates]
  simp [basisEntry, Pi.single_apply, rootIndex_injective.eq_iff]

private theorem spin_coordinates (S : DiracMatrix) (i j : NamedMode) :
    Quantum.coordinates (spin S (namedColumn j)) (rootIndex i) = spinEntry S i j := by
  rw [spin,GaussCoframeSpin.coordinates_spin]
  change (∑ r : Fin 4, S i.1 r * Quantum.coordinates (namedColumn j) (rootIndex (r,i.2))) = _
  simp_rw [basis_coordinates]
  rfl

private theorem internal_coordinates (M : SU7MotherLieMatrix) (i j : NamedMode) :
    Quantum.coordinates (diracExteriorMotherLieAction M (namedColumn j)) (rootIndex i) = internalEntry M i j := by
  rw [coordinates_two,named_value]
  by_cases h : i.1 = j.1
  · simp only [diracExteriorMotherLieAction, internalMatterLinearAction, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.single_apply, h, ite_true, exteriorSpinorMotherLieAction,
      LinearMap.prodMap_apply]
    exact (actual_exterior_entry M i.2.1 i.2.2 j.2.1 j.2.2).trans (by simp [internalEntry,h])
  · simp [diracExteriorMotherLieAction,internalMatterLinearAction,h,internalEntry]

def connectionEntry (mu : Fin 4) (i j : NamedMode) : ℂ :=
  spinEntry (diracSpinConnectionLift (actual.gravityConnection 0) mu) i j +
  internalEntry (p286LieBlockEmbed (actual.gaugeConnection 0 mu)) i j

private theorem connection_coordinates (mu : Fin 4) (i j : NamedMode) :
    Quantum.coordinates (FullQuantum.connection actual 0 mu (namedColumn j)) (rootIndex i) = connectionEntry mu i j := by
  change Quantum.coordinates ((spin _ + diracExteriorMotherLieAction _) (namedColumn j)) (rootIndex i) = _
  simp only [LinearMap.add_apply,map_add,Pi.add_apply]
  rw [spin_coordinates,internal_coordinates]
  rfl

private theorem phase_coordinates (i j : NamedMode) :
    Quantum.coordinates (FullPhase.phaseGenerator (namedColumn j)) (rootIndex i) = spinEntry diracGammaFive i j := by
  change Quantum.coordinates ((spin diracGammaFive + (2 : ℂ) • MixedSymbol.degreeSix) (namedColumn j)) (rootIndex i) = _
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,Pi.add_apply,Pi.smul_apply]
  rw [spin_coordinates,coordinates_two]
  simp [MixedSymbol.degreeSix]

private theorem spin_action_coordinates (S : DiracMatrix) (v : DiracExteriorMatterCarrier) (i : NamedMode) :
    Quantum.coordinates (spin S v) (rootIndex i) =
      ∑r : Fin 4, S i.1 r * Quantum.coordinates v (rootIndex (r,i.2)) :=
  GaussCoframeSpin.coordinates_spin S v (rootIndex i)

def jetEntry (p : Fin 4 → ℂ) (mu b : Fin 4) (i j : NamedMode) : ℂ :=
  Complex.I * (p mu * spinEntry (diracGamma b) i j +
    ∑ r : Fin 4, diracGamma b i.1 r * connectionEntry mu (r,i.2) j) +
  (if mu = 0 then (frequency : ℂ) *
    (∑ r : Fin 4, diracGamma b i.1 r * spinEntry diracGammaFive (r,i.2) j) else 0)

private theorem jet_coordinates (p : Fin 4 → ℂ) (mu b : Fin 4) (i j : NamedMode) :
    Quantum.coordinates (sourceJet p mu b (namedColumn j)) (rootIndex i) = jetEntry p mu b i j := by
  unfold sourceJet jetEntry
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,map_add,map_smul,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Module.End.one_apply]
  rw [spin_coordinates,spin_action_coordinates]
  simp_rw [connection_coordinates]
  congr 1
  split_ifs <;> simp only [LinearMap.smul_apply,map_smul,Pi.smul_apply,smul_eq_mul,
    Module.End.mul_apply,spin_action_coordinates,LinearMap.zero_apply,map_zero,Pi.zero_apply]
  simp_rw [phase_coordinates]

def coframeEntry (p : Fin 4 → ℂ) (a nu : Fin 4) (i j : NamedMode) : ℂ :=
  ∑ mu : Fin 4, ∑ b : Fin 4, (adjugateDerivative a nu mu b : ℂ) * jetEntry p mu b i j

private theorem coframe_coordinates (p : Fin 4 → ℂ) (a nu : Fin 4) (i j : NamedMode) :
    Quantum.coordinates (coframeVertex p a nu (namedColumn j)) (rootIndex i) = coframeEntry p a nu i j := by
  unfold coframeVertex
  simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_add,map_sum,map_smul,
    Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,yukawa_two,mul_zero,add_zero]
  simp_rw [jet_coordinates]
  rfl

def rawEntry (p : Fin 4 → ℂ) (a : Fin 97) (i j : NamedMode) : ℂ :=
  if h : a.val < 9 then 0
  else if h : a.val < 57 then (lapse : ℂ) *
    ((if (⟨(a.val-9)/12,by omega⟩ : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
      ∑ r : Fin 4, diracGamma ⟨(a.val-9)/12,by omega⟩ i.1 r *
        internalEntry (nativeMother ⟨(a.val-9)%12,Nat.mod_lt _ (by decide)⟩) (r,i.2) j)
  else if h : a.val < 73 then coframeEntry p ⟨(a.val-57)/4,by omega⟩ ⟨(a.val-57)%4,Nat.mod_lt _ (by decide)⟩ i j
  else (lapse : ℂ) *
    ((if (⟨(a.val-73)/6,by omega⟩ : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
      ∑ r : Fin 4, diracGamma ⟨(a.val-73)/6,by omega⟩ i.1 r *
        spinEntry (lorentzMatrix ⟨(a.val-73)%6,Nat.mod_lt _ (by decide)⟩) (r,i.2) j)

private theorem principal_coordinates (mu : Fin 4) (v : DiracExteriorMatterCarrier) (i : NamedMode) :
    Quantum.coordinates (principal mu v) (rootIndex i) =
    (if mu = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
      ∑r : Fin 4, diracGamma mu i.1 r * Quantum.coordinates v (rootIndex (r,i.2)) := by
  simp only [principal,LinearMap.smul_apply,map_smul,Pi.smul_apply,smul_eq_mul,spin_action_coordinates]

private theorem raw_coordinates (p : Fin 4 → ℂ) (a : Fin 97) (i j : NamedMode) :
    Quantum.coordinates (rawVertex p a (namedColumn j)) (rootIndex i) = rawEntry p a i j := by
  unfold rawVertex rawEntry
  split
  · simp only [LinearMap.smul_apply,map_smul,Pi.smul_apply,smul_eq_mul,yukawa_two,mul_zero]
  · split
    · simp only [LinearMap.smul_apply,Module.End.mul_apply,map_smul,Pi.smul_apply,
        smul_eq_mul,principal_coordinates]
      simp only [MixedSpectatorContactVertices.gauge]
      simp_rw [internal_coordinates]
    · split
      · exact coframe_coordinates p _ _ i j
      · simp only [LinearMap.smul_apply,Module.End.mul_apply,map_smul,Pi.smul_apply,
          smul_eq_mul,principal_coordinates]
        simp_rw [spin_coordinates]

def primitiveEntry (p : Fin 4 → ℂ) (dual : Bool) (a : Fin 97) (i j : Support) : ℂ :=
  let v := ∑ r : Fin 4, diracGammaZero i.1 r * rawEntry p a (r,(supportNamed i).2) (supportNamed j)
  if dual then -star v else v

theorem actual_primitive_entry (p : Fin 4 → ℂ) (dual : Bool) (a : Fin 97) (i j : Support) :
    sourceVertex p a (supportMode dual i) (supportMode dual j) = primitiveEntry p dual a i j := by
  have hp : Quantum.operatorMatrix (spin diracGammaZero * rawVertex p a)
      (rootIndex (supportNamed i)) (rootIndex (supportNamed j)) =
      ∑ r : Fin 4, diracGammaZero i.1 r * rawEntry p a (r,(supportNamed i).2) (supportNamed j) := by
    rw [matrix_entry]
    simp only [Module.End.mul_apply,spin,GaussCoframeSpin.coordinates_spin]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    exact raw_coordinates p a (r,(supportNamed i).2) (supportNamed j)
  cases dual
  · simpa [sourceVertex,supportMode,rootMode,SourceRealScalarFock.branches,primitiveEntry] using hp
  · simpa [sourceVertex,supportMode,rootMode,SourceRealScalarFock.branches,primitiveEntry] using congrArg (fun z : ℂ => -star z) hp



theorem actual_candidate_support (dual : Bool) (t : Fin 2) (p : Fin 6) (slot : Fin 3) :
    ActualCandidateQuarticGram.candidateMode dual t p slot =
      supportMode dual (((![![0,1,2],![0,0,3]] t) slot), NamedMatterWedgeQt.colorPerm p slot) := by
  fin_cases t <;> fin_cases slot <;>
    simp [ActualCandidateQuarticGram.candidateMode,supportMode,supportNamed]

/-- Every scalar source has zero actual Λ²-to-Λ² matrix entries, on both independent branches. -/
theorem actual_scalar_entry_zero (dual : Bool) (a : Fin 70) (i j : Support) :
    MixedSpectatorScalar61Exchange.sourceVertex a (supportMode dual i) (supportMode dual j) = 0 := by
  rw [MixedSpectatorScalar61Exchange.sourceVertex_original]
  have hp (phi : SourceQuantumScalarChart.Scalar) : GaussYukawaCoefficient.primal phi
      (rootIndex (supportNamed i)) (rootIndex (supportNamed j)) = 0 := by
    change Quantum.operatorMatrix (FullQuantum.yukawaHamiltonian _) _ _ = 0
    rw [matrix_entry]
    simp only [FullQuantum.yukawaHamiltonian,LinearMap.smul_apply,LinearMap.comp_apply,
      map_smul,Pi.smul_apply,smul_eq_mul,GaussCoframeSpin.coordinates_spin]
    change (lapse : ℂ) * (∑ r : Fin 4, diracGammaZero i.1 r * Quantum.coordinates
      (diracDualRightChiralYukawaAction _ (namedColumn (supportNamed j)))
      (rootIndex (r,(supportNamed i).2))) = 0
    simp only [yukawa_two,mul_zero,Finset.sum_const_zero]
  cases dual
  · change GaussYukawaCoefficient.primal (MixedSpectatorScalar61Exchange.sourceChart a) (rootIndex (supportNamed i)) (rootIndex (supportNamed j)) = 0
    exact hp _
  · change -star (GaussYukawaCoefficient.primal (MixedSpectatorScalar61Exchange.sourceChart a) (rootIndex (supportNamed i)) (rootIndex (supportNamed j))) = 0
    rw [hp]
    simp

end LowEnergy.ActualCandidateVertexEntries
