import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Occupied

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveField
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame} {current : Occurrence frame}

abbrev CommonPrimitive (source : Inlet current) :=
  CPS1MolecularFrame.PrimitiveIndex source.old.reference ⊕ AddedPrimitive source

def commonJet (source : Inlet current) (index : CommonPrimitive source) (jet : Fin 3 → Nat) : SpinSpace :=
  match index with
  | .inl old => CPS1Deformation.rawJetAt source.old.reference source.old.positions old jet
  | .inr added => addedJet source added jet

def oldCoefficient (source : Inlet current) (primitive : CPS1MolecularFrame.PrimitiveIndex source.old.reference)
    (slot : OldElectronIndex source) : ℂ :=
  ∑ basis, source.old.occupied basis slot*CPS1MolecularFrame.basisCoefficient source.old.reference primitive basis

def residualCoefficient (source : Inlet current) (added : AddedPrimitive source)
    (primitive : CommonPrimitive source) : ℂ :=
  match primitive with
  | .inl old => -(∑ slot, inner ℂ (source.oldFields slot) (addedField source added)*oldCoefficient source old slot)
  | .inr water => if water = added then 1 else 0

def occupiedCoefficient (source : Inlet current) (primitive : CommonPrimitive source)
    (slot : OccupiedIndex source) : ℂ :=
  match slot with
  | .inl old => match primitive with | .inl index => oldCoefficient source index old | .inr _ => 0
  | .inr added => ∑ raw, CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
      (residualField source) raw (selectedDirection source added)*residualCoefficient source raw primitive

def occupiedJet (source : Inlet current) (slot : OccupiedIndex source) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ primitive, occupiedCoefficient source primitive slot • commonJet source primitive jet

theorem old_coefficient_synthesis (source : Inlet current) (slot : OldElectronIndex source) :
    (∑ primitive, oldCoefficient source primitive slot • commonJet source (.inl primitive) 0) =
      source.oldFields slot := by
  simp only [oldCoefficient,commonJet,Inlet.oldFields,CPS1Deformation.Material.currentFields,
    CPS1Deformation.occupiedFieldsAt,CPS1ElectronicEvolution.fields,CPS1Deformation.basisAt,
    CPS1Deformation.basisJetAt,Finset.sum_smul,mul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]

theorem residual_coefficient_synthesis (source : Inlet current) (index : AddedPrimitive source) :
    (∑ primitive, residualCoefficient source index primitive • commonJet source primitive 0) =
      residualField source index := by
  classical
  rw [Fintype.sum_sum_type]
  have oldPart : (∑ primitive, residualCoefficient source index (.inl primitive) •
      commonJet source (.inl primitive) 0) = -oldProjection source (addedField source index) := by
    simp only [residualCoefficient,neg_smul,Finset.sum_neg_distrib,Finset.sum_smul,mul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum,old_coefficient_synthesis,oldProjection]
  have newPart : (∑ primitive, residualCoefficient source index (.inr primitive) •
      commonJet source (.inr primitive) 0) = addedField source index := by
    simp only [residualCoefficient,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rfl
  rw [oldPart,newPart]
  exact neg_add_eq_sub _ _

theorem occupied_jet_fields (source : Inlet current) (slot : OccupiedIndex source) :
    occupiedJet source slot 0 = occupiedFields source slot := by
  classical
  cases slot with
  | inl old =>
    simp only [occupiedJet,occupiedCoefficient,Fintype.sum_sum_type,zero_smul,Finset.sum_const_zero,
      add_zero,occupiedFields,Sum.elim_inl]
    exact old_coefficient_synthesis source old
  | inr added =>
    simp only [occupiedJet,occupiedCoefficient,Finset.sum_smul,mul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum,residual_coefficient_synthesis]
    exact (CPS1MolecularFrame.FiniteNormed.field_synthesis (residualField source) (selectedDirection source added)).symm

def commonCentre (source : Inlet current) : CommonPrimitive source → Point
  | .inl old => source.old.positions old.1.1
  | .inr water => position source.body water.1.1
def commonMode (source : Inlet current) : CommonPrimitive source → Nat
  | .inl old => old.1.2.val
  | .inr water => water.1.2.val
def commonSpin (source : Inlet current) : CommonPrimitive source → Bool
  | .inl old => old.2
  | .inr water => water.2

def commonNuclearIntegral (source : Inlet current) (p q : CommonPrimitive source) (spin : Bool) (nuclear : Point) : ℂ :=
  if commonSpin source p = spin ∧ commonSpin source q = spin then
    CPS1MolecularFrame.primitiveNuclearIntegral (commonCentre source p) (commonCentre source q)
      (commonMode source p) (commonMode source q) nuclear 0 0 else 0

def commonPairIntegral (source : Inlet current) (p q r s : CommonPrimitive source)
    (spin secondSpin : Bool) : ℂ :=
  if commonSpin source p = spin ∧ commonSpin source q = spin ∧
      commonSpin source r = secondSpin ∧ commonSpin source s = secondSpin then
    CPS1MolecularFrame.primitivePairIntegral (commonCentre source p) (commonCentre source q)
      (commonCentre source r) (commonCentre source s) (commonMode source p) (commonMode source q)
      (commonMode source r) (commonMode source s) 0 0 0 0 else 0

def nodeSlot (node : CPS1AtomicDynamics.Body.Node) : Nat :=
  match node.particle.address with | .nucleus slot | .electron slot _ => slot
def nodeIsWater (source : Inlet current) (node : CPS1AtomicDynamics.Body.Node) : Bool :=
  ((source.body.atoms[nodeSlot node]?).map isWater).getD false
def waterNodes (source : Inlet current) : List CPS1AtomicDynamics.Body.Node := source.body.nodes.filter (nodeIsWater source)

def oldNuclearNode (source : Inlet current) (nuclear : CPS1MolecularFrame.NuclearIndex source.old.reference) :
    CPS1AtomicDynamics.Body.Node :=
  ⟨(CPS1MolecularFrame.nucleus source.old.reference nuclear).particle,source.old.nuclearRow nuclear⟩
def commonNuclei (source : Inlet current) : List CPS1AtomicDynamics.Body.Node :=
  List.ofFn (oldNuclearNode source) ++ (waterNodes source).filter isNucleus

def nuclearIntegral (source : Inlet current) (i j : OccupiedIndex source) (nuclear : Point) : ℂ :=
  ∑ spin : Bool, ∑ p, ∑ q, star (occupiedCoefficient source p i)*occupiedCoefficient source q j*
    commonNuclearIntegral source p q spin nuclear
def pairIntegral (source : Inlet current) (i j k l : OccupiedIndex source) (spin secondSpin : Bool) : ℂ :=
  ∑ p, ∑ q, ∑ r, ∑ s,
    (star (occupiedCoefficient source p i)*occupiedCoefficient source q j*
      star (occupiedCoefficient source r k)*occupiedCoefficient source s l)*
      commonPairIntegral source p q r s spin secondSpin
def twoBody (source : Inlet current) (i j k l : OccupiedIndex source) : ℂ :=
  ∑ spin : Bool, ∑ secondSpin : Bool, pairIntegral source i k j l spin secondSpin

def kinetic (source : Inlet current) (i j : OccupiedIndex source) : ℂ :=
  ((1/(2*source.old.reference.geometry.electronInertia) : ℝ) : ℂ)*
    ∑ axis : Fin 3, inner ℂ (occupiedJet source i (raise 0 axis)) (occupiedJet source j (raise 0 axis))
def attraction (source : Inlet current) (i j : OccupiedIndex source) : ℂ :=
  ((commonNuclei source).map (fun nuclear => -(nuclear.particle.charge : ℂ)*
    nuclearIntegral source i j (Geometry.nucleusPosition nuclear))).sum
def electronicEnergy (source : Inlet current) : ℝ :=
  (∑ i, (kinetic source i i+attraction source i i)).re+(1/2)*
    (∑ i, ∑ j, (twoBody source i j i j-twoBody source i j j i)).re
def energy (source : Inlet current) : ℝ := CPS1AtomicDynamics.Body.energy (commonNuclei source)+electronicEnergy source
def incomingEnergy (source : Inlet current) : ℝ := source.old.energy+CPS1AtomicDynamics.Body.energy (waterNodes source)
def price (source : Inlet current) : ℝ := energy source-incomingEnergy source
def incomingReserve (source : Inlet current) : ℝ := source.old.reserve+source.body.reserve

structure Material (current : Occurrence frame) where
  source : Inlet current
  reserve : ℝ

def Material.account {current : Occurrence frame} (state : Material current) : ℝ := energy state.source+state.reserve
def Material.bath {current : Occurrence frame} (state : Material current) : List CPS1EnzymeBath.Joint.Component :=
  state.source.old.currentJoint.components
def Material.atomic {current : Occurrence frame} (_state : Material current) : CPS1AddressedHydrolysis.Atomic.Occurrence frame :=
  current.ingress.atomic

inductive FieldFailure
  | inlet (failure : InletFailure)
  | incompleteSource (missing : List (CPS1AddressedChemicalReaction.Source.LocalMaterial frame × CPS1AddressedReactiveJoint.Missing))
  | incompatibleElectronInertia
  | collision
  | negativeReserve
  | energyShortage

def admitField? (current : Occurrence frame) : Except (FieldFailure (frame := frame)) (Material current) := by
  classical
  exact match inlet current with
    | .error failure => .error (.inlet failure)
    | .ok source =>
      if source.body.missing ≠ [] then .error (.incompleteSource source.body.missing)
      else if ¬ (∀ node ∈ waterNodes source, isElectron node = true →
          node.row.inertia = source.old.reference.geometry.electronInertia) then .error .incompatibleElectronInertia
      else if ¬ CPS1AtomicDynamics.Body.ready (commonNuclei source) then .error .collision
      else if incomingReserve source < 0 then .error .negativeReserve
      else if incomingReserve source < price source then .error .energyShortage
      else .ok ⟨source,incomingReserve source-price source⟩

theorem field_price_paid (current : Occurrence frame) (state : Material current)
    (actual : admitField? current = .ok state) :
    state.reserve ≥ 0 ∧ state.account = incomingEnergy state.source+incomingReserve state.source ∧
      state.source.body.missing = [] ∧ CPS1AtomicDynamics.Body.ready (commonNuclei state.source) := by
  unfold admitField? at actual
  cases selected : inlet current with
  | error => simp only [selected] at actual; cases actual
  | ok source =>
    simp only [selected] at actual
    split at actual
    · cases actual
    · rename_i complete
      split at actual
      · cases actual
      · split at actual
        · cases actual
        · rename_i ready
          split at actual
          · cases actual
          · split at actual
            · cases actual
            · rename_i paid
              cases Except.ok.inj actual
              refine ⟨sub_nonneg.mpr (le_of_not_gt paid),?_,not_not.mp complete,not_not.mp ready⟩
              simp only [Material.account,price]
              ring

inductive LivePhysical (current : Occurrence frame)
  | residual (species : CPS1Deformation.Species frame)
  | common (state : Material current)

def physicalStock {current : Occurrence frame} (state : Material current) : List (LivePhysical current) :=
  .common state :: (current.old.current.stock.erase (.deformed state.source.old)).map LivePhysical.residual

theorem physical_token_once {current : Occurrence frame} (state : Material current) :
    current.old.current.stock.Perm (.deformed state.source.old ::
      current.old.current.stock.erase (.deformed state.source.old)) ∧
    physicalStock state = .common state ::
      (current.old.current.stock.erase (.deformed state.source.old)).map LivePhysical.residual ∧
    state.bath = state.source.old.reference.geometry.originJoint.components ∧
    state.atomic = current.ingress.atomic ∧
    (∀ old, occupiedFields state.source (.inl old) = state.source.old.currentFields old) ∧
    Orthonormal ℂ (occupiedFields state.source) ∧
    type_of% (occupied_electron_account state.source) :=
  ⟨List.perm_cons_erase state.source.held,rfl,rfl,rfl,occupied_prefix state.source,
    occupied_orthonormal state.source,occupied_electron_account state.source⟩

end
end CPS1ReactiveField
