import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Runtime.Runtime

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient SourceCoulomb MeasureTheory
open UnifiedOrbitals
noncomputable section

def readSpatial (runtime : LivingRuntimeState process) :
    ActuationResult × ((Basis → List Term) × (Point → Point → ℂ)) :=
  match facade.readoutAt runtime .spatial with
  | .inl ⟨_,result⟩ => result
  | .inr impossible => nomatch impossible

def readTerms (runtime : LivingRuntimeState process) (i : Basis) := (readSpatial runtime).2.1 i
def readGamma (runtime : LivingRuntimeState process) := (readSpatial runtime).2.2
def readAO (runtime : LivingRuntimeState process) (i : Basis) (x : Point) : ℝ :=
  orbital (readTerms runtime i) zeroJet x
def readNucleus (runtime : LivingRuntimeState process) (a : Fin 13) (k : Fin 3) : ℝ :=
  (readSpatial runtime).1.frame.position a k

theorem same_spatial_body (runtime : LivingRuntimeState process) : (readSpatial runtime).1=readCurrent runtime := rfl
theorem terms_from_current (runtime : LivingRuntimeState process) (i : Basis) :
    readTerms runtime i=termsAt (readCurrent runtime) i := rfl
theorem gamma_from_current (runtime : LivingRuntimeState process) :
    readGamma runtime=gammaAt (readCurrent runtime) := rfl

theorem actual_centres (i : Basis) : type_of% (face_factorizes afterFirst .spatial) ∧
    List.Forall (fun term => ∃ a : Fin 13, term.centre=(readCurrent afterFirst).frame.position a) (readTerms afterFirst i) :=
  ⟨face_factorizes afterFirst .spatial,current_frame_centres i⟩

theorem actual_ao (i : Basis) (x : Point) : readAO afterFirst i x=translatedAO i x :=
  generated_ao i x

theorem actual_gamma (x y : Point) : type_of% (face_factorizes afterFirst .spatial) ∧
    readGamma afterFirst x y=movingGamma .leave duration x y :=
  ⟨face_factorizes afterFirst .spatial,(generatedReceipt.generatedGamma x y).symm⟩

def readAttraction (runtime : LivingRuntimeState process) (i j : Basis) : ℝ :=
  ∑ a : Fin 13, -WholeBandBasin.Family.All.Nuclear.nuclearCharge a*
    ∫ x : Point, readAO runtime i x*readAO runtime j x*kernel (x-readNucleus runtime a)

def readRepulsion (runtime : LivingRuntimeState process) (a b : Fin 13) : ℝ :=
  WholeBandBasin.Family.All.Nuclear.nuclearCharge a*WholeBandBasin.Family.All.Nuclear.nuclearCharge b*
    kernel (readNucleus runtime a-readNucleus runtime b)

def readElectronRepulsion (runtime : LivingRuntimeState process) (i j k l : Basis) : ℝ :=
  ∫ z : Point × Point, readAO runtime i z.1*readAO runtime j z.1*
    (readAO runtime k z.2*readAO runtime l z.2)*kernel (z.2-z.1)

theorem actual_attraction (i j : Basis) : type_of% (face_factorizes afterFirst .spatial) ∧
    readAttraction afterFirst i j=Attraction.Precise.aoIntegral i j := by
  refine ⟨face_factorizes afterFirst .spatial,?_⟩
  have fields : readAttraction afterFirst i j=attraction i j := by
    simp only [readAttraction,actual_ao,attraction]
    rfl
  exact fields.trans (attraction_translation i j)

theorem actual_repulsion (a b : Fin 13) : type_of% (face_factorizes afterFirst .spatial) ∧
    readRepulsion afterFirst a b=WholeBandBasin.Family.All.Nuclear.PreciseTarget.nuclearRepulsion a b :=
  ⟨face_factorizes afterFirst .spatial,repulsion_translation a b⟩

theorem actual_electron_repulsion (i j k l : Basis) : type_of% (face_factorizes afterFirst .spatial) ∧
    readElectronRepulsion afterFirst i j k l=UnifiedOrbitals.electronRepulsion i j k l := by
  refine ⟨face_factorizes afterFirst .spatial,?_⟩
  unfold readElectronRepulsion
  simp only [actual_ao]
  exact electron_repulsion_translation i j k l

theorem actual_work : type_of% (face_factorizes seed .firstActuation) ∧
    0 < SIWork.energyJoule*((readCurrent seed).resource.momentum-(readCurrent afterFirst).resource.momentum) ∧
    SIWork.energyJoule*((readCurrent seed).resource.momentum-(readCurrent afterFirst).resource.momentum)=
      SIWork.energyJoule*(((readCurrent afterFirst).frame.total : ℝ)-((readCurrent seed).frame.total : ℝ)) :=
  ⟨action_certificate.1,action_certificate.2.positiveWork,action_certificate.2.work⟩

theorem actual_whole_account : type_of% (face_factorizes afterFirst .energy) ∧
    wholeBodyAccount (readCurrent afterFirst)=wholeBodyAccount (readCurrent seed) :=
  ⟨face_factorizes afterFirst .energy,action_certificate.2.wholeAccount⟩

theorem actual_history : type_of% (face_factorizes afterFirst .history) ∧
    SIWork.energyJoule*wholeBodyAccount (readCurrent afterFirst)=
      SIWork.wholeAccountJoule (SIWork.Runtime.readCurrent SIWork.Runtime.afterFirst) :=
  ⟨face_factorizes afterFirst .history,action_certificate.2.historicalAccount⟩

theorem actual_original_history :
    type_of% (actual_history.2.trans (SIWork.Runtime.actual_original_history 1).2) :=
  actual_history.2.trans (SIWork.Runtime.actual_original_history 1).2

theorem initial_input_same : readCurrent seed=(SIWork.Runtime.readCurrent SIWork.Runtime.afterFirst).body := rfl

def faceSumEquiv : Projection ≃ Fin 9 ⊕ SIWork.Runtime.Face where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .clocks => .inl 2 | .history => .inl 3
    | .energy => .inl 4 | .firstActuation => .inl 5 | .readiness => .inl 6 | .wholeLedger => .inl 7
    | .spatial => .inl 8 | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.clocks,.history,.energy,.firstActuation,.readiness,.wholeLedger,.spatial] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 298 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) SIWork.Runtime.faceEquiv).trans finSumFinEquiv)

structure InstalledSpatialAction : Prop where
  source : type_of% initial_input_same
  parentRow : type_of% parent_entry_exact
  actualAction : type_of% generated_action_answer
  targetVisit : type_of% generated_visit
  generatedNext : type_of% generated_action_next
  action : type_of% action_certificate
  actual : type_of% actual_generated
  nonreturning : type_of% actual_nonzero
  clocks : type_of% actual_clocks
  positive : type_of% actual_positive
  spatialBody : type_of% same_spatial_body
  terms : type_of% terms_from_current
  fullGamma : type_of% gamma_from_current
  centres : type_of% actual_centres
  gamma : type_of% actual_gamma
  attraction : type_of% actual_attraction
  repulsion : type_of% actual_repulsion
  coulomb : type_of% actual_electron_repulsion
  work : type_of% actual_work
  account : type_of% actual_whole_account
  history : type_of% actual_history
  originalHistory : type_of% actual_original_history
  wholeLedger : type_of% whole_ledger_installed
  parentFaces : type_of% parent_is_installed
  noReissue : type_of% action_not_reissued
  retaining : type_of% retained_without_tick
  allFaces : Nonempty (Projection ≃ Fin 298)

theorem sourceGeneratedSpatialAction : InstalledSpatialAction :=
  ⟨initial_input_same,parent_entry_exact,generated_action_answer,generated_visit,generated_action_next,
   action_certificate,actual_generated,actual_nonzero,actual_clocks,actual_positive,same_spatial_body,
   terms_from_current,gamma_from_current,actual_centres,actual_gamma,actual_attraction,actual_repulsion,
   actual_electron_repulsion,actual_work,actual_whole_account,actual_history,actual_original_history,whole_ledger_installed,
   parent_is_installed,action_not_reissued,retained_without_tick,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Runtime
