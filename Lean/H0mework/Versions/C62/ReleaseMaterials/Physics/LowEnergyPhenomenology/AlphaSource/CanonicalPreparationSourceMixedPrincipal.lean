import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalPreparedGreen

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback
open scoped Matrix BigOperators

def planeMomentum (time space : ℂ) : Fin 4→ℂ := ![time,space,0,0]
def planeTerms (terms : List SourceTerm) : List SourceTerm :=
  terms.filter (fun a=>decide (a.powers.second=0 ∧ a.powers.third=0))

private theorem planeTerm_zero (a : SourceTerm) (time space : ℂ)
    (off : ¬(a.powers.second=0 ∧ a.powers.third=0)) : a.matrix (planeMomentum time space)=0 :=by
  have vanishing : a.powers.value (planeMomentum time space)=0 :=by
    simp only [Powers.value,planeMomentum,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    by_cases s : a.powers.second=0
    · have u : a.powers.third≠0:=by tauto
      simp [u]
    · simp [s]
  simp [SourceTerm.matrix,vanishing]

theorem planeTerms_generated (terms : List SourceTerm) (time space : ℂ) :
    sourceMatrix (planeTerms terms) (planeMomentum time space)=sourceMatrix terms (planeMomentum time space) :=by
  induction terms with
  | nil=>rfl
  | cons a rest ih=>
    simp only [planeTerms,List.filter_cons] at ih ⊢
    split_ifs with on
    · rw [sourceMatrix_cons,ih,sourceMatrix_cons]
    · rw [ih,sourceMatrix_cons,planeTerm_zero a time space (by simpa using on),zero_add]

def kernelTerms : List SourceTerm := [
  ⟨21,0,⟨0,0,0,0⟩,⟨⟨0,3/10⟩,⟨0,0⟩⟩⟩,
  ⟨34,0,⟨0,0,0,0⟩,⟨⟨0,-3/10⟩,⟨0,0⟩⟩⟩,
  ⟨79,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨83,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨21,1,⟨0,0,0,0⟩,⟨⟨0,3/10⟩,⟨0,0⟩⟩⟩,
  ⟨34,1,⟨0,0,0,0⟩,⟨⟨0,-3/10⟩,⟨0,0⟩⟩⟩,
  ⟨79,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨85,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩
]
def timeCorrectionTerms : List SourceTerm := [
  ⟨15,0,⟨1,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨16,0,⟨1,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨22,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,-5/72⟩⟩⟩,
  ⟨33,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,-5/72⟩⟩⟩,
  ⟨51,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,-5/72⟩⟩⟩,
  ⟨52,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,5/72⟩⟩⟩,
  ⟨57,0,⟨1,0,0,0⟩,⟨⟨0,-5/12⟩,⟨0,0⟩⟩⟩,
  ⟨59,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨-25/108,0⟩⟩⟩,
  ⟨62,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨-25/108,0⟩⟩⟩,
  ⟨66,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨-25/108,0⟩⟩⟩,
  ⟨15,1,⟨1,0,0,0⟩,⟨⟨6/11,0⟩,⟨0,0⟩⟩⟩,
  ⟨16,1,⟨1,0,0,0⟩,⟨⟨-5/11,0⟩,⟨0,0⟩⟩⟩,
  ⟨19,1,⟨1,0,0,0⟩,⟨⟨3/11,0⟩,⟨0,0⟩⟩⟩,
  ⟨20,1,⟨1,0,0,0⟩,⟨⟨5/11,0⟩,⟨0,0⟩⟩⟩,
  ⟨67,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨5/198,0⟩⟩⟩,
  ⟨69,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨-5/198,0⟩⟩⟩,
  ⟨73,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨-5/198,0⟩⟩⟩,
  ⟨75,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨5/198,0⟩⟩⟩
]
def spaceCorrectionTerms : List SourceTerm := [
  ⟨10,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,5/72⟩⟩⟩,
  ⟨27,0,⟨0,1,0,0⟩,⟨⟨1/4,0⟩,⟨0,0⟩⟩⟩,
  ⟨28,0,⟨0,1,0,0⟩,⟨⟨-1/4,0⟩,⟨0,0⟩⟩⟩,
  ⟨46,0,⟨0,1,0,0⟩,⟨⟨1/4,0⟩,⟨0,0⟩⟩⟩,
  ⟨58,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨179/540,0⟩⟩⟩,
  ⟨70,0,⟨0,1,0,0⟩,⟨⟨0,-5/12⟩,⟨0,0⟩⟩⟩,
  ⟨72,0,⟨0,1,0,0⟩,⟨⟨0,-5/12⟩,⟨0,0⟩⟩⟩,
  ⟨27,1,⟨0,1,0,0⟩,⟨⟨39/67,0⟩,⟨0,0⟩⟩⟩,
  ⟨28,1,⟨0,1,0,0⟩,⟨⟨-34/67,0⟩,⟨0,0⟩⟩⟩,
  ⟨31,1,⟨0,1,0,0⟩,⟨⟨15/67,0⟩,⟨0,0⟩⟩⟩,
  ⟨32,1,⟨0,1,0,0⟩,⟨⟨25/67,0⟩,⟨0,0⟩⟩⟩,
  ⟨46,1,⟨0,1,0,0⟩,⟨⟨-3/67,0⟩,⟨0,0⟩⟩⟩,
  ⟨70,1,⟨0,1,0,0⟩,⟨⟨0,5/67⟩,⟨0,0⟩⟩⟩,
  ⟨76,1,⟨0,1,0,0⟩,⟨⟨0,5/67⟩,⟨0,0⟩⟩⟩
]
def principalTerms : List SourceTerm := [
  ⟨0,0,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,-25/18⟩⟩⟩,
  ⟨0,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,-25/54⟩⟩⟩,
  ⟨1,1,⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,10/99⟩⟩⟩,
  ⟨1,1,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,-12/335⟩⟩⟩
]

def jetFrameTerms : List SourceTerm := kernelTerms++timeCorrectionTerms++spaceCorrectionTerms
def residualTerms : List SourceTerm := fastNormalizeTerms (productTerms (planeTerms activeTerms) jetFrameTerms)
def quadraticTerms : List SourceTerm := residualTerms.filter (fun a=>decide (a.powers.total=2))
def cubicTerms : List SourceTerm := residualTerms.filter (fun a=>decide (a.powers.total=3))

def kernelFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix kernelTerms p
def reflectedKernelFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix (reflectedTerms kernelTerms) p
def jetFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix jetFrameTerms p

def sourcePrincipal (time space : ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  sourceMatrix principalTerms (planeMomentum time space)

private theorem principal_certificate :
    fastNormalizeTerms (productTerms (reflectedTerms kernelTerms)
      (productTerms (planeTerms activeTerms) jetFrameTerms)++negativeTerms principalTerms)=[] :=by decide +kernel

/-- The original mixed field produces the complete two-mode principal tensor; all projected cubic terms cancel. -/
theorem sourcePrincipal_generated (time space : ℂ) :
    reflectedKernelFrame (planeMomentum time space)*activeKernel (planeMomentum time space)*jetFrame (planeMomentum time space)=
      sourcePrincipal time space :=by
  have h:=normalization_equal _ _ principal_certificate (planeMomentum time space)
  rw [productTerms_value,productTerms_value,planeTerms_generated] at h
  simpa only [reflectedKernelFrame,activeKernel,jetFrame,sourcePrincipal,mul_assoc] using h

private theorem residual_orders :
    fastNormalizeTerms (residualTerms++negativeTerms (quadraticTerms++cubicTerms))=[] :=by decide +kernel

/-- The unprojected field keeps its actual quadratic and cubic complement residual. -/
theorem sourceFrame_residual (time space : ℂ) :
    activeKernel (planeMomentum time space)*jetFrame (planeMomentum time space)=
      sourceMatrix quadraticTerms (planeMomentum time space)+sourceMatrix cubicTerms (planeMomentum time space) :=by
  have h:=normalization_equal _ _ residual_orders (planeMomentum time space)
  rw [residualTerms,fastNormalizeTerms_value,productTerms_value,planeTerms_generated,sourceMatrix_append] at h
  exact h

private theorem active_frame_certificate :
    fastNormalizeTerms (productTerms (projectionTerms activeFlag) jetFrameTerms++negativeTerms jetFrameTerms)=[] :=by decide +kernel

theorem sourceFrame_active (p : Fin 4→ℂ) : activeProjection*jetFrame p=jetFrame p :=by
  have h:=normalization_equal _ _ active_frame_certificate p
  rw [productTerms_value,projectionTerms_value] at h
  exact h

theorem kernel_reflected (p : Fin 4→ℂ) : reflectedKernelFrame p=(kernelFrame (-p)).transpose :=
  reflectedTerms_value kernelTerms p

end LowEnergy.PreparationVacuumMixedPrincipal
