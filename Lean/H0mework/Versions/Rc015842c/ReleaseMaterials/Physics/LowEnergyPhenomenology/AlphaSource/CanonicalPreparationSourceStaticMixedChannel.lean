import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalPreparedGreen

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalFieldChannel
open PreparationVacuumOriginalGreenFeedback
open scoped Matrix BigOperators

/-- Literal restriction of the original Fourier variables to the first static spatial axis. -/
def staticAxis (k : ℂ) : Fin 4→ℂ := ![0,k,0,0]
def axisTerms (terms : List SourceTerm) : List SourceTerm :=
  terms.filter (fun a=>decide (a.powers.temporal=0 ∧ a.powers.second=0 ∧ a.powers.third=0))

private theorem axisTerm_zero (a : SourceTerm) (k : ℂ)
    (off : ¬(a.powers.temporal=0 ∧ a.powers.second=0 ∧ a.powers.third=0)) :
    a.matrix (staticAxis k)=0 :=by
  have vanishing : a.powers.value (staticAxis k)=0 :=by
    simp only [Powers.value,staticAxis,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    by_cases t : a.powers.temporal=0
    · by_cases s : a.powers.second=0
      · have u : a.powers.third≠0:=by tauto
        simp [u]
      · simp [s]
    · simp [t]
  simp [SourceTerm.matrix,vanishing]

theorem axisTerms_generated (terms : List SourceTerm) (k : ℂ) :
    sourceMatrix (axisTerms terms) (staticAxis k)=sourceMatrix terms (staticAxis k) :=by
  induction terms with
  | nil=>rfl
  | cons a rest ih=>
    simp only [axisTerms,List.filter_cons] at ih ⊢
    split_ifs with on
    · rw [sourceMatrix_cons,ih,sourceMatrix_cons]
    · rw [ih,sourceMatrix_cons,axisTerm_zero a k (by simpa using on),zero_add]

def channelNumeratorTerms : List SourceTerm := [
  ⟨10,0,⟨0,1,0,0⟩,⟨⟨0,-9/200⟩,⟨0,0⟩⟩⟩,
  ⟨10,0,⟨0,3,0,0⟩,⟨⟨0,-301/1088⟩,⟨0,0⟩⟩⟩,
  ⟨10,0,⟨0,5,0,0⟩,⟨⟨0,-1775/19584⟩,⟨0,0⟩⟩⟩,
  ⟨21,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-9023/50000⟩⟩⟩,
  ⟨21,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,-597691/2448000⟩⟩⟩,
  ⟨21,0,⟨0,4,0,0⟩,⟨⟨0,0⟩,⟨0,-7267/146880⟩⟩⟩,
  ⟨21,0,⟨0,6,0,0⟩,⟨⟨0,0⟩,⟨0,-45/2176⟩⟩⟩,
  ⟨21,0,⟨0,8,0,0⟩,⟨⟨0,0⟩,⟨0,-125/13056⟩⟩⟩,
  ⟨27,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨-1679/5000,0⟩⟩⟩,
  ⟨27,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨-8263/16320,0⟩⟩⟩,
  ⟨27,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨-2141/13824,0⟩⟩⟩,
  ⟨27,0,⟨0,7,0,0⟩,⟨⟨0,0⟩,⟨-75/8704,0⟩⟩⟩,
  ⟨28,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨1103/3750,0⟩⟩⟩,
  ⟨28,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨6641/14688,0⟩⟩⟩,
  ⟨28,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨33157/235008,0⟩⟩⟩,
  ⟨28,0,⟨0,7,0,0⟩,⟨⟨0,0⟩,⟨75/8704,0⟩⟩⟩,
  ⟨31,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨-1/8,0⟩⟩⟩,
  ⟨31,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨-7957/48960,0⟩⟩⟩,
  ⟨31,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨-45/1088,0⟩⟩⟩,
  ⟨32,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨-5/24,0⟩⟩⟩,
  ⟨32,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨-7957/29376,0⟩⟩⟩,
  ⟨32,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨-75/1088,0⟩⟩⟩,
  ⟨34,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,9023/50000⟩⟩⟩,
  ⟨34,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,601159/2448000⟩⟩⟩,
  ⟨34,0,⟨0,4,0,0⟩,⟨⟨0,0⟩,⟨0,51103/587520⟩⟩⟩,
  ⟨34,0,⟨0,6,0,0⟩,⟨⟨0,0⟩,⟨0,45/4352⟩⟩⟩,
  ⟨46,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨71/5000,0⟩⟩⟩,
  ⟨46,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨3749/61200,0⟩⟩⟩,
  ⟨46,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨-9/1088,0⟩⟩⟩,
  ⟨46,0,⟨0,7,0,0⟩,⟨⟨0,0⟩,⟨-25/2176,0⟩⟩⟩,
  ⟨58,0,⟨0,1,0,0⟩,⟨⟨-537/2500,0⟩,⟨0,0⟩⟩⟩,
  ⟨58,0,⟨0,3,0,0⟩,⟨⟨-179/2400,0⟩,⟨0,0⟩⟩⟩,
  ⟨58,0,⟨0,5,0,0⟩,⟨⟨-27/136,0⟩,⟨0,0⟩⟩⟩,
  ⟨58,0,⟨0,7,0,0⟩,⟨⟨-75/1088,0⟩,⟨0,0⟩⟩⟩,
  ⟨61,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨-5/144,0⟩⟩⟩,
  ⟨61,0,⟨0,4,0,0⟩,⟨⟨0,0⟩,⟨-7957/176256,0⟩⟩⟩,
  ⟨61,0,⟨0,6,0,0⟩,⟨⟨0,0⟩,⟨-25/2176,0⟩⟩⟩,
  ⟨64,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨0,25/1728⟩⟩⟩,
  ⟨64,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨0,39785/2115072⟩⟩⟩,
  ⟨64,0,⟨0,7,0,0⟩,⟨⟨0,0⟩,⟨0,125/26112⟩⟩⟩,
  ⟨70,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,-71/3000⟩⟩⟩,
  ⟨70,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨0,-12871/146880⟩⟩⟩,
  ⟨70,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨0,15/544⟩⟩⟩,
  ⟨70,0,⟨0,7,0,0⟩,⟨⟨0,0⟩,⟨0,125/6528⟩⟩⟩,
  ⟨72,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,9/500⟩⟩⟩,
  ⟨72,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨0,-7039/146880⟩⟩⟩,
  ⟨72,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨0,15/544⟩⟩⟩,
  ⟨72,0,⟨0,7,0,0⟩,⟨⟨0,0⟩,⟨0,125/6528⟩⟩⟩,
  ⟨76,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,-1/24⟩⟩⟩,
  ⟨76,0,⟨0,3,0,0⟩,⟨⟨0,0⟩,⟨0,-5041/73440⟩⟩⟩,
  ⟨76,0,⟨0,5,0,0⟩,⟨⟨0,0⟩,⟨0,-15/544⟩⟩⟩,
  ⟨79,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨-9023/15000,0⟩⟩⟩,
  ⟨79,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨-550159/734400,0⟩⟩⟩,
  ⟨79,0,⟨0,4,0,0⟩,⟨⟨0,0⟩,⟨-4133/22032,0⟩⟩⟩,
  ⟨83,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨-27/625,0⟩⟩⟩,
  ⟨83,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨-1559/12240,0⟩⟩⟩,
  ⟨83,0,⟨0,4,0,0⟩,⟨⟨0,0⟩,⟨-13249/88128,0⟩⟩⟩,
  ⟨83,0,⟨0,6,0,0⟩,⟨⟨0,0⟩,⟨-25/544,0⟩⟩⟩,
  ⟨85,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨-67/120,0⟩⟩⟩,
  ⟨85,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨-507619/734400,0⟩⟩⟩,
  ⟨85,0,⟨0,4,0,0⟩,⟨⟨0,0⟩,⟨-165/1088,0⟩⟩⟩
]

def channelDenominatorTerms : List SourceTerm := [
  ⟨21,0,⟨0,2,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨21,0,⟨0,4,0,0⟩,⟨⟨7957/6120,0⟩,⟨0,0⟩⟩⟩,
  ⟨21,0,⟨0,6,0,0⟩,⟨⟨45/136,0⟩,⟨0,0⟩⟩⟩
]

private theorem channel_source_certificate :
    fastNormalizeTerms (productTerms (axisTerms activeTerms) channelNumeratorTerms++
      negativeTerms channelDenominatorTerms)=[] :=by decide +kernel

def channelNumerator (k : ℂ) : Fin 289→ℂ := fun i=>sourceMatrix channelNumeratorTerms (staticAxis k) i 0
def channelDrive (k : ℂ) : Fin 289→ℂ := fun i=>sourceMatrix channelDenominatorTerms (staticAxis k) i 0

theorem channel_actual_active (k : ℂ) :
    activeKernel (staticAxis k)*ᵥchannelNumerator k=channelDrive k :=by
  have actual:=normalization_equal (productTerms (axisTerms activeTerms) channelNumeratorTerms)
    channelDenominatorTerms channel_source_certificate (staticAxis k)
  rw [productTerms_value,axisTerms_generated] at actual
  exact congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>fun i=>A i 0) actual

end LowEnergy.PreparationVacuumPhysicalFieldChannel
