import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedInteraction.Channels
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Response

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace CPS1AddressedInteraction
noncomputable section
open CPS1ElectronicSource CPS1Deformation CPS1AddressedTransfer
open CPS1MolecularFrame (ActualIndex NuclearIndex)
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

private theorem sum_rotate {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (value : α → β → γ → M) :
    (∑ first, ∑ second, ∑ third, value first second third) =
      ∑ third, ∑ first, ∑ second, value first second third := by
  calc
    _ = ∑ first, ∑ third, ∑ second, value first second third := by
      apply Finset.sum_congr rfl
      intro first _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def matrixAction (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (matrix : Matrix (ActualIndex source) (ActualIndex source) ℂ) : SpinSpace →L[ℂ] SpinSpace :=
  ∑ first, ∑ second,
    ((basisSynthesis source positions).conjTranspose * matrix * basisSynthesis source positions) first second •
      (innerSL ℂ (normedBasisAt source positions second)).smulRight (normedBasisAt source positions first)

theorem matrix_action_sum {ι : Type*} [Fintype ι]
    (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (matrices : ι → Matrix (ActualIndex source) (ActualIndex source) ℂ) :
    matrixAction source positions (∑ channel, matrices channel) =
      ∑ channel, matrixAction source positions (matrices channel) := by
  classical
  simp only [matrixAction,Matrix.mul_sum,Matrix.sum_mul,Matrix.sum_apply,Finset.sum_smul]
  exact sum_rotate _

def channelAction (state : Material frame) (time : ℝ) (channel : Channel state.reference) :
    SpinSpace →L[ℂ] SpinSpace :=
  matrixAction state.reference (state.movedPositions time)
    (channelMatrix state.reference (state.movedPositions time) (seedOccupation state time) channel)

theorem action_split (state : Material frame) (time : ℝ) :
    ∑ channel : Channel state.reference, channelAction state time channel = responseAction state time := by
  simp only [channelAction]
  rw [← matrix_action_sum,fock_split]
  rfl

theorem midpoint_flux_sum {ι σ : Type*} [Fintype ι] [Fintype σ]
    (projection : SpinSpace →L[ℂ] SpinSpace) (actions : ι → SpinSpace →L[ℂ] SpinSpace)
    (before after : σ → SpinSpace) :
    Generic.midpointFlux projection (∑ channel, actions channel) before after =
      ∑ channel, Generic.midpointFlux projection (actions channel) before after := by
  classical
  simp only [Generic.midpointFlux,sum_apply,map_sum,inner_sum,Complex.im_sum]
  rw [Finset.sum_comm]

def contribution (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (channel : Channel state.reference) : ℝ :=
  Generic.midpointFlux (siteProjection state.reference (state.movedPositions time) nuclear)
    (channelAction state time channel) (seedFields state time) (responseFields state time)

theorem zero_matrix_no_contribution (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (channel : Channel state.reference)
    (zero : channelMatrix state.reference (state.movedPositions time) (seedOccupation state time) channel = 0) :
    contribution state nuclear time channel = 0 := by
  unfold contribution channelAction
  rw [zero]
  simp [matrixAction,Generic.midpointFlux]

theorem contribution_source_nonzero (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (channel : Channel state.reference)
    (nonzero : contribution state nuclear time channel ≠ 0) :
    channelMatrix state.reference (state.movedPositions time) (seedOccupation state time) channel ≠ 0 := by
  exact fun zero => nonzero (zero_matrix_no_contribution state nuclear time channel zero)

theorem flux_split (state : Material frame) (nuclear : NuclearIndex state.reference) (time : ℝ) :
    ∑ channel : Channel state.reference, contribution state nuclear time channel =
      responseFlux state nuclear time := by
  unfold contribution
  rw [← midpoint_flux_sum,action_split]
  rfl

def residual (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (selected : Channel state.reference) : ℝ := by
  classical
  exact ∑ channel ∈ Finset.univ.erase selected, contribution state nuclear time channel

theorem selected_and_residual (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (selected : Channel state.reference) :
    contribution state nuclear time selected + residual state nuclear time selected =
      responseFlux state nuclear time := by
  classical
  unfold residual
  rw [← flux_split]
  exact Finset.add_sum_erase (Finset.univ : Finset (Channel state.reference))
    (fun channel => contribution state nuclear time channel) (Finset.mem_univ selected)

def signedChannels (state : Material frame) (nuclear : NuclearIndex state.reference) (time : ℝ) :
    Finset (Channel state.reference) :=
  Finset.univ.filter (fun channel =>
    0 < responseFlux state nuclear 0 * contribution state nuclear time channel)

theorem signed_channel_exists (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (positive : 0 < time)
    (signed : 0 < responseFlux state nuclear 0 * transferredPopulation state nuclear time) :
    (signedChannels state nuclear time).Nonempty := by
  classical
  have total : 0 < responseFlux state nuclear 0 * responseFlux state nuclear time := by
    rw [response_population] at signed
    have reordered : responseFlux state nuclear 0 * (2*time*responseFlux state nuclear time) =
        (2*time)*(responseFlux state nuclear 0 * responseFlux state nuclear time) := by ring
    rw [reordered] at signed
    exact pos_of_mul_pos_right signed (le_of_lt (mul_pos (by norm_num) positive))
  have sumPositive : 0 < ∑ channel : Channel state.reference,
      responseFlux state nuclear 0 * contribution state nuclear time channel := by
    rw [← Finset.mul_sum,flux_split]
    exact total
  by_contra absent
  have all (channel : Channel state.reference) :
      responseFlux state nuclear 0 * contribution state nuclear time channel ≤ 0 := by
    apply le_of_not_gt
    intro positiveChannel
    exact absent ⟨channel,Finset.mem_filter.mpr ⟨Finset.mem_univ channel,positiveChannel⟩⟩
  exact not_lt_of_ge (Finset.sum_nonpos (fun channel _ => all channel)) sumPositive

/-- The source pulse computes every contribution first. Selection is internal;
no partner, coupling, endpoint, or success table enters this mouth. -/
def select? (state : Material frame) (nuclear : NuclearIndex state.reference) (time : ℝ) :
    Option (Channel state.reference) :=
  if actual : 0 < time ∧ 0 < responseFlux state nuclear 0 * transferredPopulation state nuclear time then
    some (signed_channel_exists state nuclear time actual.1 actual.2).choose else none

theorem selected_sound (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (channel : Channel state.reference) (selected : select? state nuclear time = some channel) :
    0 < responseFlux state nuclear 0 * contribution state nuclear time channel ∧
      contribution state nuclear time channel ≠ 0 := by
  classical
  unfold select? at selected
  split at selected
  · rename_i actual
    have member := (signed_channel_exists state nuclear time actual.1 actual.2).choose_spec
    have equality := Option.some.inj selected
    rw [equality] at member
    have signed := (Finset.mem_filter.mp member).2
    exact ⟨signed,fun zero => by rw [zero,mul_zero] at signed; exact lt_irrefl _ signed⟩
  · cases selected

theorem select_complete (state : Material frame) (nuclear : NuclearIndex state.reference)
    (time : ℝ) (positive : 0 < time)
    (signed : 0 < responseFlux state nuclear 0 * transferredPopulation state nuclear time) :
    ∃ channel, select? state nuclear time = some channel := by
  have actual := And.intro positive signed
  exact ⟨(signed_channel_exists state nuclear time actual.1 actual.2).choose,
    by rw [select?,dif_pos actual]⟩

end
end CPS1AddressedInteraction
