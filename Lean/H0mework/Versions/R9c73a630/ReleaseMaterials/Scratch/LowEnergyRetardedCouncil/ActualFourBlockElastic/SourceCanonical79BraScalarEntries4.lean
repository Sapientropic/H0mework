import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators Matrix

theorem actual_scalar_entry_55_18 : axialInverse Complex.I 0 55 18 =
    (((-353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 45 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator45_point,actual_denominator_point]
  have hn : numeratorPoint 45 = ((-3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_19 : axialInverse Complex.I 0 55 19 =
    (((353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 63 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator63_point,actual_denominator_point]
  have hn : numeratorPoint 63 = ((3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_22 : axialInverse Complex.I 0 55 22 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_23 : axialInverse Complex.I 0 55 23 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_30 : axialInverse Complex.I 0 55 30 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 46 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator46_point,actual_denominator_point]
  have hn : numeratorPoint 46 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_31 : axialInverse Complex.I 0 55 31 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 64 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator64_point,actual_denominator_point]
  have hn : numeratorPoint 64 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_34 : axialInverse Complex.I 0 55 34 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_35 : axialInverse Complex.I 0 55 35 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_55 : axialInverse Complex.I 0 55 55 =
    (((-27/527) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 147 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator147_point,actual_denominator_point]
  have hn : numeratorPoint 147 = ((-9656970072795275222271143/5422647100435200000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_56 : axialInverse Complex.I 0 55 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 148 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator148_point,actual_denominator_point]
  have hn : numeratorPoint 148 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_61 : axialInverse Complex.I 0 55 61 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 149 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator149_point,actual_denominator_point]
  have hn : numeratorPoint 149 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_63 : axialInverse Complex.I 0 55 63 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 149 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator149_point,actual_denominator_point]
  have hn : numeratorPoint 149 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_67 : axialInverse Complex.I 0 55 67 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_71 : axialInverse Complex.I 0 55 71 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 150 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator150_point,actual_denominator_point]
  have hn : numeratorPoint 150 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_73 : axialInverse Complex.I 0 55 73 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 151 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator151_point,actual_denominator_point]
  have hn : numeratorPoint 151 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_55_77 : axialInverse Complex.I 0 55 77 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_18 : axialInverse Complex.I 0 56 18 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 64 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator64_point,actual_denominator_point]
  have hn : numeratorPoint 64 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_19 : axialInverse Complex.I 0 56 19 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 46 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator46_point,actual_denominator_point]
  have hn : numeratorPoint 46 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_22 : axialInverse Complex.I 0 56 22 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_23 : axialInverse Complex.I 0 56 23 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_30 : axialInverse Complex.I 0 56 30 =
    (((-353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 45 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator45_point,actual_denominator_point]
  have hn : numeratorPoint 45 = ((-3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_31 : axialInverse Complex.I 0 56 31 =
    (((353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 63 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator63_point,actual_denominator_point]
  have hn : numeratorPoint 63 = ((3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_34 : axialInverse Complex.I 0 56 34 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_35 : axialInverse Complex.I 0 56 35 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_55 : axialInverse Complex.I 0 56 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 152 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator152_point,actual_denominator_point]
  have hn : numeratorPoint 152 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_56 : axialInverse Complex.I 0 56 56 =
    (((-27/527) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 147 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator147_point,actual_denominator_point]
  have hn : numeratorPoint 147 = ((-9656970072795275222271143/5422647100435200000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_61 : axialInverse Complex.I 0 56 61 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 151 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator151_point,actual_denominator_point]
  have hn : numeratorPoint 151 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_63 : axialInverse Complex.I 0 56 63 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 151 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator151_point,actual_denominator_point]
  have hn : numeratorPoint 151 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_67 : axialInverse Complex.I 0 56 67 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_71 : axialInverse Complex.I 0 56 71 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 149 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator149_point,actual_denominator_point]
  have hn : numeratorPoint 149 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_73 : axialInverse Complex.I 0 56 73 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 153 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator153_point,actual_denominator_point]
  have hn : numeratorPoint 153 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_56_77 : axialInverse Complex.I 0 56 77 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_6 : axialInverse Complex.I 0 57 6 =
    (((-3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 250 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator250_point,actual_denominator_point]
  have hn : numeratorPoint 250 = ((65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_7 : axialInverse Complex.I 0 57 7 =
    (((3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 274 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator274_point,actual_denominator_point]
  have hn : numeratorPoint 274 = ((-65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_10 : axialInverse Complex.I 0 57 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_11 : axialInverse Complex.I 0 57 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_42 : axialInverse Complex.I 0 57 42 =
    (((-125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 384 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator384_point,actual_denominator_point]
  have hn : numeratorPoint 384 = ((123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_43 : axialInverse Complex.I 0 57 43 =
    (((125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 402 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator402_point,actual_denominator_point]
  have hn : numeratorPoint 402 = ((-123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_46 : axialInverse Complex.I 0 57 46 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_48 : axialInverse Complex.I 0 57 48 =
    (((-1/500) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 426 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator426_point,actual_denominator_point]
  have hn : numeratorPoint 426 = ((65124842331217710284987/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_50 : axialInverse Complex.I 0 57 50 =
    (((-257/31620) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 438 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator438_point,actual_denominator_point]
  have hn : numeratorPoint 438 = ((31759173584673532340117/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_52 : axialInverse Complex.I 0 57 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_53 : axialInverse Complex.I 0 57 53 =
    (((-257/31620) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 438 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator438_point,actual_denominator_point]
  have hn : numeratorPoint 438 = ((31759173584673532340117/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_57 : axialInverse Complex.I 0 57 57 =
    (((-1067/31620) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 455 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator455_point,actual_denominator_point]
  have hn : numeratorPoint 455 = ((131856179824306066174727/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_58 : axialInverse Complex.I 0 57 58 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 456 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator456_point,actual_denominator_point]
  have hn : numeratorPoint 456 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_60 : axialInverse Complex.I 0 57 60 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 457 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator457_point,actual_denominator_point]
  have hn : numeratorPoint 457 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_64 : axialInverse Complex.I 0 57 64 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 458 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator458_point,actual_denominator_point]
  have hn : numeratorPoint 458 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_57_66 : axialInverse Complex.I 0 57 66 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 459 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator459_point,actual_denominator_point]
  have hn : numeratorPoint 459 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_6 : axialInverse Complex.I 0 58 6 =
    (((183076564992/16920965818375) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 251 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator251_point,actual_denominator_point]
  have hn : numeratorPoint 251 = ((-57342033395887339912/176518460300625) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_7 : axialInverse Complex.I 0 58 7 =
    (((-183076564992/16920965818375) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 275 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator275_point,actual_denominator_point]
  have hn : numeratorPoint 275 = ((57342033395887339912/176518460300625) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_10 : axialInverse Complex.I 0 58 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 290 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator290_point,actual_denominator_point]
  have hn : numeratorPoint 290 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_11 : axialInverse Complex.I 0 58 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 301 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator301_point,actual_denominator_point]
  have hn : numeratorPoint 301 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_42 : axialInverse Complex.I 0 58 42 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 385 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator385_point,actual_denominator_point]
  have hn : numeratorPoint 385 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_43 : axialInverse Complex.I 0 58 43 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 403 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator403_point,actual_denominator_point]
  have hn : numeratorPoint 403 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_46 : axialInverse Complex.I 0 58 46 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 412 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator412_point,actual_denominator_point]
  have hn : numeratorPoint 412 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_47 : axialInverse Complex.I 0 58 47 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 418 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator418_point,actual_denominator_point]
  have hn : numeratorPoint 418 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_48 : axialInverse Complex.I 0 58 48 =
    (((3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 427 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator427_point,actual_denominator_point]
  have hn : numeratorPoint 427 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_50 : axialInverse Complex.I 0 58 50 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 439 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator439_point,actual_denominator_point]
  have hn : numeratorPoint 439 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_52 : axialInverse Complex.I 0 58 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_53 : axialInverse Complex.I 0 58 53 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 439 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator439_point,actual_denominator_point]
  have hn : numeratorPoint 439 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_54 : axialInverse Complex.I 0 58 54 =
    (((-71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 450 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator450_point,actual_denominator_point]
  have hn : numeratorPoint 450 = ((112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_57 : axialInverse Complex.I 0 58 57 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 456 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator456_point,actual_denominator_point]
  have hn : numeratorPoint 456 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_58 : axialInverse Complex.I 0 58 58 =
    (((834525625209/10829418123760) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 461 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator461_point,actual_denominator_point]
  have hn : numeratorPoint 461 = ((-133828919564583539723963/241006537797120000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_58_66 : axialInverse Complex.I 0 58 66 =
    (((-1324754695809/10829418123760) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 464 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator464_point,actual_denominator_point]
  have hn : numeratorPoint 464 = ((70814877447622241572721/80335512599040000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_6 : axialInverse Complex.I 0 60 6 =
    (((589179744633/16920965818375) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 252 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator252_point,actual_denominator_point]
  have hn : numeratorPoint 252 = ((-94483963429912028319931/90377451673920000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_10 : axialInverse Complex.I 0 60 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 291 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator291_point,actual_denominator_point]
  have hn : numeratorPoint 291 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_11 : axialInverse Complex.I 0 60 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 302 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator302_point,actual_denominator_point]
  have hn : numeratorPoint 302 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_42 : axialInverse Complex.I 0 60 42 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 386 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator386_point,actual_denominator_point]
  have hn : numeratorPoint 386 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_46 : axialInverse Complex.I 0 60 46 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 413 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator413_point,actual_denominator_point]
  have hn : numeratorPoint 413 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_47 : axialInverse Complex.I 0 60 47 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 419 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator419_point,actual_denominator_point]
  have hn : numeratorPoint 419 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_48 : axialInverse Complex.I 0 60 48 =
    (((-3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 428 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator428_point,actual_denominator_point]
  have hn : numeratorPoint 428 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_50 : axialInverse Complex.I 0 60 50 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 440 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator440_point,actual_denominator_point]
  have hn : numeratorPoint 440 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_53 : axialInverse Complex.I 0 60 53 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 440 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator440_point,actual_denominator_point]
  have hn : numeratorPoint 440 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_54 : axialInverse Complex.I 0 60 54 =
    (((-71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 451 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator451_point,actual_denominator_point]
  have hn : numeratorPoint 451 = ((112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_60_57 : axialInverse Complex.I 0 60 57 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 457 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator457_point,actual_denominator_point]
  have hn : numeratorPoint 457 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_18 : axialInverse Complex.I 0 61 18 =
    (((136349674707/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 47 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator47_point,actual_denominator_point]
  have hn : numeratorPoint 47 = ((1708713367652148228219566147/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_19 : axialInverse Complex.I 0 61 19 =
    (((-161401238457/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 65 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator65_point,actual_denominator_point]
  have hn : numeratorPoint 65 = ((-2022655751102641216301029897/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_22 : axialInverse Complex.I 0 61 22 =
    (((-290390625/13206607468) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 77 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator77_point,actual_denominator_point]
  have hn : numeratorPoint 77 = ((-636605335142066462879/832918594626846720) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_30 : axialInverse Complex.I 0 61 30 =
    (((-124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 50 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator50_point,actual_denominator_point]
  have hn : numeratorPoint 50 = (((-310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_31 : axialInverse Complex.I 0 61 31 =
    (((124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 68 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator68_point,actual_denominator_point]
  have hn : numeratorPoint 68 = (((310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_34 : axialInverse Complex.I 0 61 34 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 80 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator80_point,actual_denominator_point]
  have hn : numeratorPoint 80 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_35 : axialInverse Complex.I 0 61 35 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 90 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator90_point,actual_denominator_point]
  have hn : numeratorPoint 90 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_55 : axialInverse Complex.I 0 61 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 149 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator149_point,actual_denominator_point]
  have hn : numeratorPoint 149 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_56 : axialInverse Complex.I 0 61 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 150 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator150_point,actual_denominator_point]
  have hn : numeratorPoint 150 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_61 : axialInverse Complex.I 0 61 61 =
    (((124062880485/270735453094) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 154 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator154_point,actual_denominator_point]
  have hn : numeratorPoint 154 = ((310947426562899120376716337/19521529561566720000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_63 : axialInverse Complex.I 0 61 63 =
    (((45/82) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 155 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator155_point,actual_denominator_point]
  have hn : numeratorPoint 155 = ((124127395813734391271631521/6507176520522240000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_61_67 : axialInverse Complex.I 0 61 67 =
    (((-298920165/3301651867) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 156 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator156_point,actual_denominator_point]
  have hn : numeratorPoint 156 = ((-30717380439152026719089113/9760764780783360000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_63_18 : axialInverse Complex.I 0 63 18 =
    (((180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 48 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator48_point,actual_denominator_point]
  have hn : numeratorPoint 48 = ((2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
