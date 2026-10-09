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

theorem actual_scalar_entry_47_54 : axialInverse Complex.I 0 47 54 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_58 : axialInverse Complex.I 0 47 58 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 418 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator418_point,actual_denominator_point]
  have hn : numeratorPoint 418 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_60 : axialInverse Complex.I 0 47 60 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 419 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator419_point,actual_denominator_point]
  have hn : numeratorPoint 419 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_64 : axialInverse Complex.I 0 47 64 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 419 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator419_point,actual_denominator_point]
  have hn : numeratorPoint 419 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_66 : axialInverse Complex.I 0 47 66 =
    (((-1278864375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 418 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator418_point,actual_denominator_point]
  have hn : numeratorPoint 418 = ((67268017457021435105/192805230237696) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_6 : axialInverse Complex.I 0 48 6 =
    (((-74169/4108750) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 245 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator245_point,actual_denominator_point]
  have hn : numeratorPoint 245 = ((54425902611455749970447/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_7 : axialInverse Complex.I 0 48 7 =
    (((74169/4108750) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 269 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator269_point,actual_denominator_point]
  have hn : numeratorPoint 269 = ((-54425902611455749970447/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_10 : axialInverse Complex.I 0 48 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_11 : axialInverse Complex.I 0 48 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_42 : axialInverse Complex.I 0 48 42 =
    (((25/3287) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 379 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator379_point,actual_denominator_point]
  have hn : numeratorPoint 379 = ((-99064256664462595505/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_43 : axialInverse Complex.I 0 48 43 =
    (((-25/3287) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 397 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator397_point,actual_denominator_point]
  have hn : numeratorPoint 397 = ((99064256664462595505/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_46 : axialInverse Complex.I 0 48 46 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_48 : axialInverse Complex.I 0 48 48 =
    (((227367/4108750) : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 423 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator423_point,actual_denominator_point]
  have hn : numeratorPoint 423 = ((-55614673691429301116507/60251634449280000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_50 : axialInverse Complex.I 0 48 50 =
    (((-1/500) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 424 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator424_point,actual_denominator_point]
  have hn : numeratorPoint 424 = ((65124842331217710284987/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_52 : axialInverse Complex.I 0 48 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_53 : axialInverse Complex.I 0 48 53 =
    (((-1/500) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 424 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator424_point,actual_denominator_point]
  have hn : numeratorPoint 424 = ((65124842331217710284987/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_57 : axialInverse Complex.I 0 48 57 =
    (((-1/500) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 426 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator426_point,actual_denominator_point]
  have hn : numeratorPoint 426 = ((65124842331217710284987/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_58 : axialInverse Complex.I 0 48 58 =
    (((3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 427 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator427_point,actual_denominator_point]
  have hn : numeratorPoint 427 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_60 : axialInverse Complex.I 0 48 60 =
    (((-3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 428 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator428_point,actual_denominator_point]
  have hn : numeratorPoint 428 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_64 : axialInverse Complex.I 0 48 64 =
    (((3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 429 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator429_point,actual_denominator_point]
  have hn : numeratorPoint 429 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_48_66 : axialInverse Complex.I 0 48 66 =
    (((-3/1000) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 430 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator430_point,actual_denominator_point]
  have hn : numeratorPoint 430 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_49_1 : axialInverse Complex.I 0 49 1 =
    (((-347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 13 / denominator Complex.I 0 0) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator13_point,actual_denominator_point]
  have hn : numeratorPoint 13 = ((-43072206347365833771256137787/2529990231179046912000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_49_36 : axialInverse Complex.I 0 49 36 =
    (((-71/1640) : ℂ)*(Real.sqrt 15 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 132 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator132_point,actual_denominator_point]
  have hn : numeratorPoint 132 = (((-8813045102775141780285837991/1405550128432803840000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_49_49 : axialInverse Complex.I 0 49 49 =
    (((2827/12300) : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 137 / denominator Complex.I 0 0) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator137_point,actual_denominator_point]
  have hn : numeratorPoint 137 = ((350908147965427124124902309867/18974926733842851840000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_6 : axialInverse Complex.I 0 50 6 =
    (((-3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 246 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator246_point,actual_denominator_point]
  have hn : numeratorPoint 246 = ((65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_7 : axialInverse Complex.I 0 50 7 =
    (((3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 270 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator270_point,actual_denominator_point]
  have hn : numeratorPoint 270 = ((-65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_10 : axialInverse Complex.I 0 50 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_11 : axialInverse Complex.I 0 50 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_13 : axialInverse Complex.I 0 50 13 =
    (((-125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 336 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator336_point,actual_denominator_point]
  have hn : numeratorPoint 336 = ((123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_24 : axialInverse Complex.I 0 50 24 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 338 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator338_point,actual_denominator_point]
  have hn : numeratorPoint 338 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_42 : axialInverse Complex.I 0 50 42 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 380 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator380_point,actual_denominator_point]
  have hn : numeratorPoint 380 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_43 : axialInverse Complex.I 0 50 43 =
    (((-125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 398 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator398_point,actual_denominator_point]
  have hn : numeratorPoint 398 = ((123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_46 : axialInverse Complex.I 0 50 46 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_48 : axialInverse Complex.I 0 50 48 =
    (((-1/500) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 424 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator424_point,actual_denominator_point]
  have hn : numeratorPoint 424 = ((65124842331217710284987/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_50 : axialInverse Complex.I 0 50 50 =
    (((-1067/31620) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 434 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator434_point,actual_denominator_point]
  have hn : numeratorPoint 434 = ((131856179824306066174727/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_52 : axialInverse Complex.I 0 50 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 435 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator435_point,actual_denominator_point]
  have hn : numeratorPoint 435 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_53 : axialInverse Complex.I 0 50 53 =
    (((-257/31620) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 436 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator436_point,actual_denominator_point]
  have hn : numeratorPoint 436 = ((31759173584673532340117/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_57 : axialInverse Complex.I 0 50 57 =
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

theorem actual_scalar_entry_50_58 : axialInverse Complex.I 0 50 58 =
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

theorem actual_scalar_entry_50_60 : axialInverse Complex.I 0 50 60 =
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

theorem actual_scalar_entry_50_64 : axialInverse Complex.I 0 50 64 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 441 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator441_point,actual_denominator_point]
  have hn : numeratorPoint 441 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_50_66 : axialInverse Complex.I 0 50 66 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 442 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator442_point,actual_denominator_point]
  have hn : numeratorPoint 442 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_51_0 : axialInverse Complex.I 0 51 0 =
    (((-347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 13 / denominator Complex.I 0 0) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator13_point,actual_denominator_point]
  have hn : numeratorPoint 13 = ((-43072206347365833771256137787/2529990231179046912000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_51_37 : axialInverse Complex.I 0 51 37 =
    (((71/1640) : ℂ)*(Real.sqrt 15 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 121 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator121_point,actual_denominator_point]
  have hn : numeratorPoint 121 = (((8813045102775141780285837991/1405550128432803840000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_51_51 : axialInverse Complex.I 0 51 51 =
    (((2827/12300) : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 137 / denominator Complex.I 0 0) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator137_point,actual_denominator_point]
  have hn : numeratorPoint 137 = ((350908147965427124124902309867/18974926733842851840000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_7 : axialInverse Complex.I 0 52 7 =
    (((-81/26350) : ℂ)*(Real.sqrt 15 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 247 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator247_point,actual_denominator_point]
  have hn : numeratorPoint 247 = (((123576550913126584981/1338925209984000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_11 : axialInverse Complex.I 0 52 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_12 : axialInverse Complex.I 0 52 12 =
    (((-353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 318 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator318_point,actual_denominator_point]
  have hn : numeratorPoint 318 = ((43622522472333684498293/90377451673920000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_25 : axialInverse Complex.I 0 52 25 =
    (((-8/155) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 362 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator362_point,actual_denominator_point]
  have hn : numeratorPoint 362 = ((2100801365523151944677/5648590729620000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_43 : axialInverse Complex.I 0 52 43 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 381 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator381_point,actual_denominator_point]
  have hn : numeratorPoint 381 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_47 : axialInverse Complex.I 0 52 47 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_48 : axialInverse Complex.I 0 52 48 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_50 : axialInverse Complex.I 0 52 50 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 444 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator444_point,actual_denominator_point]
  have hn : numeratorPoint 444 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_52 : axialInverse Complex.I 0 52 52 =
    (((-27/527) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 445 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator445_point,actual_denominator_point]
  have hn : numeratorPoint 445 = ((123576550913126584981/334731302496000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_53 : axialInverse Complex.I 0 52 53 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 435 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator435_point,actual_denominator_point]
  have hn : numeratorPoint 435 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_54 : axialInverse Complex.I 0 52 54 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_57 : axialInverse Complex.I 0 52 57 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_58 : axialInverse Complex.I 0 52 58 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_52_66 : axialInverse Complex.I 0 52 66 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_6 : axialInverse Complex.I 0 53 6 =
    (((-3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 248 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator248_point,actual_denominator_point]
  have hn : numeratorPoint 248 = ((65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_7 : axialInverse Complex.I 0 53 7 =
    (((3/250) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 272 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator272_point,actual_denominator_point]
  have hn : numeratorPoint 272 = ((-65124842331217710284987/180754903347840000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_10 : axialInverse Complex.I 0 53 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_11 : axialInverse Complex.I 0 53 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*(((6/25) * (Real.sqrt 15 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_13 : axialInverse Complex.I 0 53 13 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 338 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator338_point,actual_denominator_point]
  have hn : numeratorPoint 338 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_24 : axialInverse Complex.I 0 53 24 =
    (((-125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 336 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator336_point,actual_denominator_point]
  have hn : numeratorPoint 336 = ((123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_42 : axialInverse Complex.I 0 53 42 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 382 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator382_point,actual_denominator_point]
  have hn : numeratorPoint 382 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_43 : axialInverse Complex.I 0 53 43 =
    (((-125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 400 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator400_point,actual_denominator_point]
  have hn : numeratorPoint 400 = ((123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_46 : axialInverse Complex.I 0 53 46 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_48 : axialInverse Complex.I 0 53 48 =
    (((-1/500) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 424 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator424_point,actual_denominator_point]
  have hn : numeratorPoint 424 = ((65124842331217710284987/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_50 : axialInverse Complex.I 0 53 50 =
    (((-257/31620) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 436 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator436_point,actual_denominator_point]
  have hn : numeratorPoint 436 = ((31759173584673532340117/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_52 : axialInverse Complex.I 0 53 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 444 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator444_point,actual_denominator_point]
  have hn : numeratorPoint 444 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_53 : axialInverse Complex.I 0 53 53 =
    (((-1067/31620) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 434 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator434_point,actual_denominator_point]
  have hn : numeratorPoint 434 = ((131856179824306066174727/542264710043520000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_57 : axialInverse Complex.I 0 53 57 =
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

theorem actual_scalar_entry_53_58 : axialInverse Complex.I 0 53 58 =
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

theorem actual_scalar_entry_53_60 : axialInverse Complex.I 0 53 60 =
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

theorem actual_scalar_entry_53_64 : axialInverse Complex.I 0 53 64 =
    (((1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 441 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator441_point,actual_denominator_point]
  have hn : numeratorPoint 441 = ((-65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_53_66 : axialInverse Complex.I 0 53 66 =
    (((-1/40) : ℂ))/(lapse : ℂ) := by
  change (1 : ℂ) * (numeratorPolynomial Complex.I 0 442 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator442_point,actual_denominator_point]
  have hn : numeratorPoint 442 = ((65124842331217710284987/361509806695680000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_6 : axialInverse Complex.I 0 54 6 =
    (((-347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 249 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator249_point,actual_denominator_point]
  have hn : numeratorPoint 249 = ((551178543632501108997329/156172236492533760) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_7 : axialInverse Complex.I 0 54 7 =
    (((347/1640) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 273 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator273_point,actual_denominator_point]
  have hn : numeratorPoint 273 = ((-551178543632501108997329/156172236492533760) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_42 : axialInverse Complex.I 0 54 42 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 383 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator383_point,actual_denominator_point]
  have hn : numeratorPoint 383 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_43 : axialInverse Complex.I 0 54 43 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 401 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator401_point,actual_denominator_point]
  have hn : numeratorPoint 401 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_47 : axialInverse Complex.I 0 54 47 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)*0*((Real.sqrt 2 : ℂ) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_52 : axialInverse Complex.I 0 54 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_54 : axialInverse Complex.I 0 54 54 =
    (((2827/12300) : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 448 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator448_point,actual_denominator_point]
  have hn : numeratorPoint 448 = ((-4490437299276889438430689/1171291773694003200) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_58 : axialInverse Complex.I 0 54 58 =
    (((-71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 450 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator450_point,actual_denominator_point]
  have hn : numeratorPoint 450 = ((112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_60 : axialInverse Complex.I 0 54 60 =
    (((-71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 451 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator451_point,actual_denominator_point]
  have hn : numeratorPoint 451 = ((112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_64 : axialInverse Complex.I 0 54 64 =
    (((71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 452 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator452_point,actual_denominator_point]
  have hn : numeratorPoint 452 = ((-112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_54_66 : axialInverse Complex.I 0 54 66 =
    (((71/1640) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) * (numeratorPolynomial Complex.I 0 453 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator453_point,actual_denominator_point]
  have hn : numeratorPoint 453 = ((-112777165988206278786197/43381176803481600) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
