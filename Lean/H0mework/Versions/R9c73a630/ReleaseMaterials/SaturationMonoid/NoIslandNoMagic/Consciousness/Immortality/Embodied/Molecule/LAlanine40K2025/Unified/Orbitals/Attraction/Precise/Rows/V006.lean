import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V006_006_044
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V006_044_078
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V006_078_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_6 (j : Basis) (ordered : (6 : Basis) ≤ j) :
    |aoIntegral (6 : Basis) j - (recordedAttraction (6 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (6 : Basis) = ⟨6,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(6 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(6 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(6 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(6 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(6 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(6 : Basis) ≤ (5 : Basis) by decide) ordered)
  · convert vcell6_6_error using 1; norm_num
  · convert vcell6_7_error using 1; norm_num
  · convert vcell6_8_error using 1; norm_num
  · convert vcell6_9_error using 1; norm_num
  · convert vcell6_10_error using 1; norm_num
  · convert vcell6_11_error using 1; norm_num
  · convert vcell6_12_error using 1; norm_num
  · convert vcell6_13_error using 1; norm_num
  · convert vcell6_14_error using 1; norm_num
  · convert vcell6_15_error using 1; norm_num
  · convert vcell6_16_error using 1; norm_num
  · convert vcell6_17_error using 1; norm_num
  · convert vcell6_18_error using 1; norm_num
  · convert vcell6_19_error using 1; norm_num
  · convert vcell6_20_error using 1; norm_num
  · convert vcell6_21_error using 1; norm_num
  · convert vcell6_22_error using 1; norm_num
  · convert vcell6_23_error using 1; norm_num
  · convert vcell6_24_error using 1; norm_num
  · convert vcell6_25_error using 1; norm_num
  · convert vcell6_26_error using 1; norm_num
  · convert vcell6_27_error using 1; norm_num
  · convert vcell6_28_error using 1; norm_num
  · convert vcell6_29_error using 1; norm_num
  · convert vcell6_30_error using 1; norm_num
  · convert vcell6_31_error using 1; norm_num
  · convert vcell6_32_error using 1; norm_num
  · convert vcell6_33_error using 1; norm_num
  · convert vcell6_34_error using 1; norm_num
  · convert vcell6_35_error using 1; norm_num
  · convert vcell6_36_error using 1; norm_num
  · convert vcell6_37_error using 1; norm_num
  · convert vcell6_38_error using 1; norm_num
  · convert vcell6_39_error using 1; norm_num
  · convert vcell6_40_error using 1; norm_num
  · convert vcell6_41_error using 1; norm_num
  · convert vcell6_42_error using 1; norm_num
  · convert vcell6_43_error using 1; norm_num
  · convert vcell6_44_error using 1; norm_num
  · convert vcell6_45_error using 1; norm_num
  · convert vcell6_46_error using 1; norm_num
  · convert vcell6_47_error using 1; norm_num
  · convert vcell6_48_error using 1; norm_num
  · convert vcell6_49_error using 1; norm_num
  · convert vcell6_50_error using 1; norm_num
  · convert vcell6_51_error using 1; norm_num
  · convert vcell6_52_error using 1; norm_num
  · convert vcell6_53_error using 1; norm_num
  · convert vcell6_54_error using 1; norm_num
  · convert vcell6_55_error using 1; norm_num
  · convert vcell6_56_error using 1; norm_num
  · convert vcell6_57_error using 1; norm_num
  · convert vcell6_58_error using 1; norm_num
  · convert vcell6_59_error using 1; norm_num
  · convert vcell6_60_error using 1; norm_num
  · convert vcell6_61_error using 1; norm_num
  · convert vcell6_62_error using 1; norm_num
  · convert vcell6_63_error using 1; norm_num
  · convert vcell6_64_error using 1; norm_num
  · convert vcell6_65_error using 1; norm_num
  · convert vcell6_66_error using 1; norm_num
  · convert vcell6_67_error using 1; norm_num
  · convert vcell6_68_error using 1; norm_num
  · convert vcell6_69_error using 1; norm_num
  · convert vcell6_70_error using 1; norm_num
  · convert vcell6_71_error using 1; norm_num
  · convert vcell6_72_error using 1; norm_num
  · convert vcell6_73_error using 1; norm_num
  · convert vcell6_74_error using 1; norm_num
  · convert vcell6_75_error using 1; norm_num
  · convert vcell6_76_error using 1; norm_num
  · convert vcell6_77_error using 1; norm_num
  · convert vcell6_78_error using 1; norm_num
  · convert vcell6_79_error using 1; norm_num
  · convert vcell6_80_error using 1; norm_num
  · convert vcell6_81_error using 1; norm_num
  · convert vcell6_82_error using 1; norm_num
  · convert vcell6_83_error using 1; norm_num
  · convert vcell6_84_error using 1; norm_num
  · convert vcell6_85_error using 1; norm_num
  · convert vcell6_86_error using 1; norm_num
  · convert vcell6_87_error using 1; norm_num
  · convert vcell6_88_error using 1; norm_num
  · convert vcell6_89_error using 1; norm_num
  · convert vcell6_90_error using 1; norm_num
  · convert vcell6_91_error using 1; norm_num
  · convert vcell6_92_error using 1; norm_num
  · convert vcell6_93_error using 1; norm_num
  · convert vcell6_94_error using 1; norm_num
  · convert vcell6_95_error using 1; norm_num
  · convert vcell6_96_error using 1; norm_num
  · convert vcell6_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
