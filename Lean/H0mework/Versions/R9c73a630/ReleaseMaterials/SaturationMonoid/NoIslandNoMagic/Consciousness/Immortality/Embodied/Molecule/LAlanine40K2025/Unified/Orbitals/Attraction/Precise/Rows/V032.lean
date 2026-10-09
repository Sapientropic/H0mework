import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V032_032_046
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V032_046_056
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V032_056_067
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V032_067_079
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V032_079_092
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V032_092_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_32 (j : Basis) (ordered : (32 : Basis) ≤ j) :
    |aoIntegral (32 : Basis) j - (recordedAttraction (32 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (32 : Basis) = ⟨32,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(32 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (13 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (14 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (15 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (16 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (17 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (18 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (19 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (20 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (21 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (22 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (23 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (24 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (25 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (26 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (27 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (28 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (29 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (30 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(32 : Basis) ≤ (31 : Basis) by decide) ordered)
  · convert vcell32_32_error using 1; norm_num
  · convert vcell32_33_error using 1; norm_num
  · convert vcell32_34_error using 1; norm_num
  · convert vcell32_35_error using 1; norm_num
  · convert vcell32_36_error using 1; norm_num
  · convert vcell32_37_error using 1; norm_num
  · convert vcell32_38_error using 1; norm_num
  · convert vcell32_39_error using 1; norm_num
  · convert vcell32_40_error using 1; norm_num
  · convert vcell32_41_error using 1; norm_num
  · convert vcell32_42_error using 1; norm_num
  · convert vcell32_43_error using 1; norm_num
  · convert vcell32_44_error using 1; norm_num
  · convert vcell32_45_error using 1; norm_num
  · convert vcell32_46_error using 1; norm_num
  · convert vcell32_47_error using 1; norm_num
  · convert vcell32_48_error using 1; norm_num
  · convert vcell32_49_error using 1; norm_num
  · convert vcell32_50_error using 1; norm_num
  · convert vcell32_51_error using 1; norm_num
  · convert vcell32_52_error using 1; norm_num
  · convert vcell32_53_error using 1; norm_num
  · convert vcell32_54_error using 1; norm_num
  · convert vcell32_55_error using 1; norm_num
  · convert vcell32_56_error using 1; norm_num
  · convert vcell32_57_error using 1; norm_num
  · convert vcell32_58_error using 1; norm_num
  · convert vcell32_59_error using 1; norm_num
  · convert vcell32_60_error using 1; norm_num
  · convert vcell32_61_error using 1; norm_num
  · convert vcell32_62_error using 1; norm_num
  · convert vcell32_63_error using 1; norm_num
  · convert vcell32_64_error using 1; norm_num
  · convert vcell32_65_error using 1; norm_num
  · convert vcell32_66_error using 1; norm_num
  · convert vcell32_67_error using 1; norm_num
  · convert vcell32_68_error using 1; norm_num
  · convert vcell32_69_error using 1; norm_num
  · convert vcell32_70_error using 1; norm_num
  · convert vcell32_71_error using 1; norm_num
  · convert vcell32_72_error using 1; norm_num
  · convert vcell32_73_error using 1; norm_num
  · convert vcell32_74_error using 1; norm_num
  · convert vcell32_75_error using 1; norm_num
  · convert vcell32_76_error using 1; norm_num
  · convert vcell32_77_error using 1; norm_num
  · convert vcell32_78_error using 1; norm_num
  · convert vcell32_79_error using 1; norm_num
  · convert vcell32_80_error using 1; norm_num
  · convert vcell32_81_error using 1; norm_num
  · convert vcell32_82_error using 1; norm_num
  · convert vcell32_83_error using 1; norm_num
  · convert vcell32_84_error using 1; norm_num
  · convert vcell32_85_error using 1; norm_num
  · convert vcell32_86_error using 1; norm_num
  · convert vcell32_87_error using 1; norm_num
  · convert vcell32_88_error using 1; norm_num
  · convert vcell32_89_error using 1; norm_num
  · convert vcell32_90_error using 1; norm_num
  · convert vcell32_91_error using 1; norm_num
  · convert vcell32_92_error using 1; norm_num
  · convert vcell32_93_error using 1; norm_num
  · convert vcell32_94_error using 1; norm_num
  · convert vcell32_95_error using 1; norm_num
  · convert vcell32_96_error using 1; norm_num
  · convert vcell32_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
