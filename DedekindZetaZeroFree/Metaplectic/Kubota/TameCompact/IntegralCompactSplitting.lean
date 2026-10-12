module

public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.SmallZeroEntryCocycle
public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.SmallNonzeroEntryCocycle
public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.MixedEntryCocycle
public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.UnitEntryCocycle
public import DedekindZetaZeroFree.Metaplectic.Kubota.LocalCoverChartTopology

@[expose] public section

open scoped NumberField ValuativeRel Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGoodCompactSplitting

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (hv : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)

include hv

theorem kappa_mul (g h : KPTameCompact.K0 F v) :
    KPTameCompact.kappa F v ζ hζ (g * h) =
      KPTameCompact.kappa F v ζ hζ g *
        KPTameCompact.kappa F v ζ hζ h *
          KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v)
            (KPTameCompact.inclusion F v g)
            (KPTameCompact.inclusion F v h) := by
  have hg := (KPTameCompact.det_norm_and_entries F v g).2 1 0
  have hh := (KPTameCompact.det_norm_and_entries F v h).2 1 0
  rcases hg.lt_or_eq with hg | hg <;> rcases hh.lt_or_eq with hh | hh
  · by_cases hz : KPTameCompact.c F v g = 0 ∨ KPTameCompact.c F v h = 0
    · exact KPTameCompact.kappa_mul_small_zero F ζ hζ v hv g h hg hh hz
    · push Not at hz
      exact KPTameCompact.kappa_mul_small_nonzero F v ζ hζ hv g h hz.1 hz.2 hg hh
  · exact KPTameCompact.kappa_mul_small_unit F ζ hζ v hv g h ⟨hg, hh⟩
  · exact KPTameCompact.kappa_mul_unit_small F ζ hζ v hv g h ⟨hg, hh⟩
  · exact KPTameCompact.unit_unit F ζ hζ v hv g h hg hh

theorem kappa_one :
    KPTameCompact.kappa F v ζ hζ (1 : KPTameCompact.K0 F v) = 1 := by
  apply KPTameCompact.kappa_zero F v ζ hζ
  simp [KPTameCompact.c, Matrix.one_apply]

def kStar : KPTameCompact.K0 F v →*
    KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) where
  toFun g := ⟨KPTameCompact.inclusion F v g, KPTameCompact.kappa F v ζ hζ g⟩
  map_one' := by
    exact congrArg₂ KPLocalCover.CubicGL2Raw.mk
      ((KPTameCompact.inclusion F v).map_one) (kappa_one F ζ hζ v hv)
  map_mul' g h := by
    exact congrArg₂ KPLocalCover.CubicGL2Raw.mk
      ((KPTameCompact.inclusion F v).map_mul g h) (kappa_mul F ζ hζ v hv g h)

theorem kStar_eq_section_on_Gamma (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F v m)
    (g : KPTameCompact.K0 F v)
    (hg : KPTameCompact.inclusion F v g ∈ KPLocalCube.Gamma F v m) :
    kStar F ζ hζ v hv g =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v)
        (KPTameCompact.inclusion F v g) := by
  apply congrArg (@KPLocalCover.CubicGL2Raw.mk F _ _ ζ hζ (Sum.inr v)
    (KPTameCompact.inclusion F v g))
  obtain ⟨td, htd⟩ := (hm.2 _ hg).1 1
  obtain ⟨te, hte⟩ := (hm.2 _ hg).2
  have hd : ((td ^ 3 : (KPTameCompact.K F v)ˣ) : KPTameCompact.K F v) =
      KPTameCompact.d F v g := htd
  have hdet : te ^ 3 = Matrix.GeneralLinearGroup.det (KPTameCompact.inclusion F v g) := hte
  simp only [KPTameCompact.kappa]
  split_ifs with hc hd' hn
  · have he : Units.mk0 (KPTameCompact.d F v g / KPTameCompact.Δ F v g)
        (div_ne_zero hd' (Matrix.GeneralLinearGroup.det_ne_zero
          (KPTameCompact.inclusion F v g))) = (td / te) ^ 3 := by
      apply Units.ext
      simp only [div_pow, Units.val_div_eq_div_val]
      rw [hd, hdet]
      rfl
    rw [he]
    exact ((KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.1 _ _).2
  all_goals rfl

theorem kStar_continuous (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F v m) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ v m
    Continuous (kStar F ζ hζ v hv) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ v m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ v m hm).2.2
  have hi : Continuous (KPTameCompact.inclusion F v) :=
    (continuous_subtype_val : Continuous (KPTameCompact.O F v).subtype).generalLinearGroup_map
  let S : Set (KPTameCompact.K0 F v) :=
    KPTameCompact.inclusion F v ⁻¹' (KPLocalCube.Gamma F v m : Set _)
  have hS : IsOpen S := (KPLocalCube.Gamma_compact_open F v m hm.1).2.preimage hi
  let q : S → KPLocalCube.Gamma F v m := fun g =>
    ⟨KPTameCompact.inclusion F v g.val, g.property⟩
  have hq : Continuous q := (hi.comp continuous_subtype_val).subtype_mk _
  have hchart := (KPLocalChartTopology.translatedChart_isOpenEmbedding
    F ζ hζ v m hm 1).continuous
  have hres : Continuous (fun g : S => kStar F ζ hζ v hv g.val) := by
    convert hchart.comp hq using 1
    ext g
    simp only [Function.comp_apply, KPLocalChartTopology.translatedChart, one_mul]
    exact kStar_eq_section_on_Gamma F ζ hζ v hv m hm g.val g.property
  apply continuous_of_continuousAt_one (kStar F ζ hζ v hv)
  apply (continuousOn_iff_continuous_restrict.mpr hres).continuousAt
  apply hS.mem_nhds
  change KPTameCompact.inclusion F v 1 ∈ KPLocalCube.Gamma F v m
  rw [map_one]
  exact Subgroup.one_mem _

theorem kStar_compact_image (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F v m) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ v m
    IsCompact (Set.range (kStar F ζ hζ v hv)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ v m
  letI : ValuativeRel (KPTameCompact.K F v) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F v
  letI : IsNonarchimedeanLocalField (KPTameCompact.K F v) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v
  letI : CompactSpace (KPTameCompact.O F v) := inferInstance
  letI : CompactSpace (Matrix (Fin 2) (Fin 2) (KPTameCompact.O F v)) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → KPTameCompact.O F v))
  letI : CompactSpace (KPTameCompact.K0 F v) := inferInstance
  exact isCompact_range (kStar_continuous F ζ hζ v hv m hm)

theorem kStar_open_image (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F v m) :
    letI := KPLocalChartTopology.translatedTopology F ζ hζ v m
    IsOpen (Set.range (kStar F ζ hζ v hv)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ v m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ v m hm).2.2
  have hopen := (KPLocalChartTopology.translatedChart_isOpenEmbedding
    F ζ hζ v m hm 1).isOpen_range
  have hsub : Set.range (KPLocalChartTopology.translatedChart F ζ hζ v m 1) ⊆
      Set.range (kStar F ζ hζ v hv) := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨g, hg, he⟩ := k.property
    refine ⟨g, ?_⟩
    simp only [KPLocalChartTopology.translatedChart, one_mul]
    rw [kStar_eq_section_on_Gamma F ζ hζ v hv m hm g (he ▸ k.property), he]
  rw [← MonoidHom.coe_range]
  apply Subgroup.isOpen_of_mem_nhds
  apply Filter.mem_of_superset (hopen.mem_nhds (x := 1) ?_) hsub
  refine ⟨1, ?_⟩
  simp only [KPLocalChartTopology.translatedChart, one_mul]
  rfl

theorem kStar_upper_triangular (g : KPTameCompact.K0 F v)
    (hc : KPTameCompact.c F v g = 0) :
    kStar F ζ hζ v hv g =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v)
        (KPTameCompact.inclusion F v g) := by
  exact congrArg (@KPLocalCover.CubicGL2Raw.mk F _ _ ζ hζ (Sum.inr v) (KPTameCompact.inclusion F v g))
    (KPTameCompact.kappa_zero F v ζ hζ g hc)

theorem kStar_swap (g : KPTameCompact.K0 F v)
    (hc : KPTameCompact.c F v g = 1) :
    kStar F ζ hζ v hv g =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v)
        (KPTameCompact.inclusion F v g) := by
  exact congrArg (@KPLocalCover.CubicGL2Raw.mk F _ _ ζ hζ (Sum.inr v) (KPTameCompact.inclusion F v g))
    (KPTameCompact.kappa_norm_one F v ζ hζ g (by rw [hc, norm_one]))

theorem kStar_unit_diagonal (u u' : (KPTameCompact.O F v)ˣ)
    (g : KPTameCompact.K0 F v)
    (hg : (g : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F v)) =
      !![(u : KPTameCompact.O F v), 0; 0, (u' : KPTameCompact.O F v)]) :
    kStar F ζ hζ v hv g =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v)
        (KPTameCompact.inclusion F v g) := by
  apply kStar_upper_triangular F ζ hζ v hv
  simp [KPTameCompact.c, hg]

theorem kStar_swap_matrix (g : KPTameCompact.K0 F v)
    (hg : (g : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F v)) = !![0, 1; 1, 0]) :
    kStar F ζ hζ v hv g =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v)
        (KPTameCompact.inclusion F v g) := by
  apply kStar_swap F ζ hζ v hv
  simp [KPTameCompact.c, hg]

theorem kStar_upper_root_matrix (t : KPTameCompact.O F v)
    (g : KPTameCompact.K0 F v)
    (hg : (g : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F v)) = !![1, t; 0, 1]) :
    kStar F ζ hζ v hv g =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v)
        (KPTameCompact.inclusion F v g) := by
  apply kStar_upper_triangular F ζ hζ v hv
  simp [KPTameCompact.c, hg]

end
end DedekindZetaZeroFree.KPGoodCompactSplitting

section

open scoped NumberField ValuativeRel Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGoodCompactSplitting

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))
variable (hv : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)

include hv

theorem projection_kStar (g : KPTameCompact.K0 F v) :
    KPLocalCover.projection F ζ hζ (Sum.inr v)
      (kStar F ζ hζ v hv g) = KPTameCompact.inclusion F v g := rfl

end
end DedekindZetaZeroFree.KPGoodCompactSplitting

end
