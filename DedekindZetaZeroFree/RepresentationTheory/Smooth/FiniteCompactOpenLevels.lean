module

public import DedekindZetaZeroFree.Eisenstein.Induction.LocalSphericalSections

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FiniteLevels
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

def localLevel (q : HeightOneSpectrum (𝓞 F)) :
    CompactOpenLevel (KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :=
  if h : q ∈ C.exceptional then (LocalSeed.finite_has_level F ζ hζ P C q).choose
  else (C.canonical q).iwasawa.compact

theorem local_fixed (q : HeightOneSpectrum (𝓞 F))
    (k : (localLevel F ζ hζ P C q).toOpenSubgroup)
    (g : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :
    (LocalSeed.finite F ζ hζ P C q).val (g * k.val) =
      (LocalSeed.finite F ζ hζ P C q).val g := by
  by_cases h : q ∈ C.exceptional
  · exact (LocalSeed.finite_has_level F ζ hζ P C q).choose_spec.2
      ⟨k.val, by simpa only [localLevel, dif_pos h] using k.property⟩ g
  · exact LocalSeed.finite_right_fixed F ζ hζ P C q h
      ⟨k.val, by simpa only [localLevel, dif_neg h] using k.property⟩ g

theorem localLevel_standard : ∀ᶠ q in Filter.cofinite,
    (localLevel F ζ hζ P C q).toOpenSubgroup.toSubgroup =
      pglCompact F ζ hζ (Sum.inr q) := by
  filter_upwards [C.exceptional.finite_toSet.eventually_cofinite_notMem,
    (bad_finite F).eventually_cofinite_notMem] with q hq hb
  obtain ⟨ht, hc⟩ := C.actual_compact q hq
  have hq' : q ∉ C.exceptional := hq
  simp only [localLevel, dif_neg hq']
  rw [hc]
  change (KPLocalExceptionalConstruction.actualGoodCompactSplit F ζ hζ q ht).range =
    (finiteCompact F ζ hζ q).map (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q))
  simp only [finiteCompact, dif_neg hb]
  rw [KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.range_comp]

def productLevel : ActualFiniteFactor.ProductLevelData F ζ hζ where
  localLevel := localLevel F ζ hζ P C
  cofinally_standard := localLevel_standard F ζ hζ P C

theorem raw_local_fixed (u : RestrictedCover F ζ hζ)
    (hu : u ∈ ActualFiniteFactor.productTuples F ζ hζ (productLevel F ζ hζ P C))
    (q : HeightOneSpectrum (𝓞 F))
    (g : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :
    (LocalSeed.finite F ζ hζ P C q).val
      (g * KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q))) =
        (LocalSeed.finite F ζ hζ P C q).val g := by
  exact local_fixed F ζ hζ P C q
    ⟨_, (Subgroup.mem_iInf.mp hu.2) q⟩ g

end DedekindZetaZeroFree.EisensteinReferenceSections.FiniteLevels

end
