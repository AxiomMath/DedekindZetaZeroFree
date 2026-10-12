module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Iwasawa.IntegralCompactSubgroup

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def localCompactFactorMax (v : KPHilbert.Place F) :
    Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  match v with
  | Sum.inl w => archimedeanLocalCompact F ζ hζ w
  | Sum.inr q => if KPAdelicCoverRestrictedProduct.Bad F q then
      integralRawCompact F ζ hζ q else KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q

def fullCompactPreimageMax :
    Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) where
  carrier := {x | ∀ v, x v ∈ localCompactFactorMax F ζ hζ v}
  one_mem' v := by
    rw [RestrictedProduct.one_apply]
    exact (localCompactFactorMax F ζ hζ v).one_mem
  mul_mem' hx hy v := by
    rw [RestrictedProduct.mul_apply]
    exact (localCompactFactorMax F ζ hζ v).mul_mem (hx v) (hy v)
  inv_mem' hx v := by
    rw [RestrictedProduct.inv_apply]
    exact (localCompactFactorMax F ζ hζ v).inv_mem (hx v)

def iwasawaCompactSubgroupMax : Subgroup (KPLiteralRaw.G F ζ hζ) :=
  (fullCompactPreimageMax F ζ hζ).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

theorem localCompactFactor_le_max (v : KPHilbert.Place F) :
    localCompactFactor F ζ hζ v ≤ localCompactFactorMax F ζ hζ v := by
  cases v with
  | inl w => exact le_rfl
  | inr q =>
    dsimp [localCompactFactorMax, localCompactFactor]
    split_ifs
    · exact finiteCompact_le_integralRawCompact F ζ hζ q
    · exact le_rfl

theorem localCompactFactorMax_eq_compact_eventually :
    ∀ᶠ v in Filter.cofinite, localCompactFactorMax F ζ hζ v =
      KPAdelicCoverRestrictedProduct.compact F ζ hζ v := by
  have hf : {v : KPHilbert.Place F | ∃ w : InfinitePlace F, v = Sum.inl w}.Finite := by
    exact (Set.finite_range Sum.inl).subset (by rintro v ⟨w,rfl⟩; exact ⟨w,rfl⟩)
  have hb := (KPAdelicCoverRestrictedProduct.bad_finite F).image
    (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)
  have hfi : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite,
      ¬ (∃ w : InfinitePlace F, v = Sum.inl w) := by
    exact Filter.eventually_cofinite.mpr (by simpa using hf)
  have hbi : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite,
      v ∉ Sum.inr '' {q | KPAdelicCoverRestrictedProduct.Bad F q} := by
    apply Filter.eventually_cofinite.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hb
  filter_upwards [hfi, hbi] with v hv hvb
  cases v with
  | inl w => exact False.elim (hv ⟨w,rfl⟩)
  | inr q =>
    have hn : ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      intro h
      exact hvb ⟨q,h,rfl⟩
    simp [localCompactFactorMax, hn, KPAdelicCoverRestrictedProduct.compact]

theorem fullCompactPreimage_le_max :
    fullCompactPreimage F ζ hζ ≤ fullCompactPreimageMax F ζ hζ :=
  fun _ hx v => localCompactFactor_le_max F ζ hζ v (hx v)

theorem iwasawaCompactSubgroupFull_le_max :
    iwasawaCompactSubgroupFull F ζ hζ ≤ iwasawaCompactSubgroupMax F ζ hζ :=
  Subgroup.map_mono (fullCompactPreimage_le_max F ζ hζ)

theorem complexCompactLift_mem_iwasawaCompactSubgroupMax (w : InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2) :
    KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k ∈
      iwasawaCompactSubgroupMax F ζ hζ :=
  iwasawaCompactSubgroupFull_le_max F ζ hζ
    (complexCompactLift_mem_iwasawaCompactSubgroupFull F ζ hζ w k)

end DedekindZetaZeroFree.PrincipalOfKP

end
