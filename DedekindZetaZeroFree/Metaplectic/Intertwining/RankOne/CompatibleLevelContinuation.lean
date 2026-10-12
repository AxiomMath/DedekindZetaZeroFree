module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.FiniteLevelMeromorphicContinuation

@[expose] public section

set_option maxHeartbeats 4000000
noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem actual_common_level (δ : Sign) (φ : compactPicture S.borel P S.iwasawa δ) :
    ∃ J : CompactOpenLevel (ActualCover F ζ hζ q),
      (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup ∧
      φ ∈ compactLevel S.borel P S.iwasawa δ J := by
  let f := compactTrivialization S.borel P S.iwasawa δ 0 φ
  obtain ⟨U, hU⟩ := f.property.2
  let J : CompactOpenLevel (ActualCover F ζ hζ q) :=
    ⟨U ⊓ S.iwasawa.compact.toOpenSubgroup,
      S.iwasawa.compact.isCompact.of_isClosed_subset
        (U ⊓ S.iwasawa.compact.toOpenSubgroup).isClosed (by intro g hg; exact hg.2)⟩
  have hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup :=
    fun _ hg => hg.2
  refine ⟨J, hJ, ?_⟩
  apply (compact_level_identification S.borel P S.iwasawa δ J hJ 0 φ).mpr
  intro j
  apply Subtype.ext
  exact hU j j.property.1

theorem actual_level_mono (δ : Sign) (J J' : CompactOpenLevel (ActualCover F ζ hζ q))
    (h : (J'.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ J.toOpenSubgroup) :
    compactLevel S.borel P S.iwasawa δ J ≤ compactLevel S.borel P S.iwasawa δ J' := by
  intro φ hφ j k k' hk
  exact hφ ⟨j, h j.property⟩ k k' hk

variable (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
  (ε : Sign)

theorem actualContinuedLevel_compatible
    (J J' : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (hJ' : (J'.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (φ' : compactLevel S.borel P S.iwasawa (sourceSign ε) J')
    (hφ : φ.val = φ'.val) (s : ℂ) :
    (actualContinuedLevel F ζ hζ q S P J hJ μ hμ π hπ ε s φ).val =
      (actualContinuedLevel F ζ hζ q S P J' hJ' μ hμ π hπ ε s φ').val := by
  have hinj : Function.Injective (algebraMap F (LocalField F q)) := (algebraMap F (LocalField F q)).injective
  let η : LocalField F q := (algebraMap F (LocalField F q) ζ) ^ 4
  have hη : IsPrimitiveRoot η 3 := by
    simpa [η] using (hζ.map_of_injective hinj).pow_of_dvd (p := 4) (by norm_num) (by norm_num)
  have hv : valuation (LocalField F q) η = 1 := by
    have hp : (valuation (LocalField F q) η) ^ 3 = 1 := by
      rw [← map_pow, hη.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hp
  have hη' : IsPrimitiveRoot (⟨η, hv.le⟩ : (valuation (LocalField F q)).integer) 3 :=
    hη.of_map_of_injective (f := (valuation (LocalField F q)).integer.subtype) Subtype.val_injective
  exact continuedLevel_compatible (LocalField F q) S.borel P S.iwasawa J J' hJ hJ' μ hμ
    ⟨η, hv.le⟩ hη' ε _ _
    (actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ π hπ ε)
    (actualLevelNumerator_spec F ζ hζ q S P J' hJ' μ hμ π hπ ε) φ φ' hφ s

 def gluedValue (s : ℂ) (φ : compactPicture S.borel P S.iwasawa (sourceSign ε)) :
    compactPicture S.borel P S.iwasawa (targetSign ε) :=
  let J := (actual_common_level F ζ hζ q S P (sourceSign ε) φ).choose
  let H := (actual_common_level F ζ hζ q S P (sourceSign ε) φ).choose_spec
  (actualContinuedLevel F ζ hζ q S P J H.1 μ hμ π hπ ε s ⟨φ, H.2⟩).val

 theorem gluedValue_eq_level (s : ℂ)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
    gluedValue F ζ hζ q S P μ hμ π hπ ε s φ.val =
      (actualContinuedLevel F ζ hζ q S P J hJ μ hμ π hπ ε s φ).val := by
  let L := (actual_common_level F ζ hζ q S P (sourceSign ε) φ.val).choose
  let H := (actual_common_level F ζ hζ q S P (sourceSign ε) φ.val).choose_spec
  change (actualContinuedLevel F ζ hζ q S P L H.1 μ hμ π hπ ε s ⟨φ.val, H.2⟩).val = _
  exact actualContinuedLevel_compatible F ζ hζ q S P μ hμ π hπ ε L J H.1 hJ ⟨φ.val, H.2⟩ φ rfl s

def actualContinued (s : ℂ) :
    compactPicture S.borel P S.iwasawa (sourceSign ε) →ₗ[ℂ]
      compactPicture S.borel P S.iwasawa (targetSign ε) where
  toFun := gluedValue F ζ hζ q S P μ hμ π hπ ε s
  map_add' φ ψ := by
    obtain ⟨J, hJ, hφ⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ
    obtain ⟨J', hJ', hψ⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) ψ
    let L : CompactOpenLevel (ActualCover F ζ hζ q) :=
      ⟨J.toOpenSubgroup ⊓ J'.toOpenSubgroup,
        J.isCompact.of_isClosed_subset (J.toOpenSubgroup ⊓ J'.toOpenSubgroup).isClosed (by intro g hg; exact hg.1)⟩
    have hL : (L.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup := fun _ hg => hJ hg.1
    have hf : φ ∈ compactLevel S.borel P S.iwasawa (sourceSign ε) L :=
      actual_level_mono F ζ hζ q S P _ J L (fun _ hg => hg.1) hφ
    have hg : ψ ∈ compactLevel S.borel P S.iwasawa (sourceSign ε) L :=
      actual_level_mono F ζ hζ q S P _ J' L (fun _ hg => hg.2) hψ
    rw [gluedValue_eq_level F ζ hζ q S P μ hμ π hπ ε s L hL ⟨φ + ψ, add_mem hf hg⟩,
      gluedValue_eq_level F ζ hζ q S P μ hμ π hπ ε s L hL ⟨φ, hf⟩,
      gluedValue_eq_level F ζ hζ q S P μ hμ π hπ ε s L hL ⟨ψ, hg⟩]
    exact congrArg Subtype.val (map_add (actualContinuedLevel F ζ hζ q S P L hL μ hμ π hπ ε s) ⟨φ, hf⟩ ⟨ψ, hg⟩)
  map_smul' c φ := by
    obtain ⟨J, hJ, hf⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ
    rw [gluedValue_eq_level F ζ hζ q S P μ hμ π hπ ε s J hJ ⟨c • φ, (compactLevel S.borel P S.iwasawa (sourceSign ε) J).smul_mem c hf⟩,
      gluedValue_eq_level F ζ hζ q S P μ hμ π hπ ε s J hJ ⟨φ, hf⟩]
    exact congrArg Subtype.val (map_smul (actualContinuedLevel F ζ hζ q S P J hJ μ hμ π hπ ε s) c ⟨φ, hf⟩)

theorem actualContinued_eq_level (s : ℂ)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
    actualContinued F ζ hζ q S P μ hμ π hπ ε s φ.val =
      (actualContinuedLevel F ζ hζ q S P J hJ μ hμ π hπ ε s φ).val :=
  gluedValue_eq_level F ζ hζ q S P μ hμ π hπ ε s J hJ φ

end DedekindZetaZeroFree.KPRankOneShellRepair

end
