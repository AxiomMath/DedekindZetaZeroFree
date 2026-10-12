module

public import DedekindZetaZeroFree.Metaplectic.Kubota.PGL.LocalCover

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def depth (q : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (KPLocalChartTopology.deep_chart_topology F ζ hζ q).choose

theorem depth_admissible (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalChartTopology.MatrixChartDepth F q (depth F ζ hζ q) :=
  (KPLocalChartTopology.deep_chart_topology F ζ hζ q).choose_spec.1

def localTopology (v : KPHilbert.Place F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  match v with
  | Sum.inl w => KPLocalChartTopology.complexTopology F ζ hζ w
  | Sum.inr q => KPLocalChartTopology.translatedTopology F ζ hζ q (depth F ζ hζ q)

attribute [local instance] localTopology

def Bad (q : HeightOneSpectrum (𝓞 F)) : Prop :=
  ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) = 2 ∨
    ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) = 3

lemma char_mem (q : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (hn : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) = n) :
    (n : 𝓞 F) ∈ q.asIdeal := by
  letI : ValuativeRel (KPTameCompact.K F q) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  let ν : Valuation (KPTameCompact.K F q) (WithZero (Multiplicative ℤ)) := Valued.v
  letI : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hz : (n : KPTameCompact.O F q ⧸ KPTameCompact.p F q) = 0 := by
    rw [← hn]
    exact CharP.cast_eq_zero _ (ringChar _)
  have hp : (n : KPTameCompact.O F q) ∈ KPTameCompact.p F q := by
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa using hz)
  have hnu : ¬ IsUnit (n : KPTameCompact.O F q) := by
    exact (IsLocalRing.mem_maximalIdeal _).mp hp
  have hlt := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hnu
  have ht : ν (n : KPTameCompact.K F q) < 1 := by
    rw [← Valuation.vlt_one_iff, Valuation.vlt_one_iff (ValuativeRel.valuation _)]
    exact hlt
  have he : ν (n : KPTameCompact.K F q) = q.valuation F (algebraMap (𝓞 F) F (n : 𝓞 F)) := by
    simpa only [map_natCast] using q.valuedAdicCompletion_eq_valuation (K := F) (n : 𝓞 F)
  rw [he, q.valuation_lt_one_iff_mem] at ht
  exact ht

theorem bad_finite : {q : HeightOneSpectrum (𝓞 F) | Bad F q}.Finite := by
  have hfin : {q : HeightOneSpectrum (𝓞 F) | q.asIdeal ∣ Ideal.span {(6 : 𝓞 F)}}.Finite :=
    Ideal.finite_factors (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using
        (show (6 : 𝓞 F) ≠ 0 by norm_num))
  apply hfin.subset
  intro q hq
  change q.asIdeal ∣ Ideal.span {(6 : 𝓞 F)}
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  rcases hq with h2 | h3
  · have h := char_mem F q 2 h2
    convert q.asIdeal.mul_mem_left 3 h using 1 <;> norm_num
  · have h := char_mem F q 3 h3
    convert q.asIdeal.mul_mem_left 2 h using 1 <;> norm_num

theorem deepLift_mul (q : HeightOneSpectrum (𝓞 F))
    (g h : KPLocalCube.Gamma F q (depth F ζ hζ q)) :
    KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (g * h).val =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr q) g.val *
        KPLocalCover.sectionMap F ζ hζ (Sum.inr q) h.val := by
  obtain ⟨s, hs, _, _⟩ := KPDeepRawSplitting.raw_section_splitting F ζ hζ q
    (depth F ζ hζ q) (fun g hg h hh =>
      KPDeepRawSplitting.sigmaTwo_eq_one_on_Gamma F ζ hζ q (depth F ζ hζ q)
        (depth_admissible F ζ hζ q).2 g h hg hh)
  rw [← hs, ← hs, ← hs]
  exact s.map_mul g h

def deepLift (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalCube.Gamma F q (depth F ζ hζ q) →*
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) where
  toFun g := KPLocalCover.sectionMap F ζ hζ (Sum.inr q) g.val
  map_one' := rfl
  map_mul' := deepLift_mul F ζ hζ q

def finiteCompact (q : HeightOneSpectrum (𝓞 F)) :
    Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :=
  if h : Bad F q then (deepLift F ζ hζ q).range
  else (KPGoodCompactSplitting.kStar F ζ hζ q
    (fun h3 => h (Or.inr h3))).range

def compact (v : KPHilbert.Place F) : Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  match v with
  | Sum.inl _ => ⊤
  | Sum.inr q => finiteCompact F ζ hζ q

abbrev RestrictedCover := RestrictedProduct
  (fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F ζ hζ v)
  (fun v => (compact F ζ hζ v : Set _)) Filter.cofinite

instance restrictedTopology : TopologicalSpace (RestrictedCover F ζ hζ) :=
  inferInstanceAs (TopologicalSpace (RestrictedProduct
    (fun v : KPHilbert.Place F => KPLocalCover.CubicGL2Raw F ζ hζ v)
    (fun v => (compact F ζ hζ v : Set _)) Filter.cofinite))

def localToRestricted (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v →* RestrictedCover F ζ hζ :=
  RestrictedProduct.mulSingleMonoidHom (compact F ζ hζ) v

abbrev CentralTuples := RestrictedProduct
  (fun _ : KPHilbert.Place F => rootsOfUnity 3 F)
  (fun _ => ((⊥ : Subgroup (rootsOfUnity 3 F)) : Set _)) Filter.cofinite

theorem centralTuples_finiteSupport (ε : CentralTuples F) :
    Function.HasFiniteMulSupport (fun v => ε v) := by
  have h : ∀ᶠ v in Filter.cofinite, ε v = 1 :=
    ε.eventually.mono (fun _ hv => hv)
  simpa only [Filter.eventually_cofinite, Function.HasFiniteMulSupport,
    Function.mulSupport] using h

def centralProduct : CentralTuples F →* rootsOfUnity 3 F where
  toFun ε := ∏ᶠ v, ε v
  map_one' := by simp
  map_mul' ε δ := finprod_mul_distrib
    (centralTuples_finiteSupport F ε) (centralTuples_finiteSupport F δ)

def centralTupleMap : CentralTuples F →* RestrictedCover F ζ hζ :=
  RestrictedProduct.mapAlongMonoidHom _ _ id Filter.tendsto_id
    (fun v => KPLocalCover.centralInjection F ζ hζ v)
    (Filter.Eventually.of_forall (fun v => by
      intro ε hε
      have : ε = 1 := hε
      simpa [this] using (compact F ζ hζ v).one_mem))

theorem finiteCompact_compact_open (q : HeightOneSpectrum (𝓞 F)) :
    IsCompact (finiteCompact F ζ hζ q : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) ∧
      IsOpen (finiteCompact F ζ hζ q : Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) := by
  let m := depth F ζ hζ q
  have hm := depth_admissible F ζ hζ q
  change @IsCompact _ (KPLocalChartTopology.translatedTopology F ζ hζ q m) _ ∧
    @IsOpen _ (KPLocalChartTopology.translatedTopology F ζ hζ q m) _
  letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
  unfold finiteCompact
  split_ifs with hb
  · have he : (deepLift F ζ hζ q : KPLocalCube.Gamma F q m → _ ) =
        KPLocalChartTopology.translatedChart F ζ hζ q m 1 := by
      funext g
      exact (one_mul _).symm
    rw [MonoidHom.coe_range, he]
    letI : CompactSpace (KPLocalCube.Gamma F q m) :=
      isCompact_iff_compactSpace.mp (KPLocalCube.Gamma_compact_open F q m hm.1).1
    have ho := KPLocalChartTopology.translatedChart_isOpenEmbedding F ζ hζ q m hm 1
    exact ⟨isCompact_range ho.continuous, ho.isOpen_range⟩
  · rw [MonoidHom.coe_range]
    exact ⟨KPGoodCompactSplitting.kStar_compact_image F ζ hζ q _ m hm,
      KPGoodCompactSplitting.kStar_open_image F ζ hζ q _ m hm⟩

theorem compact_open (v : KPHilbert.Place F) :
    IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v)) := by
  cases v with
  | inl w => exact isOpen_univ
  | inr q => exact (finiteCompact_compact_open F ζ hζ q).2

theorem compact_inf_kernel (v : KPHilbert.Place F) :
    v ∈ Set.range Sum.inr →
      compact F ζ hζ v ⊓ (KPLocalCover.projection F ζ hζ v).ker = ⊥ := by
  rintro ⟨q, rfl⟩
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  have hc : x ∈ finiteCompact F ζ hζ q := hx.1
  have hk : KPLocalCover.projection F ζ hζ (Sum.inr q) x = 1 := hx.2
  unfold finiteCompact at hc
  split_ifs at hc with hb
  · obtain ⟨g, rfl⟩ := hc
    have hg : g = 1 := Subtype.ext hk
    rw [hg, map_one]
  · obtain ⟨g, rfl⟩ := hc
    have hg : g = 1 := KPTameCompact.inclusion_injective F q (by
      rw [map_one]
      exact hk)
    rw [hg, map_one]

end
end DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
