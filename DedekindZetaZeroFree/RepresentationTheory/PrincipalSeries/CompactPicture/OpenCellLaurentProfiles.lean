module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps

open scoped NumberField Valued ValuativeRel Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

private theorem norm_root (y : (LocalField F q)ˣ) (r : ℂˣ) :
    normPower (LocalField F q) y (additiveParameter F q r) =
    (r : ℂ) ^ (-(WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q) (valuation (LocalField F q) (y : LocalField F q))) : ℤ)) := by
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by exact_mod_cast Nat.card_pos (α := IsLocalRing.ResidueField (Valuation.integer (valuation (LocalField F q))))
  have hq1 : 1 < residueCardinality (LocalField F q) := Finite.one_lt_card
  have hlog : (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hq1)).ne'
  rw [normPower, localAbs, Real.log_rpow hq]
  unfold additiveParameter
  rw [Complex.ofReal_mul]
  have he : -Complex.log (r : ℂ) / (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ) *
      (↑((WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
        (valuation (LocalField F q) (y : LocalField F q))) : ℤ) : ℝ) *
       (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) =
      (-(WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
        (valuation (LocalField F q) (y : LocalField F q))) : ℤ) : ℂ) * Complex.log (r : ℂ) := by
    simp only [Complex.ofReal_intCast, Int.cast_neg]
    field_simp [hlog]
  rw [he]
  simpa only [Int.cast_neg] using (Complex.exp_int_mul (Complex.log (r : ℂ))
    (-(WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (y : LocalField F q))) : ℤ))).trans (by rw [Complex.exp_log r.ne_zero])

private theorem pointwise_monomial
    (B : Binding F ζ hζ q A P) (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (g : Cover F ζ hζ q) :
    ∃ n : ℤ, ∀ r : ℂˣ,
      (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r).val g =
        (r : ℂ)^n • (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ 1).val g := by
  classical
  let f (r : ℂˣ) := actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r
  have hf (r : ℂˣ) := (Classical.choose_spec (center_pure_coordinate_section F ζ hζ q T A P B rep hrep d
    (additiveParameter F q r) φ hφ hcφ)).1
  by_cases hg : ∃ (b : A.B) (x : LocalField F q), g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x
  · obtain ⟨b,x,rfl⟩ := hg
    let n : ℤ := -(WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q) (valuation (LocalField F q) (A.coordinate (A.retract b) : LocalField F q))) : ℤ)
    refine ⟨n, ?_⟩
    intro r
    have hx : (f r).val (openCoordinate F ζ hζ q x) = (f 1).val (openCoordinate F ζ hζ q x) :=
      (centerCoordinates T rep hrep).injective ((hf r).1 x |>.trans ((hf 1).1 x).symm)
    change (f r).val _ = (r : ℂ)^n • (f 1).val _
    rw [(f r).property.1, (f 1).property.1, hx]
    change (inducingScalar A (additiveParameter F q r) b) •
      centerTorus F ζ hζ q T A .plus (A.retract b) ((f 1).val (openCoordinate F ζ hζ q x)) =
      (r : ℂ)^n • ((inducingScalar A (additiveParameter F q 1) b) •
      centerTorus F ζ hζ q T A .plus (A.retract b) ((f 1).val (openCoordinate F ζ hζ q x)))
    rw [smul_smul]
    congr 1
    simp only [inducingScalar, norm_root, Units.val_one, one_zpow, mul_one]
    exact mul_comm _ _
  · refine ⟨0, fun r => ?_⟩
    change (f r).val g = (r : ℂ)^0 • (f 1).val g
    have hr : (f r).val g = 0 := (hf r).2 g hg
    have h1 : (f 1).val g = 0 := (hf 1).2 g hg
    rw [hr,h1]; simp

private theorem two_smul_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    {v : V} (hv : v ≠ 0) {m n : ℤ} (h : (2 : ℂ)^m • v = (2 : ℂ)^n • v) : m = n := by
  have hs := smul_left_injective ℂ hv h
  have hr : (2 : ℝ)^m = (2 : ℝ)^n := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zpow, Complex.ofReal_ofNat] using hs
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hr

private theorem lc_of_fixed {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (f : G → V) (hf : SmoothVector vectorRightTranslation f) : IsLocallyConstant f := by
  obtain ⟨J,hJ⟩ := hf
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous (fun y : G => g⁻¹ * y) := continuous_const.mul continuous_id
  have hm : ∀ᶠ y in nhds g, g⁻¹ * y ∈ J :=
    hc.continuousAt.preimage_mem_nhds (by simpa using J.isOpen.mem_nhds J.one_mem)
  filter_upwards [hm] with y hy
  have he := congrFun (hJ (g⁻¹ * y) hy) g
  simpa [vectorRightTranslation] using he

private theorem reconstruction {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (K : CompactOpenLevel G)
    (B : Subgroup G) (ρ : Representation ℂ B V)
    (family : ℂˣ → G → V)
    (hsm : ∀ r, SmoothVector vectorRightTranslation (family r))
    (hcov : ∀ r (b : B) (k k' : K.toOpenSubgroup),
      (k' : G) = (b : G) * (k : G) → family r k' = ρ b (family r k))
    (hmono : ∀ g, ∃ n : ℤ, ∀ r, family r g = (r : ℂ)^n • family 1 g) :
    ∃ (L : CompactOpenLevel G), (L.toOpenSubgroup : Subgroup G) ≤ K.toOpenSubgroup ∧
      ∃ (n : K.toOpenSubgroup → ℤ) (hn : (Set.range n).Finite),
      (∀ (r : ℂˣ) (k : K.toOpenSubgroup), family r k = (r : ℂ)^(n k) • family 1 k) ∧
      ∀ i : ℤ, let c := fun k : K.toOpenSubgroup => if n k = i then family 1 k else 0
      (∀ (b : B) (k k' : K.toOpenSubgroup), (k' : G) = (b : G) * (k : G) → c k' = ρ b (c k)) ∧
      SmoothVector (vectorRightTranslation (G := K.toOpenSubgroup)) c ∧
      (∀ (j : L.toOpenSubgroup) (k k' : K.toOpenSubgroup), (k' : G) = (k : G)*(j : G) → c k' = c k) := by
  classical
  let two : ℂˣ := Units.mk0 2 (by norm_num)
  let rawN (g : G) := Classical.choose (hmono g)
  have hraw (g : G) (r : ℂˣ) : family r g = (r : ℂ)^(rawN g) • family 1 g := Classical.choose_spec (hmono g) r
  let n (k : K.toOpenSubgroup) : ℤ := if family 1 k = 0 then 0 else rawN k
  have hnmono (k : K.toOpenSubgroup) (r : ℂˣ) : family r k = (r : ℂ)^(n k) • family 1 k := by
    dsimp [n]
    split_ifs with h
    · rw [hraw, h]; simp
    · exact hraw k r
  have ninv (k k' : K.toOpenSubgroup)
      (h1 : family 1 k' = family 1 k) (h2 : family two k' = family two k) : n k' = n k := by
    by_cases hz : family 1 k = 0
    · simp [n,h1,hz]
    · apply two_smul_injective hz
      rw [hnmono k' two, hnmono k two, h1] at h2
      exact h2
  obtain ⟨U,hU⟩ := hsm 1
  obtain ⟨W,hW⟩ := hsm two
  let L : CompactOpenLevel G :=
    ⟨K.toOpenSubgroup ⊓ U ⊓ W, (K.isCompact.inter_right U.isClosed).inter_right W.isClosed⟩
  have hL : (L.toOpenSubgroup : Subgroup G) ≤ K.toOpenSubgroup := fun g hg => hg.1.1
  have fixed (r : ℂˣ) (j : L.toOpenSubgroup) (k k' : K.toOpenSubgroup)
      (he : (k' : G) = (k : G)*(j : G)) : family r k' = family r k ∧ n k' = n k := by
    have h1 : family 1 k' = family 1 k := by
      have ht := congrFun (hU j j.property.1.2) k
      change family 1 ((k : G)*(j : G)) = family 1 k at ht
      rwa [← he] at ht
    have h2 : family two k' = family two k := by
      have ht := congrFun (hW j j.property.2) k
      change family two ((k : G)*(j : G)) = family two k at ht
      rwa [← he] at ht
    have hn := ninv k k' h1 h2
    exact ⟨by rw [hnmono k' r, hnmono k r, hn,h1],hn⟩
  have hnlc : IsLocallyConstant n := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro k
    have hl1 : IsLocallyConstant (fun k : K.toOpenSubgroup => family 1 k) := (lc_of_fixed (family 1) (hsm 1)).comp_continuous continuous_subtype_val
    have hl2 : IsLocallyConstant (fun k : K.toOpenSubgroup => family two k) := (lc_of_fixed (family two) (hsm two)).comp_continuous continuous_subtype_val
    have a := (IsLocallyConstant.iff_eventually_eq _).mp hl1 k
    have b := (IsLocallyConstant.iff_eventually_eq _).mp hl2 k
    filter_upwards [a,b] with k' h1 h2
    exact ninv k k' h1 h2
  letI : CompactSpace K.toOpenSubgroup := isCompact_iff_compactSpace.mp K.isCompact
  refine ⟨L,hL,n,hnlc.range_finite,(fun r k => hnmono k r),?_⟩
  intro i
  dsimp only
  have ccov (b : B) (k k' : K.toOpenSubgroup) (he : (k' : G) = (b : G)*(k : G)) :
      (if n k' = i then family 1 k' else 0) = ρ b (if n k = i then family 1 k else 0) := by
    have h1 := hcov 1 b k k' he
    by_cases hz : family 1 k = 0
    · have hz' : family 1 k' = 0 := by rw [h1,hz,map_zero]
      simp [hz,hz']
    · have hn : n k' = n k := by
        have hne : ρ b (family 1 k) ≠ 0 := by
          intro hh
          have ht := congrArg (ρ b⁻¹) hh
          apply hz
          simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply, map_zero] using ht
        apply two_smul_injective hne
        have h2 := hcov two b k k' he
        rw [hnmono k' two, hnmono k two, h1, map_smul] at h2
        exact h2
      simp only [hn]
      split_ifs <;> simp [h1]
  have cfixed (j : L.toOpenSubgroup) (k k' : K.toOpenSubgroup)
      (he : (k' : G) = (k : G)*(j : G)) :
      (if n k' = i then family 1 k' else 0) = (if n k = i then family 1 k else 0) := by
    rw [(fixed 1 j k k' he).1, (fixed 1 j k k' he).2]
  refine ⟨ccov, ?_, cfixed⟩
  let LJ : OpenSubgroup K.toOpenSubgroup := L.toOpenSubgroup.comap K.toOpenSubgroup.toSubgroup.subtype continuous_subtype_val
  refine ⟨LJ, ?_⟩
  intro j hj
  funext k
  exact cfixed ⟨j,hj⟩ k (k*j) rfl

theorem compact_profile_uniform_laurent
    (I : IwasawaData A) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ (L : CompactOpenLevel (Cover F ζ hζ q)),
      (L.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup ∧
      ∃ ψ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .plus L,
        ∀ r : ℂˣ,
          actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r =
            centerCompactTrivialization F ζ hζ q T A I .plus (additiveParameter F q r)
              (ψ.sum (fun n f => (r : ℂ) ^ n • f)).val := by
  classical
  let family (r : ℂˣ) := (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r).val
  have hsm : ∀ r, SmoothVector vectorRightTranslation (family r) :=
    fun r => (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r).property.2
  have hcov (r : ℂˣ) (b : A.B) (k k' : I.compact.toOpenSubgroup)
      (he : (k' : Cover F ζ hζ q) = (b : Cover F ζ hζ q)*(k : Cover F ζ hζ q)) :
      family r k' = centerInducingAction F ζ hζ q T A .plus 0 b (family r k) := by
    have ht := (actualSection F ζ hζ q T A P B rep hrep d φ hφ hcφ r).property.1 b k
    have hb : (b : Cover F ζ hζ q) ∈ I.compact.toOpenSubgroup := by
      have he' : (b : Cover F ζ hζ q) = (k' : Cover F ζ hζ q)*(k : Cover F ζ hζ q)⁻¹ := by
        rw [he]; group
      rw [he']
      exact I.compact.toOpenSubgroup.mul_mem k'.property (I.compact.toOpenSubgroup.inv_mem k.property)
    have ha : centerInducingAction F ζ hζ q T A .plus (additiveParameter F q r) b =
        centerInducingAction F ζ hζ q T A .plus 0 b := by
      apply LinearMap.ext
      intro v
      change (inducingScalar A (additiveParameter F q r) b) •
        (centerTorus F ζ hζ q T A .plus (A.retract b) v) = (inducingScalar A 0 b) •
        (centerTorus F ζ hζ q T A .plus (A.retract b) v)
      simp [inducingScalar,normPower, I.intersection_norm b hb]
    change family r _ = _ at ht
    rw [← he,ha] at ht
    exact ht
  obtain ⟨L,hL,n,hn,hm,hc⟩ := reconstruction I.compact A.B
    (centerInducingAction F ζ hζ q T A .plus 0) family hsm hcov
    (pointwise_monomial F ζ hζ q T A P B rep hrep d φ hφ hcφ)
  let c (i : ℤ) : centerCompactLevel F ζ hζ q T A I .plus L :=
    ⟨⟨fun k => if n k = i then family 1 k else 0, (hc i).1, (hc i).2.1⟩, (hc i).2.2⟩
  have cs (i : ℤ) (hi : c i ≠ 0) : i ∈ hn.toFinset := by
    apply hn.mem_toFinset.mpr
    by_contra hni
    apply hi
    apply Subtype.ext
    apply Subtype.ext
    funext k
    have hne : n k ≠ i := fun h => hni ⟨k,h⟩
    simp [c,hne]
  let ψ : ℤ →₀ centerCompactLevel F ζ hζ q T A I .plus L := Finsupp.onFinset hn.toFinset c cs
  refine ⟨L,hL,ψ,?_⟩
  intro r
  apply (centerCompactTrivialization F ζ hζ q T A I .plus (additiveParameter F q r)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  funext k
  change family r k = ((ψ.sum (fun i v => (r : ℂ)^i • v)).val).val k
  rw [hm r k]
  rw [show ψ.sum (fun i v => (r : ℂ)^i • v) = ∑ i ∈ hn.toFinset, (r : ℂ)^i • c i from
    Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  change (r : ℂ)^n k • family 1 k = ∑ i ∈ hn.toFinset, (r : ℂ)^i • (if n k = i then family 1 k else 0)
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq, if_pos (hn.mem_toFinset.mpr ⟨k,rfl⟩)]

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps
