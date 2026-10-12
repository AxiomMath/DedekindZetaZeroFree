module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TamePolarizationsAndTwistedCoinvariants

@[expose] public section

section
noncomputable section
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.Stabilization
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw

private theorem scalar_root_invariant
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (f : scalarSections F ζ hζ q S P hP ε)
    (x : LocalField F q) (g : ActualCover F ζ hζ q) :
    f.val (KPPGLLocalCover.N F ζ hζ (Sum.inr q) x * g) = f.val g := by
  let n := S.borel.upperRoot (Multiplicative.ofAdd x)
  have hn : n ∈ (HL F ζ hζ q S P).comap S.borel.retract := by
    change S.heisenberg.π (S.borel.retract n) ∈ P.L
    rw [S.borel.retract_upperRoot, map_one]
    exact P.L.one_mem
  let b : BL F ζ hζ q S P := ⟨n, ⟨n, hn, rfl⟩⟩
  have he : (b : ActualCover F ζ hζ q) = KPPGLLocalCover.N F ζ hζ (Sum.inr q) x :=
    (S.openCell P).upper_eq x
  have hr : retractL F ζ hζ q S P b = 1 := by
    apply Subtype.ext
    change S.borel.retract (inBorel F ζ hζ q S P b) = 1
    have hb : inBorel F ζ hζ q S P b = n := rfl
    rw [hb, S.borel.retract_upperRoot]
  have hc : chi F ζ hζ q S P hP ε b = 1 := by
    unfold chi
    rw [hr]
    cases ε <;> simp [chiH, normPower, localAbs, residueCardinality]
  rw [← he, f.property.1, hc, one_mul]

private theorem scalar_borel_root_invariant
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (f : scalarSections F ζ hζ q S P hP ε)
    (x : LocalField F q) (b : S.borel.B) :
    f.val (b.val * KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) = f.val b.val := by
  obtain ⟨s, hs⟩ := S.borel.borel_decomposition b
  let h := S.borel.retract b
  have ht := KPJacquetOpenCellSections.torus_conjugates_upperRoot_ratio F ζ hζ q
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q) h x
  have he : (S.borel.torus h : ActualCover F ζ hζ q) = h.val := S.torus_full h
  have hn : (S.borel.upperRoot s : ActualCover F ζ hζ q) =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) (Multiplicative.toAdd s) :=
    (S.openCell P).upper_eq _
  have hcomm : (S.borel.upperRoot s : ActualCover F ζ hζ q) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) x =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) x * (S.borel.upperRoot s : ActualCover F ζ hζ q) := by
    rw [hn, ← KPPGLLocalCover.N_add, ← KPPGLLocalCover.N_add, add_comm]
  have hb : b.val = h.val * (S.borel.upperRoot s : ActualCover F ζ hζ q) := by
    exact congrArg Subtype.val hs |>.trans (by
      change (S.borel.torus h : ActualCover F ζ hζ q) * _ = _
      rw [he])
  change h.val * KPPGLLocalCover.N F ζ hζ (Sum.inr q) x * h.val⁻¹ =
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) _ at ht
  have ht' := congrArg (fun g : ActualCover F ζ hζ q => g * h.val) ht
  simp only [mul_assoc, inv_mul_cancel, mul_one] at ht'
  rw [hb, mul_assoc, hcomm, ← mul_assoc, ht', mul_assoc]
  exact scalar_root_invariant F ζ hζ q S P hP ε f _ _

theorem scalar_tail_translation
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) (u : (LocalField F q)ˣ)
    (f : scalarSections F ζ hζ q S P hP ε) (t : LocalField F q) :
    ∃ R : ℕ, ∀ x : LocalField F q, x ∉ expandingBall F q π R →
      f.val (KPPGLLocalCover.A F ζ hζ (Sum.inr q) u *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) (x + t)) =
      f.val (KPPGLLocalCover.A F ζ hζ (Sum.inr q) u *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) := by
  classical
  let d := scalarAction F ζ hζ q S P hP ε
    (KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) f - f
  obtain ⟨J, hJ⟩ := d.property.2
  have hd (b : S.borel.B) : d.val b.val = 0 := by
    change f.val (b.val * KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) - f.val b.val = 0
    rw [scalar_borel_root_invariant F ζ hζ q S P hP ε f, sub_self]
  have hL := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.1
  have hn : {y : LocalField F q |
      KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) y ∈ J} ∈ nhds 0 := by
    apply hL.continuousAt.preimage_mem_nhds
    have hz : KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) 0 = 1 :=
      (KPLocalSmoothRepresentation.lowerRoot F ζ hζ q).map_one
    rw [hz]
    exact J.isOpen.mem_nhds J.one_mem
  obtain ⟨e, he, heJ⟩ := Metric.mem_nhds_iff.mp hn
  have hlarge : ∀ x : LocalField F q, e⁻¹ < ‖x‖ →
      d.val (KPPGLLocalCover.A F ζ hζ (Sum.inr q) u *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      simp [h] at hx
      linarith [inv_pos.mpr he]
    have hxi : ‖x⁻¹‖ < e := by
      rw [norm_inv]
      exact (inv_lt_comm₀ (norm_pos_iff.mpr hx0) he).mpr hx
    let g := KPPGLLocalCover.A F ζ hζ (Sum.inr q) u *
      KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) x
    let A := KubotaRankTwo.d (LocalField F q) u 1 *
      KPStandardLocalRootLifts.weylSwap (LocalField F q) *
      KubotaRankTwo.n (LocalField F q) x
    have hA : Matrix.ProjGenLinGroup.mk A =
        KPLocalSmoothRepresentation.projection F ζ hζ q g := by
      change Matrix.ProjGenLinGroup.mk (_ * _ * _) = _
      simp only [map_mul]
      rfl
    have hdelta : g ∈ KPJacquetBruhatCharts.delta F ζ hζ q := by
      refine ⟨A, hA, ?_⟩
      simpa [A, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.n,
        Matrix.GeneralLinearGroup.mkOfDetNeZero] using hx0
    have hc : KPJacquetBruhatCharts.deltaCoordinate F ζ hζ q ⟨g, hdelta⟩ = x⁻¹ := by
      rw [KPJacquetBruhatCharts.deltaCoordinate_eq F ζ hζ q _ A hA]
      simp [A, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        KPStandardLocalRootLifts.weylSwap, KubotaRankTwo.n,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, one_div]
    let b := (KPJacquetBruhatCharts.deltaInverse F ζ hζ q ⟨g, hdelta⟩).1
    have hb : b.val * KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) x⁻¹ = g := by
      change (g * (KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q)
        (KPJacquetBruhatCharts.deltaCoordinate F ζ hζ q ⟨g, hdelta⟩))⁻¹) * _ = g
      rw [hc, inv_mul_cancel_right]
    have hj := hJ (KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) x⁻¹)
      (heJ (by simpa only [Metric.mem_ball, dist_zero_right] using hxi))
    have hv := congrFun hj b.val
    change d.val (b.val * KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) x⁻¹) = d.val b.val at hv
    rw [hb] at hv
    exact hv.trans (hd ⟨b.val, S.borel_eq.symm ▸ b.property⟩)
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  have hp : ‖(π : LocalField F q)‖ < 1 := by
    have hh := not_le.mpr hv
    rw [← map_one (valuation (LocalField F q)), ← Valuation.Compatible.vle_iff_le] at hh
    change ¬ Valued.v (1 : LocalField F q) ≤ Valued.v (π : LocalField F q) at hh
    rw [← Valued.toNormedField.norm_le_iff] at hh
    simpa using not_le.mp hh
  have hp0 : 0 < ‖(π : LocalField F q)‖ := norm_pos_iff.mpr π.ne_zero
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hp0 |>.mpr hp)).eventually
      (Filter.eventually_ge_atTop e⁻¹))
  refine ⟨R, ?_⟩
  intro x hx
  have hnorm : ‖(π : LocalField F q)‖⁻¹ ^ R < ‖x‖ := by
    by_contra h
    apply hx
    let a : LocalField F q := ((π ^ R : (LocalField F q)ˣ) : LocalField F q)⁻¹
    have ha : a ≠ 0 := inv_ne_zero (π ^ R).ne_zero
    have hn : ‖a‖ = ‖(π : LocalField F q)‖⁻¹ ^ R := by
      simp [a, norm_inv, norm_pow, inv_pow]
    refine ⟨⟨x / a, ?_⟩, (mul_div_cancel₀ x ha).symm⟩
    rw [Valuation.mem_integer_iff, ← map_one (valuation (LocalField F q)),
      ← Valuation.Compatible.vle_iff_le]
    change Valued.v (x / a) ≤ Valued.v (1 : LocalField F q)
    rw [← Valued.toNormedField.norm_le_iff, norm_one, norm_div,
      div_le_one (norm_pos_iff.mpr ha), hn]
    exact not_lt.mp h
  have hz := hlarge x ((hR R le_rfl).trans_lt hnorm)
  change f.val ((_ * _ * KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) - f.val _ = 0 at hz
  rw [mul_assoc, ← KPPGLLocalCover.N_add] at hz
  exact sub_eq_zero.mp hz

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.Stabilization

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.Stabilization
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries Raw

variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

private theorem valuation_norm_le (x y : LocalField F q) :
    valuation (LocalField F q) x ≤ valuation (LocalField F q) y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v y ↔ _
  exact (Valued.toNormedField.norm_le_iff).symm

private theorem expandingBall_norm (π : (LocalField F q)ˣ) (r : ℕ) (x : LocalField F q) :
    x ∈ expandingBall F q π r ↔ ‖x‖ ≤ ‖(π : LocalField F q)‖⁻¹ ^ r := by
  let a : LocalField F q := ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (π ^ r).ne_zero
  have hn : ‖a‖ = ‖(π : LocalField F q)‖⁻¹ ^ r := by
    simp [a, norm_inv, norm_pow, inv_pow]
  have hm : ∀ y : LocalField F q, y ∈ (valuation (LocalField F q)).integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← map_one (valuation (LocalField F q)), valuation_norm_le]
    simp
  change (∃ u : (valuation (LocalField F q)).integer, x = a * (u : LocalField F q)) ↔ _
  rw [← hn]
  constructor
  · rintro ⟨u, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((hm _).mp u.property)
  · intro hx
    refine ⟨⟨x / a, (hm _).mpr ?_⟩, (mul_div_cancel₀ x ha).symm⟩
    rw [norm_div, div_le_one (norm_pos_iff.mpr ha)]
    exact hx

private theorem eventually_mem_ball (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (t : LocalField F q) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, t ∈ expandingBall F q π r := by
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  have hn : ‖(π : LocalField F q)‖ < 1 := by
    have hh := not_le.mpr hv
    rw [← map_one (valuation (LocalField F q)), valuation_norm_le] at hh
    simpa using not_le.mp hh
  have hp : 0 < ‖(π : LocalField F q)‖ := norm_pos_iff.mpr π.ne_zero
  have ht := tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hp |>.mpr hn)
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop ‖t‖))
  exact ⟨r₀, fun r hr => (expandingBall_norm F q π r t).mpr (hr₀ r hr)⟩

private theorem ball_translate (π : (LocalField F q)ˣ) (r : ℕ)
    (t : LocalField F q) (ht : t ∈ expandingBall F q π r) :
    (fun x => x + t) ⁻¹' expandingBall F q π r = expandingBall F q π r := by
  ext x
  simp only [Set.mem_preimage, expandingBall_norm] at *
  constructor
  · intro hx
    have h := IsUltrametricDist.norm_add_le_max (x + t) (-t)
    simpa using h.trans (max_le hx (by simpa using ht))
  · intro hx
    exact (IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht)

theorem shell_vanishing_of_tail_translation
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hconductor : HasConductorIntegers F q ψ)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (φ : LocalField F q → ℂ)
    (hint : ∀ r : ℕ,
      IntegrableOn (fun x => φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ))
        (expandingBall F q π r) μ)
    (htail : ∀ t : LocalField F q, ∃ R : ℕ,
      ∀ x : LocalField F q, x ∉ expandingBall F q π R → φ (x + t) = φ x) :
    ∃ R : ℕ, ∀ r ≥ R,
      (∫ x in expandingBall F q π (r + 1) \ expandingBall F q π r,
        φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ) ∂μ) = 0 := by
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  have hni : (π : LocalField F q)⁻¹ ∉ (valuation (LocalField F q)).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact not_le.mpr (one_lt_inv₀ ((Valuation.pos_iff (valuation (LocalField F q))).mpr π.ne_zero) |>.mpr hv)
  have hw := mt (hconductor ((π : LocalField F q)⁻¹)).mp hni
  push Not at hw
  obtain ⟨o, ho⟩ := hw
  let t : LocalField F q := -((o : LocalField F q) * (π : LocalField F q)⁻¹)
  have hc : (ψ (Multiplicative.ofAdd (-t)) : ℂ) ≠ 1 := by
    intro h
    apply ho
    apply Units.ext
    simpa [t] using h
  obtain ⟨R, hR⟩ := htail t
  obtain ⟨T, hT⟩ := eventually_mem_ball F q π hπ t
  have hn : 1 ≤ ‖(π : LocalField F q)‖⁻¹ := by
    have hh := not_le.mpr hv
    rw [← map_one (valuation (LocalField F q)), valuation_norm_le] at hh
    have hp : 0 < ‖(π : LocalField F q)‖ := norm_pos_iff.mpr π.ne_zero
    exact le_of_lt (one_lt_inv₀ hp |>.mpr (by simpa using not_le.mp hh))
  have hmeas : ∀ r, MeasurableSet (expandingBall F q π r) := by
    intro r
    have hset : expandingBall F q π r =
        (fun x : LocalField F q => ‖x‖) ⁻¹' Set.Iic (‖(π : LocalField F q)‖⁻¹ ^ r) := by
      ext x
      exact expandingBall_norm F q π r x
    rw [hset]
    exact measurableSet_Iic.preimage (by fun_prop)
  refine ⟨max R T, ?_⟩
  intro r hr
  have hRr : R ≤ r := (le_max_left _ _).trans hr
  have hTr : T ≤ r := (le_max_right _ _).trans hr
  have hsub : expandingBall F q π R ⊆ expandingBall F q π r := by
    intro x hx
    rw [expandingBall_norm] at hx ⊢
    exact hx.trans (pow_le_pow_right₀ hn hRr)
  let shell := expandingBall F q π (r + 1) \ expandingBall F q π r
  let g := fun x : LocalField F q => φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ)
  have hs : (fun x => x + t) ⁻¹' shell = shell := by
    dsimp [shell]
    rw [ball_translate F q π (r + 1) t (hT _ (by omega)),
      ball_translate F q π r t (hT _ hTr)]
  have he : ∀ x ∈ shell, g (x + t) = (ψ (Multiplicative.ofAdd (-t)) : ℂ) * g x := by
    intro x hx
    have hφ := hR x (fun h => hx.2 (hsub h))
    have hψ : (ψ (Multiplicative.ofAdd (-(x+t))) : ℂ) =
        (ψ (Multiplicative.ofAdd (-x)) : ℂ) * (ψ (Multiplicative.ofAdd (-t)) : ℂ) := by
      rw [← Units.val_mul, ← map_mul]
      congr 2
      change -(x+t) = -x + -t
      abel
    change φ (x+t) * (ψ (Multiplicative.ofAdd (-(x+t))) : ℂ) = _
    rw [hφ, hψ]
    change _ = (ψ (Multiplicative.ofAdd (-t)) : ℂ) * (φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ))
    ring
  have hp := measurePreserving_add_right μ t
  have hm := (Homeomorph.addRight t : LocalField F q ≃ₜ LocalField F q).measurableEmbedding
  have hi := hp.setIntegral_preimage_emb hm g shell
  rw [hs] at hi
  have heq : (∫ x in shell, g (x + t) ∂μ) =
      (ψ (Multiplicative.ofAdd (-t)) : ℂ) * (∫ x in shell, g x ∂μ) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun ((hmeas _).diff (hmeas _)) he
  have hz : ((ψ (Multiplicative.ofAdd (-t)) : ℂ) - 1) *
      (∫ x in shell, g x ∂μ) = 0 := by
    rw [sub_mul, one_mul, ← heq, hi, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.Stabilization

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests.Stabilization
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries Raw

private theorem pi_mem_integer
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    (π : LocalField F q) ∈ (valuation (LocalField F q)).integer := by
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  exact (Valuation.mem_integer_iff (valuation (LocalField F q)) (π : LocalField F q)).mpr
    (le_of_lt hv)

private theorem ball_subset_succ
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (r : ℕ) : expandingBall F q π r ⊆ expandingBall F q π (r + 1) := by
  have hπO := pi_mem_integer F q π hπ
  rintro x ⟨o, rfl⟩
  refine ⟨⟨(π : LocalField F q) * (o : LocalField F q),
    (valuation (LocalField F q)).integer.mul_mem hπO o.2⟩, ?_⟩
  have hval : ((π ^ (r + 1) : (LocalField F q)ˣ) : LocalField F q) =
      ((π ^ r : (LocalField F q)ˣ) : LocalField F q) * (π : LocalField F q) := by
    rw [pow_succ, Units.val_mul]
  rw [hval]
  field_simp

private theorem ball_measurable
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ) (r : ℕ) :
    MeasurableSet (expandingBall F q π r) := by
  have hset : expandingBall F q π r =
      (fun x : LocalField F q =>
        ((π ^ r : (LocalField F q)ˣ) : LocalField F q) * x) ⁻¹' (𝒪[LocalField F q]) := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      simp only [Set.mem_preimage]
      have : ((π ^ r : (LocalField F q)ˣ) : LocalField F q) *
          (((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹ * (o : LocalField F q)) =
          (o : LocalField F q) := by
        field_simp
      rw [this]
      exact o.2
    · intro hx
      exact ⟨⟨_, hx⟩, by field_simp⟩
  rw [hset]
  exact MeasurableSet.preimage (valuation (LocalField F q)).isOpen_integer.measurableSet
    (measurable_const.mul measurable_id)

theorem integrals_stabilize_of_shell_vanishing
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (μ : Measure (LocalField F q)) (g : LocalField F q → ℂ)
    (hint : ∀ r : ℕ, IntegrableOn g (expandingBall F q π r) μ)
    (hvan : ∃ R : ℕ, ∀ r ≥ R,
      (∫ x in expandingBall F q π (r + 1) \ expandingBall F q π r, g x ∂μ) = 0) :
    ∃ z : ℂ, ∃ R : ℕ, ∀ r ≥ R,
      IntegrableOn g (expandingBall F q π r) μ ∧
      (∫ x in expandingBall F q π r, g x ∂μ) = z := by
  obtain ⟨R, hR⟩ := hvan
  refine ⟨∫ x in expandingBall F q π R, g x ∂μ, R, ?_⟩

  have key : ∀ k : ℕ,
      (∫ x in expandingBall F q π (R + k), g x ∂μ) =
        ∫ x in expandingBall F q π R, g x ∂μ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsd := setIntegral_sdiff (ball_measurable F q π (R + k))
        (hint (R + k + 1)) (ball_subset_succ F q π hπ (R + k))
      have hz : (∫ x in expandingBall F q π (R + k + 1) \ expandingBall F q π (R + k),
          g x ∂μ) = 0 := hR (R + k) (Nat.le_add_right R k)
      rw [hz] at hsd
      have heq : (∫ x in expandingBall F q π (R + k + 1), g x ∂μ) =
          ∫ x in expandingBall F q π (R + k), g x ∂μ := sub_eq_zero.mp hsd.symm
      rw [Nat.add_succ, heq, ih]
  intro r hr
  refine ⟨hint r, ?_⟩
  rw [← Nat.add_sub_of_le hr]
  exact key (r - R)

end DedekindZetaZeroFree.KPTameJacquetBruhatTests.Stabilization

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameJacquetBruhatTests
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open Raw
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

private theorem stable_unique
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) {z z' : ℂ}
    (hz : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z)
    (hz' : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z') : z = z' := by
  obtain ⟨r, hr⟩ := hz
  obtain ⟨r', hr'⟩ := hz'
  exact (hr (max r r') (le_max_left _ _)).2.symm.trans
    (hr' (max r r') (le_max_right _ _)).2

private theorem stable_add
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (a : ActualCover F ζ hζ q)
    (f g : scalarSections F ζ hζ q S P hP ε) (z z' : ℂ)
    (hf : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z)
    (hg : HasStableValue F ζ hζ q S P hP ε π ψ μ a g z') :
    HasStableValue F ζ hζ q S P hP ε π ψ μ a (f + g) (z + z') := by
  have he : jacquetIntegrand F ζ hζ q S P hP ε ψ a (f + g) =
      jacquetIntegrand F ζ hζ q S P hP ε ψ a f +
        jacquetIntegrand F ζ hζ q S P hP ε ψ a g := by
    funext x
    simp [jacquetIntegrand.eq_1, add_mul]
  obtain ⟨r₀, hr⟩ := hf
  obtain ⟨s₀, hs⟩ := hg
  refine ⟨max r₀ s₀, ?_⟩
  intro r hrr
  obtain ⟨hfi, hfv⟩ := hr r ((le_max_left _ _).trans hrr)
  obtain ⟨hgi, hgv⟩ := hs r ((le_max_right _ _).trans hrr)
  rw [he]
  exact ⟨hfi.add hgi, by simp only [Pi.add_apply]; rw [integral_add hfi hgi, hfv, hgv]⟩

private theorem stable_smul
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) (z c : ℂ)
    (hf : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z) :
    HasStableValue F ζ hζ q S P hP ε π ψ μ a (c • f) (c * z) := by
  have he : jacquetIntegrand F ζ hζ q S P hP ε ψ a (c • f) =
      fun x => c * jacquetIntegrand F ζ hζ q S P hP ε ψ a f x := by
    funext x
    simp [jacquetIntegrand.eq_1, mul_assoc]
  obtain ⟨r₀, hr⟩ := hf
  refine ⟨r₀, ?_⟩
  intro r hrr
  obtain ⟨hint, hval⟩ := hr r hrr
  rw [he]
  exact ⟨hint.const_mul _, by rw [integral_const_mul, hval]⟩

private theorem valuation_norm_le (x y : LocalField F q) :
    valuation (LocalField F q) x ≤ valuation (LocalField F q) y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← Valuation.Compatible.vle_iff_le]
  change Valued.v x ≤ Valued.v y ↔ _
  exact (Valued.toNormedField.norm_le_iff).symm

private theorem expandingBall_norm (π : (LocalField F q)ˣ) (r : ℕ) (x : LocalField F q) :
    x ∈ expandingBall F q π r ↔ ‖x‖ ≤ ‖(π : LocalField F q)‖⁻¹ ^ r := by
  let a : LocalField F q := ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (π ^ r).ne_zero
  have hn : ‖a‖ = ‖(π : LocalField F q)‖⁻¹ ^ r := by
    simp [a, norm_inv, norm_pow, inv_pow]
  have hm : ∀ y : LocalField F q, y ∈ (valuation (LocalField F q)).integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← map_one (valuation (LocalField F q)), valuation_norm_le]
    simp
  change (∃ u : (valuation (LocalField F q)).integer, x = a * (u : LocalField F q)) ↔ _
  rw [← hn]
  constructor
  · rintro ⟨u, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((hm _).mp u.property)
  · intro hx
    refine ⟨⟨x / a, (hm _).mpr ?_⟩, (mul_div_cancel₀ x ha).symm⟩
    rw [norm_div, div_le_one (norm_pos_iff.mpr ha)]
    exact hx

private theorem eventually_mem_ball (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (t : LocalField F q) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, t ∈ expandingBall F q π r := by
  have hv : valuation (LocalField F q) (π : LocalField F q) < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [hπ, map_one]
    norm_num
  have hn : ‖(π : LocalField F q)‖ < 1 := by
    have hh := not_le.mpr hv
    rw [← map_one (valuation (LocalField F q)), valuation_norm_le] at hh
    simpa using not_le.mp hh
  have hp : 0 < ‖(π : LocalField F q)‖ := norm_pos_iff.mpr π.ne_zero
  have ht := tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hp |>.mpr hn)
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop ‖t‖))
  exact ⟨r₀, fun r hr => (expandingBall_norm F q π r t).mpr (hr₀ r hr)⟩

private theorem ball_translate (π : (LocalField F q)ˣ) (r : ℕ)
    (t : LocalField F q) (ht : t ∈ expandingBall F q π r) :
    (fun x => x + t) ⁻¹' expandingBall F q π r = expandingBall F q π r := by
  ext x
  simp only [Set.mem_preimage, expandingBall_norm] at *
  constructor
  · intro hx
    have h := IsUltrametricDist.norm_add_le_max (x + t) (-t)
    simpa using h.trans (max_le hx (by simpa using ht))
  · intro hx
    exact (IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht)

private theorem integrand_root
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (a : ActualCover F ζ hζ q)
    (f : scalarSections F ζ hζ q S P hP ε) (t x : LocalField F q) :
    jacquetIntegrand F ζ hζ q S P hP ε ψ a
      (scalarAction F ζ hζ q S P hP ε
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ q (Multiplicative.ofAdd t)) f) x =
    (ψ (Multiplicative.ofAdd t) : ℂ) *
      jacquetIntegrand F ζ hζ q S P hP ε ψ a f (x + t) := by
  change f.val ((a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) *
    (ψ (Multiplicative.ofAdd (-x)) : ℂ) = _
  rw [mul_assoc, ← KPPGLLocalCover.N_add]
  have he : (ψ (Multiplicative.ofAdd (-x)) : ℂ) =
      (ψ (Multiplicative.ofAdd t) : ℂ) * (ψ (Multiplicative.ofAdd (-(x+t))) : ℂ) := by
    rw [← Units.val_mul, ← map_mul]
    congr 2
    change -x = t + -(x+t)
    abel
  rw [he]
  simp only [jacquetIntegrand.eq_1]
  ring

private theorem stable_root
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (a : ActualCover F ζ hζ q) (f : scalarSections F ζ hζ q S P hP ε)
    (t : Multiplicative (LocalField F q)) (z : ℂ)
    (hz : HasStableValue F ζ hζ q S P hP ε π ψ μ a f z) :
    HasStableValue F ζ hζ q S P hP ε π ψ μ a
      (scalarAction F ζ hζ q S P hP ε (KPLocalSmoothRepresentation.upperRoot F ζ hζ q t) f)
      ((ψ t : ℂ) * z) := by
  obtain ⟨r₀, hr₀⟩ := hz
  obtain ⟨s₀, hs₀⟩ := eventually_mem_ball F q π hπ (Multiplicative.toAdd t)
  refine ⟨max r₀ s₀, ?_⟩
  intro r hr
  obtain ⟨hfi, hfv⟩ := hr₀ r ((le_max_left _ _).trans hr)
  have hball := ball_translate F q π r (Multiplicative.toAdd t) (hs₀ r ((le_max_right _ _).trans hr))
  have he : jacquetIntegrand F ζ hζ q S P hP ε ψ a
      (scalarAction F ζ hζ q S P hP ε (KPLocalSmoothRepresentation.upperRoot F ζ hζ q t) f) =
      fun x => (ψ t : ℂ) * jacquetIntegrand F ζ hζ q S P hP ε ψ a f (x + Multiplicative.toAdd t) := by
    funext x
    exact integrand_root F ζ hζ q S P hP ε ψ a f (Multiplicative.toAdd t) x
  have hp := measurePreserving_add_right μ (Multiplicative.toAdd t)
  have hm := (Homeomorph.addRight (Multiplicative.toAdd t) : LocalField F q ≃ₜ LocalField F q).measurableEmbedding
  have hi := (hp.integrableOn_comp_preimage hm).mpr hfi
  have hv := hp.setIntegral_preimage_emb hm (jacquetIntegrand F ζ hζ q S P hP ε ψ a f) (expandingBall F q π r)
  rw [hball] at hi hv
  rw [he]
  exact ⟨hi.const_mul _, by rw [integral_const_mul, hv, hfv]⟩

private theorem family_of_stable_values
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ) (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (μ : Measure (LocalField F q))
    (hex : ∀ j f, ∃ z, HasStableValue F ζ hζ q S P hP ε π ψ μ
      (eta F ζ hζ q π j) f z)
    (hroot : ∀ j t f z,
      HasStableValue F ζ hζ q S P hP ε π ψ μ (eta F ζ hζ q π j) f z →
      HasStableValue F ζ hζ q S P hP ε π ψ μ (eta F ζ hζ q π j)
        (scalarAction F ζ hζ q S P hP ε (KPLocalSmoothRepresentation.upperRoot F ζ hζ q t) f)
        ((ψ t : ℂ) * z)) :
    ∃ L : Fin 3 → whittakerSpace F ζ hζ q S P hP ε ψ,
      ∀ j f, HasStableValue F ζ hζ q S P hP ε π ψ μ
        (eta F ζ hζ q π j) f ((L j).val f) := by
  classical
  let value := fun j f => (hex j f).choose
  have hv : ∀ j f, HasStableValue F ζ hζ q S P hP ε π ψ μ
      (eta F ζ hζ q π j) f (value j f) := fun j f => (hex j f).choose_spec
  let lm : Fin 3 → scalarSections F ζ hζ q S P hP ε →ₗ[ℂ] ℂ := fun j =>
    { toFun := value j
      map_add' := fun f g => stable_unique F ζ hζ q S P hP ε π ψ μ _ _
        (hv j (f + g)) (stable_add F ζ hζ q S P hP ε π ψ μ _ f g _ _ (hv j f) (hv j g))
      map_smul' := fun c f => stable_unique F ζ hζ q S P hP ε π ψ μ _ _
        (hv j (c • f)) (stable_smul F ζ hζ q S P hP ε π ψ μ _ f _ c (hv j f)) }
  refine ⟨fun j => ⟨lm j, ?_⟩, hv⟩
  intro t f
  exact stable_unique F ζ hζ q S P hP ε π ψ μ _ _
    (hv j _) (hroot j t f _ (hv j f))

theorem scalar_section_continuous
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (f : scalarSections F ζ hζ q S P hP ε) : Continuous f.val := by
  obtain ⟨J, hJ⟩ := f.property.2
  have hf : IsLocallyConstant f.val := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ J},
      J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simpa using J.one_mem
    · intro x hx
      have he := congrFun (hJ (g⁻¹ * x) hx) g
      simpa only [rightTranslationRepresentation_apply, mul_inv_cancel_left] using he
  exact hf.continuous

theorem expanding_ball_compact (π : (LocalField F q)ˣ) (r : ℕ) :
    IsCompact (expandingBall F q π r) := by
  let a : LocalField F q := ((π ^ r : (LocalField F q)ˣ) : LocalField F q)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (π ^ r).ne_zero
  have he : expandingBall F q π r =
      {x | valuation (LocalField F q) x ≤ valuation (LocalField F q) a} := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      change valuation (LocalField F q) (a * o) ≤ valuation (LocalField F q) a
      rw [map_mul]
      exact mul_le_of_le_one_right (show 0 ≤ valuation (LocalField F q) a from bot_le)
        o.property
    · intro hx
      have ho : valuation (LocalField F q) (a⁻¹ * x) ≤ 1 := by
        rw [map_mul, map_inv₀]
        exact (inv_mul_le_one₀ ((valuation (LocalField F q)).pos_iff.mpr ha)).mpr hx
      exact ⟨⟨a⁻¹ * x, ho⟩, by dsimp [a]; simp [ha]⟩
  rw [he]
  exact IsNonarchimedeanLocalField.isCompact_closedBall _ _

theorem jacquet_integrable_on_expanding_ball
    (hP : IsTamePolarization F ζ hζ q S P) (ε : Sign)
    (π : (LocalField F q)ˣ)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ) (hψ : Continuous ψ)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (a : ActualCover F ζ hζ q) (f : scalarSections F ζ hζ q S P hP ε) (r : ℕ) :
    IntegrableOn (jacquetIntegrand F ζ hζ q S P hP ε ψ a f)
      (expandingBall F q π r) μ := by
  have hN : Continuous (KPPGLLocalCover.N F ζ hζ (Sum.inr q)) :=
    (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
  have hf : Continuous (fun x : LocalField F q =>
      f.val (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) :=
    (scalar_section_continuous F ζ hζ q S P hP ε f).comp
      (continuous_const.mul hN)
  have hc : Continuous (fun x : LocalField F q =>
      (ψ (Multiplicative.ofAdd (-x)) : ℂ)) :=
    Units.continuous_val.comp (hψ.comp (continuous_ofAdd.comp continuous_neg))
  exact (hf.mul hc).continuousOn.integrableOn_compact (expanding_ball_compact F q π r)

theorem stable_whittaker_family
    (hP : IsTamePolarization F ζ hζ q S P)
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (hψ : Continuous ψ) (hunitary : ∀ x, ‖(ψ x : ℂ)‖ = 1)
    (hconductor : HasConductorIntegers F q ψ)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (ε : Sign) :
    ∃ L : Fin 3 → whittakerSpace F ζ hζ q S P hP ε ψ,
      ∀ j f, HasStableValue F ζ hζ q S P hP ε π ψ μ
        (eta F ζ hζ q π j) f ((L j).val f) := by
  apply family_of_stable_values F ζ hζ q S P hP ε π ψ μ
  · intro j f
    have hint := jacquet_integrable_on_expanding_ball F ζ hζ q S P hP ε π ψ hψ μ
      (eta F ζ hζ q π j) f
    have htail := Stabilization.scalar_tail_translation F ζ hζ q S P hP htame
      π hπ ε (π ^ j.val) f
    have hvan := Stabilization.shell_vanishing_of_tail_translation F q π hπ ψ
      hconductor μ
      (fun x => f.val (eta F ζ hζ q π j * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) hint htail
    exact Stabilization.integrals_stabilize_of_shell_vanishing F q π hπ μ
      (jacquetIntegrand F ζ hζ q S P hP ε ψ (eta F ζ hζ q π j) f) hint hvan
  · intro j t f z hz
    exact stable_root F ζ hζ q S P hP ε π hπ ψ μ _ f t z hz

end DedekindZetaZeroFree.KPTameJacquetBruhatTests

end

end
