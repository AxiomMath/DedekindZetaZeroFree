module

public import DedekindZetaZeroFree.Analysis.IsolatedSpectralProjections
public import DedekindZetaZeroFree.Analysis.SpectralTheory.ExteriorCoercivity.BelowThresholdDiscreteness
public import DedekindZetaZeroFree.Analysis.OperatorTheory.Resolvents.ShiftedPencilHolomorphy

@[expose] public section

namespace DedekindZetaZeroFree

theorem realSpectrum_mem_iff_resolventSet
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hDense : Dense (Δ.domain : Set H))
    (B : H →L[ℂ] H) (hbase : KPResolventPencil.GenuineInverse Δ (-1) B) (μ : ℝ) :
    (μ ∈ KPBelowThreshold.realSpectrum B ↔ (μ : ℂ) ∉ KPResolventPencil.resolventSet Δ) := by
  rw [KPBelowThreshold.realSpectrum]
  simp only [Set.mem_setOf_eq]
  rw [← KPResolventPencil.isUnit_shiftedPencil_iff Δ hDense B hbase (μ : ℂ)]
  rw [not_iff_not]
  congr 1
  rw [KPResolventPencil.shiftedPencil]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  norm_num

theorem spectrum_iff_pencil
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (μ : ℝ) (hμ : 0 ≤ μ) :
    (((1 + μ)⁻¹ : ℝ) : ℂ) ∈ spectrum ℂ B ↔ ¬ IsUnit (1 - (μ + 1) • B) := by
  have hne : ((1 + μ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have hc : (((1 + μ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact inv_ne_zero (by positivity)
  have hinv : ((((1 + μ)⁻¹ : ℝ) : ℂ))⁻¹ = ((1 + μ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, inv_inv]
  have h1 : ((Units.mk0 (((1 + μ)⁻¹ : ℝ) : ℂ) hc) • (1 : H →L[ℂ] H))
      = algebraMap ℂ (H →L[ℂ] H) (((1 + μ)⁻¹ : ℝ) : ℂ) := by
    rw [Units.smul_def, Units.val_mk0, Algebra.algebraMap_eq_smul_one]
  have h2 : ((Units.mk0 (((1 + μ)⁻¹ : ℝ) : ℂ) hc)⁻¹ • B)
      = ((1 + μ : ℝ) : ℂ) • B := by
    rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, hinv]
  rw [spectrum.mem_iff, not_iff_not, ← h1]
  rw [IsUnit.smul_sub_iff_sub_inv_smul (Units.mk0 _ hc) B, h2]
  have heq : (1 - ((1 + μ : ℝ) : ℂ) • B : H →L[ℂ] H) = 1 - (μ + 1) • B := by
    congr 1
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    congr 1
    push_cast
    rw [add_comm]
    rfl
  rw [heq]

theorem spectrum_mem_iff_resolventSet
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hDense : Dense (Δ.domain : Set H))
    (B : H →L[ℂ] H) (hbase : KPResolventPencil.GenuineInverse Δ (-1) B)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    (((1 + μ)⁻¹ : ℝ) : ℂ) ∈ spectrum ℂ B ↔
      (μ : ℂ) ∉ KPResolventPencil.resolventSet Δ := by
  rw [spectrum_iff_pencil B μ hμ]
  rw [← realSpectrum_mem_iff_resolventSet Δ hDense B hbase μ]
  exact Iff.rfl

theorem eigenspace_transfer
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hDense : Dense (Δ.domain : Set H))
    (B : H →L[ℂ] H) (hbase : KPResolventPencil.GenuineInverse Δ (-1) B)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    KPBelowThreshold.eigenspace Δ μ =
      KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹) := by
  obtain ⟨hR, hleft0, hright0⟩ := hbase
  have hright : ∀ v : Δ.domain, B (Δ v + (v : H)) = (v : H) := by
    intro v
    have h := hright0 v
    rwa [neg_smul, one_smul, sub_neg_eq_add] at h
  have hleft : ∀ u : H, Δ ⟨B u, hR u⟩ + B u = u := by
    intro u
    have h := hleft0 u
    rwa [neg_smul, one_smul, sub_neg_eq_add] at h
  have hcinv : (((1 + μ : ℝ) : ℂ))⁻¹ = (((1 + μ)⁻¹ : ℝ) : ℂ) :=
    (Complex.ofReal_inv (1 + μ)).symm
  have hβc : (((1 + μ)⁻¹ : ℝ) : ℂ) * ((1 + μ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
  have hcβ : ((1 + μ : ℝ) : ℂ) * (((1 + μ)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [mul_comm, hβc]
  have hμc : ((1 + μ : ℝ) : ℂ) - 1 = (μ : ℂ) := by push_cast; ring
  have hs : ∀ (a : ℂ) (y : H), a • y - y = (a - 1) • y := by
    intro a y; rw [sub_smul, one_smul]
  ext x
  constructor
  · intro hx
    rw [KPBelowThreshold.eigenspace, Submodule.mem_map] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    rw [LinearMap.mem_ker] at hv
    have hv' : Δ v = (μ : ℂ) • (v : H) := sub_eq_zero.mp hv
    change (B - (((1 + μ)⁻¹ : ℝ) : ℂ) • (1 : H →L[ℂ] H)) x = 0
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero]
    have hstep : Δ v + (v : H) = ((1 + μ : ℝ) : ℂ) • (v : H) := by
      rw [hv', Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul, add_comm]
    have hB : B (((1 + μ : ℝ) : ℂ) • (v : H)) = (v : H) := by
      rw [← hstep]; exact hright v
    rw [map_smul] at hB
    have h2 := congrArg (fun y => (((1 + μ : ℝ) : ℂ))⁻¹ • y) hB
    rw [smul_smul, hcinv, hβc, one_smul] at h2
    rw [← hvx]
    exact h2
  · intro hx
    rw [KPIsolatedProjection.eigenspace] at hx
    change (B - (((1 + μ)⁻¹ : ℝ) : ℂ) • (1 : H →L[ℂ] H)) x = 0 at hx
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at hx
    rw [KPBelowThreshold.eigenspace, Submodule.mem_map]
    have hx1 : x = ((1 + μ : ℝ) : ℂ) • B x := by
      rw [hx, smul_smul, hcβ, one_smul]
    have hxdom : x ∈ Δ.domain := by
      rw [hx1]; exact Δ.domain.smul_mem _ (hR x)
    refine ⟨⟨x, hxdom⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker]
    show Δ ⟨x, hxdom⟩ - (μ : ℂ) • x = 0
    have hdom : (⟨x, hxdom⟩ : Δ.domain) = ((1 + μ : ℝ) : ℂ) • ⟨B x, hR x⟩ := by
      ext
      simp only [Submodule.coe_smul]
      exact hx1
    have hDx : Δ ⟨x, hxdom⟩ = ((1 + μ : ℝ) : ℂ) • Δ ⟨B x, hR x⟩ := by
      rw [hdom]; exact map_smul Δ.toFun ((1 + μ : ℝ) : ℂ) ⟨B x, hR x⟩
    have hl : Δ ⟨B x, hR x⟩ = x - B x := eq_sub_iff_add_eq.mpr (hleft x)
    rw [hDx, hl, hx, smul_sub, smul_smul, hcβ, one_smul, hs, hμc, sub_self]

private theorem inverse_isPositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hDense : Dense (Δ.domain : Set H))
    (B : H →L[ℂ] H) (hΔ : IsSelfAdjoint Δ)
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (hdom : ∀ u : H, B u ∈ Δ.domain)
    (hleft : ∀ u : H, Δ ⟨B u, hdom u⟩ + B u = u) : B.IsPositive := by
  have hformal : Δ.IsFormalAdjoint Δ := by
    have h := LinearPMap.adjoint_isFormalAdjoint hDense
    rwa [LinearPMap.isSelfAdjoint_def.mp hΔ] at h
  refine ⟨?_, KPBelowThreshold.form_nonneg hpos hdom hleft⟩
  intro x y
  change inner ℂ (B x) y = inner ℂ x (B y)
  calc
    inner ℂ (B x) y = inner ℂ (B x) (Δ ⟨B y, hdom y⟩ + B y) := by rw [hleft]
    _ = inner ℂ (Δ ⟨B x, hdom x⟩ + B x) (B y) := by
      rw [inner_add_right, inner_add_left]
      have hf := hformal ⟨B x, hdom x⟩ ⟨B y, hdom y⟩
      dsimp at hf
      rw [hf]
    _ = inner ℂ x (B y) := by rw [hleft]

private theorem positive_spectrum_interval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hp : B.IsPositive) (hn : ‖B‖ ≤ 1) :
    spectrum ℂ B ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  intro z hz
  have he := hp.isSelfAdjoint.mem_spectrum_eq_re hz
  have hr : z.re ∈ spectrum ℝ B := by
    apply (spectrum.algebraMap_mem_iff ℂ).mp
    change (z.re : ℂ) ∈ spectrum ℂ B
    rwa [← he]
  have h0 := SpectrumRestricts.nnreal_iff.mp hp.spectrumRestricts z.re hr
  have h1 := spectrum.norm_le_norm_mul_of_mem hz
  have hid : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hz1 : z.re ≤ 1 := by
    have hh : ‖B‖ * ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by nlinarith [norm_nonneg B, norm_nonneg (1 : H →L[ℂ] H)]
    exact le_trans (Complex.re_le_norm z) (h1.trans hh)
  exact ⟨z.re, ⟨h0, hz1⟩, he.symm⟩

private theorem reciprocal_isolated
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hspec : spectrum ℂ B ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hsp : μ ∈ KPBelowThreshold.realSpectrum B)
    (hi : KPBelowThreshold.IsIsolatedFiniteEigenvalue Δ B μ) :
    KPIsolatedProjection.IsIsolatedSpectralPoint B ((1 + μ)⁻¹) := by
  have hβ : 0 < (1 + μ)⁻¹ := by positivity
  have hf : ContinuousAt (fun t : ℝ => t⁻¹ - 1) ((1 + μ)⁻¹) :=
    (continuousAt_id.inv₀ (ne_of_gt hβ)).sub continuousAt_const
  obtain ⟨η, hη, hi⟩ := hi.2.2
  obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp hf η hη
  refine ⟨(spectrum_iff_pencil B μ hμ).mpr hsp, min δ ((1 + μ)⁻¹),
    lt_min hδ hβ, ?_⟩
  intro w hw hd
  obtain ⟨t, ht, rfl⟩ := hspec hw
  have hdist : dist t ((1 + μ)⁻¹) < min δ ((1 + μ)⁻¹) := by
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using hd
  have htpos : 0 < t := by
    have hh := lt_of_lt_of_le hdist (min_le_right _ _)
    rw [Real.dist_eq] at hh
    have hh' := (abs_lt.mp hh).1
    linarith
  have hν : 0 ≤ t⁻¹ - 1 := by
    have hh : 1 ≤ t⁻¹ := (one_le_inv₀ htpos).mpr ht.2
    linarith
  have heq : (1 + (t⁻¹ - 1))⁻¹ = t := by
    rw [show 1 + (t⁻¹ - 1) = t⁻¹ by ring, inv_inv]
  have hνspec : t⁻¹ - 1 ∈ KPBelowThreshold.realSpectrum B := by
    apply (spectrum_iff_pencil B (t⁻¹ - 1) hν).mp
    rwa [heq]
  have hclose : |(t⁻¹ - 1) - μ| < η := by
    have hh := hc (lt_of_lt_of_le hdist (min_le_left _ _))
    simpa only [inv_inv, show (1 + μ) - 1 = μ by ring, Real.dist_eq] using hh
  have he : t⁻¹ - 1 = μ := hi _ hνspec hclose
  have htβ : t = (1 + μ)⁻¹ := by
    rw [← he, heq]
  rw [htβ]

theorem kp_cont_resolvent_spectrum_transfer
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hDense : Dense (Δ.domain : Set H))
    (B : H →L[ℂ] H) (d : ℝ) (hd : 0 < d)
    (hΔ : IsSelfAdjoint Δ)
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (hbase : KPResolventPencil.GenuineInverse Δ (-1) B)
    (hcoercivity : ∀ ε : ℝ, 0 < ε →
      ∃ K : H →L[ℂ] H, IsCompactOperator K ∧
        ∀ u : H, (d - ε) * ‖B u‖ ^ 2 ≤
          (inner ℂ (B u) (u - B u)).re + ‖K u‖ ^ 2) :
    B.IsPositive ∧ IsSelfAdjoint B ∧ ‖B‖ ≤ 1 ∧
    spectrum ℂ B ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1 ∧
    (∀ β : ℂ, β ∈ spectrum ℂ B → β ≠ 0 →
      β.im = 0 ∧ 0 < β.re ∧
      0 ≤ β.re⁻¹ - 1 ∧
      β⁻¹ - 1 ∉ KPResolventPencil.resolventSet Δ) ∧
    (∀ μ : ℝ, 0 ≤ μ →
      ((μ : ℂ) ∉ KPResolventPencil.resolventSet Δ ↔
        (((1 + μ)⁻¹ : ℝ) : ℂ) ∈ spectrum ℂ B)) ∧
    (∀ μ : ℝ,
      μ ∈ KPBelowThreshold.realSpectrum B ↔
        (μ : ℂ) ∉ KPResolventPencil.resolventSet Δ) ∧
    (∀ μ : ℝ, 0 ≤ μ →
      KPBelowThreshold.eigenspace Δ μ =
        KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹)) ∧
    (∀ μ : ℝ, 0 ≤ μ → μ < d →
      ((μ : ℂ) ∉ KPResolventPencil.resolventSet Δ ↔
        KPBelowThreshold.IsIsolatedFiniteEigenvalue Δ B μ)) ∧
    (∀ μ : ℝ, 0 ≤ μ → μ < d →
      (μ : ℂ) ∉ KPResolventPencil.resolventSet Δ →
        KPIsolatedProjection.IsIsolatedSpectralPoint B ((1 + μ)⁻¹) ∧
        KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹) ≠ ⊥ ∧
        Module.Finite ℂ (KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹))) ∧
    (∀ a b : ℝ, b < d →
      (KPBelowThreshold.realSpectrum B ∩ Set.Icc a b).Finite) ∧
    (∀ a : ℝ, a < d →
      ¬ AccPt a (Filter.principal (KPBelowThreshold.realSpectrum B ∩ Set.Iio d))) := by
  have hbase' := hbase
  obtain ⟨hdom, hl, hr⟩ := hbase'
  have hleft : ∀ u : H, Δ ⟨B u, hdom u⟩ + B u = u := by
    intro u
    simpa only [neg_smul, one_smul, sub_neg_eq_add] using hl u
  have hright : ∀ v : Δ.domain, B (Δ v + (v : H)) = (v : H) := by
    intro v
    simpa only [neg_smul, one_smul, sub_neg_eq_add] using hr v
  have hp := inverse_isPositive Δ hDense B hΔ hpos hdom hleft
  have hn := KPBelowThreshold.norm_le_one hpos hdom hleft
  have hs := positive_spectrum_interval B hp hn
  obtain ⟨_, _, hi, ha⟩ := kp_cont_below_threshold_discreteness
    Δ B d hd hΔ hp.isSelfAdjoint hpos hdom hleft hright hcoercivity
  have hreal := realSpectrum_mem_iff_resolventSet Δ hDense B hbase
  have heig := eigenspace_transfer Δ hDense B hbase
  have hrecip := spectrum_mem_iff_resolventSet Δ hDense B hbase
  have hi_iff : ∀ μ : ℝ, 0 ≤ μ → μ < d →
      ((μ : ℂ) ∉ KPResolventPencil.resolventSet Δ ↔
      KPBelowThreshold.IsIsolatedFiniteEigenvalue Δ B μ) := by
    intro μ hμ hμd
    constructor
    · intro hm
      exact hi μ ((hreal μ).mpr hm) hμd
    · intro hm
      apply (hrecip μ hμ).mp
      rw [ContinuousLinearMap.spectrum_eq]
      apply Module.End.HasEigenvalue.mem_spectrum
      change Module.End.eigenspace (B.toLinearMap) (((1 + μ)⁻¹ : ℝ) : ℂ) ≠ ⊥
      rw [Module.End.eigenspace_def]
      have he : KPIsolatedProjection.eigenspace B ((1 + μ)⁻¹) ≠ ⊥ := by
        rw [← heig μ hμ]
        exact hm.1
      exact he
  refine ⟨hp, hp.isSelfAdjoint, hn, hs, ?_, ?_, hreal, heig, hi_iff, ?_, ?_, ha⟩
  · intro β hβ hβ0
    obtain ⟨t, ht, rfl⟩ := hs hβ
    have ht0 : t ≠ 0 := by
      intro h
      apply hβ0
      simp [h]
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hμ : 0 ≤ t⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ htpos).mpr ht.2)
    refine ⟨by simp, by simpa using htpos, by simpa using hμ, ?_⟩
    have hm := (hrecip (t⁻¹ - 1) hμ).mp
    have he : (1 + (t⁻¹ - 1))⁻¹ = t := by
      rw [show 1 + (t⁻¹ - 1) = t⁻¹ by ring, inv_inv]
    have hm' := hm (by rwa [he])
    simpa only [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_one] using hm'
  · intro μ hμ
    exact (hrecip μ hμ).symm
  · intro μ hμ hμd hm
    have his := (hi_iff μ hμ hμd).mp hm
    refine ⟨reciprocal_isolated Δ B hs μ hμ ((hreal μ).mpr hm) his, ?_, ?_⟩
    · rw [← heig μ hμ]
      exact his.1
    · rw [← heig μ hμ]
      exact his.2.1
  · intro a b hbd
    by_contra hfin
    obtain ⟨x, hx, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hfin
      (isCompact_Icc : IsCompact (Set.Icc a b)) Set.inter_subset_right
    apply ha x (lt_of_le_of_lt hx.2 hbd)
    apply hacc.mono
    rw [Filter.principal_mono]
    intro y hy
    exact ⟨hy.1, lt_of_le_of_lt hy.2.2 hbd⟩

end DedekindZetaZeroFree
