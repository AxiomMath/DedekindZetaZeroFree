module

public import DedekindZetaZeroFree.Analysis.OperatorTheory.Resolvents.IsolatedLaurentExpansion
public import DedekindZetaZeroFree.Analysis.OperatorTheory.Resolvents.BoundedUnboundedSpectrumCorrespondence

@[expose] public section

namespace DedekindZetaZeroFree

namespace KPBelowThresholdResolvent

def domain (d : ℝ) : Set ℂ :=
  (Complex.ofReal '' Set.Ici d)ᶜ

def poleSet
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (d : ℝ) : Set ℂ :=
  {z | ∃ μ : ℝ, μ < d ∧ KPBelowThreshold.eigenspace Δ μ ≠ ⊥ ∧ z = (μ : ℂ)}

noncomputable def poleProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (μ : ℝ) : H →L[ℂ] H :=
  KPIsolatedProjection.projection B ((1 + μ)⁻¹)

private theorem isOpen_domain (d : ℝ) : IsOpen (domain d) := by
  have he : Complex.ofReal '' Set.Ici d = {z : ℂ | z.im = 0 ∧ d ≤ z.re} := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa using ht
    · rintro ⟨hi, hr⟩
      exact ⟨z.re, hr, Complex.ext (by simp) (by simpa using hi.symm)⟩
  rw [domain, he]
  exact ((isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)).isOpen_compl

 theorem eigen_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H)
    (hpos : ∀ v : Δ.domain, 0 ≤ (inner ℂ (v : H) (Δ v)).re)
    (μ : ℝ) (he : KPBelowThreshold.eigenspace Δ μ ≠ ⊥) : 0 ≤ μ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
  obtain ⟨v, hv, rfl⟩ := (Submodule.mem_map).mp hx
  have hev : Δ v = (μ : ℂ) • (v : H) := sub_eq_zero.mp hv
  have hp := hpos v
  rw [hev, inner_smul_right, Complex.mul_re] at hp
  have hn : 0 < ‖(v : H)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hinner : (inner ℂ (v : H) (v : H)).re = ‖(v : H)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (v : H)
  have hp' : 0 ≤ μ * ‖(v : H)‖ ^ 2 := by
    simpa only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hinner] using hp
  nlinarith

private theorem eigen_not_resolvent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (μ : ℝ)
    (he : KPBelowThreshold.eigenspace Δ μ ≠ ⊥) :
    (μ : ℂ) ∉ KPResolventPencil.resolventSet Δ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
  obtain ⟨v, hv, rfl⟩ := (Submodule.mem_map).mp hx
  intro hres
  obtain ⟨R, hR⟩ := hres
  have h := hR.2.2 v
  have hz : Δ v - (μ : ℂ) • (v : H) = 0 := hv
  rw [hz, map_zero] at h
  exact hx0 h.symm

private theorem nonresolvent_mem_poleSet
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Δ : H →ₗ.[ℂ] H) (hDense : Dense (Δ.domain : Set H))
    (B : H →L[ℂ] H) (hbase : KPResolventPencil.GenuineInverse Δ (-1) B)
    (d : ℝ) (hB : IsSelfAdjoint B)
    (hspec : spectrum ℂ B ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1)
    (htransfer : ∀ μ : ℝ, 0 ≤ μ → μ < d →
      ((μ : ℂ) ∉ KPResolventPencil.resolventSet Δ ↔
        KPBelowThreshold.IsIsolatedFiniteEigenvalue Δ B μ))
    (z : ℂ) (hz : z ∈ domain d) (hres : z ∉ KPResolventPencil.resolventSet Δ) :
    z ∈ poleSet Δ d := by
  classical
  have he : cfc (fun w : ℂ => 1 - (z + 1) * w) B =
      KPResolventPencil.shiftedPencil B z := by
    rw [cfc_sub (fun _ : ℂ => 1) (fun w : ℂ => (z + 1) * w) B
      continuousOn_const (by fun_prop), cfc_const_one ℂ B hB.isStarNormal]
    change 1 - cfc (fun w : ℂ => (z + 1) • w) B = _
    rw [cfc_smul_id (z + 1) B hB.isStarNormal]
    rfl
  have hu : ¬ IsUnit (cfc (fun w : ℂ => 1 - (z + 1) * w) B) := by
    rw [he, KPResolventPencil.isUnit_shiftedPencil_iff Δ hDense B hbase]
    exact hres
  rw [isUnit_cfc_iff _ B (by fun_prop) hB.isStarNormal] at hu
  push_neg at hu
  obtain ⟨w, hw, hwzero⟩ := hu
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hspec hw
  have hmul : (z + 1) * (t : ℂ) = 1 := (sub_eq_zero.mp hwzero).symm
  have ht : t ≠ 0 := by
    intro ht
    simp [ht] at hmul
  have hreal : (z.re + 1) * t = 1 := by
    simpa using congrArg Complex.re hmul
  have him : z.im * t = 0 := by
    simpa using congrArg Complex.im hmul
  have hzreal : z = (z.re : ℂ) := Complex.ext (by simp) (by
    simpa using (mul_eq_zero.mp him).resolve_right ht)
  have hz0 : 0 ≤ z.re := by
    have hzt : 0 ≤ z.re * t := by nlinarith
    exact (mul_nonneg_iff_of_pos_right (lt_of_le_of_ne ht0 (Ne.symm ht))).mp hzt
  have hzd : z.re < d := by
    by_contra h
    apply hz
    exact ⟨z.re, le_of_not_gt h, hzreal.symm⟩
  have hzr : (z.re : ℂ) ∉ KPResolventPencil.resolventSet Δ := by
    rwa [← hzreal]
  exact ⟨z.re, hzd, ((htransfer z.re hz0 hzd).mp hzr).1, hzreal⟩

end KPBelowThresholdResolvent

open KPBelowThresholdResolvent Filter Topology

theorem kp_cont_below_threshold_resolvent
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
    (-1 : ℂ) ∈ KPResolventPencil.resolventSet Δ ∧
    KPResolventPencil.shiftedResolvent B (-1) = B ∧
    B.IsPositive ∧ IsSelfAdjoint B ∧ ‖B‖ ≤ 1 ∧
    MeromorphicOn (KPResolventPencil.shiftedResolvent B) (domain d) ∧
    KPResolventPencil.resolventSet Δ ∩ domain d = domain d \ poleSet Δ d ∧
    AnalyticOnNhd ℂ (KPResolventPencil.shiftedResolvent B)
      (domain d \ poleSet Δ d) ∧
    (∀ z ∈ domain d \ poleSet Δ d,
      KPResolventPencil.GenuineInverse Δ z (KPResolventPencil.shiftedResolvent B z) ∧
      (∀ x : H, KPResolventPencil.shiftedResolvent B z x ∈ Δ.domain) ∧
      ∀ R : H →L[ℂ] H, KPResolventPencil.GenuineInverse Δ z R →
        R = KPResolventPencil.shiftedResolvent B z) ∧
    (∀ z ∈ domain d,
      (z ∈ poleSet Δ d ↔
        meromorphicOrderAt (KPResolventPencil.shiftedResolvent B) z =
          ((-1 : ℤ) : WithTop ℤ))) ∧
    (∀ μ : ℝ, μ < d → KPBelowThreshold.eigenspace Δ μ ≠ ⊥ →
      0 ≤ μ ∧
      poleProjection B μ ≠ 0 ∧
      IsSelfAdjoint (poleProjection B μ) ∧
      poleProjection B μ * poleProjection B μ = poleProjection B μ ∧
      (poleProjection B μ).range = KPBelowThreshold.eigenspace Δ μ ∧
      FiniteDimensional ℂ (poleProjection B μ).range ∧
      Tendsto (fun z : ℂ => (z - (μ : ℂ)) • KPResolventPencil.shiftedResolvent B z)
        (𝓝[≠] (μ : ℂ)) (𝓝 (-poleProjection B μ)) ∧
      (¬ ∃ G : ℂ → (H →L[ℂ] H),
        ContinuousAt G (μ : ℂ) ∧
        G =ᶠ[𝓝[≠] (μ : ℂ)] KPResolventPencil.shiftedResolvent B) ∧
      ∃ r : ℝ, 0 < r ∧ Metric.ball (μ : ℂ) r ⊆ domain d ∧
        AnalyticOnNhd ℂ (KPIsolatedLaurent.holomorphicComplement B ((1 + μ)⁻¹))
          (Metric.ball (μ : ℂ) r) ∧
        ∀ z : ℂ, 0 < ‖z - (μ : ℂ)‖ → ‖z - (μ : ℂ)‖ < r →
          z ∈ KPResolventPencil.resolventSet Δ ∧
          KPResolventPencil.shiftedResolvent B z =
            ((μ : ℂ) - z)⁻¹ • poleProjection B μ +
              KPIsolatedLaurent.holomorphicComplement B ((1 + μ)⁻¹) z) := by
  classical
  obtain ⟨hBpos, hB, hnorm, hspec, hspecpoints, hrecip, hreal,
    heigen, hfinite, hisolated, hwindows, hacc⟩ :=
    kp_cont_resolvent_spectrum_transfer Δ hDense B d hd hΔ hpos hbase hcoercivity
  have hset : KPResolventPencil.resolventSet Δ ∩ domain d = domain d \ poleSet Δ d := by
    ext z
    constructor
    · rintro ⟨hr, hz⟩
      refine ⟨hz, ?_⟩
      rintro ⟨μ, hμd, he, rfl⟩
      exact eigen_not_resolvent Δ μ he hr
    · rintro ⟨hz, hnp⟩
      refine ⟨?_, hz⟩
      by_contra hr
      exact hnp (nonresolvent_mem_poleSet Δ hDense B hbase d hB hspec hfinite z hz hr)
  have hsubset : domain d \ poleSet Δ d ⊆ KPResolventPencil.resolventSet Δ := by
    intro z hz
    rw [← hset] at hz
    exact hz.1
  have hanalytic := (KPResolventPencil.analyticOnNhd_shiftedResolvent Δ hDense B hbase).mono hsubset
  have hiso (μ : ℝ) (hμd : μ < d) (he : KPBelowThreshold.eigenspace Δ μ ≠ ⊥) :=
    hisolated μ (eigen_nonneg Δ hpos μ he) hμd (eigen_not_resolvent Δ μ he)
  have hβne (μ : ℝ) (he : KPBelowThreshold.eigenspace Δ μ ≠ ⊥) : (1 + μ)⁻¹ ≠ 0 :=
    inv_ne_zero (by have := eigen_nonneg Δ hpos μ he; positivity)
  have hloc (μ : ℝ) (he : KPBelowThreshold.eigenspace Δ μ ≠ ⊥) :
      KPIsolatedLaurent.poleLocation ((1 + μ)⁻¹) = μ := by
    simp [KPIsolatedLaurent.poleLocation]
  have hsimple (μ : ℝ) (hμd : μ < d) (he : KPBelowThreshold.eigenspace Δ μ ≠ ⊥) :=
    KPIsolatedLaurent.simplePole B hB ((1 + μ)⁻¹) (hβne μ he) (hiso μ hμd he).1
  refine ⟨⟨B, hbase⟩, KPResolventPencil.shiftedResolvent_neg_one B,
    hBpos, hB, hnorm, ?_, hset, hanalytic, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hp : z ∈ poleSet Δ d
    · obtain ⟨μ, hμd, he, rfl⟩ := hp
      simpa only [hloc μ he] using (hsimple μ hμd he).2.1
    · exact (hanalytic z ⟨hz, hp⟩).meromorphicAt
  · intro z hz
    obtain ⟨hgenuine, hunique⟩ := KPResolventPencil.shiftedResolvent_genuine_unique
      Δ hDense B hbase z
      ((KPResolventPencil.isUnit_shiftedPencil_iff Δ hDense B hbase z).mpr (hsubset hz))
    exact ⟨hgenuine, hgenuine.1, hunique⟩
  · intro z hz
    constructor
    · rintro ⟨μ, hμd, he, rfl⟩
      simpa only [hloc μ he] using (hsimple μ hμd he).2.2.1
    · intro ho
      by_contra hp
      have hn := (hanalytic z ⟨hz, hp⟩).meromorphicOrderAt_nonneg
      rw [ho] at hn
      exact (not_le_of_gt (show ((-1 : ℤ) : WithTop ℤ) < 0 from by
        exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))) hn
  · intro μ hμd he
    have hμ := eigen_nonneg Δ hpos μ he
    obtain ⟨hi, heB, hfB⟩ := hiso μ hμd he
    obtain ⟨hPne, hPsa, hPP, hPrange, hBP, hPB⟩ :=
      KPIsolatedProjection.projection_spec B hB ((1 + μ)⁻¹) (hβne μ he) hi
    obtain ⟨hPne', hmero, horder, htendsto, hnonrem, hfrank⟩ := hsimple μ hμd he
    have hrange : (poleProjection B μ).range = KPBelowThreshold.eigenspace Δ μ := by
      rw [heigen μ hμ]
      exact hPrange
    have hfd : FiniteDimensional ℂ (poleProjection B μ).range := by
      rw [hrange, heigen μ hμ]
      exact hfB
    refine ⟨hμ, hPne, hPsa, hPP, hrange, hfd, ?_, ?_, ?_⟩
    · simpa only [hloc μ he, poleProjection] using htendsto
    · simpa only [hloc μ he, poleProjection] using hnonrem
    · obtain ⟨r, hr, hcorrect, hhol, hlaurent⟩ :=
        KPIsolatedLaurent.exists_laurent_disk B hB ((1 + μ)⁻¹) (hβne μ he) hi
      rw [hloc μ he] at hhol hlaurent
      have hμdomain : (μ : ℂ) ∈ domain d := by
        rintro ⟨t, ht, heq⟩
        have htμ : t = μ := by exact_mod_cast heq
        subst t
        exact (not_le_of_gt hμd) ht
      obtain ⟨s, hs, hsball⟩ := Metric.isOpen_iff.mp (isOpen_domain d) (μ : ℂ) hμdomain
      refine ⟨min r s, lt_min hr hs, ?_, ?_, ?_⟩
      · exact (Metric.ball_subset_ball (min_le_right r s)).trans hsball
      · exact hhol.mono (Metric.ball_subset_ball (min_le_left r s))
      · intro z hz0 hzr
        obtain ⟨hunit, hformula⟩ := hlaurent z hz0 (lt_of_lt_of_le hzr (min_le_left r s))
        exact ⟨(KPResolventPencil.isUnit_shiftedPencil_iff Δ hDense B hbase z).mp hunit,
          hformula⟩

end DedekindZetaZeroFree
