module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.OriginRegularization
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PositiveSideJetSeminorms

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open MeasureTheory Filter

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma iteratedDeriv_eq_zero_of_lt_support (b : ℝ) (h : ℝ → ℂ)
    (hpos : PositiveSideSupport b h) (m : ℕ) :
    ∀ x : ℝ, b < x → iteratedDeriv m h x = 0 := by
  induction m with
  | zero => intro x hx; simpa using hpos x hx
  | succ m ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have h1 : iteratedDeriv m h =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) (fun y hy => ih y hy)
    simpa using h1.deriv_eq

private lemma norm_iteratedDeriv_le_S (b : ℝ) (hb : 0 < b) (m : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) {x : ℝ} (hx : x ∈ Set.Icc 0 b) :
    ‖iteratedDeriv m h x‖ ≤ S b m h := by
  have hfin := S_finite b hb m h hh
  have hterm : ‖iteratedDeriv m h x‖ ≤
      sSup ((fun y : ℝ => ‖iteratedDeriv m h y‖) '' Set.Icc 0 b) :=
    le_csSup (hfin m (Finset.mem_range.mpr (Nat.lt_succ_self m)))
      (Set.mem_image_of_mem _ hx)
  have hnonneg : ∀ i ∈ Finset.range (m + 1),
      0 ≤ sSup ((fun y : ℝ => ‖iteratedDeriv i h y‖) '' Set.Icc 0 b) := by
    intro i hi
    exact le_trans (norm_nonneg _)
      (le_csSup (hfin i hi) (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr hb.le)))
  have hsingle : sSup ((fun y : ℝ => ‖iteratedDeriv m h y‖) '' Set.Icc 0 b) ≤ S b m h := by
    rw [S]
    exact Finset.single_le_sum hnonneg (Finset.mem_range.mpr (Nat.lt_succ_self m))
  exact hterm.trans hsingle

private lemma norm_mellin_le (b : ℝ) (hb : 0 < b) (m : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hpos : PositiveSideSupport b h) (s : ℂ) (hs : 0 < s.re) :
    ‖mellin (iteratedDeriv m h) s‖ ≤ S b m h * b ^ s.re / s.re := by
  set g : ℝ → ℂ := iteratedDeriv m h with hg
  set σ : ℝ := s.re with hσ
  have hσpos : 0 < σ := by rw [hσ]; exact hs
  have hSnn : 0 ≤ S b m h := S_nonneg b hb m h hh
  have hgcont : Continuous g := by
    rw [hg]; exact hh.continuous_iteratedDeriv m (by simp)
  set F : ℝ → ℝ := Set.indicator (Set.Ioc (0 : ℝ) b) (fun t => S b m h * t ^ (σ - 1)) with hF
  have hFapply : ∀ t : ℝ, F t = if t ∈ Set.Ioc (0 : ℝ) b then S b m h * t ^ (σ - 1) else 0 := by
    intro t; rw [hF]; exact Set.indicator_apply ..
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • g t‖ ≤ F t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hnorm : ‖(t : ℂ) ^ (s - 1) • g t‖ = t ^ (σ - 1) * ‖g t‖ := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
    rw [hnorm]
    by_cases htb : t ≤ b
    · have htmem : t ∈ Set.Ioc (0 : ℝ) b := ⟨ht0, htb⟩
      rw [hFapply t, if_pos htmem]
      have hgt : ‖g t‖ ≤ S b m h := by
        rw [hg]
        exact norm_iteratedDeriv_le_S b hb m h hh ⟨ht0.le, htb⟩
      calc t ^ (σ - 1) * ‖g t‖ ≤ t ^ (σ - 1) * S b m h := by gcongr
        _ = S b m h * t ^ (σ - 1) := by ring
    · have hnotmem : t ∉ Set.Ioc (0 : ℝ) b := fun hmem => htb hmem.2
      rw [hFapply t, if_neg hnotmem]
      have hg0 : g t = 0 := by
        rw [hg]
        exact iteratedDeriv_eq_zero_of_lt_support b h hpos m t (lt_of_not_ge htb)
      rw [hg0, norm_zero, mul_zero]

  have hφint : IntegrableOn (fun t : ℝ => S b m h * t ^ (σ - 1)) (Set.Ioc (0 : ℝ) b) := by
    have h1 : IntervalIntegrable (fun t : ℝ => t ^ (σ - 1)) volume (0 : ℝ) b :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    exact h1.1.const_mul (S b m h)
  have hFint : Integrable F volume := by
    rw [hF]
    exact (integrable_indicator_iff measurableSet_Ioc).2 hφint
  have hFintOn : IntegrableOn F (Set.Ioi (0 : ℝ)) volume := hFint.integrableOn

  have hFint_eq : ∫ t in Set.Ioi (0 : ℝ), F t = S b m h * b ^ σ / σ := by
    have h1 : ∫ t in Set.Ioi (0 : ℝ), F t = ∫ t, F t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hFapply x, if_neg]
        intro hmem
        exact hx hmem.1)
    have h2 : ∫ t, F t = ∫ t in Set.Ioc (0 : ℝ) b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t := by
      rw [hF]
      exact integral_indicator measurableSet_Ioc
    have h3 : ∫ t in Set.Ioc (0 : ℝ) b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t
        = ∫ t in (0 : ℝ)..b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t :=
      (intervalIntegral.integral_of_le hb.le).symm
    have h4 : ∫ t in (0 : ℝ)..b, (fun t : ℝ => S b m h * t ^ (σ - 1)) t
        = S b m h * ∫ t in (0 : ℝ)..b, t ^ (σ - 1) :=
      intervalIntegral.integral_const_mul (S b m h) (fun t : ℝ => t ^ (σ - 1))
    have h5 : ∫ t in (0 : ℝ)..b, t ^ (σ - 1) = b ^ σ / σ := by
      rw [integral_rpow (Or.inl (by linarith))]
      have hσ' : σ - 1 + 1 = σ := by ring
      rw [hσ', Real.zero_rpow (ne_of_gt hσpos)]
      simp
    rw [h1, h2, h3, h4, h5]
    ring

  have hcont_cpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Set.Ioi (0 : ℝ)) :=
    fun t ht => (Complex.continuousAt_ofReal_cpow_const t (s - 1)
      (Or.inr (ne_of_gt ht))).continuousWithinAt
  have hint : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • g t‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Integrable.mono' hFintOn ?_ ?_
    · exact (hcont_cpow.smul hgcont.continuousOn).norm.aestronglyMeasurable measurableSet_Ioi
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall (fun t ht => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hpt t ht)
  have hle : (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • g t‖) ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] F :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun t ht => hpt t ht))
  calc ‖mellin g s‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • g t‖ := by
        rw [mellin]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), F t := setIntegral_mono_ae_restrict hint hFintOn hle
    _ = S b m h * b ^ σ / σ := hFint_eq

private theorem originMellinQ_bound_of_re_bounds (b : ℝ) (hb : 0 < b) (K : Set ℂ) (σlo σhi : ℝ)
    (hK : IsCompact K)
    (hlo : ∀ s ∈ K, σlo ≤ s.re) (hhi : ∀ s ∈ K, s.re ≤ σhi) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h → PositiveSideSupport b h →
        ∀ s : ℂ, s ∈ K → ‖originMellinQ h s‖ ≤ C * S b N h := by
  set m : ℕ := Nat.ceil (max 0 (-σlo)) + 1 with hm
  have hmσ : -(m : ℝ) < σlo := by
    have h1 : (-σlo : ℝ) ≤ max 0 (-σlo) := le_max_right _ _
    have h2 : max 0 (-σlo) ≤ (Nat.ceil (max 0 (-σlo)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (max 0 (-σlo)) : ℝ) + 1 ≤ (m : ℝ) := by
      rw [hm]; push_cast; linarith
    linarith

  obtain ⟨CΓ, hCΓ⟩ : ∃ CΓ : ℝ, ∀ s ∈ K, ‖(Complex.Gammaℂ (s + (m : ℂ)))⁻¹‖ ≤ CΓ :=
    hK.exists_bound_of_continuousOn
      ((Complex.differentiable_Gammaℂ_inv.continuous.comp
        (continuous_id.add continuous_const)).continuousOn)

  obtain ⟨CB, hCB⟩ : ∃ CB : ℝ,
      ∀ x ∈ Set.Icc σlo σhi, ‖b ^ (x + m) / (x + m)‖ ≤ CB := by
    refine isCompact_Icc.exists_bound_of_continuousOn ?_
    apply ContinuousOn.div
    · exact (continuous_const.rpow (continuous_id.add continuous_const)
        (fun x => Or.inl (ne_of_gt hb))).continuousOn
    · fun_prop
    · intro x hx
      have : (0 : ℝ) < x + (m : ℝ) := by linarith [hx.1, hmσ]
      simpa using ne_of_gt this
  refine ⟨m, max CΓ 1 * max CB 1, by positivity, ?_⟩
  intro h hh hc hpos s hs
  have hslo : σlo ≤ s.re := hlo s hs
  have hsm : -(m : ℝ) < s.re := lt_of_lt_of_le hmσ hslo
  have hre : (s + (m : ℂ)).re = s.re + m := by simp
  have hrepos : 0 < (s + (m : ℂ)).re := by
    rw [hre]; push_cast; linarith
  have hSnn : 0 ≤ S b m h := S_nonneg b hb m h hh
  have h1 : ‖((-1 : ℂ) ^ m / (2 * (Real.pi : ℂ)) ^ m)‖ ≤ 1 := by
    rw [norm_div, norm_pow, norm_pow, norm_neg, norm_one, one_pow]
    have h2pi : (1 : ℝ) ≤ ‖(2 * (Real.pi : ℂ))‖ := by
      have hsq : ‖(2 * (Real.pi : ℂ))‖ ^ 2 = (2 * Real.pi) ^ 2 := by
        simp [Complex.sq_norm, Complex.normSq_ofReal, Complex.ofReal_mul]
      nlinarith [norm_nonneg (2 * (Real.pi : ℂ)), Real.pi_gt_three]
    exact div_le_one_of_le₀ (one_le_pow₀ h2pi) (by positivity)
  have h2 : ‖mellin (iteratedDeriv m h) (s + (m : ℂ))‖
      ≤ S b m h * b ^ (s + (m : ℂ)).re / (s + (m : ℂ)).re :=
    norm_mellin_le b hb m h hh hpos (s + (m : ℂ)) hrepos
  have h2' : ‖mellin (iteratedDeriv m h) (s + (m : ℂ))‖
      ≤ S b m h * (b ^ (s + (m : ℂ)).re / (s + (m : ℂ)).re) := by
    rw [← mul_div_assoc]; exact h2
  have h3 : ‖(Complex.Gammaℂ (s + (m : ℂ)))⁻¹‖ ≤ max CΓ 1 :=
    le_trans (hCΓ s hs) (le_max_left _ _)
  have h4 : b ^ (s + (m : ℂ)).re / (s + (m : ℂ)).re ≤ max CB 1 := by
    have hmem : s.re ∈ Set.Icc σlo σhi := ⟨hslo, hhi s hs⟩
    have hthis := hCB s.re hmem
    rw [Real.norm_of_nonneg (by positivity)] at hthis
    rw [hre]
    exact le_trans hthis (le_max_left _ _)
  rw [originMellinQ_eq_chart h hh hc m s hsm, originMellinChart]
  calc ‖((-1 : ℂ) ^ m / (2 * (Real.pi : ℂ)) ^ m) * mellin (iteratedDeriv m h) (s + (m : ℂ))
        * (Complex.Gammaℂ (s + (m : ℂ)))⁻¹‖
      ≤ ‖((-1 : ℂ) ^ m / (2 * (Real.pi : ℂ)) ^ m)‖ * ‖mellin (iteratedDeriv m h) (s + (m : ℂ))‖
        * ‖(Complex.Gammaℂ (s + (m : ℂ)))⁻¹‖ := by
        calc ‖((-1 : ℂ) ^ m / (2 * (Real.pi : ℂ)) ^ m) * mellin (iteratedDeriv m h) (s + (m : ℂ))
              * (Complex.Gammaℂ (s + (m : ℂ)))⁻¹‖
            ≤ ‖((-1 : ℂ) ^ m / (2 * (Real.pi : ℂ)) ^ m) * mellin (iteratedDeriv m h) (s + (m : ℂ))‖
              * ‖(Complex.Gammaℂ (s + (m : ℂ)))⁻¹‖ := norm_mul_le _ _
          _ ≤ (‖((-1 : ℂ) ^ m / (2 * (Real.pi : ℂ)) ^ m)‖
              * ‖mellin (iteratedDeriv m h) (s + (m : ℂ))‖) * ‖(Complex.Gammaℂ (s + (m : ℂ)))⁻¹‖ := by
              gcongr
              exact norm_mul_le _ _
    _ ≤ 1 * (S b m h * (b ^ (s + (m : ℂ)).re / (s + (m : ℂ)).re)) * (max CΓ 1) := by
        refine mul_le_mul (mul_le_mul h1 h2' (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) ?_
        exact mul_nonneg zero_le_one (mul_nonneg hSnn (by positivity))
    _ ≤ (max CΓ 1 * max CB 1) * S b m h := by
        have hstep : S b m h * (b ^ (s + (m : ℂ)).re / (s + (m : ℂ)).re) ≤ S b m h * max CB 1 :=
          mul_le_mul_of_nonneg_left h4 hSnn
        calc 1 * (S b m h * (b ^ (s + (m : ℂ)).re / (s + (m : ℂ)).re)) * (max CΓ 1)
            ≤ (S b m h * max CB 1) * (max CΓ 1) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right hstep (by positivity)
          _ = (max CΓ 1 * max CB 1) * S b m h := by ring

theorem originMellinQ_compact_source_bound (b : ℝ) (hb : 0 < b)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        PositiveSideSupport b h →
          ∀ s : ℂ, s ∈ K → ‖originMellinQ h s‖ ≤ C * S b N h := by
  by_cases hne : K.Nonempty
  · obtain ⟨s0, _, hmin⟩ := hK.exists_isMinOn hne (by fun_prop :
      ContinuousOn (fun s : ℂ => s.re) K)
    obtain ⟨s1, _, hmax⟩ := hK.exists_isMaxOn hne (by fun_prop :
      ContinuousOn (fun s : ℂ => s.re) K)
    exact originMellinQ_bound_of_re_bounds b hb K s0.re s1.re hK (fun s hs => hmin hs)
      (fun s hs => hmax hs)
  · exact ⟨0, 1, one_pos, fun h hh hc hpos s hs => absurd ⟨s, hs⟩ hne⟩

theorem originMellinQ_rectangle_source_bound (b : ℝ) (hb : 0 < b)
    (a a' : ℝ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        PositiveSideSupport b h →
          ∀ s : ℂ, a ≤ s.re → s.re ≤ a' → |s.im| ≤ 1 →
            ‖originMellinQ h s‖ ≤ C * S b N h := by
  have hK : IsCompact {s : ℂ | a ≤ s.re ∧ s.re ≤ a' ∧ |s.im| ≤ 1} := by
    have himg : {s : ℂ | a ≤ s.re ∧ s.re ≤ a' ∧ |s.im| ≤ 1} =
        (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
          (Set.Icc a a' ×ˢ Set.Icc (-1 : ℝ) 1) := by
      ext s
      constructor
      · intro hs
        refine ⟨(s.re, s.im), ⟨⟨hs.1, hs.2.1⟩, ?_⟩, ?_⟩
        · have hs' : |s.im| ≤ 1 := hs.2.2
          rw [abs_le] at hs'
          exact ⟨hs'.1, hs'.2⟩
        · exact Complex.re_add_im s
      · rintro ⟨p, hp, rfl⟩
        simp only [Set.mem_prod, Set.mem_Icc] at hp
        have hre' : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).re = p.1 := by simp
        have him' : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
        simp only [Set.mem_setOf_eq, hre', him']
        exact ⟨hp.1.1, hp.1.2, by rw [abs_le]; exact ⟨hp.2.1, hp.2.2⟩⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨N, C, hC, h⟩ := originMellinQ_bound_of_re_bounds b hb _ a a' hK (fun s hs => hs.1)
    (fun s hs => hs.2.1)
  exact ⟨N, C, hC, fun h' hh hc hpos s hs1 hs2 hs3 => h h' hh hc hpos s ⟨hs1, hs2, hs3⟩⟩

end DedekindZetaZeroFree.LargeSieve.Vendor

end
