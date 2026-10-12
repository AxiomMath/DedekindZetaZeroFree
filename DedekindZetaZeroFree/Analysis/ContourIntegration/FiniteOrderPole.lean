module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleResidueSums
public import DedekindZetaZeroFree.Analysis.VerticalIntegralReciprocalPowers

@[expose] public section

open scoped Classical Topology
open MeasureTheory Filter

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma verticalIntegrable_finset_sum {ι : Type*} (s : Finset ι) {c₀ : ℝ} {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, Complex.VerticalIntegrable (f i) c₀) :
    Complex.VerticalIntegrable (fun z => ∑ i ∈ s, f i z) c₀ := by
  have hf' : ∀ i ∈ s, Integrable (fun t : ℝ => f i (c₀ + t * Complex.I)) volume := hf
  have h : Integrable (∑ i ∈ s, fun t : ℝ => f i (c₀ + t * Complex.I)) volume :=
    Finset.sum_induction (fun i => fun t : ℝ => f i (c₀ + t * Complex.I))
      (fun g => Integrable g volume) (fun a b ha hb => ha.add hb)
      (integrable_zero ℝ ℂ volume) hf'
  show Integrable (fun t : ℝ => (fun z => ∑ i ∈ s, f i z) (c₀ + t * Complex.I)) volume
  convert h using 1
  ext t
  simp only [Finset.sum_apply]

private lemma verticalIntegral_finset_sum {ι : Type*} (s : Finset ι) (c₀ : ℝ) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Complex.VerticalIntegrable (f i) c₀) :
    verticalIntegral c₀ (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, verticalIntegral c₀ (f i) := by
  have hf' : ∀ i ∈ s, Integrable (fun t : ℝ => f i (c₀ + t * Complex.I)) volume := hf
  simp only [verticalIntegral]
  rw [← Finset.mul_sum]
  congr 1
  exact integral_finsetSum s hf'

theorem verticalIntegral_sub_eq_of_finite_order_pole
    {a b p : ℝ} (hap : a < p) (hpb : p < b)
    {r : ℕ} (hr : 1 ≤ r) (c : ℕ → ℂ) (F : ℂ → ℂ)
    (hF : ∃ U : Set ℂ, IsOpen U ∧
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b} ⊆ U ∧
      DifferentiableOn ℂ F (U \ {(p : ℂ)}))
    (hregular : ∃ (G : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b} ⊆ U ∧
      DifferentiableOn ℂ G U ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ (p : ℂ) →
        F s = G s + ∑ m ∈ Finset.Icc 1 r, c m / (s - (p : ℂ)) ^ m)
    (ha : Complex.VerticalIntegrable F a)
    (hb : Complex.VerticalIntegrable F b)
    (hgrowth : ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ σ : ℝ, σ ∈ Set.Icc a b → ∀ t : ℝ, 1 ≤ |t| →
        ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ k) :
    verticalIntegral b F - verticalIntegral a F = c 1 := by
  obtain ⟨UF, hUFopen, hUFstrip, hFdiff⟩ := hF
  obtain ⟨G, UG, hUGopen, hUGstrip, hGdiff, hGF⟩ := hregular
  have hpstrip : (p : ℂ) ∈ UF := hUFstrip ⟨le_of_lt hap, le_of_lt hpb⟩

  set H : ℂ → ℂ := fun z => ∑ m ∈ Finset.Icc 2 r, c m / (z - (p : ℂ)) ^ m with hHdef
  set F₁ : ℂ → ℂ := F - H with hF₁def
  set g₀ : ℂ → ℂ := F₁ - fun z => c 1 / (z - (p : ℂ)) with hg₀def

  have hIcc : Finset.Icc 1 r = insert 1 (Finset.Icc 2 r) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsplit : ∀ s : ℂ, ∑ m ∈ Finset.Icc 1 r, c m / (s - (p : ℂ)) ^ m
      = c 1 / (s - (p : ℂ)) + ∑ m ∈ Finset.Icc 2 r, c m / (s - (p : ℂ)) ^ m := by
    intro s
    rw [hIcc, Finset.sum_insert (by simp)]
    norm_num

  have hG₀ : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ (p : ℂ) → g₀ s = G s := by
    intro s hs1 hs2 hsp
    have hFs := hGF s hs1 hs2 hsp
    simp only [hg₀def, hF₁def, hHdef, Pi.sub_apply]
    rw [hFs, hsplit]
    ring

  have hHdiff : DifferentiableOn ℂ H (UF \ {(p : ℂ)}) := by
    rw [hHdef]
    have hterm : ∀ m ∈ Finset.Icc 2 r,
        DifferentiableOn ℂ (fun z : ℂ => c m / (z - (p : ℂ)) ^ m) (UF \ {(p : ℂ)}) := by
      intro m _
      refine DifferentiableOn.div (differentiableOn_const (c m)) ((differentiableOn_id.sub_const _).pow m) ?_
      intro z hz
      exact pow_ne_zero m (sub_ne_zero.mpr fun h => hz.2 (by simpa using h))
    have h := DifferentiableOn.sum (u := Finset.Icc 2 r)
      (A := fun m => fun z : ℂ => c m / (z - (p : ℂ)) ^ m) hterm
    convert h using 1
    ext z
    simp only [Finset.sum_apply]
  have hF₁diff : DifferentiableOn ℂ F₁ (UF \ {(p : ℂ)}) := by
    rw [hF₁def]
    exact hFdiff.sub hHdiff

  have hHint : ∀ c₀ : ℝ, c₀ ≠ p → Complex.VerticalIntegrable H c₀ := by
    intro c₀ hc₀
    rw [hHdef]
    have hfun : (fun z : ℂ => ∑ m ∈ Finset.Icc 2 r, c m / (z - (p : ℂ)) ^ m)
        = fun z : ℂ => ∑ m ∈ Finset.Icc 2 r,
            (fun w : ℂ => c m * (1 / (w - (p : ℂ)) ^ m)) z := by
      funext z
      simp only [div_eq_mul_inv, one_div, one_mul]
    rw [hfun]
    exact verticalIntegrable_finset_sum _ fun m hm =>
      verticalIntegrable_const_mul_one_div_pow (c m) hc₀ (Finset.mem_Icc.mp hm).1
  have hH_a : Complex.VerticalIntegrable H a := hHint a (ne_of_lt hap)
  have hH_b : Complex.VerticalIntegrable H b := hHint b (ne_of_gt hpb)
  have hF₁_a : Complex.VerticalIntegrable F₁ a := by
    rw [hF₁def]
    exact ha.sub hH_a
  have hF₁_b : Complex.VerticalIntegrable F₁ b := by
    rw [hF₁def]
    exact hb.sub hH_b

  have hHzero : ∀ c₀ : ℝ, c₀ ≠ p → verticalIntegral c₀ H = 0 := by
    intro c₀ hc₀
    rw [hHdef]
    have hfun : (fun z : ℂ => ∑ m ∈ Finset.Icc 2 r, c m / (z - (p : ℂ)) ^ m)
        = fun z : ℂ => ∑ m ∈ Finset.Icc 2 r,
            (fun w : ℂ => c m * (1 / (w - (p : ℂ)) ^ m)) z := by
      funext z
      simp only [div_eq_mul_inv, one_div, one_mul]
    rw [hfun, verticalIntegral_finset_sum (Finset.Icc 2 r) c₀
      (fun m w => c m * (1 / (w - (p : ℂ)) ^ m)) (fun m hm =>
        verticalIntegrable_const_mul_one_div_pow (c m) hc₀ (Finset.mem_Icc.mp hm).1)]
    refine Finset.sum_eq_zero fun m hm => ?_
    exact verticalIntegral_const_mul_one_div_pow_eq_zero (c m) hc₀ (Finset.mem_Icc.mp hm).1
  have hF_eq_a : verticalIntegral a F = verticalIntegral a F₁ := by
    have h1 : F = fun z => F₁ z + H z := by
      funext z
      rw [hF₁def]
      simp only [Pi.sub_apply]
      ring
    rw [h1, verticalIntegral_add a F₁ H hF₁_a hH_a, hHzero a (ne_of_lt hap), add_zero]
  have hF_eq_b : verticalIntegral b F = verticalIntegral b F₁ := by
    have h1 : F = fun z => F₁ z + H z := by
      funext z
      rw [hF₁def]
      simp only [Pi.sub_apply]
      ring
    rw [h1, verticalIntegral_add b F₁ H hF₁_b hH_b, hHzero b (ne_of_gt hpb), add_zero]

  have hgrowth₁ : ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ (σ : ℝ) (t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖F₁ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ k := by
    obtain ⟨C, k, hC, hbound⟩ := hgrowth
    refine ⟨C + ∑ m ∈ Finset.Icc 2 r, ‖c m‖, k, ?_, ?_⟩
    · positivity
    · intro σ t hσ ht
      have hA1 : 1 ≤ (1 + |t|) ^ k := one_le_pow₀ (by linarith [abs_nonneg t])
      have hS : 0 ≤ ∑ m ∈ Finset.Icc 2 r, ‖c m‖ := Finset.sum_nonneg fun m _ => norm_nonneg _
      have hHle : ‖H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ∑ m ∈ Finset.Icc 2 r, ‖c m‖ := by
        rw [hHdef]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        have hw : 1 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - (p : ℂ)‖ := by
          have him : (((σ : ℂ) + (t : ℂ) * Complex.I) - (p : ℂ)).im = t := by simp
          calc (1 : ℝ) ≤ |t| := ht
            _ = |(((σ : ℂ) + (t : ℂ) * Complex.I) - (p : ℂ)).im| := by rw [him]
            _ ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - (p : ℂ)‖ := Complex.abs_im_le_norm _
        rw [norm_div, norm_pow, div_le_iff₀ (pow_pos (by linarith) m)]
        nlinarith [norm_nonneg (c m), one_le_pow₀ hw (n := m)]
      calc ‖F₁ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖F ((σ : ℂ) + (t : ℂ) * Complex.I) - H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
            simp only [hF₁def, Pi.sub_apply]
        _ ≤ ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ + ‖H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
            norm_sub_le _ _
        _ ≤ C * (1 + |t|) ^ k + ∑ m ∈ Finset.Icc 2 r, ‖c m‖ :=
            add_le_add (hbound σ hσ t ht) hHle
        _ ≤ (C + ∑ m ∈ Finset.Icc 2 r, ‖c m‖) * (1 + |t|) ^ k := by
            nlinarith [hS, hA1]

  have hg₀diff : DifferentiableOn ℂ g₀ (UF \ {(p : ℂ)}) := by
    rw [hg₀def]
    have h2 : DifferentiableOn ℂ (fun z : ℂ => c 1 / (z - (p : ℂ))) (UF \ {(p : ℂ)}) :=
      DifferentiableOn.div (differentiableOn_const (c 1)) (differentiableOn_id.sub_const _) fun z hz =>
        sub_ne_zero.mpr fun h => hz.2 (by simpa using h)
    exact hF₁diff.sub h2
  have hGcont : ContinuousAt G (p : ℂ) :=
    (hGdiff.differentiableAt (hUGopen.mem_nhds (hUGstrip ⟨le_of_lt hap, le_of_lt hpb⟩))).continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hGcont 1 one_pos
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] (p : ℂ))
      (norm ∘ fun z => g₀ z - g₀ (p : ℂ)) := by
    have hopen : IsOpen {s : ℂ | a < s.re ∧ s.re < b} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hstr : ∀ᶠ z in 𝓝 (p : ℂ), a < z.re ∧ z.re < b :=
      hopen.mem_nhds (by simpa using ⟨hap, hpb⟩)
    refine ⟨‖G (p : ℂ)‖ + 1 + ‖g₀ (p : ℂ)‖, ?_⟩
    have hstr' : ∀ᶠ z in 𝓝[≠] (p : ℂ), a < z.re ∧ z.re < b :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hstr
    have hball' : ∀ᶠ z in 𝓝[≠] (p : ℂ), z ∈ Metric.ball (p : ℂ) δ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (p : ℂ) hδpos)
    have hne : ∀ᶠ z in 𝓝[≠] (p : ℂ), z ≠ (p : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
    have hmain : ∀ᶠ z in 𝓝[≠] (p : ℂ),
        ‖g₀ z - g₀ (p : ℂ)‖ ≤ ‖G (p : ℂ)‖ + 1 + ‖g₀ (p : ℂ)‖ := by
      filter_upwards [hstr', hball', hne] with z hz hzball hzne
      have hGz : g₀ z = G z := hG₀ z (le_of_lt hz.1) (le_of_lt hz.2) hzne
      rw [hGz]
      have hnorm : ‖G z‖ ≤ ‖G (p : ℂ)‖ + 1 := by
        have h1 : dist (G z) (G (p : ℂ)) < 1 := hδ (Metric.mem_ball.mp hzball)
        rw [dist_eq_norm] at h1
        have h2 : ‖G z‖ ≤ ‖G z - G (p : ℂ)‖ + ‖G (p : ℂ)‖ := by
          calc ‖G z‖ = ‖(G z - G (p : ℂ)) + G (p : ℂ)‖ := by rw [sub_add_cancel]
            _ ≤ ‖G z - G (p : ℂ)‖ + ‖G (p : ℂ)‖ := norm_add_le _ _
        linarith
      calc ‖G z - g₀ (p : ℂ)‖ ≤ ‖G z‖ + ‖g₀ (p : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖G (p : ℂ)‖ + 1 + ‖g₀ (p : ℂ)‖ := by linarith
    rw [Filter.eventually_map]
    simpa only [Function.comp_apply] using hmain
  set g : ℂ → ℂ := Function.update g₀ (p : ℂ) ((𝓝[≠] (p : ℂ)).limUnder g₀) with hgdef
  have hgdiff : DifferentiableOn ℂ g UF := by
    rw [hgdef]
    exact Complex.differentiableOn_update_limUnder_of_isLittleO (hUFopen.mem_nhds hpstrip) hg₀diff
      (Filter.IsBoundedUnder.isLittleO_sub_self_inv hbdd)
  have hgreg : ∀ s ∈ UF, (∀ j : Fin 1, s ≠ (p : ℂ)) →
      g s = F₁ s - ∑ j : Fin 1, c 1 / (s - (p : ℂ)) := by
    intro s _ hsne
    have hsne' : s ≠ (p : ℂ) := fun h => hsne 0 h
    rw [hgdef, Function.update_of_ne hsne', hg₀def]
    simp only [Pi.sub_apply, Fin.sum_univ_one]

  have hres : verticalIntegral b F₁ - verticalIntegral a F₁ = c 1 := by
    have h := verticalIntegral_sub_eq_sum_residues (a := a) (b := b) (by linarith) 1
      (fun _ : Fin 1 => p) (fun _ => c 1)
      (fun i j _ => Subsingleton.elim i j)
      (fun _ => ⟨hap, hpb⟩)
      F₁ UF hUFopen (by simpa only [Set.mem_Icc] using hUFstrip)
      (by simpa only [Set.range_const] using hF₁diff)
      ⟨g, hgdiff, hgreg⟩ hF₁_a hF₁_b hgrowth₁
    simpa only [Fin.sum_univ_one] using h
  rw [hF_eq_b, hF_eq_a]
  exact hres

end DedekindZetaZeroFree.LargeSieve.Vendor
