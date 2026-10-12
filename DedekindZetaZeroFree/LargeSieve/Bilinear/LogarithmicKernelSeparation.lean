module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.BoxCoefficientBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.LogLocalizedEulerJets
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.DoubleReflectionBounds

@[expose] public section

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped ContDiff

namespace DedekindZetaZeroFree.LargeSieve.KernelSeparation

def logLocalized (χ ψ : ℝ → ℂ) (K : ℝ → ℂ) (scale : ℝ) (p : ℝ × ℝ) : ℂ :=
  χ p.1 * ψ p.2 * K (scale * Real.exp ((p.1 + p.2) / 2))

theorem logLocalized_smooth_support (R : ℝ) (χ ψ K : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hsχ : Function.support χ ⊆ Set.Icc (-R) R)
    (hsψ : Function.support ψ ⊆ Set.Icc (-R) R)
    (hK : ContDiffOn ℝ ∞ K (Set.Ioi 0))
    (scale : ℝ) (hscale : 0 < scale) :
    ContDiff ℝ ∞ (logLocalized χ ψ K scale) ∧
    Function.support (logLocalized χ ψ K scale) ⊆
      Set.Icc (-R) R ×ˢ Set.Icc (-R) R := by
  have harg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => scale * Real.exp ((p.1 + p.2) / 2)) := by
    fun_prop
  have hKcomp : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => K (scale * Real.exp ((p.1 + p.2) / 2))) :=
    hK.comp_contDiff harg (fun p => mul_pos hscale (Real.exp_pos _))
  have hχ1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => χ p.1) := hχ.comp contDiff_fst
  have hψ2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ψ p.2) := hψ.comp contDiff_snd
  constructor
  · change ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
        χ p.1 * ψ p.2 * K (scale * Real.exp ((p.1 + p.2) / 2)))
    exact hχ1.mul hψ2 |>.mul hKcomp
  · intro p hp
    have hχne : χ p.1 ≠ 0 := by
      intro h
      exact hp (by simp [logLocalized, h])
    have hψne : ψ p.2 ≠ 0 := by
      intro h
      exact hp (by simp [logLocalized, h])
    exact ⟨hsχ (Function.mem_support.mpr hχne), hsψ (Function.mem_support.mpr hψne)⟩

end DedekindZetaZeroFree.LargeSieve.KernelSeparation

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.KernelSeparation

theorem boxJet_le_nine_mul (R : ℝ) (hR : 0 ≤ R) (H : ℝ × ℝ → ℂ)
    (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ i ≤ 2, ∀ j ≤ 2, ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R,
      ‖DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.mixedDeriv i j H x y‖ ≤ L) :
    DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.boxJet R H ≤ 9 * L := by
  have hterm : ∀ i ∈ Finset.range 3, ∀ j ∈ Finset.range 3,
      sSup {v : ℝ | ∃ x ∈ Set.Icc (-R) R, ∃ y ∈ Set.Icc (-R) R,
        v = ‖DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.mixedDeriv i j H x y‖} ≤ L := by
    intro i hi j hj
    refine csSup_le ?_ ?_
    · exact ⟨‖DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.mixedDeriv i j H 0 0‖,
        0, Set.mem_Icc.mpr ⟨by linarith, hR⟩, 0, Set.mem_Icc.mpr ⟨by linarith, hR⟩, rfl⟩
    rintro v ⟨x, hx, y, hy, rfl⟩
    exact hbound i (by have := Finset.mem_range.mp hi; omega)
      j (by have := Finset.mem_range.mp hj; omega) x hx y hy
  rw [DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.boxJet]
  calc ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        sSup {v : ℝ | ∃ x ∈ Set.Icc (-R) R, ∃ y ∈ Set.Icc (-R) R,
          v = ‖DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.mixedDeriv i j H x y‖}
      ≤ ∑ _i ∈ Finset.range 3, ∑ _j ∈ Finset.range 3, L := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hterm i hi j hj
    _ = 9 * L := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end DedekindZetaZeroFree.LargeSieve.KernelSeparation

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped ContDiff

namespace DedekindZetaZeroFree.LargeSieve.KernelSeparation

private lemma partial_smooth (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (fun t => H (p.1,t)) p.2) := by
  induction n with
  | zero => simpa using hH
  | succ n ih =>
    have hh : ContDiff ℝ ∞ (Function.uncurry (fun (p : ℝ × ℝ) (t : ℝ) =>
        iteratedDeriv n (fun u => H (p.1,u)) t)) := by
      exact ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd := hh.fderiv_apply (g := fun p : ℝ × ℝ => p.2)
      (k := fun _ => (1 : ℝ)) contDiff_snd contDiff_const (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    simpa only [iteratedDeriv_succ, deriv] using hd

private lemma mixed_smooth (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (i j : ℕ) :
    Continuous (fun p : ℝ × ℝ => DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.mixed i j H p.1 p.2) := by
  have hj := partial_smooth H hH j
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (fun t => H (p.2,t)) p.1) :=
    hj.comp (contDiff_snd.prodMk contDiff_fst)
  have hi := partial_smooth _ hs i
  exact (hi.comp (contDiff_snd.prodMk contDiff_fst)).continuous

theorem logLocalized_mixed_derivative_bound
    (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (χ ψ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (K : ℝ → ℂ) (B : ℝ),
      ContDiffOn ℝ ∞ K (Set.Ioi 0) → 0 ≤ B →
      (∀ j ≤ 4, ∀ x : ℝ, 0 < x →
        ‖DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter j K x‖ ≤ B * Real.rpow x (-c)) →
      ∀ scale : ℝ, 0 < scale →
      ∀ i ≤ 2, ∀ j ≤ 2, ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R,
        ‖DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.mixedDeriv i j (logLocalized χ ψ K scale) x y‖ ≤
          A * B * Real.rpow scale (-c) := by
  obtain ⟨A, hA, hbound⟩ := DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.uniform_jet_bound R c hR hc χ ψ hχ hψ
  refine ⟨A, hA, ?_⟩
  intro K B hK hB hEuler scale hs i hi j hj x hx y hy
  let H := DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.localized χ ψ K scale
  have hH : ContDiff ℝ ∞ H := by
    have hk : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
        K (scale * Real.exp ((p.1 + p.2) / 2))) := by
      apply hK.comp_contDiff
      · fun_prop
      · intro p; exact mul_pos hs (Real.exp_pos _)
    exact (hχ.comp contDiff_fst).mul (hψ.comp contDiff_snd) |>.mul hk
  let T := fun a b : ℕ => {z : ℝ | ∃ u ∈ Set.Icc (-R) R,
      ∃ v ∈ Set.Icc (-R) R, z = ‖DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.mixed a b H u v‖}
  have hbdd : BddAbove (T i j) := by
    have hbox : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) :=
      isCompact_Icc.prod isCompact_Icc
    have hcpt := hbox.image (mixed_smooth H hH i j).norm
    have heq : T i j = (fun p : ℝ × ℝ =>
        ‖DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.mixed i j H p.1 p.2‖) ''
        (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
      ext z
      constructor
      · rintro ⟨u, hu, v, hv, rfl⟩
        exact ⟨(u,v), ⟨hu,hv⟩, rfl⟩
      · rintro ⟨⟨u,v⟩, ⟨hu,hv⟩, rfl⟩
        exact ⟨u,hu,v,hv,rfl⟩
    rw [heq]
    exact hcpt.bddAbove
  have hnonneg : ∀ a b, 0 ≤ sSup (T a b) := by
    intro a b
    apply Real.sSup_nonneg
    rintro z ⟨u,hu,v,hv,rfl⟩
    exact norm_nonneg _
  have hp : ‖DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.mixed i j H x y‖ ≤
      DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.jet R H := by
    calc
      _ ≤ sSup (T i j) := le_csSup hbdd ⟨x,hx,y,hy,rfl⟩
      _ ≤ ∑ b ∈ Finset.range 3, sSup (T i b) :=
        Finset.single_le_sum (fun b _ => hnonneg i b) (Finset.mem_range.mpr (by omega))
      _ ≤ ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, sSup (T a b) :=
        Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hnonneg a b))
          (Finset.mem_range.mpr (by omega))
      _ = _ := rfl
  exact hp.trans (hbound K B hK hB hEuler scale hs)

end DedekindZetaZeroFree.LargeSieve.KernelSeparation

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped Classical ContDiff NumberField
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace DedekindZetaZeroFree.LargeSieve.Vendor.KernelSeparation

def phase (t x : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (x : ℂ))

def coefficient (H : ℝ × ℝ → ℂ) (t s : ℝ) : ℂ :=
  ∫ x : ℝ, ∫ y : ℝ, H (x, y) * phase (-t) x * phase (-s) y

def fourierL1 (H : ℝ × ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, ∫ s : ℝ, ‖coefficient H t s‖

def mixedDeriv (i j : ℕ) (H : ℝ × ℝ → ℂ) (x y : ℝ) : ℂ :=
  iteratedDeriv i (fun u : ℝ => iteratedDeriv j (fun v : ℝ => H (u, v)) y) x

def boxJet (R : ℝ) (H : ℝ × ℝ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
    sSup {v : ℝ | ∃ x ∈ Set.Icc (-R) R, ∃ y ∈ Set.Icc (-R) R,
      v = ‖mixedDeriv i j H x y‖}

 abbrev P := WithLp 2 (ℝ × ℝ)
 def f (H : ℝ × ℝ → ℂ) : P → ℂ := fun p => H p.ofLp
 def sm (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) : 𝓢(P, ℂ) :=
  (hc.comp_homeomorph (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toHomeomorph).toSchwartzMap
    (hH.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).contDiff)
private lemma ff (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) : Integrable (𝓕 (f H)) := by
  exact ((𝓕 (sm H hH hc) : 𝓢(P,ℂ))).integrable
private lemma np (t x : ℝ) : ‖phase t x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp
private lemma kernel (p q : P) :
    Complex.exp (↑(-2 * Real.pi * inner ℝ p q) * Complex.I) =
      phase (-q.ofLp.1) p.ofLp.1 * phase (-q.ofLp.2) p.ofLp.2 := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  simp only [WithLp.prod_inner_apply, Real.inner_apply]
  push_cast
  ring
private lemma coef (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (t s : ℝ) :
    coefficient H t s = 𝓕 (f H) ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm (t,s)) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ
  have he : MeasurePreserving (e : P → ℝ × ℝ) volume (volume.prod volume) :=
    WithLp.volume_preserving_ofLp ℝ ℝ
  have hi : Integrable (fun p : ℝ × ℝ => H p * phase (-t) p.1 * phase (-s) p.2)
      (volume.prod volume) := by
    refine Integrable.mono' (hH.continuous.integrable_of_hasCompactSupport hc).norm ?_ ?_
    · apply Continuous.aestronglyMeasurable
      dsimp [phase]
      fun_prop
    · filter_upwards with p
      simp only [norm_mul, np, mul_one, le_refl]
  rw [Real.fourier_eq']
  simp_rw [kernel]
  simp only [smul_eq_mul]
  change coefficient H t s = ∫ p : P, (phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2) * H p.ofLp
  rw [show (∫ p : P, (phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2) * H p.ofLp) =
      ∫ p : P, (fun q : ℝ × ℝ => H q * phase (-t) q.1 * phase (-s) q.2) (e p) by
    apply integral_congr_ae
    filter_upwards with p
    change phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2 * H p.ofLp =
      H p.ofLp * phase (-t) p.ofLp.1 * phase (-s) p.ofLp.2
    ring]
  rw [he.integral_comp e.toHomeomorph.measurableEmbedding (fun q => H q * phase (-t) q.1 * phase (-s) q.2), integral_prod _ hi]
  rfl
private lemma ikernel (p q : P) :
    Complex.exp (↑(2 * Real.pi * inner ℝ p q) * Complex.I) =
      phase q.ofLp.1 p.ofLp.1 * phase q.ofLp.2 p.ofLp.2 := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  simp only [WithLp.prod_inner_apply, Real.inner_apply]
  push_cast
  ring

theorem compact_smooth_fourier
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hcomp : HasCompactSupport H) :
    Integrable (fun p : ℝ × ℝ => coefficient H p.1 p.2) (volume.prod volume) ∧
    Integrable (fun t : ℝ => ∫ s : ℝ, ‖coefficient H t s‖) ∧
    0 ≤ fourierL1 H ∧
    (∀ x y : ℝ,
      Integrable (fun p : ℝ × ℝ => coefficient H p.1 p.2 * phase p.1 x * phase p.2 y)
        (volume.prod volume) ∧
      H (x, y) = ∫ t : ℝ, ∫ s : ℝ, coefficient H t s * phase t x * phase s y) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ
  have he : MeasurePreserving (e : P → ℝ × ℝ) volume (volume.prod volume) :=
    WithLp.volume_preserving_ofLp ℝ ℝ
  have eap (p : P) : e p = p.ofLp := rfl
  have esp (q : ℝ × ℝ) : (e.symm q).ofLp = q := e.apply_symm_apply q
  have eps (p : P) : e.symm p.ofLp = p := e.symm_apply_apply p
  have hint : Integrable (fun p : ℝ × ℝ => coefficient H p.1 p.2)
      (volume.prod volume) := by
    apply (he.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mp
    convert ff H hH hcomp using 1
    ext p
    change coefficient H (e p).1 (e p).2 = 𝓕 (f H) p
    rw [eap]
    have hz := coef H hH hcomp p.ofLp.1 p.ofLp.2
    change coefficient H p.ofLp.1 p.ofLp.2 = 𝓕 (f H) (e.symm p.ofLp) at hz
    simpa only [eps] using hz
  refine ⟨hint, hint.integral_norm_prod_left, ?_, fun x y => ?_⟩
  · exact integral_nonneg (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  have hbound : Integrable
      (fun p : ℝ × ℝ => coefficient H p.1 p.2 * phase p.1 x * phase p.2 y)
      (volume.prod volume) := by
    refine Integrable.mono' hint.norm ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hh : Continuous (fun p : ℝ × ℝ => coefficient H p.1 p.2) := by
        have heq : (fun p : ℝ × ℝ => coefficient H p.1 p.2) = (𝓕 (sm H hH hcomp) : 𝓢(P,ℂ)) ∘ e.symm := by
          funext p
          exact coef H hH hcomp p.1 p.2
        rw [heq]
        exact (𝓕 (sm H hH hcomp) : 𝓢(P,ℂ)).continuous.comp e.symm.continuous
      dsimp [phase]
      fun_prop
    · filter_upwards with p
      simp only [norm_mul, np, mul_one, le_refl]
  refine ⟨hbound, ?_⟩
  have hinv : 𝓕⁻ (𝓕 (f H)) = f H :=
    (sm H hH hcomp).continuous.fourierInv_fourier_eq (sm H hH hcomp).integrable (ff H hH hcomp)
  have hfwd : Integrable (fun p : ℝ × ℝ =>
      coefficient H p.1 p.2 * phase p.1 x * phase p.2 y) (volume.prod volume) := hbound
  rw [← integral_prod _ hfwd]
  have htw : (fun p : ℝ × ℝ => coefficient H p.1 p.2 * phase p.1 x * phase p.2 y) ∘ e =
      fun p : P => (𝓕 (f H)) p * Complex.exp (↑(2 * Real.pi * inner ℝ p (e.symm (x,y))) * Complex.I) := by
    funext p
    simp only [Function.comp_apply]
    have hp : 𝓕 (f H) p = coefficient H p.ofLp.1 p.ofLp.2 := by
      have hz := (coef H hH hcomp p.ofLp.1 p.ofLp.2).symm
      change 𝓕 (f H) (e.symm p.ofLp) = coefficient H p.ofLp.1 p.ofLp.2 at hz
      simpa only [eps] using hz
    rw [hp, ikernel]
    rw [eap, esp]
    have hp1 : phase p.ofLp.1 x = phase x p.ofLp.1 := by unfold phase; congr 1; ring
    have hp2 : phase p.ofLp.2 y = phase y p.ofLp.2 := by unfold phase; congr 1; ring
    rw [hp1, hp2, mul_assoc]
  rw [← he.integral_comp e.toHomeomorph.measurableEmbedding _]
  change H (x,y) = ∫ p : P, ((fun p : ℝ × ℝ => coefficient H p.1 p.2 * phase p.1 x * phase p.2 y) ∘ e) p
  rw [htw]
  have hz := congrFun hinv (e.symm (x,y))
  rw [Real.fourierInv_eq'] at hz
  convert hz.symm using 1
  · change H (x,y) = H (e.symm (x,y)).ofLp
    rw [esp]
  · congr 1
    ext p
    simp only [smul_eq_mul, mul_comm]

theorem fourierL1_le_boxJet (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ × ℝ → ℂ,
      ContDiff ℝ ∞ H →
      Function.support H ⊆ Set.Icc (-R) R ×ˢ Set.Icc (-R) R →
      fourierL1 H ≤ C * boxJet R H := by
  obtain ⟨C, hC, hbound⟩ := DedekindZetaZeroFree.LargeSieve.Vendor.BoxFourier.coefficient_box_bound R hR
  refine ⟨C * Real.pi ^ 2, mul_pos hC (sq_pos_of_pos Real.pi_pos), ?_⟩
  intro H hH hsupp
  have hpoint (t s : ℝ) : ‖coefficient H t s‖ ≤
      (C * boxJet R H * (1 + t ^ 2)⁻¹) * (1 + s ^ 2)⁻¹ := by
    have hp : 0 < (1 + t ^ 2) * (1 + s ^ 2) := by positivity
    have h := hbound H hH hsupp t s
    change (1 + t ^ 2) * (1 + s ^ 2) * ‖coefficient H t s‖ ≤ C * boxJet R H at h
    have hd : ‖coefficient H t s‖ ≤ C * boxJet R H / ((1 + t ^ 2) * (1 + s ^ 2)) :=
      (le_div_iff₀ hp).mpr (by nlinarith [h])
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hd
  have hinner (t : ℝ) : (∫ s : ℝ, ‖coefficient H t s‖) ≤
      C * boxJet R H * (1 + t ^ 2)⁻¹ * Real.pi := by
    calc
      _ ≤ ∫ s : ℝ, (C * boxJet R H * (1 + t ^ 2)⁻¹) * (1 + s ^ 2)⁻¹ := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => norm_nonneg _))
          (integrable_inv_one_add_sq.const_mul _) (Filter.Eventually.of_forall (hpoint t))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  calc
    fourierL1 H ≤ ∫ t : ℝ, C * boxJet R H * (1 + t ^ 2)⁻¹ * Real.pi := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun t => integral_nonneg (fun s => norm_nonneg _)))
        ((integrable_inv_one_add_sq.const_mul _).mul_const _)
        (Filter.Eventually.of_forall hinner)
    _ = (C * Real.pi ^ 2) * boxJet R H := by
      rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]
      ring

def logLocalized (χ ψ : ℝ → ℂ) (K : ℝ → ℂ) (scale : ℝ) (p : ℝ × ℝ) : ℂ :=
  χ p.1 * ψ p.2 * K (scale * Real.exp ((p.1 + p.2) / 2))

theorem logLocalized_uniform_fourier_bound
    (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (χ ψ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hsχ : Function.support χ ⊆ Set.Icc (-R) R)
    (hsψ : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ → ℂ) (B : ℝ),
      ContDiffOn ℝ ∞ K (Set.Ioi 0) → 0 ≤ B →
      (∀ j ≤ 4, ∀ x : ℝ, 0 < x → ‖DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter j K x‖ ≤ B * Real.rpow x (-c)) →
      ∀ scale : ℝ, 0 < scale →
        ContDiff ℝ ∞ (logLocalized χ ψ K scale) ∧
        Function.support (logLocalized χ ψ K scale) ⊆ Set.Icc (-R) R ×ˢ Set.Icc (-R) R ∧
        boxJet R (logLocalized χ ψ K scale) ≤ C * B * Real.rpow scale (-c) ∧
        fourierL1 (logLocalized χ ψ K scale) ≤ C * B * Real.rpow scale (-c) := by
  obtain ⟨A, hA, hderiv⟩ := DedekindZetaZeroFree.LargeSieve.KernelSeparation.logLocalized_mixed_derivative_bound
    R c hR hc χ ψ hχ hψ
  obtain ⟨F, hF, hfourier⟩ := fourierL1_le_boxJet R hR
  let C := max (9 * A) (F * (9 * A))
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro K B hK hB hEuler scale hscale
  obtain ⟨hsmooth, hsupp⟩ := DedekindZetaZeroFree.LargeSieve.KernelSeparation.logLocalized_smooth_support
    R χ ψ K hχ hψ hsχ hsψ hK scale hscale
  change ContDiff ℝ ∞ (logLocalized χ ψ K scale) at hsmooth
  change Function.support (logLocalized χ ψ K scale) ⊆
    Set.Icc (-R) R ×ˢ Set.Icc (-R) R at hsupp
  have hjet : boxJet R (logLocalized χ ψ K scale) ≤
      (9 * A) * B * Real.rpow scale (-c) := by
    have hj := DedekindZetaZeroFree.LargeSieve.KernelSeparation.boxJet_le_nine_mul R hR.le
      (DedekindZetaZeroFree.LargeSieve.KernelSeparation.logLocalized χ ψ K scale)
      (A * B * Real.rpow scale (-c))
      (mul_nonneg (mul_nonneg hA.le hB) (Real.rpow_nonneg hscale.le _))
      (hderiv K B hK hB hEuler scale hscale)
    change boxJet R (logLocalized χ ψ K scale) ≤
      9 * (A * B * Real.rpow scale (-c)) at hj
    simpa only [mul_assoc] using hj
  have hnonneg : 0 ≤ B * Real.rpow scale (-c) :=
    mul_nonneg hB (Real.rpow_nonneg hscale.le _)
  refine ⟨hsmooth, hsupp, ?_, ?_⟩
  · exact hjet.trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (le_max_left (9 * A) (F * (9 * A))) hnonneg)
  · calc
      fourierL1 (logLocalized χ ψ K scale) ≤ F * boxJet R (logLocalized χ ψ K scale) :=
        hfourier _ hsmooth hsupp
      _ ≤ F * ((9 * A) * B * Real.rpow scale (-c)) :=
        mul_le_mul_of_nonneg_left hjet hF.le
      _ ≤ C * B * Real.rpow scale (-c) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (le_max_right (9 * A) (F * (9 * A))) hnonneg

end DedekindZetaZeroFree.LargeSieve.Vendor.KernelSeparation

end

end
