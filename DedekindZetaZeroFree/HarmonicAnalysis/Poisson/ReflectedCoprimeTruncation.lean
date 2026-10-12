module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.ReflectedPrimalTail
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ReflectedSmallDualTail
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedDualCutoffTail
public import DedekindZetaZeroFree.Nonvanishing.Mellin.ReflectedSquareEulerJets

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open MeasureTheory Filter

namespace DedekindZetaZeroFree.LargeSieve.ReflectedCoprimeTruncation

variable {F : Type} [Field F] [NumberField F]

def mass (W : ℝ → ℂ) : ℂ := ∫ t in Set.Ioi (0 : ℝ), W (t ^ 2)

def rho (m : Ideal (𝓞 F)) : ℂ :=
  ∑ d ∈ idealDivisors m,
    (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ)

def originCoefficient (data : PrincipalHeckeData F) (W : ℝ → ℂ) : ℂ :=
  -(2 : ℂ) ^ (principalComplexPlaces F - 1) * SquareSecondPass.kappa data * mellin W 1

def originalSum (F : Type) [Field F] [NumberField F]
    (W : ℝ → ℂ) (T : ℝ) (m : Ideal (𝓞 F)) : ℂ :=
  ∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ I ⊔ m = ⊤ then
    SquareSecondPass.weight (principalDiscriminant F) (principalComplexPlaces F) W
      ((Ideal.absNorm I : ℝ) / T) else 0

def truncatedMainTerm (data : PrincipalHeckeData F) (W : ℝ → ℂ)
    (m : Ideal (𝓞 F)) (T Y Z L : ℝ) : ℂ :=
  SquareSecondPass.kappa data * (T : ℂ) * mass W * rho m -
  SquareSecondPass.kappa data * (T : ℂ) * mass W *
    (∑ d ∈ (idealDivisors m).filter (fun d => Z < (Ideal.absNorm d : ℝ)),
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ)) +
  originCoefficient data W *
    (∑ d ∈ (idealDivisors m).filter (fun d => (Ideal.absNorm d : ℝ) ≤ Z),
      (UniqueFactorizationMonoid.moebius d : ℂ)) +
  ∑ d ∈ (idealDivisors m).filter
      (fun d => Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z),
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      ((T : ℂ) / (Ideal.absNorm d : ℂ)) *
      ∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
        SquareSecondPass.reflectedTransform (principalDiscriminant F)
          (principalComplexPlaces F) W
          (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))

def remainder (F : Type) [Field F] [NumberField F]
    (W : ℝ → ℂ) (m : Ideal (𝓞 F)) (T Y Z L : ℝ) : ℂ :=
  ReflectedTails.primalTail F
    (SquareSecondPass.weight (principalDiscriminant F) (principalComplexPlaces F) W) T
    ((idealDivisors m).filter (fun d => Z < (Ideal.absNorm d : ℝ)))
    (fun d => (UniqueFactorizationMonoid.moebius d : ℂ)) +
  ReflectedTails.smallDualTail F
    (SquareSecondPass.reflectedTransform (principalDiscriminant F)
      (principalComplexPlaces F) W) T
    ((idealDivisors m).filter (fun d => (Ideal.absNorm d : ℝ) ≤ Y))
    (fun d => (UniqueFactorizationMonoid.moebius d : ℂ)) +
  ∑ d ∈ (idealDivisors m).filter
      (fun d => Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z),
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      ((T : ℂ) / (Ideal.absNorm d : ℂ)) *
      ∑' b : Ideal (𝓞 F), if b ≠ ⊥ ∧ L < (Ideal.absNorm b : ℝ) then
        SquareSecondPass.reflectedTransform (principalDiscriminant F)
          (principalComplexPlaces F) W
          (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ)) else 0

theorem mass_eq_half_mellin (W : ℝ → ℂ) (a b : ℝ)
    (hW : ContDiff ℝ ∞ W) (hsupp : Function.support W ⊆ Set.Icc a b)
    (ha : 0 < a) (hab : a < b) :
    IntegrableOn (fun t : ℝ => W (t ^ 2)) (Set.Ioi 0) ∧
      mass W = (1 / 2 : ℂ) * mellin W (1 / 2) := by
  have hc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨compact_comp_sq_integrableOn W hW hc, ?_⟩
  have hm : mass W = mellin (fun t : ℝ => W (t ^ (2 : ℝ))) (1 : ℂ) := by
    simp only [mass, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    rw [sub_self, Complex.cpow_zero, one_smul, Real.rpow_ofNat]
  rw [hm, mellin_comp_rpow W (1 : ℂ) (2 : ℝ)]
  norm_num

theorem kernel_eq_mellinInv (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (a b : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b)
    (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    Complex.VerticalIntegrable (reflectedSquareSpectrum D r W) c ∧
      SquareSecondPass.reflectedTransform D r W x =
        mellinInv c (reflectedSquareSpectrum D r W) x := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hCpos, hC⟩ :=
      reflectedSquareSpectrum_rapid_bound D r W a b c c 2 hD hr hW hsupp ha hab hc (le_refl c)
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I))
        volume := by
      have hdiff : DifferentiableOn ℂ (reflectedSquareSpectrum D r W) {s : ℂ | 0 < s.re} :=
        reflectedSquareSpectrum_differentiableOn D r W a b hD hr hW hsupp ha hab
      have hcont : Continuous
          (fun t : ℝ => reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)) :=
        hdiff.continuousOn.comp_continuous (by fun_prop) (fun t => by simp [hc])
      exact hcont.aestronglyMeasurable
    have hgi : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) volume :=
      integrable_inv_one_add_sq.const_mul C
    rw [Complex.VerticalIntegrable]
    refine Integrable.mono' hgi hmeas ?_
    filter_upwards with t
    have h := hC c (Set.left_mem_Icc.mpr (le_refl c)) t
    have h1 : (1 : ℝ) + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t]
    have hpos : 0 < (1 : ℝ) + t ^ 2 := by positivity
    have hpos2 : 0 < (1 + |t|) ^ 2 := by positivity
    have hle : ‖reflectedSquareSpectrum D r W ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C / (1 + |t|) ^ 2 := (le_div_iff₀ hpos2).mpr (by rw [mul_comm]; exact h)
    have hcmp : C / (1 + |t|) ^ 2 ≤ C * (1 + t ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) hCpos.le
    exact hle.trans hcmp
  · have := EulerIter_reflectedSquareTransform_eq_mellinInv D r W a b hD hr hW hsupp ha hab
      0 c x hc hx
    simp only [Vendor.EulerIter_zero] at this
    rw [this]
    have hfun : (fun s : ℂ => (-s) ^ (0 : ℕ) * reflectedSquareSpectrum D r W s) =
        reflectedSquareSpectrum D r W := by
      funext s; simp
    rw [hfun]

theorem absolutely_summable (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (W : ℝ → ℂ) (a b : ℝ)
    (hW : ContDiff ℝ ∞ W) (hsupp : Function.support W ⊆ Set.Icc a b)
    (ha : 0 < a) (hab : a < b) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (T : ℝ) (hT : 0 < T) :
    Summable (fun I : Ideal (𝓞 F) => if I ≠ ⊥ ∧ I ⊔ m = ⊤ then
      ‖SquareSecondPass.weight (principalDiscriminant F) (principalComplexPlaces F) W
        ((Ideal.absNorm I : ℝ) / T)‖ else 0) ∧
    ∀ d ∈ idealDivisors m,
      Summable (fun I : Ideal (𝓞 F) =>
        ‖ReflectedTails.primalSummand F
          (SquareSecondPass.weight (principalDiscriminant F) (principalComplexPlaces F) W)
          T d I‖) ∧
      Summable (fun I : Ideal (𝓞 F) =>
        ‖ReflectedTails.dualSummand F
          (SquareSecondPass.reflectedTransform (principalDiscriminant F)
            (principalComplexPlaces F) W) T d I‖) := by
  have hc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hs (X : ℝ) (hX : 0 < X) :=
    (SquarePoisson.reflected_and_ideal_estimates
      (principalDiscriminant F) (principalComplexPlaces F) W
      (principalDiscriminant_pos F) (principalComplexPlaces_pos F hF) hW hc).2 F X hX
  refine ⟨Summable.of_nonneg_of_le (fun I => by split_ifs <;> positivity) ?_ (hs T hT).1, ?_⟩
  · intro I
    by_cases hI : I = ⊥
    · simp [hI]
    · simp only [if_neg hI]
      split_ifs <;> try simp
      exact le_refl _
  · intro d hd
    have hd0 : 0 < (Ideal.absNorm d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h =>
        ne_bot_of_mem_idealDivisors hd (Ideal.absNorm_eq_zero_iff.mp h))
    have hscale := hs (T / (Ideal.absNorm d : ℝ)) (div_pos hT hd0)
    constructor
    · convert hscale.1 using 1
      funext I
      simp only [ReflectedTails.primalSummand]
      split_ifs <;> try simp only [norm_zero]
      congr 2
      field_simp
    · convert hscale.2 using 1
      funext I
      simp only [ReflectedTails.dualSummand]
      split_ifs <;> try simp only [norm_zero]
      congr 2
      ring

private lemma dual_split (F : Type) [Field F] [NumberField F]
    (k : ℝ → ℂ) (T L : ℝ) (d : Ideal (𝓞 F))
    (hs : Summable (ReflectedTails.dualSummand F k T d)) :
    (∑' b, ReflectedTails.dualSummand F k T d b) =
      (∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
        k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))) +
      ∑' b, ReflectedTails.dualCutoffSummand F k T L d b := by
  classical
  let s := (boundedNormIdeals F L).filter (fun b => b ≠ ⊥)
  have heq : (fun b => ReflectedTails.dualCutoffSummand F k T L d b) =
      (fun b => if b ∈ s then 0 else ReflectedTails.dualSummand F k T d b) := by
    funext b
    simp only [s, Finset.mem_filter, mem_boundedNormIdeals,
      ReflectedTails.dualCutoffSummand, ReflectedTails.dualSummand]
    by_cases hb : b = ⊥ <;> by_cases hL : (Ideal.absNorm b : ℝ) ≤ L <;>
      simp [hb, hL, not_lt_of_ge, lt_of_not_ge]
  have ht : (∑' b, if b ∈ s then 0 else ReflectedTails.dualSummand F k T d b) =
      ∑' b : {b // b ∉ s}, ReflectedTails.dualSummand F k T d b := by
    convert (tsum_subtype ({b | b ∉ s} : Set (Ideal (𝓞 F)))
      (ReflectedTails.dualSummand F k T d)).symm using 1 <;>
      try simp only [Set.indicator, Set.mem_setOf_eq, ite_not]
    rfl
  rw [heq, ht, ← hs.sum_add_tsum_subtype_compl s]
  congr 1
  exact Finset.sum_congr rfl (fun b hb => by
    simp [ReflectedTails.dualSummand, (Finset.mem_filter.mp hb).2])

private lemma sum_cut {α : Type*} (s : Finset α) (n : α → ℝ) (Z : ℝ)
    (f : α → ℂ) :
    ∑ d ∈ s, f d = (∑ d ∈ s.filter (fun d => n d ≤ Z), f d) +
      ∑ d ∈ s.filter (fun d => Z < n d), f d := by
  simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not s (fun d => n d ≤ Z) f).symm

private lemma sum_band {α : Type*} (s : Finset α) (n : α → ℝ) (Y Z : ℝ)
    (hYZ : Y ≤ Z) (f : α → ℂ) :
    (∑ d ∈ s.filter (fun d => n d ≤ Z), f d) =
      (∑ d ∈ s.filter (fun d => n d ≤ Y), f d) +
      ∑ d ∈ s.filter (fun d => Y < n d ∧ n d ≤ Z), f d := by
  have h := sum_cut (s.filter (fun d => n d ≤ Z)) n Y f
  have h₁ : (s.filter (fun d => n d ≤ Z)).filter (fun d => n d ≤ Y) =
      s.filter (fun d => n d ≤ Y) := by
    ext d; simp only [Finset.mem_filter]; constructor
    · tauto
    · intro hd; exact ⟨⟨hd.1, hd.2.trans hYZ⟩, hd.2⟩
  have h₂ : (s.filter (fun d => n d ≤ Z)).filter (fun d => Y < n d) =
      s.filter (fun d => Y < n d ∧ n d ≤ Z) := by
    ext d; simp only [Finset.mem_filter]; tauto
  rwa [h₁, h₂] at h

lemma originalSum_eq_truncatedMainTerm_add_remainder
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (W : ℝ → ℂ) (a b : ℝ) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc a b) (ha : 0 < a) (hab : a < b)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (T Y Z L : ℝ) (hT : 0 < T) (hYZ : Y ≤ Z) :
    originalSum F W T m =
      truncatedMainTerm (principalHeckeData F hF) W m T Y Z L +
      remainder F W m T Y Z L := by
  let data := principalHeckeData F hF
  let g := SquareSecondPass.weight (principalDiscriminant F) (principalComplexPlaces F) W
  let k := SquareSecondPass.reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) W
  let mu := fun d : Ideal (𝓞 F) => (UniqueFactorizationMonoid.moebius d : ℂ)
  let q := fun d : Ideal (𝓞 F) => mu d / (Ideal.absNorm d : ℂ)
  let du := fun d : Ideal (𝓞 F) => mu d * ((T : ℂ) / (Ideal.absNorm d : ℂ)) *
    ∑' I, ReflectedTails.dualSummand F k T d I
  let A := SquareSecondPass.kappa data * (T : ℂ) * mass W
  let R := originCoefficient data W
  have hc : HasCompactSupport W := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hmass := (mass_eq_half_mellin W a b hW hsupp ha hab).2
  have hfull : originalSum F W T m =
      A * (∑ d ∈ idealDivisors m, q d) + R * (∑ d ∈ idealDivisors m, mu d) +
      ∑ d ∈ idealDivisors m, du d := by
    have h := SquareSecondPass.coprime_poisson F hF W hW hc T hT m hm
    dsimp [originalSum, A, R, q, mu, du, data, k, ReflectedTails.dualSummand,
      originCoefficient, SquareSecondPass.coprimeOrigin]
    rw [hmass]
    dsimp only [SquareSecondPass.coprimeOrigin] at h
    convert h using 1 <;> ring
  have hlarge : ReflectedTails.primalTail F g T
      ((idealDivisors m).filter (fun d => Z < (Ideal.absNorm d : ℝ))) mu =
      A * (∑ d ∈ (idealDivisors m).filter (fun d => Z < (Ideal.absNorm d : ℝ)), q d) +
      R * (∑ d ∈ (idealDivisors m).filter (fun d => Z < (Ideal.absNorm d : ℝ)), mu d) +
      ∑ d ∈ (idealDivisors m).filter (fun d => Z < (Ideal.absNorm d : ℝ)), du d := by
    simp only [ReflectedTails.primalTail, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < (Ideal.absNorm d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h =>
        ne_bot_of_mem_idealDivisors (Finset.mem_filter.mp hd).1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hp := SquareSecondPass.principal_poisson F hF W hW hc
      (T / (Ideal.absNorm d : ℝ)) (div_pos hT hd0)
    have heq : (∑' I, ReflectedTails.primalSummand F g T d I) =
      ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else g ((Ideal.absNorm I : ℝ) / (T / (Ideal.absNorm d : ℝ))) := by
      apply tsum_congr; intro I; simp only [ReflectedTails.primalSummand]
      split_ifs <;> try rfl
      congr 1; field_simp
    rw [heq]
    change mu d * _ = _
    rw [show (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else g ((Ideal.absNorm I : ℝ) / (T / (Ideal.absNorm d : ℝ)))) = _ from hp]
    dsimp [A, q, R, du, data, k, ReflectedTails.dualSummand, originCoefficient]
    rw [hmass]
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    have heqdual : (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        SquareSecondPass.reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) W
          (T / (Ideal.absNorm d : ℝ) * (Ideal.absNorm I : ℝ))) =
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        SquareSecondPass.reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) W
          (T * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ)) := by
      apply tsum_congr; intro I; congr 1; congr 1; ring
    rw [heqdual]; ring
  have hdusplit : (∑ d ∈ (idealDivisors m).filter
      (fun d => Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z), du d) =
      (∑ d ∈ (idealDivisors m).filter
        (fun d => Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z),
        mu d * ((T : ℂ) / (Ideal.absNorm d : ℂ)) *
          ∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
            k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))) +
      ReflectedTails.dualCutoffTail F k T L
        ((idealDivisors m).filter (fun d => Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z)) mu := by
    simp only [ReflectedTails.dualCutoffTail, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d hd
    have hs := ((absolutely_summable F hF W a b hW hsupp ha hab m hm T hT).2
      d (Finset.mem_filter.mp hd).1).2.of_norm
    dsimp [du]
    rw [dual_split F k T L d hs]
    ring
  have hq := sum_cut (idealDivisors m) (fun d => (Ideal.absNorm d : ℝ)) Z q
  have hmu := sum_cut (idealDivisors m) (fun d => (Ideal.absNorm d : ℝ)) Z mu
  have hdu := sum_cut (idealDivisors m) (fun d => (Ideal.absNorm d : ℝ)) Z du
  have hband := sum_band (idealDivisors m) (fun d => (Ideal.absNorm d : ℝ)) Y Z hYZ du
  rw [hfull, hmu, hdu, hband, hdusplit]
  change _ = A * (∑ d ∈ idealDivisors m, q d) - A * _ + R * _ + _ +
    (ReflectedTails.primalTail F g T _ mu + ReflectedTails.smallDualTail F k T _ mu + _)
  rw [hlarge]
  simp only [ReflectedTails.smallDualTail, Complex.ofReal_div, Complex.ofReal_natCast]
  dsimp only [ReflectedTails.dualCutoffTail, ReflectedTails.dualCutoffSummand, du, q, mu, k]
  simp only [Complex.ofReal_natCast]
  ring

end DedekindZetaZeroFree.LargeSieve.ReflectedCoprimeTruncation

end
