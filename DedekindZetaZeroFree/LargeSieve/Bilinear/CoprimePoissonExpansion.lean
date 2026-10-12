module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DiagonalContribution
public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEndpoints
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Remainders.PairEnergyAndUniformTailBounds

@[expose] public section

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

open ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def originalBlock (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ a ∈ C.originalRows B unit,
      C.primitive p hp a * squareWeightSeries (c * C.d) (p.1 * p.2) C.source C.M a

def originalTailBlock (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ a ∈ C.originalRows B unit,
      C.primitive p hp a * C.originalRemainder ((c * C.d) * (p.1 * p.2))
        (Real.sqrt (C.M / norm a)) (C.Y2 B) (C.Z2 B) C.L2

private lemma compact_sq (h : ℝ → ℂ) (hc : HasCompactSupport h) :
    HasCompactSupport (fun t : ℝ => h (t ^ 2)) := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℝ) |>.mp hc.isBounded
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(|r| + 1)) (|r| + 1)) isCompact_Icc
  intro t ht
  have hmem : t ^ 2 ∈ tsupport h := subset_tsupport h ht
  have hbound : |t ^ 2| ≤ r := by
    have := hr hmem
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  have : t ^ 2 ≤ |r| := le_trans (le_abs_self _) (hbound.trans (le_abs_self _))
  constructor <;> nlinarith [sq_nonneg (t + (|r| + 1)),
    sq_nonneg (t - (|r| + 1)), abs_nonneg r]

private lemma rho_eq_divisor_sum (j : Ideal (𝓞 F)) (hj : j ≠ ⊥) :
    (sigma4Rho j : ℂ) = ∑ d ∈ idealDivisors j,
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) := by
  have he := idealEulerDeletion_eq_prod j hj 1
  simp only [idealEulerDeletion, Complex.cpow_neg_one, ← div_eq_mul_inv] at he
  rw [he, sigma4Rho, badPrimes]
  push_cast
  simp only [one_div]

private lemma sum_cut {α : Type*} (s : Finset α) (n : α → ℝ) (Z : ℝ)
    (f : α → ℂ) :
    ∑ d ∈ s, f d = (∑ d ∈ s.filter (fun d => n d ≤ Z), f d) +
      ∑ d ∈ s.filter (fun d => Z < n d), f d := by
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not s (fun d => n d ≤ Z) f).symm

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

private lemma dual_split (k : ℝ → ℂ) (T L : ℝ) (d : Ideal (𝓞 F))
    (hs : Summable (ReflectedTails.dualSummand F k T d)) :
    (∑' b, ReflectedTails.dualSummand F k T d b) =
      (∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
        k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))) +
      ∑' b, ReflectedTails.dualCutoffSummand F k T L d b := by
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

private lemma row_identity (C : Context Q) (m f a : Ideal (𝓞 F))
    (hmf : m * f ≠ ⊥) (hM : 0 < C.M) (ha : 0 < norm a)
    (Y Z L : ℝ) (hYZ : Y ≤ Z) :
    squareWeightSeries m f C.source C.M a =
      C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass * (sigma4Rho (m * f) : ℂ) -
      C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass * Context.largeDensity (m * f) Z +
      Context.middle C.originalKernel (m * f) (Real.sqrt (C.M / norm a)) Y Z L +
      C.originalRemainder (m * f) (Real.sqrt (C.M / norm a)) Y Z L := by
  let T := Real.sqrt (C.M / norm a)
  let g := fun x : ℝ => C.source (x ^ 2)
  let k := C.originalKernel
  let mu := fun d : Ideal (𝓞 F) => (UniqueFactorizationMonoid.moebius d : ℂ)
  let q := fun d : Ideal (𝓞 F) => mu d / (Ideal.absNorm d : ℂ)
  let du := fun d : Ideal (𝓞 F) => mu d * (T / ExplicitTerms.norm d : ℂ) *
    ∑' I, ReflectedTails.dualSummand F k T d I
  let A := C.kappa * (T : ℂ) * C.mass
  have hT : 0 < T := Real.sqrt_pos.mpr (div_pos hM ha)
  have hg : ContDiff ℝ ∞ g := C.source_smooth.comp (contDiff_id.pow 2)
  have hc : HasCompactSupport g := compact_sq C.source C.source_compact
  have hmass : Vendor.originMellinH g 1 = C.mass := by
    rw [Vendor.originMellinH, Vendor.Gammaℂ_mul_originMellinQ_eq_mellin g hg hc 1 (by norm_num)]
    simp [mellin, Context.mass, g]
  have hfinite : ∀ u : ℝ, 0 < u → Function.HasFiniteSupport
      (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℂ) else g ((Ideal.absNorm I : ℝ) / u)) := by
    intro u hu
    have hh := idealMellinWeight_hasFiniteSupport (F := F) (fun _ => (1 : ℂ)) hc hu
    have heq : idealMellinWeight (fun _ : Ideal (𝓞 F) => (1 : ℂ)) g u =
        (fun I => if I = ⊥ then 0 else g ((Ideal.absNorm I : ℝ) / u)) := by
      funext I; simp [idealMellinWeight]
    rw [heq] at hh
    exact hh
  have hscale : ∀ u : ℝ, 0 < u →
      (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else g ((Ideal.absNorm I : ℝ) / u)) =
        C.kappa * (u : ℂ) * C.mass + (u : ℂ) *
          ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else k (u * (Ideal.absNorm I : ℝ)) := by
    intro u hu
    rw [tsum_eq_finsum (hfinite u hu)]
    have hp := (principalPoisson F C.hF g hg hc u hu).2.2
    change (∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else g ((Ideal.absNorm I : ℝ) / u)) =
      C.kappa * (u : ℂ) * Vendor.originMellinH g 1 -
      (if principalComplexPlaces F = 1 then principalPoleCoefficient F C.hF * g 0 / 2 else 0) +
      (u : ℂ) * ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else k (u * (Ideal.absNorm I : ℝ)) at hp
    simpa [hmass, g, C.source_zero] using hp
  have hsdual : ∀ d ∈ idealDivisors (m * f),
      Summable (ReflectedTails.dualSummand F k T d) := by
    intro d hd
    have hdpos : 0 < ExplicitTerms.norm d := by
      change 0 < (Ideal.absNorm d : ℝ)
      exact_mod_cast Nat.pos_of_ne_zero (fun h =>
        ne_bot_of_mem_idealDivisors hd (Ideal.absNorm_eq_zero_iff.mp h))
    have hp := (principalPoisson F C.hF g hg hc
      (T / ExplicitTerms.norm d) (div_pos hT hdpos)).2.1
    change Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then 0 else
      k (T / ExplicitTerms.norm d * (Ideal.absNorm I : ℝ))) at hp
    convert hp using 1
    funext I
    simp only [ReflectedTails.dualSummand]
    split_ifs <;> try rfl
    congr 1
    dsimp only [ExplicitTerms.norm]
    ring
  have hfull : squareWeightSeries m f C.source C.M a =
      A * (∑ d ∈ idealDivisors (m * f), q d) +
        ∑ d ∈ idealDivisors (m * f), du d := by
    have heq : ∀ I : Ideal (𝓞 F),
        (Ideal.absNorm a : ℝ) * (Ideal.absNorm I : ℝ) ^ 2 / C.M =
          ((Ideal.absNorm I : ℝ) / T) ^ 2 := by
      intro I
      rw [div_pow, Real.sq_sqrt (le_of_lt (div_pos hM ha))]
      change (Ideal.absNorm a : ℝ) * (Ideal.absNorm I : ℝ) ^ 2 / C.M =
        (Ideal.absNorm I : ℝ) ^ 2 / (C.M / (Ideal.absNorm a : ℝ))
      field_simp
      <;> ring
    have hcopfinite : Function.HasFiniteSupport (fun I : Ideal (𝓞 F) =>
        if I ≠ ⊥ ∧ I ⊔ (m * f) = ⊤ then g ((Ideal.absNorm I : ℝ) / T) else 0) := by
      apply (hfinite T hT).subset
      intro I hI
      simp only [Function.mem_support, ne_eq] at hI ⊢
      by_cases hb : I = ⊥
      · simp [hb] at hI
      · by_cases hcop : I ⊔ (m * f) = ⊤
        · simpa [hb, hcop] using hI
        · simp [hcop] at hI
    rw [squareWeightSeries]
    simp_rw [heq]
    change (∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ I ⊔ (m * f) = ⊤ then
      g ((Ideal.absNorm I : ℝ) / T) else 0) = _
    rw [tsum_eq_finsum hcopfinite]
    have hp := poissonCoprimeExact F C.hF g hg hc T hT (m * f) hmf
    simp only [g, zero_pow (by decide : 2 ≠ 0), C.source_zero, mul_zero,
      zero_mul, add_zero] at hp
    rw [hp]
    change C.kappa * (T : ℂ) * Vendor.originMellinH g 1 *
        (∑ d ∈ idealDivisors (m * f), q d) +
        (∑ d ∈ idealDivisors (m * f), mu d * ((T : ℂ) / (Ideal.absNorm d : ℂ)) *
          ∑' I, ReflectedTails.dualSummand F k T d I) = _
    rw [hmass]
    rfl
  have hlarge : ReflectedTails.primalTail F g T
      ((idealDivisors (m * f)).filter (fun d => Z < ExplicitTerms.norm d)) mu =
      A * (∑ d ∈ (idealDivisors (m * f)).filter (fun d => Z < ExplicitTerms.norm d), q d) +
      ∑ d ∈ (idealDivisors (m * f)).filter (fun d => Z < ExplicitTerms.norm d), du d := by
    simp only [ReflectedTails.primalTail, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < ExplicitTerms.norm d := by
      change 0 < (Ideal.absNorm d : ℝ)
      exact_mod_cast Nat.pos_of_ne_zero (fun h =>
        ne_bot_of_mem_idealDivisors (Finset.mem_filter.mp hd).1 (Ideal.absNorm_eq_zero_iff.mp h))
    have heq : (∑' I, ReflectedTails.primalSummand F g T d I) =
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          g ((Ideal.absNorm I : ℝ) / (T / ExplicitTerms.norm d)) := by
      apply tsum_congr; intro I
      simp only [ReflectedTails.primalSummand]
      split_ifs <;> try rfl
      congr 1
      dsimp only [ExplicitTerms.norm]
      field_simp
    rw [heq, hscale _ (div_pos hT hdpos)]
    dsimp [A, q, du, ReflectedTails.dualSummand]
    have heqdual : (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        k (T / ExplicitTerms.norm d * (Ideal.absNorm I : ℝ))) =
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          k (T * (Ideal.absNorm I : ℝ) / ExplicitTerms.norm d) := by
      apply tsum_congr; intro I
      split_ifs <;> try rfl
      congr 1; ring
    rw [heqdual]
    dsimp only [ExplicitTerms.norm]
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  have hdusplit : (∑ d ∈ (idealDivisors (m * f)).filter
      (fun d => Y < ExplicitTerms.norm d ∧ ExplicitTerms.norm d ≤ Z), du d) =
      Context.middle k (m * f) T Y Z L +
      ReflectedTails.dualCutoffTail F k T L
        ((idealDivisors (m * f)).filter
          (fun d => Y < ExplicitTerms.norm d ∧ ExplicitTerms.norm d ≤ Z)) mu := by
    unfold Context.middle ReflectedTails.dualCutoffTail
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [du]
    rw [dual_split k T L d (hsdual d (Finset.mem_filter.mp hd).1)]
    change mu d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
      ((∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
        k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))) + _) =
      (UniqueFactorizationMonoid.moebius d : ℂ) * (T / (Ideal.absNorm d : ℝ) : ℂ) *
        (∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
          k ((Ideal.absNorm b : ℝ) * T / (Ideal.absNorm d : ℝ))) + _
    have heq : (∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
        k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))) =
        ∑ b ∈ (boundedNormIdeals F L).filter (fun b => b ≠ ⊥),
          k ((Ideal.absNorm b : ℝ) * T / (Ideal.absNorm d : ℝ)) := by
      apply Finset.sum_congr rfl; intro b _; rw [mul_comm T]
    rw [heq]
    dsimp [mu]; ring
  have hdu := sum_cut (idealDivisors (m * f)) (fun d => ExplicitTerms.norm d) Z du
  have hband := sum_band (idealDivisors (m * f)) (fun d => ExplicitTerms.norm d) Y Z hYZ du
  rw [hfull, hdu, hband, hdusplit, rho_eq_divisor_sum (m * f) hmf]
  change _ = A * _ - A * _ + Context.middle k (m * f) T Y Z L +
    (ReflectedTails.primalTail F g T _ mu + ReflectedTails.smallDualTail F k T _ mu + _)
  rw [hlarge]
  unfold Context.largeDensity ReflectedTails.smallDualTail
  change _ = A * (∑ d ∈ idealDivisors (m * f), q d) -
    A * (∑ d ∈ (idealDivisors (m * f)).filter (fun d => Z < ExplicitTerms.norm d), q d) +
    Context.middle k (m * f) T Y Z L +
    (A * (∑ d ∈ (idealDivisors (m * f)).filter (fun d => Z < ExplicitTerms.norm d), q d) +
      (∑ d ∈ (idealDivisors (m * f)).filter (fun d => Z < ExplicitTerms.norm d), du d) +
      (∑ d ∈ (idealDivisors (m * f)).filter (fun d => ExplicitTerms.norm d ≤ Y), du d) + _)
  ring

theorem compact_block_match (C : Context Q) (B : ℝ) (unit : Bool)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ) (hB : 0 < B) :
    originalBlock C B unit =
      Tprime C B unit - E4 C B unit + E5 C B unit + originalTailBlock C B unit := by
  have hMpos : 0 < C.M := by linarith
  have hMN : 1 ≤ C.M * C.N := one_le_mul_of_one_le_of_one_le hM hN
  have hpow : Real.rpow (C.M * C.N) (-C.δ) ≤ Real.rpow (C.M * C.N) C.δ :=
    Real.rpow_le_rpow_of_exponent_le hMN (by linarith)
  have hYZ : C.Y2 B ≤ C.Z2 B := by
    unfold Context.Y2 Context.Z2
    apply mul_le_mul
    · apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left hMpos.le (by linarith : 0 < B) (by linarith)
    · exact hpow
    · exact Real.rpow_nonneg (by linarith) _
    · exact Real.sqrt_nonneg _
  have hrow : ∀ a ∈ C.originalRows B unit, 0 < ExplicitTerms.norm a := by
    intro a ha
    cases unit
    · have hn := ((Sieve.mem_paperShell F (c * C.d) B a).mp
        (Finset.mem_filter.mp ha).1).2.2.1
      change 0 < (Ideal.absNorm a : ℝ)
      linarith
    · have ha' : a = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp ha).1
      subst a
      simp [ExplicitTerms.norm]
  have hc0 : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
  have hexp : ∀ p (hp : Context.ValidPair C p), ∀ a ∈ C.originalRows B unit,
      squareWeightSeries (c * C.d) (p.1 * p.2) C.source C.M a =
        C.kappa * (Real.sqrt (C.M / ExplicitTerms.norm a) : ℂ) * C.mass *
            (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ) -
          C.kappa * (Real.sqrt (C.M / ExplicitTerms.norm a) : ℂ) * C.mass *
            Context.largeDensity ((c * C.d) * (p.1 * p.2)) (C.Z2 B) +
          Context.middle C.originalKernel ((c * C.d) * (p.1 * p.2))
            (Real.sqrt (C.M / ExplicitTerms.norm a)) (C.Y2 B) (C.Z2 B) C.L2 +
          C.originalRemainder ((c * C.d) * (p.1 * p.2))
            (Real.sqrt (C.M / ExplicitTerms.norm a)) (C.Y2 B) (C.Z2 B) C.L2 := by
    intro p hp a ha
    exact row_identity C (c * C.d) (p.1 * p.2) a
      (mul_ne_zero (mul_ne_zero hc0 C.hd0) (mul_ne_zero hp.hu0 hp.hv0))
      hMpos (hrow a ha) _ _ _ hYZ
  unfold originalBlock Tprime E4 E5 originalTailBlock Context.pairSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with hpv
  · dsimp only
    rw [← mul_sub, ← mul_add, ← mul_add]
    congr 1
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hexp p hpv a ha]
    ring
  · simp

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

open ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma col_mem (C : Context Q) {u : Ideal (𝓞 F)}
    (h : C.d * u ∈ Sieve.paperShell F c C.N) (hg : Q.cls (C.d * u) = C.g) :
    u ∈ C.columns := by
  obtain ⟨hs, hc, hl, hr⟩ := (Sieve.mem_paperShell F c C.N _).mp h
  have hdpos : 0 < norm C.d := by
    change (0 : ℝ) < (Ideal.absNorm C.d : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp C.hd0)
  have hn : (Ideal.absNorm (C.d * u) : ℝ) = norm C.d * (Ideal.absNorm u : ℝ) := by
    simp [ExplicitTerms.norm, map_mul]
  apply Finset.mem_filter.mpr
  refine ⟨(Sieve.mem_idealAdmissibleFinset F c _ _).mpr ⟨?_, ?_, ?_⟩, h, hg⟩
  · exact hs.squarefree_of_dvd (dvd_mul_left u C.d)
  · exact top_unique (hc.symm.trans_le (sup_le_sup_right Ideal.mul_le_right c))
  · exact (le_div_iff₀ hdpos).mpr (by rw [mul_comm]; exact hn ▸ hr)

private lemma valid_of_original (C : Context Q) {u v : Ideal (𝓞 F)}
    (hu : C.d * u ∈ Sieve.paperShell F c C.N)
    (hv : C.d * v ∈ Sieve.paperShell F c C.N)
    (hne : C.d * u ≠ C.d * v) (hgcd : C.d * u ⊔ C.d * v = C.d)
    (hclass : Q.cls (C.d * u) = Q.cls (C.d * v)) : C.ValidPair (u,v) := by
  obtain ⟨hsu, hcu, -, -⟩ := (Sieve.mem_paperShell F c C.N _).mp hu
  obtain ⟨hsv, hcv, -, -⟩ := (Sieve.mem_paperShell F c C.N _).mp hv
  have hstrip := SquarefreeGcd.strip_squarefree_and_coprime hsu hsv
    (by rw [hgcd]) (by rw [hgcd])
  rw [hgcd] at hstrip
  obtain ⟨-, hus, hvs, huv, hdu, hdv⟩ := hstrip
  have huc : u ⊔ c = ⊤ := top_unique (hcu.symm.trans_le (sup_le_sup_right Ideal.mul_le_right c))
  have hvc : v ⊔ c = ⊤ := top_unique (hcv.symm.trans_le (sup_le_sup_right Ideal.mul_le_right c))
  have hduv : C.d ⊔ u * v = ⊤ := Ideal.isCoprime_iff_sup_eq.mp
    ((Ideal.isCoprime_iff_sup_eq.mpr hdu).mul_right (Ideal.isCoprime_iff_sup_eq.mpr hdv))
  have hquot : Q.cls u = Q.cls v := by
    letI := Q.instGroup
    apply mul_left_cancel (a := Q.cls C.d)
    rw [← Q.cls_mul C.d u C.hdc huc, ← Q.cls_mul C.d v C.hdc hvc]
    exact hclass
  refine ⟨SquarefreeGcd.ne_bot_of_squarefree hus, SquarefreeGcd.ne_bot_of_squarefree hvs,
    hus, hvs, huc, hvc, hsu, hsv, hcu, hcv, huv, hduv, hclass, hquot, ?_⟩
  intro htop
  have hut : u = ⊤ := top_unique (htop.symm.trans_le Ideal.mul_le_left)
  have hvt : v = ⊤ := top_unique (htop.symm.trans_le Ideal.mul_le_right)
  exact hne (by rw [hut, hvt])

private lemma original_of_valid (C : Context Q) {p : Ideal (𝓞 F) × Ideal (𝓞 F)}
    (hp : C.ValidPair p) : C.d * p.1 ≠ C.d * p.2 ∧
      C.d * p.1 ⊔ C.d * p.2 = C.d := by
  refine ⟨?_, ?_⟩
  · intro he
    have huv : p.1 = p.2 := mul_left_cancel₀ C.hd0 he
    have hut : p.1 = ⊤ := by simpa [← huv] using hp.huv
    exact hp.offDiagonal (by rw [← huv, hut, Ideal.top_mul])
  · rw [← Ideal.mul_sup, hp.huv, Ideal.mul_top]

private lemma row_zero (C : Context Q) {p : Ideal (𝓞 F) × Ideal (𝓞 F)}
    (hp : C.ValidPair p) {a : Ideal (𝓞 F)} (hac : a ⊔ c = ⊤)
    (had : a ⊔ C.d ≠ ⊤) : (Q.χ (C.d * p.1)) a = 0 := by
  have hind : C.d * p.1 ∣ Q.cond (C.d * p.1) := by
    have h := C.D.all_index_dvd (C.d * p.1) hp.hdu hp.hduc
    rw [C.core] at h
    exact (Ideal.isCoprime_iff_sup_eq.mpr hp.hduc).dvd_of_dvd_mul_right h
  apply (quadraticFamily_eq_zero_iff Q hp.hdu hp.hduc a).mpr
  right
  intro hcond
  apply had
  exact top_unique (hcond.symm.trans_le (sup_le_sup_left
    (Ideal.le_of_dvd (dvd_trans (dvd_mul_right C.d p.1) hind)) a))

private lemma weight_outside (C : Context Q) (hM : 1 ≤ C.M) {a : Ideal (𝓞 F)}
    (ha : a ∉ boundedNormIdeals F ((5 / 2) * C.M)) :
    C.source ((Ideal.absNorm a : ℝ) / C.M) = 0 := by
  apply Complex.ofReal_eq_zero.mpr
  apply C.hW.zero_outside
  intro hx
  apply ha
  apply mem_boundedNormIdeals.mpr
  have hm : 0 < C.M := lt_of_lt_of_le one_pos hM
  have := (div_le_iff₀ hm).mp hx.2
  linarith

private lemma rows_match (C : Context Q) (hM : 1 ≤ C.M)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    (∑ a ∈ Sieve.kernelRows F c C.M C.K,
      (C.W ((Ideal.absNorm a : ℝ) / C.M) : ℂ) *
        (Q.χ (C.d * p.1)) a * starRingEnd ℂ ((Q.χ (C.d * p.2)) a)) =
      S4all (c * C.d) C.source C.M (C.primitive p hp) -
        S4 c (c * C.d) C.K C.source C.M (C.primitive p hp) := by
  have hall : S4all (c * C.d) C.source C.M (C.primitive p hp) =
      ∑ a ∈ boundedNormIdeals F ((5/2) * C.M),
        S4allTerm (c * C.d) C.source C.M (C.primitive p hp) a := by
    apply tsum_eq_sum
    intro a ha
    simp [S4allTerm, weight_outside C hM ha]
  have hlow : S4 c (c * C.d) C.K C.source C.M (C.primitive p hp) =
      ∑ a ∈ boundedNormIdeals F ((5/2) * C.M),
        S4Term c (c * C.d) C.K C.source C.M (C.primitive p hp) a := by
    apply tsum_eq_sum
    intro a ha
    simp [S4Term, weight_outside C hM ha]
  rw [hall, hlow, ← Finset.sum_sub_distrib]
  unfold Sieve.kernelRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hrow : a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ C.K < Sieve.s a
  · rw [if_pos hrow]
    have hsc : sc c a = Sieve.s a := by
      rw [sc, primeToSquarefreeKernel_eq_of_coprime c a hrow.1 hrow.2.1]
      rfl
    by_cases had : a ⊔ C.d = ⊤
    · have hcd : a ⊔ c * C.d = ⊤ := Ideal.isCoprime_iff_sup_eq.mp
        ((Ideal.isCoprime_iff_sup_eq.mpr hrow.2.1).mul_right (Ideal.isCoprime_iff_sup_eq.mpr had))
      have hprim := (C.primitive_spec p hp).2.2 a hcd
      have hnot : ¬sc c a ≤ C.K := by rw [hsc]; exact not_le.mpr hrow.2.2
      simp only [S4allTerm, S4Term, hrow.1, hcd, hnot, and_self, and_false,
        if_true, if_false, sub_zero, and_true]
      rw [if_pos hrow.1]
      change C.source _ * _ * _ = C.source _ * _
      rw [mul_assoc, hprim.1]
    · have hnot : a ⊔ c * C.d ≠ ⊤ := by
        intro h
        apply had
        exact top_unique (h.symm.trans_le (sup_le_sup_left Ideal.mul_le_right a))
      simp [S4allTerm, S4Term, hnot, row_zero C hp hrow.2.1 had]
  · rw [if_neg hrow]
    by_cases hcd : a ≠ ⊥ ∧ a ⊔ c * C.d = ⊤
    · have hc : a ⊔ c = ⊤ := top_unique (hcd.2.symm.trans_le
        (sup_le_sup_left Ideal.mul_le_left a))
      have hsc : sc c a = Sieve.s a := by
        rw [sc, primeToSquarefreeKernel_eq_of_coprime c a hcd.1 hc]; rfl
      have hle : sc c a ≤ C.K := by
        rw [hsc]; exact le_of_not_gt (fun hk => hrow ⟨hcd.1, hc, hk⟩)
      simp [S4allTerm, S4Term, hcd.1, hcd.2, hle]
    · simp [S4allTerm, S4Term, hcd, show ¬(a ≠ ⊥ ∧ a ⊔ c * C.d = ⊤ ∧ sc c a ≤ C.K)
        from fun h => hcd ⟨h.1, h.2.1⟩]

 def originalPairs (C : Context Q) : Finset (Ideal (𝓞 F) × Ideal (𝓞 F)) :=
  (Sieve.paperShell F c C.N ×ˢ Sieve.paperShell F c C.N).filter
    (fun b => b.1 ≠ b.2 ∧ b.1 ⊔ b.2 = C.d ∧ Q.cls b.1 = C.g ∧ Q.cls b.2 = C.g)

private lemma pair_mem_original (C : Context Q) {p : Ideal (𝓞 F) × Ideal (𝓞 F)}
    (hp : p ∈ C.pairs) : (C.d * p.1, C.d * p.2) ∈ originalPairs C := by
  obtain ⟨hcols, hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨hu, hw⟩ := Finset.mem_product.mp hcols
  have huc := (Finset.mem_filter.mp hu).2
  have hvc := (Finset.mem_filter.mp hw).2
  have ho := original_of_valid C hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huc.1, hvc.1⟩,
    ho.1, ho.2, huc.2, hvc.2⟩

private lemma original_surj (C : Context Q) (b : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hb : b ∈ originalPairs C) : ∃ p ∈ C.pairs, (C.d * p.1, C.d * p.2) = b := by
  obtain ⟨hcols, hne, hgcd, hg1, hg2⟩ := Finset.mem_filter.mp hb
  obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hcols
  have hs1 := ((Sieve.mem_paperShell F c C.N _).mp hb1).1
  have hs2 := ((Sieve.mem_paperShell F c C.N _).mp hb2).1
  obtain ⟨p, ⟨h1, h2⟩, -⟩ := SquarefreeGcd.existsUnique_strip hs1 hs2
  rw [hgcd] at h1 h2
  have hu : C.d * p.1 ∈ Sieve.paperShell F c C.N := h1 ▸ hb1
  have hv : C.d * p.2 ∈ Sieve.paperShell F c C.N := h2 ▸ hb2
  have hc1 : Q.cls (C.d * p.1) = C.g := h1 ▸ hg1
  have hc2 : Q.cls (C.d * p.2) = C.g := h2 ▸ hg2
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨col_mem C hu hc1, col_mem C hv hc2⟩, ?_⟩, Prod.ext h1.symm h2.symm⟩
  apply valid_of_original C hu hv
  · simpa only [← h1, ← h2] using hne
  · simpa only [← h1, ← h2] using hgcd
  · exact hc1.trans hc2.symm

theorem pair_high_eq_all_sub_low (C : Context Q)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hK : 1 ≤ C.K) :
    offDiagonalT3 Q C.W C.M C.N C.K C.d C.g C.lam =
      C.pairSum (fun p hp => C.coefficient p *
        (S4all (c * C.d) C.source C.M (C.primitive p hp) -
          S4 c (c * C.d) C.K C.source C.M (C.primitive p hp))) := by
  let term := fun b : Ideal (𝓞 F) × Ideal (𝓞 F) =>
    C.lam b.1 * starRingEnd ℂ (C.lam b.2) *
      (∑ a ∈ Sieve.kernelRows F c C.M C.K,
        (C.W ((Ideal.absNorm a : ℝ) / C.M) : ℂ) *
          (Q.χ b.1) a * starRingEnd ℂ ((Q.χ b.2) a))
  have hoff : offDiagonalT3 Q C.W C.M C.N C.K C.d C.g C.lam =
      ∑ b ∈ originalPairs C, term b := by
    rw [originalPairs, Finset.sum_filter, Finset.sum_product]
    rfl
  rw [hoff, Context.pairSum]
  symm
  apply Finset.sum_bij (i := fun p _ => (C.d * p.1, C.d * p.2))
  · exact fun p hp => pair_mem_original C hp
  · intro p hp q hq he
    exact Prod.ext (mul_left_cancel₀ C.hd0 (congrArg Prod.fst he))
      (mul_left_cancel₀ C.hd0 (congrArg Prod.snd he))
  · intro b hb
    obtain ⟨p, hp, he⟩ := original_surj C b hb
    exact ⟨p, hp, he⟩
  · intro p hp
    have hv : C.ValidPair p := (Finset.mem_filter.mp hp).2
    rw [dif_pos hv, ← rows_match C hM p hv]
    rfl

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
set_option maxHeartbeats 2000000
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

open ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private theorem reflected_y_le_z (C : Context Q) (B : ℝ) (e : Ideal (𝓞 F))
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ) (hB : 0 < B) :
    C.Y1 B e ≤ C.Z1 B e := by
  have hM0 : 0 < C.M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : 0 < C.N := lt_of_lt_of_le zero_lt_one hN
  have hMN : 1 ≤ C.M * C.N := by nlinarith
  have hd : 0 < norm C.d := by
    unfold ExplicitTerms.norm
    exact_mod_cast Nat.pos_of_ne_zero (fun h => C.hd0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hMN0 : 0 < C.M * C.N := mul_pos hM0 hN0
  have he : 0 ≤ norm e := by unfold ExplicitTerms.norm; positivity
  unfold Context.Y1 Context.Z1
  gcongr
  · exact (Real.rpow_pos_of_pos hMN0 _).le
  · nlinarith
  · exact Real.rpow_le_rpow_of_exponent_le hMN (by linarith)

private theorem reflected_row_match (C : Context Q) (j a : Ideal (𝓞 F))
    (X Y Z L : ℝ) (hj : j ≠ ⊥) (hX : 0 < X) (ha : 0 < norm a) (hYZ : Y ≤ Z) :
    squareWeightSeries ⊤ j
      (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) X a =
      C.kappa * (Real.sqrt (X / norm a) : ℂ) * C.mass * (sigma4Rho j : ℂ) -
      C.kappa * (Real.sqrt (X / norm a) : ℂ) * C.mass * Context.largeDensity j Z +
      C.origin * Context.originDivisors j Z +
      Context.middle C.reflectedKernel j (Real.sqrt (X / norm a)) Y Z L +
      C.reflectedRemainder j (Real.sqrt (X / norm a)) Y Z L := by
  have hs : squareWeightSeries ⊤ j
      (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) X a =
      ReflectedCoprimeTruncation.originalSum F C.source (Real.sqrt (X / norm a)) j := by
    rw [squareWeightSeries, ReflectedCoprimeTruncation.originalSum]
    refine tsum_congr (fun b => ?_)
    simp only [Ideal.top_mul]
    by_cases hb : b ≠ ⊥ ∧ b ⊔ j = ⊤
    · rw [if_pos hb, if_pos hb, SquareSecondPass.weight]
      congr 1
      have hT2 := Real.sq_sqrt (le_of_lt (div_pos hX ha))
      rw [div_pow, hT2]
      dsimp [ExplicitTerms.norm]
      field_simp
    · rw [if_neg hb, if_neg hb]
  have hrho : ReflectedCoprimeTruncation.rho j = (sigma4Rho j : ℂ) := by
    have he := idealEulerDeletion_eq_prod j hj 1
    simp only [idealEulerDeletion, Complex.cpow_neg_one, ← div_eq_mul_inv] at he
    rw [ReflectedCoprimeTruncation.rho, he, sigma4Rho, badPrimes]
    push_cast
    simp only [one_div]
  rw [hs, ReflectedCoprimeTruncation.originalSum_eq_truncatedMainTerm_add_remainder F C.hF C.source (1/2) (5/2)
    C.source_smooth C.source_support (by norm_num) (by norm_num) j hj
    (Real.sqrt (X / norm a)) Y Z L (Real.sqrt_pos.2 (div_pos hX ha)) hYZ]
  rw [ReflectedCoprimeTruncation.truncatedMainTerm, hrho]
  simp only [Context.kappa, Context.mass, ReflectedCoprimeTruncation.mass,
    Context.origin, ReflectedCoprimeTruncation.originCoefficient,
    Context.largeDensity, Context.originDivisors, Context.middle,
    Context.reflectedKernel, Context.reflectedRemainder, ExplicitTerms.norm,
    Complex.ofReal_div, Complex.ofReal_natCast, mul_comm]
  rfl

def reflectedBlock (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * squareWeightSeries ⊤ (p.1 * p.2)
          (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
          (C.dualScale e p) a

def reflectedTailBlock (C : Context Q) (B : ℝ) (unit : Bool := false) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * C.reflectedRemainder (p.1 * p.2)
          (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1

theorem reflected_block_match (C : Context Q) (B : ℝ) (unit : Bool)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ) (hB : 0 < B) :
    reflectedBlock C B unit =
      T C B unit - E1 C B unit - E2 C B unit + E3 C B unit +
        reflectedTailBlock C B unit := by
  have hrow (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : Context.ValidPair C p)
      (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
      (a : Ideal (𝓞 F)) (ha : a ∈ C.reflectedRows B unit) := by
    have he0 : e ≠ ⊥ := ne_bot_of_mem_idealDivisors he
    have hj : p.1 * p.2 ≠ ⊥ := by
      exact mul_ne_zero hp.hu0 hp.hv0
    have ha0 : a ≠ ⊥ := by
      obtain ⟨tr, htr, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp htr).2.2.2
    have heN : 0 < norm e := by
      unfold ExplicitTerms.norm
      exact_mod_cast Nat.pos_of_ne_zero (fun h => he0 (Ideal.absNorm_eq_zero_iff.mp h))
    have hjN : 0 < norm (p.1 * p.2) := by
      unfold ExplicitTerms.norm
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hj (Ideal.absNorm_eq_zero_iff.mp h))
    have haN : 0 < norm a := by
      unfold ExplicitTerms.norm
      exact_mod_cast Nat.pos_of_ne_zero (fun h => ha0 (Ideal.absNorm_eq_zero_iff.mp h))
    exact reflected_row_match C (p.1 * p.2) a (C.dualScale e p)
      (C.Y1 B e) (C.Z1 B e) C.L1 hj
      (div_pos (mul_pos heN hjN) (lt_of_lt_of_le zero_lt_one hM)) haN
      (reflected_y_le_z C B e hM hN hδ hB)
  have hexpand : reflectedBlock C B unit =
      C.pairSum (fun p hp => C.coefficient p *
        ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
          ∑ a ∈ C.reflectedRows B unit, C.primitive p hp a *
            (C.kappa * (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
                (sigma4Rho (p.1 * p.2) : ℂ) -
             C.kappa * (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
                Context.largeDensity (p.1 * p.2) (C.Z1 B e) +
             C.origin * Context.originDivisors (p.1 * p.2) (C.Z1 B e) +
             Context.middle C.reflectedKernel (p.1 * p.2)
                (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1 +
             C.reflectedRemainder (p.1 * p.2)
                (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1)) := by
    unfold reflectedBlock Context.pairSum
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs with hpv
    · apply congrArg (fun z : ℂ => C.coefficient p * z)
      apply Finset.sum_congr rfl
      intro e he
      apply congrArg (fun z : ℂ => C.prefactor e p hpv * z)
      apply Finset.sum_congr rfl
      intro a ha
      apply congrArg (fun z : ℂ => C.primitive p hpv a * z)
      exact hrow p hpv e he a ha
    · rfl
  rw [hexpand]
  unfold T E1 E2 E3 reflectedTailBlock Context.pairSum
  simp only [sub_neg_eq_add, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc, ite_add, ite_sub, sub_self, add_zero]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with hpv
  · ring
  · simp

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

open ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma core_partition (C : Context Q) (m : Ideal (𝓞 F)) (hK : 1 ≤ C.K)
    (G : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ Sieve.idealAdmissibleFinset F m C.K, G a) =
      (∑ a ∈ ReflectedSigma4.unitRows c m C.K, G a) +
        ∑ B ∈ dyadicScales C, ∑ a ∈ sigma4DyadicRows F m C.K B, G a := by
  have hu : ReflectedSigma4.unitRows c m C.K = {⊤} := by
    have hk : Sieve.squarefreeKernel (⊤ : Ideal (𝓞 F)) = ⊤ :=
      Sieve.squarefreeKernel_eq_self (by simpa only [← Ideal.one_eq_top] using squarefree_one)
    have hs : sc c (⊤ : Ideal (𝓞 F)) = 1 := by
      unfold sc primeToSquarefreeKernel
      rw [hk, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
      simp
    simp [ReflectedSigma4.unitRows, hs, hK,
      show Squarefree (⊤ : Ideal (𝓞 F)) from by simpa only [← Ideal.one_eq_top] using squarefree_one]
  have hb (i : ℕ) : Sieve.clippedDyadicBlock F m C.K (i+1) =
      sigma4DyadicRows F m C.K ((2 : ℝ)^i) := by
    ext a
    simp only [Sieve.clippedDyadicBlock, Sieve.idealDyadicBlock, Finset.mem_inter,
      sigma4DyadicRows, Finset.mem_filter, Sieve.mem_idealAdmissibleFinset,
      Sieve.mem_paperShell]
    tauto
  have hz : Sieve.clippedDyadicBlock F m C.K 0 = {⊤} := by
    ext a
    simp [Sieve.clippedDyadicBlock, Sieve.idealDyadicBlock, Sieve.mem_idealAdmissibleFinset,
      hK, show Squarefree (⊤ : Ideal (𝓞 F)) from by simpa only [← Ideal.one_eq_top] using squarefree_one]
  rw [← Sieve.biUnion_clippedDyadicBlock F m C.K hK,
    Finset.sum_biUnion (Sieve.pairwiseDisjoint_clippedDyadicBlock F m C.K hK),
    Finset.sum_range_succ', hz, hu]
  rw [add_comm]
  congr 1
  simp only [dyadicScales]
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun i hi => by rw [hb])
  · intro i hi j hj hij
    exact (pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)) hij

private lemma supported_facts (C : Context Q) {t r : Ideal (𝓞 F)}
    (ht : t ∈ squarefreeBadPool c) (hr : r ∈ Sieve.idealAdmissibleFinset F c C.K) :
    t ⊔ r = ⊤ ∧ Squarefree (t*r) ∧ t*r ≠ ⊥ ∧
      t = badPart c (t*r) ∧ r = goodPart c (t*r) := by
  obtain ⟨ht0, hts, htp⟩ := (mem_squarefreeBadPool C.D.original_ne_bot).mp ht
  obtain ⟨hrs, hrc, hrn⟩ := (Sieve.mem_idealAdmissibleFinset F c C.K r).mp hr
  have hrel : IsRelPrime t r := by
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ht0).mpr
    intro p hpt hpr hp
    exact hp.not_isUnit ((Ideal.isCoprime_iff_sup_eq.mpr hrc).isRelPrime hpr (htp p hp hpt))
  have hcop : t ⊔ r = ⊤ := by
    have hu : IsUnit (t ⊔ r) := hrel
      (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
    exact Ideal.isUnit_iff.mp hu
  have hsf := squarefree_mul_iff.mpr ⟨hrel, hts, hrs⟩
  have h0 := mul_ne_zero ht0 hrs.ne_zero
  obtain ⟨htb, hrg⟩ := bad_good_unique C.D.original_ne_bot h0 ht0 hrs.ne_zero rfl hrc htp
  exact ⟨hcop, hsf, h0, htb, hrg⟩

private lemma reflected_rows_sum (C : Context Q) (B : ℝ) (unit : Bool)
    (hR : C.reflectedCoreRows B unit ⊆ Sieve.idealAdmissibleFinset F c C.K)
    (G : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ C.reflectedRows B unit, G a) =
      ∑ t ∈ squarefreeBadPool c, ∑ r ∈ C.reflectedCoreRows B unit, G (t*r) := by
  have he : C.reflectedRowIndices B unit = squarefreeBadPool c ×ˢ C.reflectedCoreRows B unit := by
    apply Finset.filter_eq_self.mpr
    intro tr htr
    obtain ⟨ht, hr⟩ := Finset.mem_product.mp htr
    exact ⟨(supported_facts C ht (hR hr)).1,
      (supported_facts C ht (hR hr)).2.1,
      (supported_facts C ht (hR hr)).2.2.1⟩
  unfold Context.reflectedRows
  rw [he, Finset.sum_image, Finset.sum_product]
  intro p hp q hq hpq
  obtain ⟨ht, hr⟩ := Finset.mem_product.mp hp
  obtain ⟨ht', hr'⟩ := Finset.mem_product.mp hq
  obtain ⟨_, _, _, hb, hg⟩ := supported_facts C ht (hR hr)
  obtain ⟨_, _, _, hb', hg'⟩ := supported_facts C ht' (hR hr')
  change p.1 * p.2 = q.1 * q.2 at hpq
  apply Prod.ext
  · rw [hb, hb', hpq]
  · rw [hg, hg', hpq]

private lemma reflected_core_subset (C : Context Q) (hK : 1 ≤ C.K)
    (B : ℝ) (unit : Bool) :
    C.reflectedCoreRows B unit ⊆ Sieve.idealAdmissibleFinset F c C.K := by
  intro r hr
  cases unit
  · obtain ⟨hr, hn⟩ := Finset.mem_filter.mp hr
    obtain ⟨hs, hc, -, -⟩ := (Sieve.mem_paperShell F c B r).mp hr
    exact (Sieve.mem_idealAdmissibleFinset F c C.K r).mpr ⟨hs, hc, hn⟩
  · change r ∈ C.reflectedCoreRows 1 true at hr
    rw [(RectangleEndpoints.row_endpoints C hK B).2.1] at hr
    obtain rfl := Finset.mem_singleton.mp hr
    simp [Sieve.mem_idealAdmissibleFinset, hK,
      show Squarefree (⊤ : Ideal (𝓞 F)) from by simpa only [← Ideal.one_eq_top] using squarefree_one]

private lemma reflected_partition (C : Context Q) (hK : 1 ≤ C.K)
    (G : Ideal (𝓞 F) → ℂ) :
    (∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K, G (t*r)) =
      (∑ a ∈ C.reflectedRows 1 true, G a) +
        ∑ B ∈ dyadicScales C, ∑ a ∈ C.reflectedRows B false, G a := by
  rw [reflected_rows_sum C 1 true (reflected_core_subset C hK 1 true)]
  simp_rw [reflected_rows_sum C _ false (reflected_core_subset C hK _ false)]
  simp only [Context.reflectedCoreRows, Bool.true_eq, ↓reduceIte]
  simp_rw [core_partition C c hK]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

private lemma transform_rapid (C : Context Q) : HasRapidDecayAtInfinity
    (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) := by
  intro A _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, A ≤ (n : ℝ) := exists_nat_ge A
  obtain ⟨R, hR, -, hb⟩ := fieldTransform_euler_two_ended_bound
    (principalDiscriminant F) (principalComplexPlaces F) C.source
    (principalDiscriminant_pos F) (principalComplexPlaces_pos F C.hF)
    C.source_smooth C.source_compact 0 n 1 zero_lt_one
  refine ⟨R, 1, hR.le, le_refl 1, fun t ht => ?_⟩
  have h1 : ‖fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source t‖ ≤
      R * Real.rpow t (-(n : ℝ)) := by simpa using hb t ht
  exact h1.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) hR.le)

private lemma all_eq_low_tail {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (K X : ℝ) (h : ℝ → ℂ)
    (hh : Summable (fun a => ‖S4allTerm ⊤ h X η a‖)) :
    S4all ⊤ h X η = S4 c ⊤ K h X η +
      ∑' a, reflectedKernelTailTerm c K h X η a := by
  have hl : Summable (fun a => S4Term c ⊤ K h X η a) := by
    apply Summable.of_norm_bounded hh
    intro a
    by_cases ha : a ≠ ⊥ ∧ sc c a ≤ K
    · simp [S4Term, S4allTerm, ha.1, ha.2]
    · simp [S4Term, S4allTerm, ha]
  have ht : Summable (fun a => reflectedKernelTailTerm c K h X η a) := by
    apply Summable.of_norm_bounded hh
    intro a
    unfold reflectedKernelTailTerm
    split_ifs <;> simp
  rw [S4all, S4, ← hl.tsum_add ht]
  apply tsum_congr
  intro a
  by_cases ha : a = ⊥
  · simp [S4Term, S4allTerm, reflectedKernelTailTerm, ha]
  · by_cases hk : sc c a ≤ K
    · simp [S4Term, S4allTerm, reflectedKernelTailTerm, ha, hk, not_lt.mpr hk]
    · simp [S4Term, S4allTerm, reflectedKernelTailTerm, ha, hk, lt_of_not_ge hk]

private lemma original_low (C : Context Q) (hM : 1 ≤ C.M) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : Context.ValidPair C p) :
    S4 c (c*C.d) C.K C.source C.M (C.primitive p hp) =
      (∑ a ∈ C.originalRows 1 true, C.primitive p hp a *
        squareWeightSeries (c*C.d) (p.1*p.2) C.source C.M a) +
      ∑ B ∈ dyadicScales C, ∑ a ∈ C.originalRows B false, C.primitive p hp a *
        squareWeightSeries (c*C.d) (p.1*p.2) C.source C.M a := by
  rw [S4_reindex_quadratic_of_radical_dvd C.D.original_ne_bot
    (mul_ne_zero C.D.original_ne_bot C.hd0) (mul_ne_zero hp.hu0 hp.hv0)
    (dvd_trans (Ideal.dvd_iff_le.mpr Ideal.le_radical) (dvd_mul_right c C.d))
    hK (lt_of_lt_of_le zero_lt_one hM) C.source
    (rapidDecay_of_compactSupport _ C.source_compact) (C.primitive p hp)
    (C.primitive_spec p hp).1 (C.primitive_quadratic p hp)]
  exact core_partition C (c*C.d) hK _

private lemma reflected_low (C : Context Q) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : Context.ValidPair C p)
    (X : ℝ) (hX : 0 < X) :
    S4 c ⊤ C.K (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
      X (C.primitive p hp) =
      (∑ a ∈ C.reflectedRows 1 true, C.primitive p hp a * squareWeightSeries ⊤ (p.1*p.2)
        (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) X a) +
      ∑ B ∈ dyadicScales C, ∑ a ∈ C.reflectedRows B false,
        C.primitive p hp a * squareWeightSeries ⊤ (p.1*p.2)
          (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) X a := by
  rw [S4_reindex_fixed_primes_quadratic C.D.original_ne_bot (by simp)
    (mul_ne_zero hp.hu0 hp.hv0) hK hX _ (transform_rapid C)
    (C.primitive p hp) (C.primitive_spec p hp).1 (C.primitive_quadratic p hp)]
  simp only [sup_top_eq, ↓reduceIte, Ideal.top_mul]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← (C.primitive p hp).map_mul']
  exact reflected_partition C hK (fun a => C.primitive p hp a * squareWeightSeries ⊤ (p.1*p.2)
    (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) X a)

private lemma pair_identity (C : Context Q) (hM : 1 ≤ C.M) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : Context.ValidPair C p) :
    S4all (c*C.d) C.source C.M (C.primitive p hp) -
      S4 c (c*C.d) C.K C.source C.M (C.primitive p hp) =
    ((∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows 1 true, C.primitive p hp a * squareWeightSeries ⊤ (p.1*p.2)
        (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
        (C.dualScale e p) a) -
      ∑ a ∈ C.originalRows 1 true, C.primitive p hp a *
        squareWeightSeries (c*C.d) (p.1*p.2) C.source C.M a) +
    (∑ B ∈ dyadicScales C, ((∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B false, C.primitive p hp a * squareWeightSeries ⊤ (p.1*p.2)
        (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
        (C.dualScale e p) a) -
      ∑ a ∈ C.originalRows B false, C.primitive p hp a *
        squareWeightSeries (c*C.d) (p.1*p.2) C.source C.M a)) +
    primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2 (C.primitive p hp) := by
  have hM0 : 0 < C.M := lt_of_lt_of_le zero_lt_one hM
  obtain ⟨-, hs, heq⟩ := S4all_primitive_mobius_poisson C.hF
    (mul_ne_zero C.D.original_ne_bot C.hd0) (mul_ne_zero hp.hu0 hp.hv0)
    (C.primitive p hp) (C.primitive_spec p hp).1 (C.primitive_quadratic p hp)
    (primitive_product_not_principal p.1 p.2 hp.hu0 hp.hv0 hp.huv hp.offDiagonal
      (C.primitive p hp) (C.primitive_spec p hp).1)
    C.source C.source_smooth C.source_compact hM0
  change S4all (c*C.d) C.source C.M (C.primitive p hp) =
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      S4all ⊤ (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
        (C.dualScale e p) (C.primitive p hp) at heq
  have hscale (e) (he : e ∈ C.mobiusDivisors) : 0 < C.dualScale e p := by
    have he0 := ne_bot_of_mem_idealDivisors he
    have heN : 0 < norm e := by
      unfold ExplicitTerms.norm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr he0)
    have hpN : 0 < norm (p.1*p.2) := by
      unfold ExplicitTerms.norm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hp.hu0 hp.hv0))
    exact div_pos (mul_pos heN hpN) hM0
  rw [heq, original_low C hM hK p hp]
  have heqs : ∀ e ∈ C.mobiusDivisors,
      S4all ⊤ (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
        (C.dualScale e p) (C.primitive p hp) =
      (∑ a ∈ C.reflectedRows 1 true, C.primitive p hp a * squareWeightSeries ⊤ (p.1*p.2)
        (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) (C.dualScale e p) a) +
      (∑ B ∈ dyadicScales C, ∑ a ∈ C.reflectedRows B false,
        C.primitive p hp a * squareWeightSeries ⊤ (p.1*p.2)
          (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source) (C.dualScale e p) a) +
      ∑' a, reflectedKernelTailTerm c C.K
        (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
        (C.dualScale e p) (C.primitive p hp) a := by
    intro e he
    rw [all_eq_low_tail (C.primitive p hp) C.K (C.dualScale e p) _ (hs e he)]
    rw [reflected_low C hK p hp _ (hscale e he)]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun e he => congrArg (C.prefactor e p hp * ·) (heqs e he))]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := C.mobiusDivisors) (t := dyadicScales C)]
  have ht : primitiveMobiusTransformTail c C.d C.W C.M C.K p.1 p.2 (C.primitive p hp) =
      ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp * ∑' a, reflectedKernelTailTerm c C.K
        (fieldTransform (principalDiscriminant F) (principalComplexPlaces F) C.source)
        (C.dualScale e p) (C.primitive p hp) a := by
    unfold primitiveMobiusTransformTail
    simp only [Context.mobiusDivisors, Context.prefactor, Context.source,
      Context.dualScale, primitiveDualScale, ExplicitTerms.norm, map_mul, Nat.cast_mul, mul_assoc,
      Complex.ofReal_natCast]
    rfl
  rw [ht]
  ring

theorem primitive_dyadic_reindex (C : Context Q)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hK : 1 ≤ C.K) :
    C.pairSum (fun p hp => C.coefficient p *
      (S4all (c * C.d) C.source C.M (C.primitive p hp) -
        S4 c (c * C.d) C.K C.source C.M (C.primitive p hp))) =
      (reflectedBlock C 1 true - originalBlock C 1 true) +
        ∑ B ∈ dyadicScales C, (reflectedBlock C B - originalBlock C B) +
          cutoffRemainder C := by
  unfold reflectedBlock originalBlock cutoffRemainder Context.pairSum
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := dyadicScales C) (t := C.pairs)]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hv : Context.ValidPair C p
  · simp only [hv, ↓reduceDIte]
    rw [pair_identity C hM hK p hv]
    simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  · simp [hv]

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

open ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem finite_assembly (C : Context Q)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ) :
    (reflectedBlock C 1 true - originalBlock C 1 true) +
      ∑ B ∈ dyadicScales C, (reflectedBlock C B - originalBlock C B) +
        cutoffRemainder C = sevenTermSum C + totalRemainder C := by
  have hblock (B : ℝ) (unit : Bool) (hB : 0 < B) :
      reflectedBlock C B unit - originalBlock C B unit =
        sevenTermBlock C B unit + R C B unit := by
    rw [reflected_block_match C B unit hM hN hδ hB,
      compact_block_match C B unit hM hN hδ hB]
    change T C B unit - E1 C B unit - E2 C B unit + E3 C B unit +
      reflectedTailBlock C B unit -
      (Tprime C B unit - E4 C B unit + E5 C B unit + originalTailBlock C B unit) =
      sevenTermBlock C B unit + (reflectedTailBlock C B unit - originalTailBlock C B unit)
    unfold sevenTermBlock
    ring
  have hscale : ∀ B ∈ dyadicScales C, 0 < B := by
    intro B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    positivity
  rw [hblock 1 true (by norm_num)]
  have hsum : (∑ B ∈ dyadicScales C, (reflectedBlock C B - originalBlock C B)) =
      ∑ B ∈ dyadicScales C, (sevenTermBlock C B + R C B) :=
    Finset.sum_congr rfl (fun B hB => hblock B false (hscale B hB))
  rw [hsum, Finset.sum_add_distrib]
  unfold sevenTermSum unitBlock totalRemainder
  ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem bilinear_explicit_assembly_identity (C : Context Q)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hK : 1 ≤ C.K) (hKM : C.K ≤ C.M)
    (hδ : 0 < C.δ) :
    offDiagonalT3 Q C.W C.M C.N C.K C.d C.g C.lam =
      sevenTermSum C + totalRemainder C := by
  rw [ExplicitAssembly.pair_high_eq_all_sub_low C hM hN hK,
    ExplicitAssembly.primitive_dyadic_reindex C hM hN hK]
  exact ExplicitAssembly.finite_assembly C hM hN hδ

theorem bilinear_explicit_assembly_diagonal
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ C : Context Q, C.W = W →
      1 ≤ C.M → 1 ≤ C.N → 0 < C.K →
      ‖Sieve.T3 F c Q C.W C.M C.N C.K C.d C.g C.lam -
          offDiagonalT3 Q C.W C.M C.N C.K C.d C.g C.lam‖ ≤
        A * C.M * Sieve.energy F c C.N C.lam := by
  obtain ⟨C₀, hC₀, hCbound⟩ := diagonalContribution_bound F W hW
  refine ⟨C₀, hC₀, ?_⟩
  intro C hCW hM hN hK
  rw [hCW]
  rw [T3_eq_diagonal_add_offDiagonal Q W hW C.M C.N C.K hM hN hK C.d C.g C.lam]
  rw [add_sub_cancel_right]
  have hnn : 0 ≤ diagonalContribution Q W C.M C.N C.d C.g C.lam
      (fun a => C.K < Sieve.s a) := by
    unfold diagonalContribution
    by_cases hd : C.d ∈ Sieve.paperShell F c C.N ∧ Q.cls C.d = C.g
    · rw [if_pos hd]
      exact finsum_nonneg (fun a => by
        by_cases ha : a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ C.K < Sieve.s a
        · rw [if_pos ha]
          exact mul_nonneg (hW.nonneg _) (by positivity)
        · rw [if_neg ha])
    · rw [if_neg hd]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact (hCbound c Q C.M C.N C.d C.g C.lam (fun a => C.K < Sieve.s a) hM hN).2

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end

end
