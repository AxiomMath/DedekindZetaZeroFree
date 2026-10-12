module

public import DedekindZetaZeroFree.Arithmetic.Ideals.MoebiusCoprimality
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.LogarithmicSummationAndResidues
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.LogarithmicTransformAdmissibility
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedSquareResidueData

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.SquarePoisson

private lemma mobius_indicator {F : Type*} [Field F] [NumberField F] (m I : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hI : I ≠ ⊥) :
    (∑ d ∈ idealDivisors m, if d ∣ I then (UniqueFactorizationMonoid.moebius d : ℂ) else 0) =
      if I ⊔ m = ⊤ then 1 else 0 := by
  let f : Ideal (𝓞 F) → ℂ := fun J => if J = I then 1 else 0
  have hg : Function.HasFiniteSupport (fun J : Ideal (𝓞 F) => if J = ⊥ then (0 : ℂ) else f J) := by
    apply (Set.finite_singleton I).subset
    intro J hJ
    have hJI : J = I := by
      by_contra h
      have : f J = 0 := by simp [f, h]
      simp [Function.mem_support, this] at hJ
    exact hJI
  have h := DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact.coprimeFinsum_eq_moebiusMultiples f hg m hm
  have hc : (∑ᶠ J : Ideal (𝓞 F), if J ≠ ⊥ ∧ J ⊔ m = ⊤ then f J else 0) =
      if I ⊔ m = ⊤ then 1 else 0 := by
    rw [finsum_eq_single (fun J : Ideal (𝓞 F) => if J ≠ ⊥ ∧ J ⊔ m = ⊤ then f J else 0) I (by intro J hJ; simp [f, hJ])]
    simp [f, hI]
  have hd (d : Ideal (𝓞 F)) :
      (∑ᶠ J : Ideal (𝓞 F), if J ≠ ⊥ ∧ d ∣ J then f J else 0) =
      if d ∣ I then 1 else 0 := by
    rw [finsum_eq_single (fun J : Ideal (𝓞 F) => if J ≠ ⊥ ∧ d ∣ J then f J else 0) I (by intro J hJ; simp [f, hJ])]
    simp [f, hI]
  rw [hc] at h
  simp_rw [hd] at h
  simpa [mul_ite] using h.symm

private lemma multiples_tsum {F : Type} [Field F] [NumberField F]
    (g : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (d : Ideal (𝓞 F)) (hd : d ≠ ⊥) :
    (∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ d ∣ I then
      g ((Ideal.absNorm I : ℝ) / X) else 0) =
    ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
      g ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ))) := by
  let f : Ideal (𝓞 F) → ℂ := fun I => if I ≠ ⊥ ∧ d ∣ I then
      g ((Ideal.absNorm I : ℝ) / X) else 0
  have hi : Function.Injective (fun J : Ideal (𝓞 F) => d * J) :=
    fun J K h => mul_left_cancel₀ hd h
  have hs : Function.support f ⊆ Set.range (fun J => d * J) := by
    intro I hI
    have h : I ≠ ⊥ ∧ d ∣ I := by
      by_contra h
      simp [Function.mem_support, f, h] at hI
    obtain ⟨J, hJ⟩ := h.2
    exact ⟨J, hJ.symm⟩
  change (∑' I, f I) = _
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro J
  by_cases hJ : J = ⊥
  · simp [f, hJ]
  · have hdN : (Ideal.absNorm d : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hd)
    have hmul : d * J ≠ ⊥ := mul_ne_zero hd hJ
    change (if d * J ≠ ⊥ ∧ d ∣ d * J then _ else 0) = _
    rw [if_pos ⟨hmul, dvd_mul_right d J⟩, if_neg hJ]
    congr 1
    rw [map_mul, Nat.cast_mul]
    field_simp

theorem finite_mobius_poisson
    (F : Type) [Field F] [NumberField F]
    (g k : ℝ → ℂ) (A R : ℂ)
    (hsum : ∀ (Y : ℝ), 0 < Y → Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℝ) else ‖g ((Ideal.absNorm I : ℝ) / Y)‖))
    (hprincipal : ∀ (Y : ℝ), 0 < Y →
      (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        g ((Ideal.absNorm I : ℝ) / Y)) =
      A * (Y : ℂ) + R +
        (Y : ℂ) * ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          k (Y * (Ideal.absNorm I : ℝ)))
    (X : ℝ) (hX : 0 < X) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    ((∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ I ⊔ m = ⊤ then
      g ((Ideal.absNorm I : ℝ) / X) else 0) =
      A * (X : ℂ) *
        (∑ d ∈ idealDivisors m,
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ)) +
      R * (∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ)) +
      ∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((X : ℂ) / (Ideal.absNorm d : ℂ)) *
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          k (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ))) ∧
    (∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ)) =
      if m = ⊤ then 1 else 0 := by
  have hmass : (∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ)) =
      if m = ⊤ then 1 else 0 := by
    have h := mobius_indicator m m hm hm
    simp only [sup_idem] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro d hd
    rw [if_pos ((mem_idealDivisors hm).mp hd)]
  refine ⟨?_, hmass⟩
  let f : Ideal (𝓞 F) → ℂ := fun I => g ((Ideal.absNorm I : ℝ) / X)
  have hdSum (d : Ideal (𝓞 F)) : Summable (fun I =>
      if I ≠ ⊥ ∧ d ∣ I then f I else 0) := by
    apply (hsum X hX).of_norm_bounded
    intro I
    by_cases hI : I = ⊥
    · simp [hI]
    · by_cases hdI : d ∣ I <;> simp [hI, hdI, f]
  have hpoint (I : Ideal (𝓞 F)) :
      (if I ≠ ⊥ ∧ I ⊔ m = ⊤ then f I else 0) =
      ∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
        (if I ≠ ⊥ ∧ d ∣ I then f I else 0) := by
    by_cases hI : I = ⊥
    · simp [hI]
    · have hid := mobius_indicator m I hm hI
      have he : (∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
          (if I ≠ ⊥ ∧ d ∣ I then f I else 0)) =
          (∑ d ∈ idealDivisors m, if d ∣ I then
            (UniqueFactorizationMonoid.moebius d : ℂ) else 0) * f I := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdI : d ∣ I <;> simp [hI, hdI]
      rw [he, hid]
      by_cases hc : I ⊔ m = ⊤ <;> simp [hI, hc]
  change (∑' I, if I ≠ ⊥ ∧ I ⊔ m = ⊤ then f I else 0) = _
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun d hd => (hdSum d).mul_left _)]
  simp_rw [tsum_mul_left]
  have hscaled (d : Ideal (𝓞 F)) (hd : d ∈ idealDivisors m) :
      (∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ d ∣ I then f I else 0) =
        A * ((X : ℂ) / (Ideal.absNorm d : ℂ)) + R +
        ((X : ℂ) / (Ideal.absNorm d : ℂ)) *
          ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
            k (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ)) := by
    have hd0 := ne_bot_of_mem_idealDivisors hd
    have hdpos : 0 < (Ideal.absNorm d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd0)
    rw [show (∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ d ∣ I then f I else 0) =
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          g ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ))) from
      multiples_tsum g X hX d hd0]
    rw [hprincipal _ (div_pos hX hdpos)]
    push_cast
    congr 2
    apply tsum_congr
    intro I
    congr 1
    congr 1
    ring
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hscaled d hd]
  ring
end DedekindZetaZeroFree.LargeSieve.SquarePoisson

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff Topology
namespace DedekindZetaZeroFree.LargeSieve.SquarePoisson

theorem reflected_and_ideal_estimates (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    (∀ (c : ℝ), 1 < c → c < 2 → ∀ (x : ℝ), 0 < x →
      Complex.VerticalIntegrable (reflectedSpectrum D r h) c ∧
        reflectedTransform D r h x = mellinInv c (reflectedSpectrum D r h) x) ∧
    (∀ (F : Type) [Field F] [NumberField F] (X : ℝ), 0 < X →
      Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℝ) else
        ‖weight D r h ((Ideal.absNorm I : ℝ) / X)‖) ∧
      Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℝ) else
        ‖reflectedTransform D r h (X * (Ideal.absNorm I : ℝ))‖)) := by
  have hadm : Vendor.LogMellinAdmissible (weight D r h) 1
      ((originPolynomial D r h).comp (Polynomial.C (2 : ℂ) * Polynomial.X))
      (spectrum D r h) := by
    convert fieldTransform_comp_sq_logMellinAdmissible D r h hD hr hh hc
        (1 / 2) (by norm_num) (by norm_num) using 1
    · rfl
    · norm_num
    · funext s
      dsimp [spectrum]
      ring
  have hspec : Vendor.reflectedLogSpectrum D r (spectrum D r h) =
      reflectedSpectrum D r h := rfl
  have hdual : Vendor.reflectedLogDual D r (spectrum D r h) 1 =
      reflectedTransform D r h := by
    funext x
    simp only [Vendor.reflectedLogDual, reflectedTransform, hspec,
      show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  have hlines : ∀ c : ℝ, 1 < c → c < 2 → ∀ x : ℝ, 0 < x →
      Complex.VerticalIntegrable (reflectedSpectrum D r h) c ∧
      reflectedTransform D r h x = mellinInv c (reflectedSpectrum D r h) x := by
    intro c hc1 hc2 x hx
    have hcδ : c < 1 + (1 : ℝ) := by linarith
    exact ⟨by simpa only [hspec] using
        Vendor.reflectedLogSpectrum_verticalIntegrable D r hD hr hadm c hc1 hcδ,
      by simpa only [hspec, hdual] using
        Vendor.reflectedLogDual_eq_mellinInv D r hD hr hadm c x hc1 hcδ hx⟩
  refine ⟨hlines, ?_⟩
  intro F _ _ X hX
  constructor
  · have hs := (Vendor.logIdealTerm_summable (F := F)
        (fun _ => (1 : ℂ)) (fun _ _ => by norm_num) hadm.physical X hX).1
    exact hs.congr (fun I => by
      by_cases hI : I = ⊥ <;> simp [Vendor.logIdealTerm, hI])
  · let a : Ideal (𝓞 F) → ℂ := fun I => if I = ⊥ then 0 else 1
    have ha0 : a ⊥ = 0 := by simp [a]
    have ha : ∀ I, ‖a I‖ ≤ 1 := by
      intro I
      by_cases hI : I = ⊥ <;> simp [a, hI]
    have hline : Complex.VerticalIntegrable (reflectedSpectrum D r h) (3 / 2) :=
      (hlines (3 / 2) (by norm_num) (by norm_num) 1 (by norm_num)).1
    have hinv : ∀ x : ℝ, 0 < x → reflectedTransform D r h x =
        mellinInv (3 / 2) (reflectedSpectrum D r h) x :=
      fun x hx => (hlines (3 / 2) (by norm_num) (by norm_num) x hx).2
    have hs := (idealMellin_dual_interchange a ha0 ha
      (reflectedSpectrum D r h) (reflectedTransform D r h)
      (c := 3 / 2) (X := X) (q := 1) (by norm_num) hX (by norm_num)
      hline hinv).1
    have hs' : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
        ‖reflectedTransform D r h (X * (Ideal.absNorm I.val : ℝ))‖) :=
      hs.congr (fun I => by simp [a, I.property])
    have hi := (summable_subtype_iff_indicator
      (s := {I : Ideal (𝓞 F) | I ≠ ⊥})
      (f := fun I => ‖reflectedTransform D r h (X * (Ideal.absNorm I : ℝ))‖)).mp hs'
    exact hi.congr (fun I => by
      by_cases hI : I = ⊥ <;> simp [Set.indicator_apply, hI])
end DedekindZetaZeroFree.LargeSieve.SquarePoisson

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open Filter
namespace DedekindZetaZeroFree.LargeSieve.SquarePoisson
private lemma deriv_pow_mul {V : ℂ → ℂ} {n j : ℕ} (hjn : j ≤ n)
    (hV : AnalyticAt ℂ V 0) :
    iteratedDeriv j (fun s : ℂ => s ^ n * V s) 0 =
      if j = n then (n.factorial : ℂ) * V 0 else 0 := by
  rw [show (fun s : ℂ => s ^ n * V s) = (fun s : ℂ => s ^ n) * V from rfl,
    iteratedDeriv_mul (by fun_prop) hV.contDiffAt]
  by_cases hj : j = n
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single n]
    · simp only [iteratedDeriv_fun_pow_zero, if_pos rfl, Nat.choose_self,
        Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero, ite_true]
    · intro i hi hin
      rw [iteratedDeriv_fun_pow_zero, if_neg hin]
      ring
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≠ n := by rw [Finset.mem_range] at hi; omega
    rw [iteratedDeriv_fun_pow_zero, if_neg hin]
    ring

private lemma origin_residue_eval
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) :
    principalLogResidue0 F hF
      ((originPolynomial (principalDiscriminant F) (principalComplexPlaces F) h).comp
        (Polynomial.C (2 : ℂ) * Polynomial.X)) X =
      -(2 : ℂ) ^ (principalComplexPlaces F - 1) *
        kappa (principalHeckeData F hF) * mellin h 1 := by
  let D := principalDiscriminant F
  let r := principalComplexPlaces F
  let data := principalHeckeData F hF
  let P := (originPolynomial D r h).comp (Polynomial.C (2 : ℂ) * Polynomial.X)
  have hD : 0 < D := principalDiscriminant_pos F
  have hr : 1 ≤ r := principalComplexPlaces_pos F hF
  have hP : P.natDegree ≤ r - 1 := by
    apply (Polynomial.natDegree_comp_le).trans
    simpa using originPolynomial_natDegree_le D r h hD hr hh hc
  have hV : AnalyticAt ℂ (fun s : ℂ => (X : ℂ) ^ s * data.zetaOriginFactor s) 0 :=
    (analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.2 hX)).mul
      (principalZetaZeroFactor_analyticAt F hF)
  have hEq : (fun s : ℂ => (X : ℂ) ^ s * principalZetaContinuation F hF s) =
      (fun s : ℂ => s ^ (r - 1) * ((X : ℂ) ^ s * data.zetaOriginFactor s)) := by
    ext s
    simp only [principalZetaContinuation, r, data]
    ring
  change ∑ j ∈ P.support, (-1 : ℂ) ^ j * P.coeff j *
    iteratedDeriv j (fun s : ℂ => (X : ℂ) ^ s * principalZetaContinuation F hF s) 0 = _
  rw [hEq, Finset.sum_eq_single (r - 1)]
  · rw [deriv_pow_mul le_rfl hV, if_pos rfl]
    simp only [Complex.cpow_zero, one_mul]
    have hcoeff := originPolynomial_coeff_top D r h hD hr hh hc
    have hPcoeff : P.coeff (r - 1) =
        (originPolynomial D r h).coeff (r - 1) * (2 : ℂ) ^ (r - 1) := by
      simp [P]
    rw [hPcoeff, hcoeff]
    have hzero : data.zetaOriginFactor 0 = -data.E 1 / (2 : ℂ) ^ r := by
      dsimp [PrincipalHeckeData.zetaOriginFactor]
      rw [PrincipalHeckeData.E_zero_eq_one data]
      simp only [zero_add, neg_zero, zero_div, Complex.cpow_zero, one_mul, zero_sub]
      rw [Complex.Gammaℂ_one, inv_div, div_one]
      rw [show (Real.pi : ℂ) / (2 * (Real.pi : ℂ)) = 1 / 2 by field_simp, div_pow]
      norm_num
      ring
    rw [hzero]
    have hhalf : (D : ℂ) ^ (-(1 / 2 : ℂ)) = ((Real.sqrt D : ℂ))⁻¹ := by
      have h1 : (Real.sqrt D : ℂ) = (D : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (le_of_lt hD) (1 / 2 : ℝ)]
      rw [h1, ← Complex.cpow_neg]
      norm_num
    rw [hhalf]
    change _ = -(2 : ℂ) ^ (r - 1) * (data.E 1 / ((Real.sqrt D : ℂ) * Complex.Gammaℂ 1 ^ r)) * mellin h 1
    rw [Complex.Gammaℂ_one]
    have hfac : ((r - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hsq : (Real.sqrt D : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hD)
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hsign : ((-1 : ℂ) ^ (r - 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm (r - 1) 2, pow_mul]
      norm_num
    push_cast
    rw [mul_pow]
    field_simp [hfac, hsq, hpi]
    ring_nf
    simp only [← pow_mul] at hsign
    rw [hsign, inv_pow]
    field_simp
    <;> ring
  · intro j hj hjn
    rw [deriv_pow_mul ((Polynomial.le_natDegree_of_mem_supp j hj).trans hP) hV, if_neg hjn]
    ring
  · intro hn
    rw [Polynomial.notMem_support_iff.mp hn]
    ring
private lemma tsum_nonzero {F : Type} [Field F] [NumberField F]
    (f : Ideal (𝓞 F) → ℂ) :
    (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else f I) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, f I := by
  change _ = ∑' I : {I : Ideal (𝓞 F) | I ≠ ⊥}, f I
  rw [tsum_subtype]
  congr 1
  ext I
  by_cases hi : I = ⊥ <;> simp [Set.indicator, hi]

theorem square_log_poisson
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) :
    let data := principalHeckeData F hF
    (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
      weight (principalDiscriminant F) (principalComplexPlaces F) h
        ((Ideal.absNorm I : ℝ) / X)) =
      kappa data * (X : ℂ) * mellin h (1 / 2) / 2 -
        (2 : ℂ) ^ (principalComplexPlaces F - 1) * kappa data * mellin h 1 +
      (X : ℂ) * ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) h
          (X * (Ideal.absNorm I : ℝ)) := by
  dsimp only
  let D := principalDiscriminant F
  let r := principalComplexPlaces F
  let H := fun s : ℂ => (1 / 2 : ℂ) * B D r h (s / 2)
  have hD : 0 < D := principalDiscriminant_pos F
  have hr : 1 ≤ r := principalComplexPlaces_pos F hF
  have hf := fieldTransform_comp_sq_logMellinAdmissible D r h hD hr hh hc
    (1 / 2) (by norm_num) (by norm_num)
  have hp := (principal_logarithmic_poisson F hF hf hX).2.2.2.2
  have hdual : Vendor.reflectedLogDual D r H (2 * (1 / 2)) =
      reflectedTransform D r h := by
    have hspec : Vendor.reflectedLogSpectrum D r H = reflectedSpectrum D r h := by
      ext s
      simp only [Vendor.reflectedLogSpectrum, Vendor.logReflectionMultiplier,
        reflectedSpectrum, spectrum, H]
      ring
    ext x
    simp only [Vendor.reflectedLogDual, reflectedTransform, hspec]
    norm_num
  change (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, weight D r h ((Ideal.absNorm I.val : ℝ) / X)) =
    principalZetaResidueCoefficient F hF * (X : ℂ) * H 1 +
      principalLogResidue0 F hF
        ((originPolynomial D r h).comp (Polynomial.C (2 : ℂ) * Polynomial.X)) X +
      (X : ℂ) * (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        Vendor.reflectedLogDual D r H (2 * (1 / 2)) (X * (Ideal.absNorm I.val : ℝ))) at hp
  rw [hdual] at hp
  rw [origin_residue_eval F hF h hh hc X hX] at hp
  have hhalf : H 1 = mellin h (1 / 2) / 2 := by
    change (1 / 2 : ℂ) * B D r h (1 / 2) = _
    rw [B_half_eq_mellin D r h hD hr hh hc]
    ring
  rw [hhalf] at hp
  rw [tsum_nonzero, tsum_nonzero]
  change _ = _
  rw [hp]
  change (kappa (principalHeckeData F hF) * (X : ℂ) * (mellin h (1 / 2) / 2) + _ + _) = _
  ring
end DedekindZetaZeroFree.LargeSieve.SquarePoisson

end

end

section
/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical ContDiff Topology
open Filter
namespace DedekindZetaZeroFree.LargeSieve.SquareSecondPass

def weight (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  fieldTransform D r h (x ^ 2)

def spectrum (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  B D r h (s / 2) / 2

def reflectedSpectrum (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) * Complex.Gammaℂ s ^ r *
    (Complex.Gammaℂ (1 - s))⁻¹ ^ r * spectrum D r h (1 - s)

def reflectedTransform (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then mellinInv (3 / 2) (reflectedSpectrum D r h) x else 0
variable {F : Type} [Field F] [NumberField F]

def kappa (data : PrincipalHeckeData F) : ℂ :=
  data.E 1 / ((Real.sqrt (principalDiscriminant F) : ℂ) *
    Complex.Gammaℂ 1 ^ principalComplexPlaces F)

theorem principal_summable (data : PrincipalHeckeData F)
    (hF : NumberField.IsTotallyComplex F) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℝ) else
      ‖weight (principalDiscriminant F) (principalComplexPlaces F) h
        ((Ideal.absNorm I : ℝ) / X)‖) ∧
    Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℝ) else
      ‖reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) h
        (X * (Ideal.absNorm I : ℝ))‖) := by
  exact (SquarePoisson.reflected_and_ideal_estimates
    (principalDiscriminant F) (principalComplexPlaces F) h
    (principalDiscriminant_pos F) (principalComplexPlaces_pos F hF) hh hc).2 F X hX

theorem principal_poisson
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) :
    let data := principalHeckeData F hF
    (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
      weight (principalDiscriminant F) (principalComplexPlaces F) h
        ((Ideal.absNorm I : ℝ) / X)) =
      kappa data * (X : ℂ) * mellin h (1 / 2) / 2 -
        (2 : ℂ) ^ (principalComplexPlaces F - 1) * kappa data * mellin h 1 +
      (X : ℂ) * ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) h
          (X * (Ideal.absNorm I : ℝ)) := by
  exact SquarePoisson.square_log_poisson F hF h hh hc X hX

def coprimeOrigin (data : PrincipalHeckeData F) (h : ℝ → ℂ) (m : Ideal (𝓞 F)) : ℂ :=
  -(2 : ℂ) ^ (principalComplexPlaces F - 1) * kappa data * mellin h 1 *
    ∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ)

theorem coprime_poisson
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    let data := principalHeckeData F hF
    (∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ I ⊔ m = ⊤ then
      weight (principalDiscriminant F) (principalComplexPlaces F) h
        ((Ideal.absNorm I : ℝ) / X) else 0) =
      kappa data * (X : ℂ) * mellin h (1 / 2) / 2 *
        (∑ d ∈ idealDivisors m,
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ)) +
      coprimeOrigin data h m +
      ∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((X : ℂ) / (Ideal.absNorm d : ℂ)) *
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) h
            (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ)) := by
  let data := principalHeckeData F hF
  let g := weight (principalDiscriminant F) (principalComplexPlaces F) h
  let k := reflectedTransform (principalDiscriminant F) (principalComplexPlaces F) h
  let A := kappa data * mellin h (1 / 2) / 2
  let R := -(2 : ℂ) ^ (principalComplexPlaces F - 1) * kappa data * mellin h 1
  have hsums (Y : ℝ) (hY : 0 < Y) :
      Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℝ) else
        ‖g ((Ideal.absNorm I : ℝ) / Y)‖) :=
    (principal_summable data hF h hh hc Y hY).1
  have hp (Y : ℝ) (hY : 0 < Y) :
      (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else g ((Ideal.absNorm I : ℝ) / Y)) =
      A * (Y : ℂ) + R + (Y : ℂ) *
        ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else k (Y * (Ideal.absNorm I : ℝ)) := by
    have hpo := principal_poisson F hF h hh hc Y hY
    dsimp [g, k, data, A, R] at *
    convert hpo using 1 <;> ring
  have hmob := (SquarePoisson.finite_mobius_poisson
    F g k A R hsums hp X hX m hm).1
  dsimp [A, R, g, k, data] at hmob
  convert hmob using 1 <;> simp only [coprimeOrigin] <;> ring

end DedekindZetaZeroFree.LargeSieve.SquareSecondPass

end

end
