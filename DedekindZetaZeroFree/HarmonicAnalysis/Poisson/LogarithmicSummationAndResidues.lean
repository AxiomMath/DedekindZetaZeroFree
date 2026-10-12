module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.ReflectedLogarithmicSpectrum
public import DedekindZetaZeroFree.LFunctions.Hecke.LogarithmicMellinContourBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicIdealInterchange
public import DedekindZetaZeroFree.Analysis.ContourIntegration.FiniteOrderResidueSums
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicIdealSummability

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open Filter MeasureTheory
open scoped NumberField Classical Topology

namespace DedekindZetaZeroFree.LargeSieve

private lemma sum_pair (g : ({0, 1} : Finset ℝ) → ℂ) :
    (∑ p : ({0, 1} : Finset ℝ), g p) = g ⟨0, by simp⟩ + g ⟨1, by simp⟩ := by
  rw [show (Finset.univ : Finset ↥({0, 1} : Finset ℝ)) = {⟨0, by simp⟩, ⟨1, by simp⟩} from by
    ext p; simp [Subtype.ext_iff, Finset.mem_insert, Finset.mem_singleton, eq_comm, or_comm]]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]

def principalLogResidue0
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (P : Polynomial ℂ) (X : ℝ) : ℂ :=
  ∑ j ∈ P.support, (-1 : ℂ) ^ j * P.coeff j *
    iteratedDeriv j
      (fun s : ℂ => (X : ℂ) ^ s * principalZetaContinuation F hF s) 0

private lemma reflection_power {D q X : ℝ} (hD : 0 < D) (hq : 0 < q) (hX : 0 < X) (s : ℂ) :
    (X : ℂ) ^ s * (D * q : ℝ) ^ ((1 : ℂ) / 2 - s) =
      (X : ℂ) / (Real.sqrt q : ℂ) * (D : ℂ) ^ ((1 : ℂ) / 2 - s) *
        (X / q : ℝ) ^ (-(1 - s : ℂ)) := by
  have hqn : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hsqrt : (q : ℂ) ^ ((1 : ℂ) / 2) = (Real.sqrt q : ℂ) := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hq.le, Real.sqrt_eq_rpow]
  push_cast
  rw [Complex.mul_cpow_ofReal_nonneg hD.le hq.le,
    Complex.div_cpow_ofReal_nonneg hX.le hq.le]
  have hpX : (X : ℂ) ^ s = (X : ℂ) * (X : ℂ) ^ (-(1 - s : ℂ)) := by
    conv_rhs => lhs; rw [← Complex.cpow_one (X : ℂ)]
    rw [← Complex.cpow_add _ _ hXn]
    congr 1; ring
  have hpq : (q : ℂ) ^ ((1 : ℂ) / 2 - s) =
      ((q : ℂ) ^ (-(1 - s : ℂ)))⁻¹ / (Real.sqrt q : ℂ) := by
    rw [← hsqrt, ← Complex.cpow_neg, ← Complex.cpow_sub _ _ hqn]
    congr 1; ring
  rw [hpX, hpq]
  ring

private lemma logarithmic_left_integral
    {F : Type} [Field F] [NumberField F]
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H)
    (D : ℝ) (r : ℕ) (hD : 0 < D) (hr : 1 ≤ r)
    (q X : ℝ) (hq : 0 < q) (hX : 0 < X) (W : ℂ)
    (a : Ideal (𝓞 F) → ℂ) (ha : ∀ I, I ≠ ⊥ → ‖a I‖ ≤ 1)
    (L Lbar : ℂ → ℂ)
    (hFE : ∀ s : ℂ, s.re < 0 → L s = W * (D * q : ℝ) ^ ((1 : ℂ) / 2 - s) *
      Complex.Gammaℂ (1 - s) ^ r * (Complex.Gammaℂ s)⁻¹ ^ r * Lbar (1 - s))
    (hDS : ∀ s : ℂ, 1 < s.re → Lbar s = idealCoefficientLSeries a s) :
    let k := Vendor.reflectedLogDual D r H δ
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖a I.val * k (X * (Ideal.absNorm I.val : ℝ) / q)‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      a I.val * k (X * (Ideal.absNorm I.val : ℝ) / q)) ∧
    Vendor.verticalIntegral (-δ / 2) (Vendor.logMellinProduct H L X) =
      W * (X : ℂ) / (Real.sqrt q : ℂ) *
        (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          a I.val * k (X * (Ideal.absNorm I.val : ℝ) / q)) := by
  let c : ℝ := 1 + δ / 2
  let K := Vendor.reflectedLogSpectrum D r H
  let k := Vendor.reflectedLogDual D r H δ
  have hc : 1 < c := by dsimp [c]; linarith [hf.delta_pos]
  have hcδ : c < 1 + δ := by dsimp [c]; linarith [hf.delta_pos]
  have hKcont : Continuous (fun t : ℝ => K ((c : ℂ) + t * Complex.I)) := by
    exact (Vendor.reflectedLogSpectrum_differentiableOn D r hD hr hf).continuousOn.comp_continuous
      (show Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I) by fun_prop)
      (fun t => by simpa using And.intro hc hcδ)
  obtain ⟨_, _, _, hdn, hds, hVI, hVeq⟩ :=
    idealLogMellin_inverseSpectrum_interchange a ha K k hc (div_pos hX hq)
      hKcont (Vendor.reflectedLogSpectrum_verticalIntegrable D r hD hr hf c hc hcδ)
      (fun x hx => Vendor.reflectedLogDual_eq_mellinInv D r hD hr hf c x hc hcδ hx)
  have hscale : ∀ n : ℝ, X / q * n = X * n / q := by intro n; ring
  simp_rw [hscale] at hdn hds hVeq
  refine ⟨hdn, hds, ?_⟩
  let G : ℂ → ℂ := fun s => K s * (X / q : ℝ) ^ (-s) * idealCoefficientLSeries a s
  have heq : Vendor.verticalIntegral (-δ / 2) (Vendor.logMellinProduct H L X) =
      Vendor.verticalIntegral (-δ / 2) (fun s => (W * (X : ℂ) / (Real.sqrt q : ℂ)) * G (1 - s)) := by
    unfold Vendor.verticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    let s : ℂ := ((-δ / 2 : ℝ) : ℂ) + t * Complex.I
    have hs : s.re < 0 := by
      dsimp [s]
      simp only [Complex.add_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hf.delta_pos]
    have ht : 1 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    change H s * (X : ℂ) ^ s * L s = _
    rw [hFE s hs]
    dsimp [G, K, Vendor.reflectedLogSpectrum, Vendor.logReflectionMultiplier]
    rw [← hDS (1 - s) ht]
    have hp := reflection_power hD hq hX s
    rw [show 1 - (1 - s) = s by ring, show 1 - s - 1 / 2 = (1 : ℂ) / 2 - s by ring]
    calc
      _ = W * H s * ((X : ℂ) ^ s * (D * q : ℝ) ^ ((1 : ℂ) / 2 - s)) *
          Complex.Gammaℂ (1 - s) ^ r * (Complex.Gammaℂ s)⁻¹ ^ r * Lbar (1 - s) := by ring
      _ = _ := by rw [hp]; ring
  rw [heq]
  have hreflect : Vendor.verticalIntegral (-δ / 2) (fun s =>
      (W * (X : ℂ) / (Real.sqrt q : ℂ)) * G (1 - s)) =
      Vendor.verticalIntegral c (fun s => (W * (X : ℂ) / (Real.sqrt q : ℂ)) * G s) := by
    have h := Vendor.verticalIntegral_one_sub (-δ / 2)
      (fun s => (W * (X : ℂ) / (Real.sqrt q : ℂ)) * G s)
    convert h using 1 <;> congr 1
    dsimp [c]; ring
  rw [hreflect, Vendor.verticalIntegral_const_mul c _ G hVI, hVeq]

theorem principal_logarithmic_contour
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H) {X : ℝ} (hX : 0 < X)
    (a b : ℝ) (haδ : -δ < a) (ha0 : a < 0) (hb : 1 < b) :
    let M := Vendor.logMellinProduct H (principalZetaContinuation F hF) X
    Complex.VerticalIntegrable M a ∧ Complex.VerticalIntegrable M b ∧
    (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, f ((Ideal.absNorm I.val : ℝ) / X)) =
      Vendor.verticalIntegral b M ∧
    Vendor.verticalIntegral b M - Vendor.verticalIntegral a M =
      principalLogResidue0 F hF P X +
        principalZetaResidueCoefficient F hF * (X : ℂ) * H 1 := by
  obtain ⟨hholo, hpp0, hpp1, hG⟩ :=
    principalLogMellinProduct_contour_data F hF hf X hX
  obtain ⟨hbd_a, hbd_b⟩ :=
    principalLogMellinProduct_boundary_integrable F hF hf X hX a b haδ ha0 hb
  obtain ⟨Cg, Ag, hCg, hAg, hgrowth⟩ :=
    principalLogMellinProduct_subquadratic_growth F hF hf X hX a b haδ ha0 hb
  refine ⟨hbd_a, hbd_b, ?_, ?_⟩
  · have hnorm : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
        ‖(fun I => principalCharacter F I) I‖ ≤ 1 :=
      fun I hI => by simp [principalCharacter_apply, hI]
    obtain ⟨_, hsrc⟩ :=
      idealLogMellin_source_interchange (fun I : Ideal (𝓞 F) => principalCharacter F I)
        hnorm hf hX hb
    have hsub : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          f ((Ideal.absNorm I.val : ℝ) / X))
        = ∑' I : Ideal (𝓞 F), idealMellinWeight (fun I => principalCharacter F I) f X I := by
      rw [show (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
            f ((Ideal.absNorm I.val : ℝ) / X))
          = ∑' x : ({I : Ideal (𝓞 F) | I ≠ ⊥}),
              f ((Ideal.absNorm x.val : ℝ) / X) from rfl,
        tsum_subtype ({I : Ideal (𝓞 F) | I ≠ ⊥})
          (fun I => f ((Ideal.absNorm I : ℝ) / X))]
      refine tsum_congr fun I => ?_
      by_cases hI : I = ⊥
      · simp [Set.indicator, idealMellinWeight, hI]
      · simp [Set.indicator, idealMellinWeight, hI, principalCharacter_apply]
    rw [hsub, ← hsrc]
    simp only [Vendor.verticalIntegral]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    simp only [Vendor.logMellinProduct]
    rw [idealCoefficientLSeries_eq_tsum_zeroBranch,
      principalZetaContinuation_eq_dirichlet F hF _ (by
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
        exact hb)]
    congr 1
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;> simp [hI, principalCharacter_apply]
  · have hab : a < b := by linarith
    have hmain := Vendor.verticalIntegral_sub_eq_sum_residues_of_finite_order
      (a := a) (b := b) hab ({0, 1} : Finset ℝ)
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with hp | hp
        · subst hp; exact ⟨ha0, by linarith⟩
        · subst hp; exact ⟨by linarith, by linarith⟩)
      (fun p => if (p.val : ℝ) = 0 then P.natDegree + 1 else 1)
      (fun p k => if (p.val : ℝ) = 0 then
          Vendor.logProductPrincipalCoeff P X (principalZetaContinuation F hF) k
        else if k = 1 then principalZetaResidueCoefficient F hF * (X : ℂ) * H 1 else 0)
      (Vendor.logMellinProduct H (principalZetaContinuation F hF) X) {s : ℂ | -δ < s.re}
      (isOpen_lt continuous_const Complex.continuous_re)
      (fun s hs => lt_of_lt_of_le haδ hs.1)
      (hholo.mono (by
        rintro s ⟨h1, h2⟩
        exact ⟨h1, (fun hs0 => h2 ⟨⟨0, by simp⟩, by simp [hs0]⟩),
          (fun hs1 => h2 ⟨⟨1, by simp⟩, by simp [hs1]⟩)⟩))
      (by
        refine ⟨hG.choose, hG.choose_spec.1, ?_⟩
        intro s hs hsne
        have hsum : (∑ p : ({0, 1} : Finset ℝ),
              ∑ k ∈ Finset.Icc 1 (if (p.val : ℝ) = 0 then P.natDegree + 1 else 1),
                (if (p.val : ℝ) = 0 then
                    Vendor.logProductPrincipalCoeff P X (principalZetaContinuation F hF) k
                  else if k = 1 then
                    principalZetaResidueCoefficient F hF * (X : ℂ) * H 1 else 0) /
                  (s - (p.val : ℂ)) ^ k)
            = (∑ j ∈ Finset.Icc 1 (P.natDegree + 1),
                Vendor.logProductPrincipalCoeff P X (principalZetaContinuation F hF) j /
                  s ^ j)
              + principalZetaResidueCoefficient F hF * (X : ℂ) * H 1 / (s - 1) := by
          rw [sum_pair]
          congr 1
          · simp
          · simp [Finset.Icc_self]
        rw [hsum, hG.choose_spec.2 s hs (hsne ⟨0, by simp⟩) (hsne ⟨1, by simp⟩)]
        ring)
      hbd_a hbd_b ⟨Cg, Ag, hCg, hAg, hgrowth⟩
    rw [hmain, sum_pair]
    simp only [Nat.succ_ne_zero, if_false, if_true, one_ne_zero, ↓reduceIte]
    rw [Vendor.logProductPrincipalCoeff_one]
    rfl

theorem principal_logarithmic_poisson
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : Vendor.LogMellinAdmissible f δ P H) {X : ℝ} (hX : 0 < X) :
    let k := Vendor.reflectedLogDual (principalDiscriminant F)
      (principalComplexPlaces F) H δ
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖f ((Ideal.absNorm I.val : ℝ) / X)‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      f ((Ideal.absNorm I.val : ℝ) / X)) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖k (X * (Ideal.absNorm I.val : ℝ))‖) ∧
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      k (X * (Ideal.absNorm I.val : ℝ))) ∧
    (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, f ((Ideal.absNorm I.val : ℝ) / X)) =
      principalZetaResidueCoefficient F hF * (X : ℂ) * H 1 +
        principalLogResidue0 F hF P X +
        (X : ℂ) * (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          k (X * (Ideal.absNorm I.val : ℝ))) := by
  have hnorm : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ‖(1 : ℂ)‖ ≤ 1 := fun _ _ => by simp
  obtain ⟨hsn, hss⟩ := Vendor.logIdealTerm_summable (fun _ : Ideal (𝓞 F) => 1)
    hnorm hf.physical X hX
  have hn : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖f ((Ideal.absNorm I.val : ℝ) / X)‖) :=
    (hsn.subtype (fun I : Ideal (𝓞 F) => I ≠ ⊥)).congr
      (fun I => by simp only [Function.comp_apply, Vendor.logIdealTerm, if_neg I.property, one_mul])
  have hs : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      f ((Ideal.absNorm I.val : ℝ) / X)) :=
    (hss.subtype (fun I : Ideal (𝓞 F) => I ≠ ⊥)).congr
      (fun I => by simp only [Function.comp_apply, Vendor.logIdealTerm, if_neg I.property, one_mul])
  obtain ⟨hdn, hds, hleft⟩ := logarithmic_left_integral hf
    (principalDiscriminant F) (principalComplexPlaces F)
    (principalDiscriminant_pos F) (principalComplexPlaces_pos F hF)
    1 X one_pos hX 1 (fun _ : Ideal (𝓞 F) => 1) hnorm
    (principalZetaContinuation F hF) (principalZetaContinuation F hF)
    (fun s hs => by simpa only [mul_one, one_mul] using
      principalZetaContinuation_functional_equation F hF s hs)
    (fun s hs => by
      rw [principalZetaContinuation_eq_dirichlet F hF s hs,
        idealCoefficientLSeries_eq_tsum_zeroBranch]
      apply tsum_congr
      intro I
      split_ifs <;> simp)
  simp only [div_one, Real.sqrt_one, Complex.ofReal_one, one_mul] at hdn hds hleft
  obtain ⟨_, _, hsrc, hshift⟩ := principal_logarithmic_contour
     F hF hf hX (-δ / 2) 2
    (by linarith [hf.delta_pos]) (by linarith [hf.delta_pos]) (by norm_num)
  refine ⟨hn, hs, hdn, hds, ?_⟩
  rw [hsrc]
  rw [hleft] at hshift
  rw [sub_eq_iff_eq_add] at hshift
  rw [hshift]
  ring

end DedekindZetaZeroFree.LargeSieve

end
