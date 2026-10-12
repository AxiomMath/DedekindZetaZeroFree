module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Coefficients.DivisorRectanglesAndEpsilonEnergyBounds
public import DedekindZetaZeroFree.LargeSieve.Bilinear.FourierRectangles.ReflectedRowInversionAndExpansion

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

 def WC (C : Context Q) : Context Q :=
  { C with lam := fun b => weightedColumn C (Function.invFun (fun u => C.d * u) b) }
private lemma wc_lam (C : Context Q) (u : Ideal (𝓞 F)) :
    (WC C).lam (C.d*u) = weightedColumn C u := by
  dsimp [WC]
  rw [Function.leftInverse_invFun (fun a b h => mul_left_cancel₀ C.hd0 h)]
 def phase (C : Context Q) (t : ℝ) (u : Ideal (𝓞 F)) : ℂ :=
  Complex.exp (((2 * Real.pi * (t * Real.log (norm u / (C.N / norm C.d)))) : ℝ) * Complex.I)
private lemma phase_norm (C : Context Q) (t : ℝ) (u : Ideal (𝓞 F)) : ‖phase C t u‖ = 1 := by
  simp [phase, Complex.norm_exp]
private lemma phase_split (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (t s : ℝ) :
    frequencyPhase C p t s = phase C t p.1 * star (phase C (-s) p.2) := by
  simp only [frequencyPhase, phase, Complex.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul, mul_neg, neg_neg]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
 def E (C : Context Q) (f : Ideal (𝓞 F)) : ℝ :=
  ∑ u ∈ C.columns, if f ∣ u then
    (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors u).toFinset.card * ‖weightedColumn C u‖^2 else 0
private lemma wc_energy (C : Context Q) (f : Ideal (𝓞 F)) : SupportedRows.energy (WC C) f = E C f := by
  unfold SupportedRows.energy E
  simp only [show (WC C).columns = C.columns from rfl, show (WC C).d = C.d from rfl, wc_lam]
private lemma wc_pairs (C : Context Q) : (WC C).pairs = C.pairs := by
  ext p
  simp only [Context.pairs, Finset.mem_filter]
  constructor <;> rintro ⟨hp, hv⟩ <;> exact ⟨hp, ⟨hv.hu0, hv.hv0, hv.hu, hv.hv, hv.huc, hv.hvc, hv.hdu, hv.hdv, hv.hduc, hv.hdvc, hv.huv, hv.hduv, hv.hclass, hv.hquotientClass, hv.offDiagonal⟩⟩
private lemma freq_core (C : Context Q) (φ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hsplit : ∀ e ∈ C.mobiusDivisors, ∀ b ∈ squarefreeBadPool c,
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p, ∀ r, r ⊔ c = ⊤ →
      C.primitive p hp e * C.primitive p hp (b*r) =
        (φ p.1 (e*b) * (Q.χ p.1) r) * star (φ p.2 (e*b) * (Q.χ p.2) r))
    (e b r f g : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
    (hb : b ∈ squarefreeBadPool c) (hrc : r ⊔ c = ⊤) (t s : ℝ) :
    frequencyCell C e (b*r) f g t s =
      SupportedRows.coreBlock (WC C) f g
        (fun u => weightedColumn C u * φ u (e*b) * phase C t u)
        (fun u => weightedColumn C u * φ u (e*b) * phase C (-s) u) r := by
  unfold frequencyCell Context.pairSum SupportedRows.coreBlock
  rw [wc_pairs]
  apply Finset.sum_congr rfl
  intro p hp
  have hpv := (Finset.mem_filter.mp hp).2
  rw [dif_pos hpv]
  dsimp only
  split_ifs with h
  · rw [mul_assoc (weightedColumn C p.1 * star (weightedColumn C p.2)),
      hsplit e he b hb p hp hpv r hrc, phase_split]
    simp only [star_mul]
    ring
  · rfl
private lemma cell_bound (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Context Q, C.D = D → 1 ≤ C.N →
      ∀ B unit, 1 ≤ B → (unit = true → B = 1) →
      ∀ e ∈ C.mobiusDivisors, ∀ P₁ P₂ : ℝ, 1 ≤ P₁ → 1 ≤ P₂ →
      ∀ f g : Ideal (𝓞 F), f ≠ ⊥ → g ≠ ⊥ → P₁ ≤ norm f → P₂ ≤ norm g →
      ∀ t s : ℝ, (∑ a ∈ C.reflectedRows B unit, ‖frequencyCell C e a f g t s‖) ≤
        A * Real.sqrt (U Q B (C.N/(norm C.d*P₁)) * U Q B (C.N/(norm C.d*P₂))) *
          Real.sqrt (E C f * E C g) := by
  obtain ⟨A, hA, hbound⟩ := SupportedRows.core_divisible_pair_bound D
  refine ⟨A * (((squarefreeBadPool c).card : ℝ) + 1), by positivity, ?_⟩
  intro C hCD hN B unit hB hunit e he P₁ P₂ hP₁ hP₂ f g hf hg hPf hPg t s
  obtain ⟨φ, hφ, hsplit⟩ := LargeDual.supported_primitive_phase_core C
  have hR := SupportedRows.reflected_core_rows_subset C B unit hunit hB
  have hnorm (t : ℝ) (b : Ideal (𝓞 F)) :
      ∀ u ∈ (WC C).columns, ‖weightedColumn C u * φ u (e*b) * phase C t u‖ ≤ ‖(WC C).lam ((WC C).d*u)‖ := by
    intro u hu
    rw [show (WC C).d = C.d from rfl, wc_lam, norm_mul, phase_norm, mul_one, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hφ u hu _)
  have hbnd (b : Ideal (𝓞 F)) (hb : b ∈ squarefreeBadPool c) :
      (∑ r ∈ C.reflectedCoreRows B unit, ‖frequencyCell C e (b*r) f g t s‖) ≤
      A * Real.sqrt (U Q B (C.N/(norm C.d*P₁)) * U Q B (C.N/(norm C.d*P₂))) * Real.sqrt (E C f * E C g) := by
    have hh := hbound (WC C) hCD hN B P₁ P₂ hB hP₁ hP₂ f g hf hg hPf hPg
      (C.reflectedCoreRows B unit) hR
      (fun u => weightedColumn C u * φ u (e*b) * phase C t u)
      (fun u => weightedColumn C u * φ u (e*b) * phase C (-s) u) (hnorm t b) (hnorm (-s) b)
    rw [wc_energy, wc_energy] at hh
    change _ ≤ A * Real.sqrt (U Q B (C.N/(norm C.d*P₁)) * U Q B (C.N/(norm C.d*P₂))) * Real.sqrt (E C f * E C g) at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [freq_core C φ hsplit e b r f g he hb ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (hR hr)).2.1 t s]
  calc
    _ ≤ ∑ tr ∈ C.reflectedRowIndices B unit, ‖frequencyCell C e (tr.1*tr.2) f g t s‖ :=
      Finset.sum_image_le_of_nonneg (f := fun a => ‖frequencyCell C e a f g t s‖)
        (g := fun tr : Ideal (𝓞 F) × Ideal (𝓞 F) => tr.1*tr.2) (by intros; positivity)
    _ ≤ ∑ tr ∈ (squarefreeBadPool c) ×ˢ C.reflectedCoreRows B unit,
        ‖frequencyCell C e (tr.1*tr.2) f g t s‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    _ ≤ ∑ b ∈ squarefreeBadPool c,
        A * Real.sqrt (U Q B (C.N/(norm C.d*P₁)) * U Q B (C.N/(norm C.d*P₂))) * Real.sqrt (E C f * E C g) := by
      rw [Finset.sum_product]
      exact Finset.sum_le_sum hbnd
    _ ≤ (A * (((squarefreeBadPool c).card : ℝ) + 1)) *
        Real.sqrt (U Q B (C.N/(norm C.d*P₁)) * U Q B (C.N/(norm C.d*P₂))) * Real.sqrt (E C f * E C g) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hz : 0 ≤ A * Real.sqrt (U Q B (C.N/(norm C.d*P₁)) * U Q B (C.N/(norm C.d*P₂))) * Real.sqrt (E C f * E C g) := by positivity
      nlinarith

private lemma incidence_le (C : Context Q) (S : Finset (Ideal (𝓞 F))) :
    (∑ f ∈ S, E C f) ≤ Origin.incidenceEnergy C := by
  unfold E Origin.incidenceEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u hu
  have hu0 : u ≠ ⊥ := ((Sieve.mem_idealAdmissibleFinset F c _ u).mp (Finset.mem_filter.mp hu).1).1.ne_zero
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((S.filter (fun f => f ∣ u)).card : ℝ) ≤ ((idealDivisors u).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (fun f hf => (mem_idealDivisors hu0).mpr (Finset.mem_filter.mp hf).2)
  calc
    _ ≤ ((idealDivisors u).card : ℝ) * ((2:ℝ)^_ * ‖weightedColumn C u‖^2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by unfold weightedColumn; ring

private lemma cost_one (C : Context Q) : 1 ≤ Origin.assemblyCost C := by
  have hm : 1 ≤ C.mobiusDivisors.card := by
    apply Finset.one_le_card.mpr
    refine ⟨⊤, ?_⟩
    refine (mem_idealDivisors ?_).mpr ?_
    · intro hh
      have hc : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
      have hcd : c * C.d ≠ ⊥ := mul_ne_zero hc C.hd0
      exact hcd (bot_unique (hh ▸ Ideal.le_radical))
    · simpa only [← Ideal.one_eq_top] using one_dvd ((c * C.d).radical)
  have hs : 1 ≤ (ErrorRectangles.scales (C.N / norm C.d)).card :=
    Finset.one_le_card.mpr ⟨1, Finset.mem_insert_self _ _⟩
  unfold Origin.assemblyCost
  have hm' : (1:ℝ) ≤ (C.mobiusDivisors.card : ℝ) := by exact_mod_cast hm
  have hs' : (1:ℝ) ≤ ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) := by exact_mod_cast hs
  nlinarith

private lemma bin_cauchy (C : Context Q) (S T : Finset (Ideal (𝓞 F))) :
    (∑ f ∈ S, ∑ g ∈ T, Real.sqrt (E C f * E C g)) ≤
      Real.sqrt ((S.card:ℝ)*(T.card:ℝ)) * Origin.incidenceEnergy C := by
  have he : ∀ f, 0 ≤ E C f := by intro f; unfold E; apply Finset.sum_nonneg; intro u hu; split_ifs <;> positivity
  have hh := Real.sum_sqrt_mul_sqrt_le (f := fun _ : Ideal (𝓞 F) × Ideal (𝓞 F) => (1:ℝ))
    (g := fun fg => E C fg.1 * E C fg.2) (S ×ˢ T) (fun _ => zero_le_one)
    (fun fg => mul_nonneg (he _) (he _))
  simp only [Real.sqrt_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hh
  rw [← Finset.sum_mul_sum] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hi : 0 ≤ Origin.incidenceEnergy C := by unfold Origin.incidenceEnergy; positivity
  calc
    _ ≤ Real.sqrt (Origin.incidenceEnergy C * Origin.incidenceEnergy C) :=
      Real.sqrt_le_sqrt (mul_le_mul (incidence_le C S) (incidence_le C T)
        (Finset.sum_nonneg (fun f hf => he f)) hi)
    _ = _ := by rw [← pow_two, Real.sqrt_sq hi]

theorem common_frequency_rectangle_bound
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c) :
    ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 < A ∧
      ∀ C : Context Q, C.D = D →
      1 ≤ C.M → 1 ≤ C.N → 1 ≤ C.K → C.K ≤ C.M →
      norm C.d ≤ 2 * C.N →
      ∀ (B : ℝ) (unit : Bool), 1 ≤ B → B ≤ C.K → (unit = true → B = 1) →
      ∀ e ∈ C.mobiusDivisors, ∀ ij : ℕ × ℕ, ∀ t s : ℝ,
        rectangleCost C B unit e ij t s ≤
          A * Real.rpow (C.M * C.N * norm C.d) η *
            rectangleValue Q B C.N (norm C.d) ij * weightedEnergy C := by
  intro η hη
  obtain ⟨L, hL, hcell⟩ := cell_bound D
  obtain ⟨H, hH, henergy⟩ := Origin.energy_epsilon D η hη
  obtain ⟨K, hK, _, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  refine ⟨L * (2*K) * H, by positivity, ?_⟩
  intro C hCD hM hN hK1 hKM hnN B unit hB hBK hunit e he ij t s
  have hn : 1 ≤ norm C.d := by
    dsimp [ExplicitTerms.norm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr C.hd0)
  have hP (j : ℕ) : 1 ≤ divisorScale j := one_le_pow₀ (by norm_num)
  have hP0 (j : ℕ) : 0 ≤ divisorScale j := le_trans zero_le_one (hP j)
  have hbin (j : ℕ) (f : Ideal (𝓞 F)) (hf : f ∈ divisorBucket F (2*C.N/norm C.d) j) :
      f ≠ ⊥ ∧ divisorScale j ≤ norm f := ⟨(Finset.mem_filter.mp hf).2.1, (Finset.mem_filter.mp hf).2.2.1⟩
  let S := divisorBucket F (2*C.N/norm C.d) ij.1
  let T := divisorBucket F (2*C.N/norm C.d) ij.2
  have hcards (j : ℕ) : ((divisorBucket F (2*C.N/norm C.d) j).card : ℝ) ≤ 2*K*divisorScale j := by
    have hh := hcount (2*divisorScale j) (by nlinarith [hP j])
      (divisorBucket F (2*C.N/norm C.d) j)
      (fun f hf => (Finset.mem_filter.mp hf).2.2.2.le)
    nlinarith
  have hcardroot : Real.sqrt ((S.card:ℝ)*(T.card:ℝ)) ≤ (2*K) * Real.sqrt (divisorScale ij.1 * divisorScale ij.2) := by
    calc
      _ ≤ Real.sqrt ((2*K*divisorScale ij.1)*(2*K*divisorScale ij.2)) :=
        Real.sqrt_le_sqrt (mul_le_mul (hcards ij.1) (hcards ij.2) (Nat.cast_nonneg _) (mul_nonneg (by positivity) (hP0 _)))
      _ = _ := by
        rw [show (2*K*divisorScale ij.1)*(2*K*divisorScale ij.2) = (2*K)^2*(divisorScale ij.1*divisorScale ij.2) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hi : 0 ≤ Origin.incidenceEnergy C := by unfold Origin.incidenceEnergy; positivity
  have hinc : Origin.incidenceEnergy C ≤ H * Real.rpow (C.M*C.N*norm C.d) η * weightedEnergy C := by
    apply (le_mul_of_one_le_left hi (cost_one C)).trans
    exact henergy C hCD hM hN hn hnN
  let V := Real.sqrt (U Q B (C.N/(norm C.d*divisorScale ij.1)) * U Q B (C.N/(norm C.d*divisorScale ij.2)))
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have heq : Real.sqrt (divisorScale ij.1 * divisorScale ij.2) * V = rectangleValue Q B C.N (norm C.d) ij := by
    dsimp [V, rectangleValue]
    rw [← Real.sqrt_mul (mul_nonneg (hP0 _) (hP0 _))]
    congr 1
    ring
  calc
    rectangleCost C B unit e ij t s ≤
        ∑ f ∈ S, ∑ g ∈ T, L * V * Real.sqrt (E C f * E C g) := by
      apply Finset.sum_le_sum
      intro f hf
      apply Finset.sum_le_sum
      intro g hg
      exact hcell C hCD hN B unit hB hunit e he _ _ (hP _) (hP _) f g
        (hbin _ f hf).1 (hbin _ g hg).1 (hbin _ f hf).2 (hbin _ g hg).2 t s
    _ = L * V * (∑ f ∈ S, ∑ g ∈ T, Real.sqrt (E C f * E C g)) := by simp only [Finset.mul_sum]
    _ ≤ L * V * (Real.sqrt ((S.card:ℝ)*(T.card:ℝ)) * Origin.incidenceEnergy C) :=
      mul_le_mul_of_nonneg_left (bin_cauchy C S T) (mul_nonneg hL.le hV)
    _ ≤ L * V * ((2*K) * Real.sqrt (divisorScale ij.1 * divisorScale ij.2) *
        (H * Real.rpow (C.M*C.N*norm C.d) η * weightedEnergy C)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL.le hV)
      exact mul_le_mul hcardroot hinc hi (by positivity)
    _ = _ := by
      rw [← heq]
      ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma norm_one_le {f : Ideal (𝓞 F)} (hf : f ≠ ⊥) : 1 ≤ norm f := by
  change (1 : ℝ) ≤ Ideal.absNorm f
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hf)

private lemma fixed_mass_le (C : Context Q) :
    (∑ e ∈ C.mobiusDivisors, (norm e)⁻¹) ≤ (idealDivisorCount (c * C.d) : ℝ) := by
  have hcd : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have hr : (c * C.d).radical ≠ ⊥ := by
    intro h
    have hh := Ideal.le_radical (I := c * C.d)
    rw [h] at hh
    exact hcd (le_bot_iff.mp hh)
  have hsub : C.mobiusDivisors ⊆ idealDivisors (c * C.d) := by
    intro e he
    exact (mem_idealDivisors hcd).mpr (((mem_idealDivisors hr).mp he).trans
      (Ideal.dvd_iff_le.mpr Ideal.le_radical))
  calc
    _ ≤ ∑ e ∈ C.mobiusDivisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      exact inv_le_one_of_one_le₀ (norm_one_le (ne_bot_of_mem_idealDivisors he))
    _ = (C.mobiusDivisors.card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

private lemma common_threshold (C : Context Q) (B : ℝ) (hM : 1 ≤ C.M)
    (hN : 1 ≤ C.N) (hB : 1 ≤ B) : Threshold C B (max 1 (norm c)) := by
  intro e he
  have hn := norm_one_le C.hd0
  have hcd : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have hr : (c * C.d).radical ≠ ⊥ := by
    intro h
    exact hcd (le_bot_iff.mp (h ▸ Ideal.le_radical))
  have hedvd : e ∣ c * C.d := ((mem_idealDivisors hr).mp he).trans
    (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  have heN : norm e ≤ norm c * norm C.d := by
    have hp := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hcd)
    have hle := Nat.le_of_dvd hp (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hedvd))
    simpa [ExplicitTerms.norm, map_mul] using (show (Ideal.absNorm e : ℝ) ≤ Ideal.absNorm (c * C.d) by exact_mod_cast hle)
  have hc : 1 ≤ max 1 (norm c) := le_max_left _ _
  have hc' : norm c ≤ max 1 (norm c) := le_max_right _ _
  have hs : Real.sqrt (norm e) ≤ max 1 (norm c) * norm C.d := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hprod : 1 ≤ max 1 (norm c) * norm C.d := one_le_mul_of_one_le_of_one_le hc hn
    have heq : norm e ≤ max 1 (norm c) * norm C.d :=
      heN.trans (mul_le_mul_of_nonneg_right hc' (by linarith))
    nlinarith
  have hn0 : 0 < norm C.d := by linarith
  have hs0 : 0 < Real.sqrt (B * C.M) := Real.sqrt_pos.mpr (by positivity)
  have hθ0 : 0 ≤ Real.rpow (C.M * C.N) C.δ := Real.rpow_nonneg (by positivity) _
  unfold Context.Z1
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ C.N))
      (mul_nonneg hn0.le hs0.le)) hθ0
  apply hh.trans_eq
  field_simp

private lemma finite_R_set (B M N n θ Cq : ℝ) :
    Set.Finite ({0} ∪ {z : ℝ | ∃ ij ∈ rectangles F B M N n θ Cq,
      z = rectangleValue Q B N n ij}) := by
  apply Set.Finite.union (Set.finite_singleton 0)
  have h := (rectangles F B M N n θ Cq).finite_toSet.image (rectangleValue Q B N n)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
  constructor <;> rintro ⟨ij, hij, rfl⟩ <;> exact ⟨ij, hij, rfl⟩

private lemma R_nonneg' (B M N n θ Cq : ℝ) : 0 ≤ R Q B M N n θ Cq := by
  exact le_csSup (finite_R_set (Q := Q) B M N n θ Cq).bddAbove (Or.inl rfl)

private lemma value_le_R (B M N n θ Cq : ℝ) (ij : ℕ × ℕ)
    (hij : ij ∈ rectangles F B M N n θ Cq) :
    rectangleValue Q B N n ij ≤ R Q B M N n θ Cq := by
  exact le_csSup (finite_R_set (Q := Q) B M N n θ Cq).bddAbove (Or.inr ⟨ij, hij, rfl⟩)

private lemma frequencyWeight_integrable : Integrable frequencyWeight := by
  unfold frequencyWeight
  simp only [mul_inv]
  rw [Measure.volume_eq_prod]
  exact integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq

private lemma frequencyWeight_integral : (∫ p : ℝ × ℝ, frequencyWeight p) = Real.pi ^ 2 := by
  simp only [frequencyWeight, mul_inv]
  rw [Measure.volume_eq_prod]
  rw [integral_prod_mul (fun x : ℝ => (1 + x ^ 2)⁻¹) (fun x : ℝ => (1 + x ^ 2)⁻¹)]
  rw [integral_univ_inv_one_add_sq]
  ring

private lemma finite_cost_epsilon (η : ℝ) (hη : 0 < η) :
    ∃ J : ℝ, 0 < J ∧ ∀ C : Context Q,
      1 ≤ C.M → 1 ≤ C.N → norm C.d ≤ 2 * C.N → ∀ B Cq : ℝ,
        (∑ e ∈ C.mobiusDivisors, (norm e)⁻¹) *
          ((rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq).card : ℝ) ≤
            J * Real.rpow (C.M * C.N * norm C.d) η := by
  let e := η / 3
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨A, hA, hdiv⟩ := ideal_divisor_count_le_rpow F e he
  let T := max 1 (norm c)
  let L := 2 + 1 / (e * Real.log 2)
  let H := L * (2 : ℝ) ^ e
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hL : 0 < L := Vendor.dyadicLength_small_power_constant_pos he
  have hH : 0 < H := mul_pos hL (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨(A * T ^ e) * H ^ 2, by positivity, ?_⟩
  intro C hM hN hnN B Cq
  have hn := norm_one_le C.hd0
  let Z := C.M * C.N * norm C.d
  have hMN : 1 ≤ C.M * C.N := one_le_mul_of_one_le_of_one_le hM hN
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hMN hn
  have hnZ : norm C.d ≤ Z := le_mul_of_one_le_left (by linarith) hMN
  have hNZ : C.N ≤ Z := by
    dsimp [Z]
    exact (le_mul_of_one_le_left (by linarith) hM).trans
      (le_mul_of_one_le_right (by linarith) hn)
  have hf : (∑ e ∈ C.mobiusDivisors, (norm e)⁻¹) ≤ (A * T ^ e) * Z ^ e := by
    have hb : norm (c * C.d) ≤ T * Z := by
      simp only [ExplicitTerms.norm, map_mul, Nat.cast_mul]
      change norm c * norm C.d ≤ T * Z
      exact mul_le_mul (le_max_right _ _) hnZ (by unfold ExplicitTerms.norm; positivity) hT.le
    calc
      _ ≤ (idealDivisorCount (c * C.d) : ℝ) := fixed_mass_le C
      _ ≤ A * (norm (c * C.d)) ^ e := hdiv _
      _ ≤ A * (T * Z) ^ e := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by unfold ExplicitTerms.norm; positivity) hb he.le) (by linarith)
      _ = (A * T ^ e) * Z ^ e := by rw [Real.mul_rpow hT.le (by linarith)]; ring
  have hX : 1 ≤ 2 * C.N / norm C.d :=
    (le_div_iff₀ (by linarith : 0 < norm C.d)).mpr (by simpa using hnN)
  have hx : 2 * C.N / norm C.d ≤ 2 * Z := by
    exact (div_le_self (by linarith : 0 ≤ 2 * C.N) hn).trans (by linarith)
  have hl : (Vendor.dyadicLength (2 * C.N / norm C.d) + 1 : ℝ) ≤ H * Z ^ e := by
    calc
      _ ≤ L * (2 * C.N / norm C.d) ^ e := Vendor.dyadicLength_small_power he hX
      _ ≤ L * (2 * Z) ^ e := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) hx he.le) hL.le
      _ = H * Z ^ e := by dsimp [H]; rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
  have hcard : ((rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq).card : ℝ) ≤
      (H * Z ^ e) ^ 2 := by
    have hnat := Finset.card_filter_le
      (s := (Finset.range (Vendor.dyadicLength (2 * C.N / norm C.d) + 1)) ×ˢ
        (Finset.range (Vendor.dyadicLength (2 * C.N / norm C.d) + 1)))
      (p := fun ij => divisorScale ij.1 ≤ 2 * C.N / norm C.d ∧
        divisorScale ij.2 ≤ 2 * C.N / norm C.d ∧
        divisorScale ij.1 * divisorScale ij.2 ≤ Cq * C.N * Real.rpow (C.M * C.N) C.δ / Real.sqrt (B * C.M) ∧
        (divisorBucket F (2 * C.N / norm C.d) ij.1).Nonempty ∧
        (divisorBucket F (2 * C.N / norm C.d) ij.2).Nonempty)
    have hh : ((rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq).card : ℝ) ≤
      (Vendor.dyadicLength (2 * C.N / norm C.d) + 1 : ℝ)^2 := by
      have hh : (rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq).card ≤
          (Vendor.dyadicLength (2 * C.N / norm C.d) + 1)^2 := by
        simpa only [rectangles, Finset.card_product, Finset.card_range, pow_two] using hnat
      exact_mod_cast hh
    exact hh.trans (pow_le_pow_left₀ (by positivity) hl 2)
  calc
    _ ≤ ((A * T ^ e) * Z ^ e) * (H * Z ^ e)^2 :=
      mul_le_mul hf hcard (Nat.cast_nonneg _) (by positivity)
    _ = ((A * T ^ e) * H ^ 2) * Z ^ η := by
      have hp : Z ^ e * Z ^ e * Z ^ e = Z ^ η := by
        rw [← Real.rpow_add (by linarith : 0 < Z), ← Real.rpow_add (by linarith : 0 < Z)]
        congr 1
        dsimp [e]
        ring
      calc
        _ = ((A * T ^ e) * H ^ 2) * (Z ^ e * Z ^ e * Z ^ e) := by ring
        _ = _ := by rw [hp]

private lemma dual_norm_bound : ∃ L : ℝ, 0 < L ∧ ∀ C : Context Q,
    1 ≤ C.M → 1 ≤ C.N → 0 < C.δ →
      dualNormCost C ≤ L * Real.rpow (Real.rpow (C.M * C.N) C.δ) 2 := by
  obtain ⟨L, hL, _, hcount⟩ := exists_ideal_count_bound_finset F
  refine ⟨8 * L, by positivity, ?_⟩
  intro C hM hN hδ
  have hθ : 1 ≤ Real.rpow (C.M * C.N) C.δ :=
    Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hN) hδ.le
  have hcut : 1 ≤ C.L1 := by
    have hh := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hN) (by linarith : 0 ≤ 2 * C.δ)
    change 1 ≤ 8 * (C.M * C.N) ^ (2 * C.δ)
    linarith
  let S := (boundedNormIdeals F C.L1).filter (fun b => b ≠ ⊥)
  have hc := hcount C.L1 hcut S (fun b hb => mem_boundedNormIdeals.mp (Finset.mem_filter.mp hb).1)
  have hsum : dualNormCost C ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ b ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        exact pow_le_one₀ (inv_nonneg.mpr (le_trans zero_le_one
          (norm_one_le (Finset.mem_filter.mp hb).2))) (inv_le_one_of_one_le₀
          (norm_one_le (Finset.mem_filter.mp hb).2))
      _ = _ := by simp
  have heq : C.L1 = 8 * Real.rpow (Real.rpow (C.M * C.N) C.δ) 2 := by
    change 8 * (C.M * C.N) ^ (2 * C.δ) = 8 * ((C.M * C.N) ^ C.δ) ^ (2 : ℝ)
    rw [← Real.rpow_mul (by positivity : 0 ≤ C.M * C.N)]
    congr 2
    ring
  calc
    _ ≤ _ := hsum.trans hc
    _ = _ := by rw [heq]; ring

private lemma integrated_cost_bound (C : Context Q) (B Cq : ℝ) (unit : Bool)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (ε A : ℝ) (hA : 0 ≤ A)
    (hrect : ∀ e ∈ C.mobiusDivisors, ∀ ij : ℕ × ℕ, ∀ t s : ℝ,
      rectangleCost C B unit e ij t s ≤
        A * Real.rpow (C.M * C.N * norm C.d) (ε / 2) *
          rectangleValue Q B C.N (norm C.d) ij * weightedEnergy C) :
    integratedCost C B Cq unit ≤ Real.pi ^ 2 *
      ((∑ e ∈ C.mobiusDivisors, (norm e)⁻¹) *
        ((rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq).card : ℝ)) *
      A * Real.rpow (C.M * C.N * norm C.d) (ε / 2) *
        R Q B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq * weightedEnergy C := by
  let Z := C.M * C.N * norm C.d
  let θ := Real.rpow (C.M * C.N) C.δ
  let S := rectangles F B C.M C.N (norm C.d) θ Cq
  let R₀ := R Q B C.M C.N (norm C.d) θ Cq
  let V := A * Z.rpow (ε / 2) * R₀ * weightedEnergy C
  have he0 : 0 ≤ weightedEnergy C := by unfold weightedEnergy; positivity
  have hR0 : 0 ≤ R₀ := R_nonneg' _ _ _ _ _ _
  have hZ0 : 0 ≤ Z := by dsimp [Z]; unfold ExplicitTerms.norm; positivity
  have hpow0 : 0 ≤ Z.rpow (ε / 2) := Real.rpow_nonneg hZ0 _
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hfreq0 : ∀ t s : ℝ, 0 ≤ frequencyCost C B Cq unit t s := by
    intro t s
    unfold frequencyCost
    apply Finset.sum_nonneg
    intro e he
    apply mul_nonneg
    · exact inv_nonneg.mpr (le_trans zero_le_one (norm_one_le (ne_bot_of_mem_idealDivisors he)))
    · apply Finset.sum_nonneg
      intro ij hij
      unfold rectangleCost
      positivity
  have hbound : ∀ t s : ℝ, frequencyCost C B Cq unit t s ≤
      (∑ e ∈ C.mobiusDivisors, (norm e)⁻¹) * (S.card : ℝ) * V := by
    intro t s
    unfold frequencyCost
    calc
      _ ≤ ∑ e ∈ C.mobiusDivisors, (norm e)⁻¹ * ∑ ij ∈ S, V := by
        apply Finset.sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_left _
          (inv_nonneg.mpr (le_trans zero_le_one (norm_one_le (ne_bot_of_mem_idealDivisors he))))
        apply Finset.sum_le_sum
        intro ij hij
        exact (hrect e he ij t s).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (value_le_R B C.M C.N (norm C.d) θ Cq ij hij) (mul_nonneg hA hpow0)) he0)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]; ring
  have hw0 : ∀ p : ℝ × ℝ, 0 ≤ frequencyWeight p := by
    intro p
    unfold frequencyWeight
    positivity
  have hh := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun p : ℝ × ℝ => mul_nonneg (hw0 p) (hfreq0 p.1 p.2)))
    (frequencyWeight_integrable.mul_const
      ((∑ e ∈ C.mobiusDivisors, (norm e)⁻¹) * (S.card : ℝ) * V))
    (Filter.Eventually.of_forall (fun p => mul_le_mul_of_nonneg_left (hbound p.1 p.2) (hw0 p)))
  change integratedCost C B Cq unit ≤ _ at hh
  rw [integral_mul_const, frequencyWeight_integral] at hh
  apply hh.trans_eq
  dsimp [S, V, R₀, θ, Z]
  ring

theorem aggregate_finite_rectangles
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c) :
    ∃ Cq : ℝ, 1 ≤ Cq ∧
      ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, 0 < H ∧
        ∀ C : Context Q, C.D = D →
          1 ≤ C.M → 1 ≤ C.N → 0 < C.δ → 1 ≤ C.K → C.K ≤ C.M →
          norm C.d ≤ 2 * C.N →
          ∀ (B : ℝ) (unit : Bool), 1 ≤ B → B ≤ C.K →
            (unit = true → B = 1) →
          Threshold C B Cq ∧
          ∀ A : ℝ, 0 ≤ A →
            (∀ e ∈ C.mobiusDivisors, ∀ ij : ℕ × ℕ, ∀ t s : ℝ,
              rectangleCost C B unit e ij t s ≤
                A * Real.rpow (C.M * C.N * norm C.d) (ε / 2) *
                  rectangleValue Q B C.N (norm C.d) ij * weightedEnergy C) →
            dualNormCost C * integratedCost C B Cq unit ≤
              H * A * Real.rpow (C.M * C.N * norm C.d) ε *
                Real.rpow (Real.rpow (C.M * C.N) C.δ) 2 *
                R Q B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) Cq *
                weightedEnergy C := by
  refine ⟨max 1 (norm c), le_max_left _ _, ?_⟩
  intro ε hε
  obtain ⟨J, hJ, hcost⟩ := finite_cost_epsilon (Q := Q) (ε / 2) (by linarith)
  obtain ⟨L, hL, hdual⟩ := dual_norm_bound (Q := Q)
  refine ⟨L * Real.pi ^ 2 * J, by positivity, ?_⟩
  intro C hCD hM hN hδ hK hKM hnN B unit hB hBK hunit
  refine ⟨common_threshold C B hM hN hB, ?_⟩
  intro A hA hrect
  have hi := integrated_cost_bound C B (max 1 (norm c)) unit hM hN ε A hA hrect
  have hc := hcost C hM hN hnN B (max 1 (norm c))
  have hd := hdual C hM hN hδ
  have hd0 : 0 ≤ dualNormCost C := by
    unfold dualNormCost
    positivity
  have hR0 := R_nonneg' (Q := Q) B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) (max 1 (norm c))
  have he0 : 0 ≤ weightedEnergy C := by unfold weightedEnergy; positivity
  have hn := norm_one_le C.hd0
  have hZ : 0 < C.M * C.N * norm C.d := by positivity
  have hp0 := Real.rpow_nonneg hZ.le (ε / 2)
  have ht0 := Real.rpow_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ C.M * C.N) C.δ) 2
  calc
    _ ≤ dualNormCost C * (Real.pi ^ 2 *
      ((∑ e ∈ C.mobiusDivisors, (norm e)⁻¹) *
        ((rectangles F B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) (max 1 (norm c))).card : ℝ)) *
      A * Real.rpow (C.M * C.N * norm C.d) (ε / 2) *
        R Q B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) (max 1 (norm c)) * weightedEnergy C) :=
      mul_le_mul_of_nonneg_left hi hd0
    _ ≤ (L * Real.rpow (Real.rpow (C.M * C.N) C.δ) 2) *
      (Real.pi ^ 2 * (J * Real.rpow (C.M * C.N * norm C.d) (ε / 2)) *
      A * Real.rpow (C.M * C.N * norm C.d) (ε / 2) *
        R Q B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) (max 1 (norm c)) * weightedEnergy C) := by
      have hm0 : 0 ≤ ∑ e ∈ C.mobiusDivisors, (norm e)⁻¹ := by
        apply Finset.sum_nonneg
        intro e he
        exact inv_nonneg.mpr (le_trans zero_le_one (norm_one_le (ne_bot_of_mem_idealDivisors he)))
      have hp0' : 0 ≤ Real.rpow (C.M * C.N * norm C.d) (ε / 2) := hp0
      have ht0' : 0 ≤ Real.rpow (Real.rpow (C.M * C.N) C.δ) 2 := ht0
      apply mul_le_mul _ _
        (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hm0 (Nat.cast_nonneg _))) hA) hp0') hR0) he0)
        (mul_nonneg hL.le ht0')
      · exact hd
      · apply mul_le_mul_of_nonneg_right _ he0
        apply mul_le_mul_of_nonneg_right _ hR0
        apply mul_le_mul_of_nonneg_right _ hp0
        apply mul_le_mul_of_nonneg_right _ hA
        exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = _ := by
      have hp : Real.rpow (C.M * C.N * norm C.d) (ε / 2) *
        Real.rpow (C.M * C.N * norm C.d) (ε / 2) = Real.rpow (C.M * C.N * norm C.d) ε := by
        change (C.M * C.N * norm C.d) ^ (ε / 2) * (C.M * C.N * norm C.d) ^ (ε / 2) = _
        rw [← Real.rpow_add hZ]
        congr 1
        ring
      calc
        _ = (L * Real.pi^2 * J) * A *
          (Real.rpow (C.M * C.N * norm C.d) (ε / 2) * Real.rpow (C.M * C.N * norm C.d) (ε / 2)) *
          Real.rpow (Real.rpow (C.M * C.N) C.δ) 2 *
          R Q B C.M C.N (norm C.d) (Real.rpow (C.M * C.N) C.δ) (max 1 (norm c)) * weightedEnergy C := by ring
        _ = _ := by rw [hp]

end DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteFourierRectangles

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.MiddleFinite

open ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorScale (j : ℕ) : ℝ := (2 : ℝ) ^ j

def divisorBucket (F : Type) [Field F] [NumberField F] (T : ℝ) (j : ℕ) :
    Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F T).filter (fun f => f ≠ ⊥ ∧
    divisorScale j ≤ norm f ∧ norm f < 2 * divisorScale j)

def rectangles (F : Type) [Field F] [NumberField F]
    (B M N n θ Cq : ℝ) : Finset (ℕ × ℕ) :=
  let J := Finset.range (Vendor.dyadicLength (2 * N / n) + 1)
  (J ×ˢ J).filter (fun ij =>
    divisorScale ij.1 ≤ 2 * N / n ∧
    divisorScale ij.2 ≤ 2 * N / n ∧
    divisorScale ij.1 * divisorScale ij.2 ≤ Cq * N * θ / Real.sqrt (B * M) ∧
    (divisorBucket F (2 * N / n) ij.1).Nonempty ∧
    (divisorBucket F (2 * N / n) ij.2).Nonempty)

def U (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (B X : ℝ) : ℝ :=
  ExplicitTerms.ErrorRectangles.U Q B X

def rectangleValue (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (B N n : ℝ) (ij : ℕ × ℕ) : ℝ :=
  Real.sqrt (divisorScale ij.1 * divisorScale ij.2 *
    U Q B (N / (n * divisorScale ij.1)) *
    U Q B (N / (n * divisorScale ij.2)))

def R (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (B M N n θ Cq : ℝ) : ℝ :=
  sSup ({0} ∪ {z : ℝ | ∃ ij ∈ rectangles F B M N n θ Cq,
    z = rectangleValue Q B N n ij})

def maskedE3 (C : Context Q) (B : ℝ) (unit : Bool)
    (ρ : Ideal (𝓞 F) → ℂ) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    ∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        ρ a * C.primitive p hp a * Context.middle C.reflectedKernel (p.1 * p.2)
          (Real.sqrt (C.dualScale e p / norm a)) (C.Y1 B e) (C.Z1 B e) C.L1

def topE3 (C : Context Q) : ℂ :=
  maskedE3 C 1 true (fun a => if a = ⊤ then 1 else 0)

private lemma finite_R_set (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (B M N n θ Cq : ℝ) :
    Set.Finite ({0} ∪ {z : ℝ | ∃ ij ∈ rectangles F B M N n θ Cq,
      z = rectangleValue Q B N n ij}) := by
  apply Set.Finite.union (Set.finite_singleton 0)
  have h := (rectangles F B M N n θ Cq).finite_toSet.image
    (rectangleValue Q B N n)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨ij, hij, rfl⟩
    exact ⟨ij, hij, rfl⟩
  · rintro ⟨ij, hij, rfl⟩
    exact ⟨ij, hij, rfl⟩

lemma R_nonneg (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (B M N n θ Cq : ℝ) : 0 ≤ R Q B M N n θ Cq := by
  apply le_csSup (finite_R_set Q B M N n θ Cq).bddAbove
  exact Or.inl rfl

lemma R_empty (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (B M N n θ Cq : ℝ) (h : rectangles F B M N n θ Cq = ∅) :
    R Q B M N n θ Cq = 0 := by
  simp [R, h]

lemma maskedE3_one (C : Context Q) (B : ℝ) (unit : Bool) :
    maskedE3 C B unit (fun _ => 1) = E3 C B unit := by
  simp only [maskedE3, E3, one_mul]

lemma top_mask_bound (a : Ideal (𝓞 F)) :
    ‖(if a = ⊤ then 1 else 0 : ℂ)‖ ≤ 1 := by
  split_ifs <;> norm_num

lemma conclusions_of_masked_bound (C : Context Q) (B M N n θ Cq rhs : ℝ)
    (unit : Bool) (hunit : unit = true → B = 1)
    (hmasked : ∀ ρ : Ideal (𝓞 F) → ℂ,
      (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
      ‖maskedE3 C B unit ρ‖ ≤ rhs)
    (hempty : rectangles F B M N n θ Cq = ∅ → rhs = 0) :
    (‖E3 C B unit‖ ≤ rhs) ∧
    (∀ ρ : Ideal (𝓞 F) → ℂ,
      (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
      ‖maskedE3 C B unit ρ‖ ≤ rhs) ∧
    (rectangles F B M N n θ Cq = ∅ →
      E3 C B unit = 0 ∧
      ∀ ρ : Ideal (𝓞 F) → ℂ,
        (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
        maskedE3 C B unit ρ = 0) ∧
    (unit = true → ‖topE3 C‖ ≤ rhs ∧
      (rectangles F B M N n θ Cq = ∅ → topE3 C = 0)) := by
  have hone : ‖E3 C B unit‖ ≤ rhs := by
    simpa only [maskedE3_one] using hmasked (fun _ => 1) (by simp)
  refine ⟨hone, hmasked, ?_, ?_⟩
  · intro h
    have hrhs := hempty h
    refine ⟨norm_le_zero_iff.mp (by simpa only [hrhs] using hone), ?_⟩
    intro ρ hρ
    exact norm_le_zero_iff.mp (by simpa only [hrhs] using hmasked ρ hρ)
  · intro hu
    have hB := hunit hu
    have htop : ‖topE3 C‖ ≤ rhs := by
      unfold topE3
      rw [← hB, ← hu]
      exact hmasked _ (fun a _ => top_mask_bound a)
    refine ⟨htop, fun h => norm_le_zero_iff.mp ?_⟩
    simpa only [hempty h] using htop

end DedekindZetaZeroFree.LargeSieve.Bilinear.MiddleFinite

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

open MiddleFinite

theorem bilinear_middle_finite_application
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : Sieve.AllIndexNormalizedFamilyData Q) (core : D.bad = c)
    (hF : NumberField.IsTotallyComplex F)
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ Cq : ℝ, 1 ≤ Cq ∧ ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
        ∀ (M N K δ : ℝ), 1 ≤ M → 1 ≤ N → 0 < δ → 1 ≤ K → K ≤ M →
        ∀ (d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥) (hd : Squarefree d)
          (hdc : d ⊔ c = ⊤),
        (Ideal.absNorm d : ℝ) ≤ 2 * N →
        ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
        Function.support lam ⊆ (Sieve.paperShell F c N : Set (Ideal (𝓞 F))) →
        ∀ (B : ℝ) (unit : Bool), 1 ≤ B → B ≤ K → (unit = true → B = 1) →
        let C : Context Q := {
          D := D, core := core, hF := hF,
          M := M, N := N, K := K, δ := δ, W := W, hW := hW,
          d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
        let n : ℝ := norm d
        let θ : ℝ := Real.rpow (M * N) δ
        let rhs : ℝ := Cε * Real.rpow (M * N * n) ε * Real.rpow θ C0 *
          (n * M / N) * MiddleFinite.R Q B M N n θ Cq * Sieve.energy F c N lam
        (‖E3 C B unit‖ ≤ rhs) ∧
        (∀ ρ : Ideal (𝓞 F) → ℂ,
          (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
          ‖maskedE3 C B unit ρ‖ ≤ rhs) ∧
        (rectangles F B M N n θ Cq = ∅ →
          E3 C B unit = 0 ∧
          ∀ ρ : Ideal (𝓞 F) → ℂ,
            (∀ a ∈ C.reflectedRows B unit, ‖ρ a‖ ≤ 1) →
            maskedE3 C B unit ρ = 0) ∧
        (unit = true → ‖topE3 C‖ ≤ rhs ∧
          (rectangles F B M N n θ Cq = ∅ → topE3 C = 0)) := by
  obtain ⟨Cq, hCq, hsum⟩ := FiniteFourierRectangles.aggregate_finite_rectangles D core
  obtain ⟨A, hA, hfourier⟩ :=
    FiniteFourierRectangles.fourier_rows_bound D core hF W hW
  refine ⟨Cq, hCq, 3, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨H, hH, hsumε⟩ := hsum ε hε
  obtain ⟨I, hI, hrect⟩ :=
    FiniteFourierRectangles.common_frequency_rectangle_bound D core (ε / 2) (by linarith)
  refine ⟨A * H * I, by positivity, ?_⟩
  intro M N K δ hM hN hδ hK hKM d hd0 hd hdc hnN g lam hlam B unit hB hBK hu
  let C : Context Q := {
    D := D, core := core, hF := hF,
    M := M, N := N, K := K, δ := δ, W := W, hW := hW,
    d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
  let n : ℝ := norm d
  let θ : ℝ := Real.rpow (M * N) δ
  let rhs : ℝ := (A * H * I) * Real.rpow (M * N * n) ε * Real.rpow θ 3 *
    (n * M / N) * MiddleFinite.R Q B M N n θ Cq * Sieve.energy F c N lam
  change (‖E3 C B unit‖ ≤ rhs) ∧ _
  apply MiddleFinite.conclusions_of_masked_bound C B M N n θ Cq rhs unit hu
  · intro ρ hρ
    have hs := hsumε C rfl hM hN hδ hK hKM hnN B unit hB hBK hu
    have hr := hrect C rfl hM hN hK hKM hnN B unit hB hBK hu
    have hf := hfourier C rfl rfl hM hN hδ hK hKM hnN hlam
      B Cq unit hB hBK hu hCq hs.1 ρ hρ
    have hg := hs.2 I hI.le hr
    have he := (FiniteFourierRectangles.inclusive_divisor_endpoint_energy C hN hK hnN).1
    have hn : 0 ≤ n := by
      dsimp [n, norm]
      positivity
    have hM0 : 0 ≤ M := le_trans zero_le_one hM
    have hN0 : 0 ≤ N := le_trans zero_le_one hN
    have hθ0 : 0 ≤ θ := Real.rpow_nonneg (mul_nonneg hM0 hN0) _
    have hp0 : 0 ≤ Real.rpow (M * N * n) ε :=
      Real.rpow_nonneg (mul_nonneg (mul_nonneg hM0 hN0) hn) _
    have hR0 : 0 ≤ MiddleFinite.R Q B M N n θ Cq := R_nonneg Q B M N n θ Cq
    have hpow : θ * Real.rpow θ 2 = Real.rpow θ 3 := by
      norm_num [Real.rpow_two, Real.rpow_natCast]
      ring
    calc
      ‖maskedE3 C B unit ρ‖ ≤
          A * M * θ * (FiniteFourierRectangles.dualNormCost C *
            FiniteFourierRectangles.integratedCost C B Cq unit) := by
        change ‖maskedE3 C B unit ρ‖ ≤ A * M * θ *
          FiniteFourierRectangles.dualNormCost C * FiniteFourierRectangles.integratedCost C B Cq unit at hf
        simpa only [mul_assoc] using hf
      _ ≤ A * M * θ *
          (H * I * Real.rpow (M * N * n) ε * Real.rpow θ 2 *
            MiddleFinite.R Q B M N n θ Cq * FiniteFourierRectangles.weightedEnergy C) := by
        apply mul_le_mul_of_nonneg_left hg
        positivity
      _ ≤ A * M * θ *
          (H * I * Real.rpow (M * N * n) ε * Real.rpow θ 2 *
            MiddleFinite.R Q B M N n θ Cq *
              ((n / N) * Sieve.energy F c N lam)) := by
        have ht2 : 0 ≤ Real.rpow θ 2 := Real.rpow_nonneg hθ0 _
        have hfac : 0 ≤ H * I * Real.rpow (M * N * n) ε * Real.rpow θ 2 *
            MiddleFinite.R Q B M N n θ Cq := by positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left he hfac) (by positivity)
      _ = rhs := by
        change A * M * θ *
          (H * I * Real.rpow (M * N * n) ε * Real.rpow θ 2 *
            MiddleFinite.R Q B M N n θ Cq * (n / N * Sieve.energy F c N lam)) =
          (A * H * I) * Real.rpow (M * N * n) ε * Real.rpow θ 3 *
            (n * M / N) * MiddleFinite.R Q B M N n θ Cq * Sieve.energy F c N lam
        rw [← hpow]
        ring
  · intro hempty
    dsimp [rhs]
    rw [MiddleFinite.R_empty Q B M N n θ Cq hempty]
    ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end

end
