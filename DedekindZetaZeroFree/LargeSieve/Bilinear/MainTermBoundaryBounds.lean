module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.BoundaryTerms.PrefixOperatorsAndIncidenceEnergy

@[expose] public section

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound
variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

private lemma rel_of_sup {a b : Ideal (𝓞 F)} (h : a ⊔ b = ⊤) :
    IsRelPrime a b := by
  intro z hza hzb
  rw [Ideal.isUnit_iff]
  exact le_antisymm le_top
    (h ▸ sup_le (Ideal.dvd_iff_le.mp hza) (Ideal.dvd_iff_le.mp hzb))

private lemma annular_rows_prime_ideal_size_gt_one (p : Ideal (𝓞 F)) (hp : Prime p) :
    1 < ((idealSize F) p : ℝ) := by
  have h0 : Ideal.absNorm p ≠ 0 := fun h => hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm p ≠ 1 :=
    fun h => hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  have h2 : 1 < Ideal.absNorm p := by omega
  have h2' : (1 : ℝ) < (Ideal.absNorm p : ℝ) := by exact_mod_cast h2
  simpa [idealSize] using h2'

private lemma boundary_core (q d : Ideal (𝓞 F)) (hd0 : d ≠ 0)
    (hd : Squarefree d) (hdq : d ⊔ q = ⊤) (K : ℝ)
    (b : Ideal (𝓞 F))
    (hb : b ∈ Vendor.CutoffDifference.boundaryElements (cutoffBase q d K) d) :
    b ⊔ q = ⊤ := by
  rcases Finset.mem_image.mp hb with ⟨⟨h, e, f⟩, hmem, rfl⟩
  rcases Finset.mem_product.mp hmem with ⟨hh, hef⟩
  rcases Finset.mem_product.mp hef with ⟨he, hf⟩
  have hhd := ((mem_idealAdmissibleFinset F (q * d) K h).mp hh).2.1
  have hdvd : ∀ x ∈ Vendor.CutoffDifference.divisors d, x ∣ d := by
    intro x hx
    exact ((Vendor.CutoffDifference.squarefree_divisor_dictionary d hd0 hd).2.2.2.2.2 x).mp hx
  have hrel : IsRelPrime (h * e * f) q :=
    (((rel_of_sup hhd).of_dvd_right (dvd_mul_right q d)).mul_left
      ((rel_of_sup hdq).of_dvd_left (hdvd e he))).mul_left
      ((rel_of_sup hdq).of_dvd_left (hdvd f hf))
  exact Ideal.isUnit_iff.mp (hrel
    (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

theorem collected_le_squarefree_rows
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q)
    (N K : ℝ) (hK : 1 ≤ K)
    (d : Ideal (𝓞 F)) (hd : Squarefree d) (hdq : d ⊔ D.bad = ⊤)
    (g : Q.G) (lam : Ideal (𝓞 F) → ℂ) :
    ‖collectedBoundary Q D.bad d N K g lam‖ ≤
      ((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 /
        Real.sqrt K *
        squarefreeRows Q D.bad d
          (K * (Ideal.absNorm d : ℝ) ^ 2) N g lam := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hK0 : 0 < K := by linarith
  let H := cutoffBase D.bad d K
  let beta := Vendor.CutoffDifference.boundaryCoefficient (idealSize F) K H d
  let S := (Vendor.CutoffDifference.boundaryElements H d).filter (fun b => beta b ≠ 0)
  let A := idealAdmissibleFinset F D.bad (K * (Ideal.absNorm d : ℝ) ^ 2)
  let T := Vendor.CutoffDifference.divisors d ×ˢ A
  let phi : Ideal (𝓞 F) × Ideal (𝓞 F) → Ideal (𝓞 F) := fun x => x.2 * x.1 ^ 2
  have hH : ∀ h ∈ H, Squarefree h ∧ IsRelPrime h d := by
    intro h hh
    have hh' := (mem_idealAdmissibleFinset F (D.bad * d) K h).mp hh
    exact ⟨hh'.1, (rel_of_sup hh'.2.1).of_dvd_right (dvd_mul_left d D.bad)⟩
  have hprops (b : Ideal (𝓞 F)) :=
    Vendor.CutoffDifference.boundary_coefficient_properties (idealSize F)
      annular_rows_prime_ideal_size_gt_one d hd0 hd K hK0 H hH b
  have hsubset : S ⊆ T.image phi := by
    intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hb, hbeta⟩
    obtain ⟨hlo, hhi, a, t, ha, ht, hbt⟩ := (hprops b).1 hbeta
    have hbc : b ⊔ D.bad = ⊤ := boundary_core D.bad d hd0 hd hdq K b hb
    have hadvd : a ∣ b := by rw [hbt]; exact dvd_mul_right a (t ^ 2)
    have haq : a ⊔ D.bad = ⊤ := top_unique
      (hbc.symm.trans_le (sup_le_sup (Ideal.dvd_iff_le.mp hadvd) le_rfl))
    have hbpos : 0 < Ideal.absNorm b := by
      have : (0 : ℝ) < Ideal.absNorm b := by simpa [idealSize] using lt_trans hK0 hlo
      exact_mod_cast this
    have hanorm : (Ideal.absNorm a : ℝ) ≤ Ideal.absNorm b := by
      exact_mod_cast Nat.le_of_dvd hbpos (Ideal.absNorm_dvd_absNorm_of_le
        (Ideal.dvd_iff_le.mp hadvd))
    have haA : a ∈ A := (mem_idealAdmissibleFinset F D.bad _ a).mpr
      ⟨ha, haq, hanorm.trans (by simpa [idealSize] using hhi)⟩
    have htT : t ∈ Vendor.CutoffDifference.divisors d :=
      ((Vendor.CutoffDifference.squarefree_divisor_dictionary d hd0 hd).2.2.2.2.2 t).mpr ht
    exact Finset.mem_image.mpr ⟨(t, a), Finset.mem_product.mpr ⟨htT, haA⟩, hbt.symm⟩
  let C : ℝ := ((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 / Real.sqrt K
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hterm (b : Ideal (𝓞 F)) (hb : b ∈ S) :
      ‖(beta b : ℂ) / (Real.sqrt (Ideal.absNorm b : ℝ) : ℂ) *
        densityRow Q D.bad d N g lam b‖ ≤ C * ‖densityRow Q D.bad d N g lam b‖ := by
    have hbeta := (Finset.mem_filter.mp hb).2
    have hlo : K < (Ideal.absNorm b : ℝ) := by
      simpa [idealSize] using ((hprops b).1 hbeta).1
    have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
    have hsqrtle : Real.sqrt K ≤ Real.sqrt (Ideal.absNorm b : ℝ) :=
      Real.sqrt_le_sqrt hlo.le
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact div_le_div₀ (sq_nonneg _) (hprops b).2 hsqrt hsqrtle
  have hsum : (∑ b ∈ S, ‖densityRow Q D.bad d N g lam b‖) ≤
      squarefreeRows Q D.bad d (K * (Ideal.absNorm d : ℝ) ^ 2) N g lam := by
    calc
      (∑ b ∈ S, ‖densityRow Q D.bad d N g lam b‖) ≤
          ∑ b ∈ T.image phi, ‖densityRow Q D.bad d N g lam b‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ x ∈ T, ‖densityRow Q D.bad d N g lam (phi x)‖ :=
        Finset.sum_image_le_of_nonneg (fun _ _ => norm_nonneg _)
      _ = squarefreeRows Q D.bad d (K * (Ideal.absNorm d : ℝ) ^ 2) N g lam := by
        simp only [T, phi, Finset.sum_product, squarefreeRows, A]
  have heq : collectedBoundary Q D.bad d N K g lam =
      ∑ b ∈ S, (beta b : ℂ) / (Real.sqrt (Ideal.absNorm b : ℝ) : ℂ) *
        densityRow Q D.bad d N g lam b := by
    dsimp [collectedBoundary, S, beta, H]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs with h
    · simp [h]
    · rfl
  rw [heq]
  calc
    ‖∑ b ∈ S, (beta b : ℂ) / (Real.sqrt (Ideal.absNorm b : ℝ) : ℂ) *
        densityRow Q D.bad d N g lam b‖ ≤
        ∑ b ∈ S, ‖(beta b : ℂ) / (Real.sqrt (Ideal.absNorm b : ℝ) : ℂ) *
          densityRow Q D.bad d N g lam b‖ := norm_sum_le _ _
    _ ≤ ∑ b ∈ S, C * ‖densityRow Q D.bad d N g lam b‖ :=
      Finset.sum_le_sum hterm
    _ = C * ∑ b ∈ S, ‖densityRow Q D.bad d N g lam b‖ := by rw [Finset.mul_sum]
    _ ≤ C * squarefreeRows Q D.bad d (K * (Ideal.absNorm d : ℝ) ^ 2) N g lam :=
      mul_le_mul_of_nonneg_left hsum hC

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound

end

end

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound
variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

private lemma prime_idealSize_real_gt_one (p : Ideal (𝓞 F)) (hp : Prime p) :
    1 < (idealSize F p : ℝ) := by
  have hn0 : Ideal.absNorm p ≠ 0 := by
    intro h
    exact hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have hn1 : Ideal.absNorm p ≠ 1 := by
    intro h
    exact hp.not_unit ((Ideal.absNorm_eq_one_iff.mp h).trans Ideal.one_eq_top.symm ▸ isUnit_one)
  change 1 < ((Ideal.absNorm p : ℝ≥0) : ℝ)
  norm_cast
  omega

private lemma column_value_sq
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (d : Ideal (𝓞 F)) (hdq : d ⊔ D.bad = ⊤)
    (N : ℝ) (g : Q.G) (u : Ideal (𝓞 F))
    (hu : u ∈ quotientColumns Q D.bad d N g)
    (p : Ideal (𝓞 F)) (hp : Prime p) (hpd : p ∣ d) :
    (Q.χ u p) ^ 2 = 1 := by
  obtain ⟨hu, hucol⟩ := Finset.mem_filter.mp hu
  obtain ⟨husf, huq, _⟩ := (mem_idealAdmissibleFinset F _ _ u).mp hu
  have hpq : IsCoprime p D.bad :=
    (Ideal.isCoprime_iff_sup_eq.mpr hdq).of_isCoprime_of_dvd_left hpd
  have hpu : IsCoprime p u :=
    (Ideal.isCoprime_iff_sup_eq.mpr hucol.1).symm.of_isCoprime_of_dvd_left hpd
  have hpc : IsCoprime p (Q.cond u) :=
    (hpu.mul_right hpq).of_isCoprime_of_dvd_right
      (D.conductor_dvd_index_bad u husf huq)
  have huc : u ⊔ c = ⊤ :=
    ((Ideal.isCoprime_iff_sup_eq.mpr huq).of_isCoprime_of_dvd_right
      D.original_dvd_bad).sup_eq
  exact DedekindZetaZeroFree.LargeSieve.quadraticFamily_value_sq_eq_one Q husf huc p hp.ne_zero hpc.sup_eq

theorem cancelled_eq_collected
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (W : ℝ → ℝ) (kappa : ℂ)
    (M N K : ℝ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (d : Ideal (𝓞 F)) (hd : Squarefree d) (hdq : d ⊔ D.bad = ⊤)
    (g : Q.G) (lam : Ideal (𝓞 F) → ℂ) :
    cancelledMainTerms Q D.bad W kappa M N K d g lam =
      kappa * (Real.sqrt M : ℂ) *
        ((∫ t in Set.Ioi (0 : ℝ), W (t ^ 2)) : ℂ) *
        collectedBoundary Q D.bad d N K g lam := by
  have hH : ∀ h ∈ cutoffBase D.bad d K, Squarefree h ∧ IsRelPrime h d := by
    intro h hh
    obtain ⟨hsf, hcop, _⟩ := (mem_idealAdmissibleFinset F _ _ h).mp hh
    refine ⟨hsf, ?_⟩
    exact ((IsCoprime.mul_right_iff.mp
      (Ideal.isCoprime_iff_sup_eq.mpr hcop)).2).isRelPrime
  have hdiff : ∀ u ∈ quotientColumns Q D.bad d N g,
      ∀ v ∈ quotientColumns Q D.bad d N g,
      cutoffDifference D.bad d K (pairCharacter Q u v) =
        ∑ b ∈ Vendor.CutoffDifference.boundaryElements (cutoffBase D.bad d K) d,
          (Vendor.CutoffDifference.boundaryCoefficient (idealSize F) K
            (cutoffBase D.bad d K) d b : ℂ) *
              Vendor.CutoffDifference.normalizedValue (idealSize F) (pairCharacter Q u v) b := by
    intro u hu v hv
    apply Vendor.CutoffDifference.main_terms_difference_collected
      (idealSize F) (pairCharacter Q u v) prime_idealSize_real_gt_one d hd.ne_zero hd
    · intro p hp hpd
      change (Q.χ u p * star (Q.χ v p)) ^ 2 = 1
      rw [mul_pow, column_value_sq Q D d hdq N g u hu p hp hpd,
        ← star_pow, column_value_sq Q D d hdq N g v hv p hp hpd]
      simp
    · exact lt_of_lt_of_le zero_lt_one hK
    · exact hH
  unfold cancelledMainTerms collectedBoundary densityRow
  congr 1
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases huv : u ⊔ v = ⊤ ∧ u * v ≠ ⊤
  · simp only [if_pos huv]
    rw [hdiff u hu v hv]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Vendor.CutoffDifference.normalizedValue, idealSize, MonoidHom.coe_mk,
      OneHom.coe_mk, NNReal.coe_natCast]
    ring
  · simp only [if_neg huv, mul_zero, Finset.sum_const_zero]

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound

end

end

section

noncomputable section
open scoped NumberField Classical NNReal

namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundary

variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

def idealSize (F : Type) [Field F] [NumberField F] : Ideal (𝓞 F) →* (ℝ≥0) where
  toFun a := (Ideal.absNorm a : ℝ≥0)
  map_one' := by simp
  map_mul' a b := by simp

def pairCharacter (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (u v : Ideal (𝓞 F)) : Ideal (𝓞 F) →* ℂ where
  toFun a := (Q.χ u) a * star ((Q.χ v) a)
  map_one' := by
    simp only [Ideal.one_eq_top, (Q.χ u).map_top', (Q.χ v).map_top', star_one, mul_one]
  map_mul' a b := by
    simp only [(Q.χ u).map_mul', (Q.χ v).map_mul', star_mul]
    ring

def cutoffBase (q d : Ideal (𝓞 F)) (K : ℝ) : Finset (Ideal (𝓞 F)) :=
  idealAdmissibleFinset F (q * d) K

def quotientColumns (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q d : Ideal (𝓞 F)) (N : ℝ) (g : Q.G) : Finset (Ideal (𝓞 F)) :=
  (idealAdmissibleFinset F q (2 * N / (Ideal.absNorm d : ℝ))).filter
    (fun u => u ⊔ d = ⊤ ∧ d * u ∈ paperShell F c N ∧ Q.cls (d * u) = g)

def cutoffDifference (q d : Ideal (𝓞 F)) (K : ℝ)
    (χ : Ideal (𝓞 F) →* ℂ) : ℂ :=
  let H := cutoffBase q d K
  Vendor.CutoffDifference.divisorCutoffSum (idealSize F) χ K H d *
      Vendor.CutoffDifference.moebiusDivisorSum (idealSize F) χ d -
    Vendor.CutoffDifference.baseCutoffSum (idealSize F) χ K H *
      (Vendor.CutoffDifference.density (idealSize F) d : ℂ)

def cancelledMainTerms (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (W : ℝ → ℝ) (kappa : ℂ)
    (M N K : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) : ℂ :=
  kappa * (Real.sqrt M : ℂ) *
    ((∫ t in Set.Ioi (0 : ℝ), W (t ^ 2)) : ℂ) *
    ∑ u ∈ quotientColumns Q q d N g, ∑ v ∈ quotientColumns Q q d N g,
      if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
        lam (d * u) * star (lam (d * v)) *
          (Vendor.CutoffDifference.density (idealSize F) (q * u * v) : ℂ) *
          cutoffDifference q d K (pairCharacter Q u v)
      else 0

def shellPrefixEnvelope (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (X Y : ℝ) : ℝ :=
  ((Vendor.dyadicLength (2 * Y) + 1 : ℕ) : ℝ) *
    (1 + X + Y +
      ∑ i ∈ Finset.range (Vendor.dyadicLength X),
        ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * Y)),
          B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i))

theorem cancelledMainTerms_le_envelope
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (W : ℝ → ℝ) (hW : SieveWeight W) (kappa : ℂ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ K → K ≤ M →
      ∀ d : Ideal (𝓞 F), Squarefree d → d ⊔ D.bad = ⊤ →
        (Ideal.absNorm d : ℝ) ≤ 2 * N →
      ∀ g : Q.G, ∀ lam : Ideal (𝓞 F) → ℂ,
        ‖cancelledMainTerms Q D.bad W kappa M N K d g lam‖ ≤
          C * (M * N * (Ideal.absNorm d : ℝ)) ^ ε * Real.sqrt (M / K) *
            shellPrefixEnvelope F c Q (K * (Ideal.absNorm d : ℝ) ^ 2) N *
            energy F c N lam := by
  intro ε hε
  let η : ℝ := ε / 3
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C₀, hC₀, hprefix⟩ :=
    MainBoundaryBound.squarefree_rows_le_prefix Q D η hη
  let w : ℂ := ∫ t in Set.Ioi (0 : ℝ), W (t ^ 2)
  let A : ℝ := max 1 (‖kappa‖ * ‖w‖)
  have hA : 0 < A := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hκw : ‖kappa‖ * ‖w‖ ≤ A := le_max_right _ _
  refine ⟨A * C₀, mul_pos hA hC₀, ?_⟩
  intro M N K hM hN hK hKM d hd hdq hdn g lam
  let n : ℝ := (Ideal.absNorm d : ℝ)
  let X : ℝ := K * n ^ 2
  let p : ℝ := M * N * n
  have hn0 : Ideal.absNorm d ≠ 0 := by
    intro hn
    exact hd.ne_zero (Ideal.absNorm_eq_zero_iff.mp hn)
  have hn1 : 1 ≤ n := by
    have hh : (1 : ℕ) ≤ Ideal.absNorm d := Nat.one_le_iff_ne_zero.mpr hn0
    dsimp [n]
    exact_mod_cast hh
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [hK, hn1, sq_nonneg n]
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hz : X * N * n ≤ p ^ 3 := by
    have hM3 : M ≤ M ^ 3 := by
      calc M = M * 1 := by ring
        _ ≤ M * M ^ 2 := by gcongr; exact one_le_pow₀ hM
        _ = M ^ 3 := by ring
    have hN3 : N ≤ N ^ 3 := by
      calc N = N * 1 := by ring
        _ ≤ N * N ^ 2 := by gcongr; exact one_le_pow₀ hN
        _ = N ^ 3 := by ring
    calc X * N * n = (K * N) * n ^ 3 := by dsimp [X]; ring
      _ ≤ (M * N) * n ^ 3 := by gcongr
      _ ≤ (M ^ 3 * N ^ 3) * n ^ 3 := by gcongr
      _ = p ^ 3 := by dsimp [p]; ring
  have hpow : (X * N * n) ^ η ≤ p ^ ε := by
    calc (X * N * n) ^ η ≤ (p ^ 3) ^ η :=
        Real.rpow_le_rpow (by positivity) hz hη.le
      _ = p ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
        congr 1
        dsimp [η]
        ring
  have hrow := MainBoundaryBound.collected_le_squarefree_rows
    Q D N K hK d hd hdq g lam
  have hprefix' := hprefix X N hX hN d hd hdq hdn g lam
  change _ ≤ C₀ * (X * N * n) ^ η * shellPrefixEnvelope F c Q X N *
    energy F c N lam at hprefix'
  have hid := MainBoundaryBound.cancelled_eq_collected Q D W kappa M N K
    hN hK d hd hdq g lam
  change cancelledMainTerms Q D.bad W kappa M N K d g lam = _ at hid
  have hsqrt : Real.sqrt M / Real.sqrt K = Real.sqrt (M / K) := by
    rw [Real.sqrt_div (by linarith : 0 ≤ M)]
  have hS0 : 0 ≤ shellPrefixEnvelope F c Q X N := by
    unfold shellPrefixEnvelope
    apply mul_nonneg (by positivity)
    apply add_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj =>
      B1_nonneg Q _ _))
  have hE0 : 0 ≤ energy F c N lam := by unfold energy; positivity
  have hroot0 : 0 ≤ Real.sqrt (M / K) := Real.sqrt_nonneg _
  have hR0 : 0 ≤ MainBoundaryBound.squarefreeRows Q D.bad d X N g lam := by
    unfold MainBoundaryBound.squarefreeRows
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hC0 : 0 ≤ C₀ := hC₀.le
  have hbound : ‖cancelledMainTerms Q D.bad W kappa M N K d g lam‖ ≤
      ‖kappa‖ * ‖w‖ * Real.sqrt (M / K) *
        (((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 *
          MainBoundaryBound.squarefreeRows Q D.bad d X N g lam) := by
    have hnorm : ‖cancelledMainTerms Q D.bad W kappa M N K d g lam‖ =
        ‖kappa‖ * Real.sqrt M * ‖w‖ *
          ‖MainBoundaryBound.collectedBoundary Q D.bad d N K g lam‖ := by
      rw [hid]
      change ‖kappa * (Real.sqrt M : ℂ) * w *
        MainBoundaryBound.collectedBoundary Q D.bad d N K g lam‖ = _
      rw [norm_mul, norm_mul, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg M)]
    rw [hnorm]
    calc ‖kappa‖ * Real.sqrt M * ‖w‖ *
          ‖MainBoundaryBound.collectedBoundary Q D.bad d N K g lam‖
        ≤ ‖kappa‖ * Real.sqrt M * ‖w‖ *
            (((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 /
                Real.sqrt K *
                MainBoundaryBound.squarefreeRows Q D.bad d X N g lam) := by
              gcongr
      _ = ‖kappa‖ * ‖w‖ * Real.sqrt (M / K) *
            (((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 *
              MainBoundaryBound.squarefreeRows Q D.bad d X N g lam) := by
              rw [← hsqrt]
              ring
  calc ‖cancelledMainTerms Q D.bad W kappa M N K d g lam‖
      ≤ ‖kappa‖ * ‖w‖ * Real.sqrt (M / K) *
        (((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 *
          MainBoundaryBound.squarefreeRows Q D.bad d X N g lam) := hbound
    _ ≤ A * Real.sqrt (M / K) *
        (((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 *
          MainBoundaryBound.squarefreeRows Q D.bad d X N g lam) := by
            gcongr
    _ ≤ A * Real.sqrt (M / K) *
        (C₀ * (X * N * n) ^ η * shellPrefixEnvelope F c Q X N *
          energy F c N lam) := by
            exact mul_le_mul_of_nonneg_left hprefix' (by positivity)
    _ ≤ A * Real.sqrt (M / K) *
        (C₀ * p ^ ε * shellPrefixEnvelope F c Q X N * energy F c N lam) := by
          gcongr
    _ = (A * C₀) * p ^ ε * Real.sqrt (M / K) *
        shellPrefixEnvelope F c Q X N * energy F c N lam := by ring

private lemma dyadicLength_pow_le {X : ℝ} (hX : 1 ≤ X) :
    (2 : ℝ) ^ DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X ≤ 2 * X := by
  rcases Nat.eq_zero_or_pos (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X) with h | h
  · rw [h, pow_zero]; linarith
  · have hlt := DedekindZetaZeroFree.LargeSieve.Vendor.pow_lt_of_lt_dyadicLength hX
      (Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp h))
    have hL : DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X - 1 + 1 = DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X :=
      Nat.sub_add_cancel h
    rw [← hL, pow_succ]
    linarith

private lemma rpow_mul_le_pow {a b s t e : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hse : s ≤ e) (hte : t ≤ e) :
    a ^ s * b ^ t ≤ (a * b) ^ e := by
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  calc a ^ s * b ^ t ≤ a ^ e * b ^ e :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le ha hse)
          (Real.rpow_le_rpow_of_exponent_le hb hte)
          (Real.rpow_nonneg hb0 t) (Real.rpow_nonneg ha0 e)
    _ = (a * b) ^ e := (Real.mul_rpow ha0 hb0).symm

theorem shellPrefixEnvelope_le_of_exponent
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (α : ℝ) (hα : 1 ≤ α) (hE : HasSieveExponent F c Q α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
        shellPrefixEnvelope F c Q X Y ≤ C * (X * Y) ^ ε * (Y + X ^ α) := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨C0, hC0, hB⟩ := hE (ε / 4) hε4
  set η : ℝ := ε / 4 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hηε : η ≤ ε := by rw [hηdef]; linarith
  have hη2ε : 2 * η ≤ ε := by rw [hηdef]; linarith
  have hηe4ε : η + ε / 4 ≤ ε := by rw [hηdef]; linarith
  set K : ℝ := 2 + 1 / (η * Real.log 2) with hKdef
  have hK : 0 < K := by
    rw [hKdef]; exact DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power_constant_pos hη
  refine ⟨max 1 (2 * K * 2 ^ η + K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) *
      (4 + 2 ^ α)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro X Y hX hY
  set L := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength X with hLdef
  set L' := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength (2 * Y) with hL'def
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos hY
  have h2Y1 : (1 : ℝ) ≤ 2 * Y := by linarith
  have hXY1 : (1 : ℝ) ≤ X * Y := by nlinarith [hX, hY]
  have hpowL : (2 : ℝ) ^ L ≤ 2 * X := by rw [hLdef]; exact dyadicLength_pow_le hX
  have hpowL' : (2 : ℝ) ^ L' ≤ 4 * Y := by
    have h := dyadicLength_pow_le h2Y1
    rw [← hL'def] at h
    linarith
  have h2η0 : 0 ≤ (2 : ℝ) ^ η := Real.rpow_nonneg (by norm_num) η
  have hYη0 : 0 ≤ Y ^ η := Real.rpow_nonneg hY0.le η
  have hXa0 : 0 ≤ X ^ α := Real.rpow_nonneg hX0.le α
  have h2a0 : 0 ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
  have h2Yeta : (2 * Y) ^ η = 2 ^ η * Y ^ η := Real.mul_rpow (by norm_num) hY0.le
  have hYeta : Y ^ η ≤ (X * Y) ^ ε := by
    have hYX : Y ≤ X * Y := by nlinarith [hX0, hY0]
    exact le_trans (Real.rpow_le_rpow hY0.le hYX hη.le)
      (Real.rpow_le_rpow_of_exponent_le hXY1 hηε)
  set Bc : ℝ := C0 * (8 * X * Y) ^ (ε / 4) * (4 * Y + 2 ^ α * X ^ α) with hBcdef
  have hBc0 : 0 ≤ Bc := by rw [hBcdef]; positivity
  have hterm : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L',
      B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i) ≤ Bc := by
    intro i hi j hj
    have hiL : i < L := Finset.mem_range.mp hi
    have hjL : j < L' := Finset.mem_range.mp hj
    have hMi : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    have hMj : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hb := hB ((2 : ℝ) ^ j) ((2 : ℝ) ^ i) hMj hMi
    have hpow_i : (2 : ℝ) ^ i ≤ 2 * X :=
      le_trans (pow_le_pow_right₀ (by norm_num) (le_of_lt hiL)) hpowL
    have hpow_j : (2 : ℝ) ^ j ≤ 4 * Y :=
      le_trans (pow_le_pow_right₀ (by norm_num) (le_of_lt hjL)) hpowL'
    have hmn : ((2 : ℝ) ^ j) * ((2 : ℝ) ^ i) ≤ 8 * X * Y := by
      nlinarith [hpow_i, hpow_j, hX0, hY0]
    have hp1 : (((2 : ℝ) ^ j) * ((2 : ℝ) ^ i)) ^ (ε / 4) ≤ (8 * X * Y) ^ (ε / 4) :=
      Real.rpow_le_rpow (by positivity) hmn hε4.le
    have hp2 : (2 : ℝ) ^ j + ((2 : ℝ) ^ i) ^ α ≤ 4 * Y + 2 ^ α * X ^ α := by
      have h1 : ((2 : ℝ) ^ i) ^ α ≤ 2 ^ α * X ^ α := by
        calc ((2 : ℝ) ^ i) ^ α ≤ (2 * X) ^ α :=
              Real.rpow_le_rpow (by positivity) hpow_i (by linarith : (0 : ℝ) ≤ α)
          _ = 2 ^ α * X ^ α := Real.mul_rpow (by norm_num) hX0.le
      linarith
    calc B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i)
        ≤ C0 * (((2 : ℝ) ^ j) * ((2 : ℝ) ^ i)) ^ (ε / 4) *
            ((2 : ℝ) ^ j + ((2 : ℝ) ^ i) ^ α) := hb
      _ ≤ C0 * (8 * X * Y) ^ (ε / 4) * (4 * Y + 2 ^ α * X ^ α) := by
          gcongr
      _ = Bc := by rw [hBcdef]
  have hSum : (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L',
        B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i)) ≤ (L : ℝ) * ((L' : ℝ) * Bc) := by
    calc (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L',
            B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i))
        ≤ ∑ _i ∈ Finset.range L, ∑ _j ∈ Finset.range L', Bc := by
          apply Finset.sum_le_sum; intro i hi
          apply Finset.sum_le_sum; intro j hj
          exact hterm i hi j hj
      _ = (L : ℝ) * ((L' : ℝ) * Bc) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hR : (((L' + 1 : ℕ) : ℝ)) ≤ K * (2 * Y) ^ η := by
    have h := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power hη h2Y1
    rw [← hL'def] at h
    push_cast at h
    push_cast
    exact h
  have hP : (L : ℝ) ≤ K * X ^ η := by
    have h := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power hη hX
    rw [← hLdef] at h
    push_cast at h
    linarith
  have hP' : (L' : ℝ) ≤ K * (2 * Y) ^ η := by
    have h := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power hη h2Y1
    rw [← hL'def] at h
    push_cast at h
    linarith
  have hRle : (((L' + 1 : ℕ) : ℝ)) ≤ K * 2 ^ η * Y ^ η := by
    calc (((L' + 1 : ℕ) : ℝ)) ≤ K * (2 * Y) ^ η := hR
      _ = K * (2 ^ η * Y ^ η) := by rw [h2Yeta]
      _ = K * 2 ^ η * Y ^ η := by ring
  have hP'le : (L' : ℝ) ≤ K * 2 ^ η * Y ^ η := by
    calc (L' : ℝ) ≤ K * (2 * Y) ^ η := hP'
      _ = K * (2 ^ η * Y ^ η) := by rw [h2Yeta]
      _ = K * 2 ^ η * Y ^ η := by ring
  have hRPP : (((L' + 1 : ℕ) : ℝ)) * (L : ℝ) * (L' : ℝ) ≤
      K ^ 3 * 2 ^ (2 * η) * X ^ η * Y ^ (2 * η) := by
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    have hL'0 : (0 : ℝ) ≤ (L' : ℝ) := Nat.cast_nonneg _
    have hK2 : (0 : ℝ) ≤ K * 2 ^ η * Y ^ η := by positivity
    calc (((L' + 1 : ℕ) : ℝ)) * (L : ℝ) * (L' : ℝ)
        ≤ (K * 2 ^ η * Y ^ η) * (K * X ^ η) * (K * 2 ^ η * Y ^ η) := by
          apply mul_le_mul
          · exact mul_le_mul hRle hP hL0 hK2
          · exact hP'le
          · exact hL'0
          · positivity
      _ = K ^ 3 * 2 ^ (2 * η) * X ^ η * Y ^ (2 * η) := by
          have h2 : (2 : ℝ) ^ η * 2 ^ η = 2 ^ (2 * η) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
          have hy : Y ^ η * Y ^ η = Y ^ (2 * η) := by
            rw [← Real.rpow_add hY0]; congr 1; ring
          rw [show (K * 2 ^ η * Y ^ η) * (K * X ^ η) * (K * 2 ^ η * Y ^ η)
              = K ^ 3 * (2 ^ η * 2 ^ η) * X ^ η * (Y ^ η * Y ^ η) by ring, h2, hy]
  have hpart1 : (((L' + 1 : ℕ) : ℝ)) * (2 * (Y + X ^ α)) ≤
      2 * K * 2 ^ η * (X * Y) ^ ε * (Y + X ^ α) := by
    have h1 : (((L' + 1 : ℕ) : ℝ)) ≤ K * 2 ^ η * (X * Y) ^ ε :=
      le_trans hRle (mul_le_mul_of_nonneg_left hYeta (by positivity))
    calc (((L' + 1 : ℕ) : ℝ)) * (2 * (Y + X ^ α))
        ≤ (K * 2 ^ η * (X * Y) ^ ε) * (2 * (Y + X ^ α)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * K * 2 ^ η * (X * Y) ^ ε * (Y + X ^ α) := by ring
  have hcore : X ^ η * Y ^ (2 * η) * (8 * X * Y) ^ (ε / 4) * (4 * Y + 2 ^ α * X ^ α) ≤
      8 ^ (ε / 4) * (4 + 2 ^ α) * (X * Y) ^ ε * (Y + X ^ α) := by
    have h8 : (8 * X * Y) ^ (ε / 4) = 8 ^ (ε / 4) * (X * Y) ^ (ε / 4) := by
      rw [show (8 : ℝ) * X * Y = 8 * (X * Y) by ring,
        Real.mul_rpow (by norm_num) (by positivity)]
    have hcomb : X ^ η * Y ^ (2 * η) * (X * Y) ^ (ε / 4) ≤ (X * Y) ^ ε := by
      have heq : X ^ η * Y ^ (2 * η) * (X * Y) ^ (ε / 4)
          = X ^ (η + ε / 4) * Y ^ (2 * η + ε / 4) := by
        rw [Real.mul_rpow hX0.le hY0.le]
        rw [show X ^ η * Y ^ (2 * η) * (X ^ (ε / 4) * Y ^ (ε / 4))
            = (X ^ η * X ^ (ε / 4)) * (Y ^ (2 * η) * Y ^ (ε / 4)) by ring]
        rw [← Real.rpow_add hX0, ← Real.rpow_add hY0]
      rw [heq]
      exact rpow_mul_le_pow hX hY (by positivity) (by positivity) hηe4ε
        (by rw [hηdef]; linarith)
    have hsum : 4 * Y + 2 ^ α * X ^ α ≤ (4 + 2 ^ α) * (Y + X ^ α) := by nlinarith [hXa0, h2a0, hY0.le]
    calc X ^ η * Y ^ (2 * η) * (8 * X * Y) ^ (ε / 4) * (4 * Y + 2 ^ α * X ^ α)
        = 8 ^ (ε / 4) * (X ^ η * Y ^ (2 * η) * (X * Y) ^ (ε / 4)) *
            (4 * Y + 2 ^ α * X ^ α) := by rw [h8]; ring
      _ ≤ 8 ^ (ε / 4) * (X * Y) ^ ε * (4 * Y + 2 ^ α * X ^ α) := by gcongr
      _ ≤ 8 ^ (ε / 4) * (X * Y) ^ ε * ((4 + 2 ^ α) * (Y + X ^ α)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 8 ^ (ε / 4) * (4 + 2 ^ α) * (X * Y) ^ ε * (Y + X ^ α) := by ring
  have hpart2 : (((L' + 1 : ℕ) : ℝ)) * (L : ℝ) * (L' : ℝ) * Bc ≤
      K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) * (4 + 2 ^ α) * (X * Y) ^ ε *
        (Y + X ^ α) := by
    calc (((L' + 1 : ℕ) : ℝ)) * (L : ℝ) * (L' : ℝ) * Bc
        ≤ (K ^ 3 * 2 ^ (2 * η) * X ^ η * Y ^ (2 * η)) * Bc :=
          mul_le_mul_of_nonneg_right hRPP hBc0
      _ = K ^ 3 * 2 ^ (2 * η) * (X ^ η * Y ^ (2 * η) * (8 * X * Y) ^ (ε / 4) *
            (4 * Y + 2 ^ α * X ^ α)) * C0 := by rw [hBcdef]; ring
      _ ≤ K ^ 3 * 2 ^ (2 * η) * (8 ^ (ε / 4) * (4 + 2 ^ α) * (X * Y) ^ ε *
            (Y + X ^ α)) * C0 := by gcongr
      _ ≤ K ^ 3 * 2 ^ (2 * η) * (8 ^ (ε / 4) * (4 + 2 ^ α) * (X * Y) ^ ε *
            (Y + X ^ α)) * (C0 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) * (4 + 2 ^ α) * (X * Y) ^ ε *
            (Y + X ^ α) := by ring
  have h1XY : 1 + X + Y ≤ 2 * (Y + X ^ α) := by
    have hXa : X ≤ X ^ α := by
      have h := Real.rpow_le_rpow_of_exponent_le hX hα
      rwa [Real.rpow_one] at h
    linarith
  have hXYe : 0 ≤ (X * Y) ^ ε * (Y + X ^ α) := by
    have : (0 : ℝ) ≤ Y + X ^ α := by linarith [hXa0, hY0.le]
    positivity
  have hnn : (0 : ℝ) ≤ (((L' + 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hfin : shellPrefixEnvelope F c Q X Y ≤
      (2 * K * 2 ^ η + K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) * (4 + 2 ^ α)) *
        (X * Y) ^ ε * (Y + X ^ α) := by
    rw [shellPrefixEnvelope]
    calc (((L' + 1 : ℕ) : ℝ)) * (1 + X + Y + ∑ i ∈ Finset.range L,
            ∑ j ∈ Finset.range L', B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i))
        ≤ (((L' + 1 : ℕ) : ℝ)) * (1 + X + Y + (L : ℝ) * ((L' : ℝ) * Bc)) :=
          mul_le_mul_of_nonneg_left (by linarith [hSum]) hnn
      _ ≤ (((L' + 1 : ℕ) : ℝ)) * (2 * (Y + X ^ α) + (L : ℝ) * ((L' : ℝ) * Bc)) :=
          mul_le_mul_of_nonneg_left (by linarith [h1XY]) hnn
      _ = (((L' + 1 : ℕ) : ℝ)) * (2 * (Y + X ^ α)) +
            (((L' + 1 : ℕ) : ℝ)) * ((L : ℝ) * ((L' : ℝ) * Bc)) := by ring
      _ ≤ 2 * K * 2 ^ η * (X * Y) ^ ε * (Y + X ^ α) +
            K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) * (4 + 2 ^ α) * (X * Y) ^ ε *
              (Y + X ^ α) := by
          apply add_le_add hpart1
          calc (((L' + 1 : ℕ) : ℝ)) * ((L : ℝ) * ((L' : ℝ) * Bc))
              = (((L' + 1 : ℕ) : ℝ)) * (L : ℝ) * (L' : ℝ) * Bc := by ring
            _ ≤ _ := hpart2
      _ = (2 * K * 2 ^ η + K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) * (4 + 2 ^ α)) *
            (X * Y) ^ ε * (Y + X ^ α) := by ring
  calc shellPrefixEnvelope F c Q X Y
      ≤ (2 * K * 2 ^ η + K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) * (4 + 2 ^ α)) *
          (X * Y) ^ ε * (Y + X ^ α) := hfin
    _ ≤ max 1 (2 * K * 2 ^ η + K ^ 3 * (C0 + 1) * 2 ^ (2 * η) * 8 ^ (ε / 4) * (4 + 2 ^ α)) *
          (X * Y) ^ ε * (Y + X ^ α) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
          (by linarith [hXa0, hY0.le])

private lemma core_bound
    {M N K n α ε : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hK : 1 ≤ K) (hKM : K ≤ M)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 2 * N) (hα : 1 ≤ α) (hα₂ : α ≤ 2) (hε : 0 < ε) :
    (M * N * n) ^ (ε/5) * ((K * n^2) * N) ^ (ε/5) * Real.sqrt (M/K) * (N + (K * n^2) ^ α)
      ≤ 8 ^ (ε/5) * (M * N) ^ ε *
          (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) := by
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos hM
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le one_pos hN
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le one_pos hn1
  have hm0 : (0:ℝ) < ε/5 := by linarith
  have hm0' : (0:ℝ) ≤ ε/5 := hm0.le
  have hsq : Real.sqrt (M/K) * K^α = Real.sqrt M * K^(α - 1/2) := by
    rw [Real.sqrt_div hM0.le K, Real.sqrt_eq_rpow M, Real.sqrt_eq_rpow K, Real.rpow_sub hK0]
    field_simp
  have hAB : (M*N*n)^(ε/5) * ((K*n^2)*N)^(ε/5) ≤ 8^(ε/5) * M^(2*(ε/5)) * N^ε := by
    rw [show (M*N*n)^(ε/5) * ((K*n^2)*N)^(ε/5) = (M*K*N^2*n^3)^(ε/5) by
      rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; ring]
    have hbase : M*K*N^2*n^3 ≤ 8*M^2*N^5 := by
      have hMK : M*K ≤ M*M := mul_le_mul_of_nonneg_left hKM hM0.le
      have hn3 : n^3 ≤ (2*N)^3 := pow_le_pow_left₀ hn0.le hn2 3
      have step : M*K*N^2*n^3 ≤ (M*M)*N^2*(2*N)^3 :=
        mul_le_mul (mul_le_mul hMK le_rfl (by positivity) (by positivity)) hn3
          (by positivity) (by positivity)
      calc M*K*N^2*n^3 ≤ (M*M)*N^2*(2*N)^3 := step
        _ = 8*M^2*N^5 := by ring
    calc (M*K*N^2*n^3)^(ε/5) ≤ (8*M^2*N^5)^(ε/5) :=
          Real.rpow_le_rpow (by positivity) hbase hm0'
      _ = 8^(ε/5) * M^(2*(ε/5)) * N^ε := by
          rw [Real.mul_rpow (by positivity) (by positivity),
              Real.mul_rpow (by positivity) (by positivity)]
          rw [← Real.rpow_natCast_mul hM0.le 2 (ε/5),
              ← Real.rpow_natCast_mul hN0.le 5 (ε/5)]
          rw [show (↑(5:ℕ):ℝ) * (ε/5) = ε by push_cast; ring]
          norm_num
  have hKpow : (K * n^2)^α ≤ K^α * n^4 := by
    have h1 : (K * n^2)^α = K^α * n^(2*α) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast_mul hn0.le 2 α]
      norm_num
    rw [h1, ← Real.rpow_natCast n 4]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 2*α ≤ 4))
      (Real.rpow_nonneg hK0.le α)
  have hMle : M^(2*(ε/5)) ≤ M^ε :=
    Real.rpow_le_rpow_of_exponent_le hM (by linarith : 2*(ε/5) ≤ ε)
  have hn4 : (1:ℝ) ≤ n^4 := one_le_pow₀ hn1
  have hstep1 : (M * N * n) ^ (ε/5) * ((K * n^2) * N) ^ (ε/5) * Real.sqrt (M/K) * (N + (K * n^2) ^ α)
      ≤ 8^(ε/5) * M^(2*(ε/5)) * N^ε * Real.sqrt (M/K) * (N + K^α * n^4) := by
    have h2 : N + (K*n^2)^α ≤ N + K^α*n^4 := by linarith [hKpow]
    have hs : 0 ≤ Real.sqrt (M/K) := Real.sqrt_nonneg _
    have h0 : 0 ≤ 8^(ε/5) * M^(2*(ε/5)) * N^ε := by positivity
    calc (M*N*n)^(ε/5) * ((K*n^2)*N)^(ε/5) * Real.sqrt (M/K) * (N + (K*n^2)^α)
        = ((M*N*n)^(ε/5) * ((K*n^2)*N)^(ε/5)) * (Real.sqrt (M/K) * (N + (K*n^2)^α)) := by ring
      _ ≤ (8^(ε/5) * M^(2*(ε/5)) * N^ε) * (Real.sqrt (M/K) * (N + K^α*n^4)) :=
          mul_le_mul hAB (mul_le_mul_of_nonneg_left h2 hs) (by positivity) h0
      _ = 8^(ε/5) * M^(2*(ε/5)) * N^ε * Real.sqrt (M/K) * (N + K^α * n^4) := by ring
  have hstep2 : 8^(ε/5) * M^(2*(ε/5)) * N^ε * Real.sqrt (M/K) * (N + K^α * n^4)
      = 8^(ε/5) * M^(2*(ε/5)) * N^ε * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4) := by
    have hh : Real.sqrt (M/K) * (K^α * n^4) = Real.sqrt M * K^(α-1/2) * n^4 := by
      rw [← mul_assoc, hsq]
    calc 8^(ε/5) * M^(2*(ε/5)) * N^ε * Real.sqrt (M/K) * (N + K^α * n^4)
        = 8^(ε/5) * M^(2*(ε/5)) * N^ε * (Real.sqrt (M/K) * N + Real.sqrt (M/K) * (K^α * n^4)) := by
          ring
      _ = 8^(ε/5) * M^(2*(ε/5)) * N^ε * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4) := by
          rw [hh]
  have hstep3 : 8^(ε/5) * M^(2*(ε/5)) * N^ε * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4)
      ≤ 8^(ε/5) * M^ε * N^ε *
          (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) := by
    have hA : Real.sqrt (M/K) * N ≤ n^4 * Real.sqrt (M/K) * N := by
      have h := mul_le_mul_of_nonneg_right hn4 (by positivity : (0:ℝ) ≤ Real.sqrt (M/K) * N)
      simpa [one_mul, mul_assoc] using h
    have hB : Real.sqrt M * K^(α-1/2) * n^4 ≤ n^4 * Real.sqrt M * K^(α-1/2) :=
      le_of_eq (by ring)
    have hAB' : Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4 ≤
        n^4 * Real.sqrt M * K^(α-1/2) + n^4 * Real.sqrt (M/K) * N :=
      le_trans (add_le_add hA hB) (le_of_eq (by ring))
    have hmain : M^(2*(ε/5)) * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4) ≤
        M^ε * (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) := by
      have h1 : M^(2*(ε/5)) * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4) ≤
          M^ε * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4) :=
        mul_le_mul hMle le_rfl (by positivity) (Real.rpow_nonneg hM0.le ε)
      have h2 : M^ε * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4) ≤
          M^ε * (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) :=
        mul_le_mul_of_nonneg_left hAB' (Real.rpow_nonneg hM0.le ε)
      exact le_trans h1 h2
    calc 8^(ε/5) * M^(2*(ε/5)) * N^ε * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4)
        = (8^(ε/5) * N^ε) * (M^(2*(ε/5)) * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4)) := by
          ring
      _ ≤ (8^(ε/5) * N^ε) * (M^ε * (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = 8^(ε/5) * M^ε * N^ε *
          (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) := by ring
  have hstep4 : 8^(ε/5) * M^ε * N^ε *
          (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N)
      = 8 ^ (ε/5) * (M * N) ^ ε *
          (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) := by
    rw [Real.mul_rpow hM0.le hN0.le]; ring
  calc (M * N * n) ^ (ε/5) * ((K * n^2) * N) ^ (ε/5) * Real.sqrt (M/K) * (N + (K * n^2) ^ α)
      ≤ 8^(ε/5) * M^(2*(ε/5)) * N^ε * Real.sqrt (M/K) * (N + K^α * n^4) := hstep1
    _ = 8^(ε/5) * M^(2*(ε/5)) * N^ε * (Real.sqrt (M/K) * N + Real.sqrt M * K^(α-1/2) * n^4) := hstep2
    _ ≤ 8^(ε/5) * M^ε * N^ε *
          (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) := hstep3
    _ = 8 ^ (ε/5) * (M * N) ^ ε *
          (n^4 * Real.sqrt M * K ^ (α - 1/2) + n^4 * Real.sqrt (M/K) * N) := hstep4

theorem cancelledMainTerms_le_of_exponent
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (W : ℝ → ℝ) (hW : SieveWeight W) (kappa : ℂ)
    (α : ℝ) (hα : 1 ≤ α) (hα₂ : α ≤ 2) (hE : HasSieveExponent F c Q α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ K → K ≤ M →
      ∀ d : Ideal (𝓞 F), Squarefree d → d ⊔ D.bad = ⊤ →
        (Ideal.absNorm d : ℝ) ≤ 2 * N →
      ∀ g : Q.G, ∀ lam : Ideal (𝓞 F) → ℂ,
        ‖cancelledMainTerms Q D.bad W kappa M N K d g lam‖ ≤
          C * (Ideal.absNorm d : ℝ) ^ (4 : ℕ) * (M * N) ^ ε *
            (Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * N) *
            energy F c N lam := by
  intro ε hε
  set m : ℝ := ε / 5 with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  have hm5 : 5 * m = ε := by rw [hm]; ring
  obtain ⟨C₁, hC₁, h5⟩ := cancelledMainTerms_le_envelope Q D W hW kappa m hmpos
  obtain ⟨C₂, hC₂, h4⟩ := shellPrefixEnvelope_le_of_exponent Q α hα hE m hmpos
  refine ⟨C₁ * C₂ * 8 ^ m, by positivity, ?_⟩
  intro M N K hM hN hK hKM d hd hdb hdn g lam
  set n : ℝ := (Ideal.absNorm d : ℝ) with hn
  set S : ℝ := shellPrefixEnvelope F c Q (K * n ^ 2) N with hS
  set E : ℝ := energy F c N lam with hE
  have hd_ne : d ≠ ⊥ := by simpa using hd.ne_zero
  have hnd0 : Ideal.absNorm d ≠ 0 := fun h => hd_ne (Ideal.absNorm_eq_zero_iff.mp h)
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]
    have : (1 : ℕ) ≤ Ideal.absNorm d := Nat.one_le_iff_ne_zero.mpr hnd0
    exact_mod_cast this
  have hX1 : (1 : ℝ) ≤ K * n ^ 2 := by
    have h2 : (1 : ℝ) ≤ n ^ 2 := one_le_pow₀ hn1
    have := mul_le_mul hK h2 (by norm_num) (by linarith : (0 : ℝ) ≤ K)
    simpa using this
  have h5' := h5 M N K hM hN hK hKM d hd hdb hdn g lam
  have h4' := h4 (K * n ^ 2) N hX1 hN
  have hcore := core_bound hM hN hK hKM hn1 (by rw [hn]; exact hdn) hα hα₂ hε
  have hE0 : 0 ≤ E := by rw [hE]; rw [energy]; positivity
  calc ‖cancelledMainTerms Q D.bad W kappa M N K d g lam‖
      ≤ C₁ * (M * N * n) ^ m * Real.sqrt (M / K) * S * E := h5'
    _ ≤ C₁ * (M * N * n) ^ m * Real.sqrt (M / K) *
          (C₂ * ((K * n ^ 2) * N) ^ m * (N + (K * n ^ 2) ^ α)) * E := by
        gcongr
    _ = C₁ * C₂ * ((M * N * n) ^ m * ((K * n ^ 2) * N) ^ m * Real.sqrt (M / K) *
          (N + (K * n ^ 2) ^ α)) * E := by ring
    _ ≤ C₁ * C₂ * (8 ^ m * (M * N) ^ ε *
          (n ^ 4 * Real.sqrt M * K ^ (α - 1 / 2) + n ^ 4 * Real.sqrt (M / K) * N)) * E := by
        gcongr
    _ = (C₁ * C₂ * 8 ^ m) * n ^ 4 * (M * N) ^ ε *
          (Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * N) * E := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundary

end

end
