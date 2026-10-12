module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SevenTermApproximation
public import DedekindZetaZeroFree.LargeSieve.Bilinear.MainTermBoundaryBounds

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorBoundary
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F]
private lemma rel {x y : Ideal (𝓞 F)} (h : x ⊔ y = ⊤) : IsRelPrime x y := by
  intro z hz hz'
  apply Ideal.isUnit_iff.mpr
  apply top_unique
  rw [← h]
  exact sup_le (Ideal.dvd_iff_le.mp hz) (Ideal.dvd_iff_le.mp hz')
private lemma sup_rel {x y : Ideal (𝓞 F)} (h : IsRelPrime x y) : x ⊔ y = ⊤ :=
  Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
private lemma norm_divisor_le {a b : Ideal (𝓞 F)} (hb : b ≠ ⊥) (hab : a ∣ b) :
    ExplicitTerms.norm a ≤ ExplicitTerms.norm b := by
  unfold ExplicitTerms.norm
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hb))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hab))
set_option backward.isDefEq.respectTransparency false in
lemma admissible_divisor_reindex (c d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥)
    (hd : Squarefree d) (hdc : d ⊔ c = ⊤) (K : ℝ) (f : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ Sieve.idealAdmissibleFinset F c K, f a) =
      ∑ h ∈ Sieve.idealAdmissibleFinset F (c*d) K, ∑ e ∈ idealDivisors d,
        if ExplicitTerms.norm (h*e) ≤ K then f (h*e) else 0 := by
  let H := Sieve.idealAdmissibleFinset F (c*d) K
  let S := (H ×ˢ idealDivisors d).filter (fun he : Ideal (𝓞 F) × Ideal (𝓞 F) => ExplicitTerms.norm (he.1*he.2) ≤ K)
  have hspec {h : Ideal (𝓞 F)} (hh : h ∈ H) : Squarefree h ∧ IsRelPrime h d ∧ IsRelPrime h c := by
    obtain ⟨hs, hc, _⟩ := (Sieve.mem_idealAdmissibleFinset F (c*d) K h).mp hh
    exact ⟨hs, (rel hc).of_dvd_right (dvd_mul_left d c), (rel hc).of_dvd_right (dvd_mul_right c d)⟩
  have hmap : ∀ he ∈ S, he.1*he.2 ∈ Sieve.idealAdmissibleFinset F c K := by
    intro he hhe
    obtain ⟨hhhe, hnorm⟩ := Finset.mem_filter.mp hhe
    obtain ⟨hh, he'⟩ := Finset.mem_product.mp hhhe
    have hed := (mem_idealDivisors hd0).mp he'
    have hh' := hspec hh
    refine (Sieve.mem_idealAdmissibleFinset F c K _).mpr ⟨?_, ?_, hnorm⟩
    · exact squarefree_mul_iff.mpr ⟨hh'.2.1.of_dvd_right hed, hh'.1, hd.squarefree_of_dvd hed⟩
    · exact sup_rel (hh'.2.2.mul_left ((rel hdc).of_dvd_left hed))
  have hinj : ∀ x ∈ S, ∀ y ∈ S, x.1*x.2 = y.1*y.2 → x=y := by
    intro x hx y hy heq
    obtain ⟨hx', _⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy', _⟩ := Finset.mem_filter.mp hy
    obtain ⟨hhx, hex⟩ := Finset.mem_product.mp hx'
    obtain ⟨hhy, hey⟩ := Finset.mem_product.mp hy'
    have hedX := (mem_idealDivisors hd0).mp hex
    have hedY := (mem_idealDivisors hd0).mp hey
    have hsx := hspec hhx
    have hsy := hspec hhy
    have heX := ne_bot_of_mem_idealDivisors hex
    have heY := ne_bot_of_mem_idealDivisors hey
    have hn := mul_ne_zero hsx.1.ne_zero heX
    have hux := bad_good_unique hd0 hn heX hsx.1.ne_zero (mul_comm _ _) (sup_rel hsx.2.1)
      (fun p hp hpe => hpe.trans hedX)
    have huy := bad_good_unique hd0 hn heY hsy.1.ne_zero (heq.trans (mul_comm _ _)) (sup_rel hsy.2.1)
      (fun p hp hpe => hpe.trans hedY)
    exact Prod.ext (hux.2.trans huy.2.symm) (hux.1.trans huy.1.symm)
  have hsur : ∀ a ∈ Sieve.idealAdmissibleFinset F c K, ∃ he ∈ S, he.1*he.2 = a := by
    intro a ha
    obtain ⟨hsa,hac,haK⟩ := (Sieve.mem_idealAdmissibleFinset F c K a).mp ha
    obtain ⟨he0,hh0,hfact,hhcop,hesup⟩ := bad_good_factorization hd0 hsa.ne_zero
    have hsf := squarefree_bad_good hd0 hsa.ne_zero hsa
    let e := badPart d a
    let h := goodPart d a
    have he_d : e ∣ d := by
      apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors he0 hd0).mpr
      rw [Multiset.le_iff_subset (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors he0 |>.mp hsf.1)]
      intro p hp
      have hpp := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
      exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hd0).mpr
        ⟨hpp, hesup p hpp (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)⟩
    have hdiv : h ∣ a := by rw [hfact]; exact dvd_mul_left _ _
    have hhc : h ⊔ c = ⊤ := sup_rel ((rel hac).of_dvd_left hdiv)
    have hhcd : h ⊔ (c*d) = ⊤ := sup_rel ((rel hhc).mul_right (rel hhcop))
    have hhH : h ∈ H := (Sieve.mem_idealAdmissibleFinset F (c*d) K h).mpr
      ⟨hsf.2, hhcd, (norm_divisor_le hsa.ne_zero hdiv).trans haK⟩
    refine ⟨(h,e), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hhH,(mem_idealDivisors hd0).mpr he_d⟩, ?_⟩, ?_⟩
    · change ExplicitTerms.norm (h*e) ≤ K
      rw [mul_comm, ← hfact]
      exact haK
    · exact (mul_comm _ _).trans hfact.symm
  have hsum : (∑ he ∈ S, f (he.1*he.2)) =
      ∑ a ∈ Sieve.idealAdmissibleFinset F c K, f a :=
    Finset.sum_bij (fun he _ => he.1*he.2) hmap hinj
      (by intro b hb; obtain ⟨a,ha,heq⟩ := hsur b hb; exact ⟨a,ha,heq⟩) (fun _ _ => rfl)
  rw [← hsum, Finset.sum_filter, Finset.sum_product]
set_option backward.isDefEq.respectTransparency false in

lemma admissible_normalized_reindex (c d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥)
    (hd : Squarefree d) (hdc : d ⊔ c = ⊤) (K : ℝ) (χ : Ideal (𝓞 F) →* ℂ) :
    (∑ a ∈ Sieve.idealAdmissibleFinset F c K,
      χ a / (Real.sqrt (ExplicitTerms.norm a) : ℂ)) =
      Vendor.CutoffDifference.divisorCutoffSum (Sieve.MainBoundary.idealSize F) χ K
        (Sieve.idealAdmissibleFinset F (c*d) K) d := by
  rw [admissible_divisor_reindex c d hd0 hd hdc K]
  have hdiv : idealDivisors d = Vendor.CutoffDifference.divisors d := by
    ext e
    rw [mem_idealDivisors hd0]
    exact ((Vendor.CutoffDifference.squarefree_divisor_dictionary d hd0 hd).2.2.2.2.2 e).symm
  rw [hdiv]
  unfold Vendor.CutoffDifference.divisorCutoffSum Vendor.CutoffDifference.normalizedValue
    Vendor.CutoffDifference.cutoff
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro e he
  have hn : ((Sieve.MainBoundary.idealSize F) (h*e) : ℝ) = ExplicitTerms.norm (h*e) := by
    simp [Sieve.MainBoundary.idealSize, ExplicitTerms.norm]
  rw [hn]
  split_ifs <;> simp
open UniqueFactorizationMonoid

private lemma ideal_radical_eq (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) :
    q.radical = UniqueFactorizationMonoid.radical q := by
  let r := UniqueFactorizationMonoid.radical q
  have hr : r ≠ ⊥ := radical_ne_zero
  have hsf : Squarefree r := squarefree_radical
  obtain ⟨hp, hprod, _, _, _, _⟩ := Vendor.CutoffDifference.squarefree_divisor_dictionary r hr hsf
  let P := (factors r).toFinset
  have heq : P.inf (fun p => p) = r := by
    have h := IsDedekindDomain.inf_prime_pow_eq_prod P (fun p => p) (fun _ => 1)
      hp (by intro i hi j hj hij; exact hij)
    calc
      P.inf (fun p => p) = ∏ p ∈ P, p := by simpa only [pow_one] using h
      _ = r := hprod
  have hgen : ∀ S : Finset (Ideal (𝓞 F)), (∀ p ∈ S, Prime p) →
      (S.inf (fun p => p)).IsRadical := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [Ideal.IsRadical]
    | insert p S hnot ih =>
      intro hpr
      rw [Finset.inf_insert]
      apply Ideal.IsRadical.inf
      · exact (Ideal.isPrime_of_prime (hpr p (by simp))).isRadical
      · exact ih (by intro t ht; exact hpr t (by simp [ht]))
  have hR : r.IsRadical := heq ▸ hgen P hp
  apply le_antisymm
  · exact (hR.radical_le_iff).mpr (Ideal.dvd_iff_le.mp radical_dvd_self)
  · obtain ⟨n, hn⟩ := exists_dvd_radical_self_pow hq
    have hle : r ^ n ≤ q := Ideal.dvd_iff_le.mp hn
    have : r ≤ (r ^ n).radical := by
      intro x hx
      exact ⟨n, Ideal.pow_mem_pow hx n⟩
    exact this.trans (Ideal.radical_mono hle)
private lemma nv_prod (n : Ideal (𝓞 F) →* ℝ≥0) (χ : Ideal (𝓞 F) →* ℂ)
    (S : Finset (Ideal (𝓞 F))) :
    Vendor.CutoffDifference.SplitData.normalizedValue n χ (∏ p ∈ S, p) =
      ∏ p ∈ S, Vendor.CutoffDifference.SplitData.normalizedValue n χ p := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Vendor.CutoffDifference.SplitData.normalizedValue,
      map_one, NNReal.coe_one, Real.sqrt_one, Complex.ofReal_one, div_one]
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Vendor.CutoffDifference.SplitData.normalizedValue_mul,
        ih, Finset.prod_insert ha]

set_option backward.isDefEq.respectTransparency false in
private lemma moebius_euler (g : Ideal (𝓞 F)) (hg0 : g ≠ ⊥) (hg : Squarefree g)
    (χ : Ideal (𝓞 F) →* ℂ) :
    Vendor.CutoffDifference.moebiusDivisorSum (Sieve.MainBoundary.idealSize F) χ g =
      ∏ p ∈ primeFactors g, (1 - χ p / (Real.sqrt (ExplicitTerms.norm p) : ℂ)) := by
  let n := Sieve.MainBoundary.idealSize F
  let v := Vendor.CutoffDifference.SplitData.normalizedValue n χ
  obtain ⟨hp,hprod,hd,hi,hmu,hmem⟩ := Vendor.CutoffDifference.squarefree_divisor_dictionary g hg0 hg
  change (∑ d ∈ Vendor.CutoffDifference.SplitData.divisors g, (moebius d : ℂ) * v d) = _
  rw [hd, Finset.sum_image hi]
  have hP : (factors g).toFinset = primeFactors g := by rw [factors_eq_normalizedFactors]; rfl
  rw [hP]
  rw [show (∏ p ∈ primeFactors g, (1 - χ p / (Real.sqrt (ExplicitTerms.norm p) : ℂ))) =
      ∏ p ∈ primeFactors g, (1 + (-v p)) by
    apply Finset.prod_congr rfl; intro p hp; change 1 - v p = 1 + -v p; ring]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S hS
  rw [hmu S (by simpa only [hP] using hS),
    show v (∏ p ∈ S, p) = ∏ p ∈ S, v p from nv_prod n χ S, Finset.prod_neg]
  push_cast
  rfl
set_option backward.isDefEq.respectTransparency false in
private lemma radical_euler (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (χ : Ideal (𝓞 F) →* ℂ) :
    (∑ e ∈ idealDivisors q.radical, (moebius e : ℂ) * χ e /
      (Real.sqrt (ExplicitTerms.norm e) : ℂ)) =
      ∏ p ∈ primeFactors q, (1 - χ p / (Real.sqrt (ExplicitTerms.norm p) : ℂ)) := by
  rw [ideal_radical_eq q hq]
  let r := UniqueFactorizationMonoid.radical q
  have hr : r ≠ ⊥ := radical_ne_zero
  have hsf : Squarefree r := squarefree_radical
  have heq : idealDivisors r = Vendor.CutoffDifference.divisors r := by
    ext e
    rw [mem_idealDivisors hr]
    exact ((Vendor.CutoffDifference.squarefree_divisor_dictionary r hr hsf).2.2.2.2.2 e).symm
  change (∑ e ∈ idealDivisors r, (moebius e : ℂ) * χ e /
      (Real.sqrt (ExplicitTerms.norm e) : ℂ)) = _
  rw [heq]
  simp_rw [mul_div_assoc]
  change Vendor.CutoffDifference.moebiusDivisorSum (Sieve.MainBoundary.idealSize F) χ r = _
  rw [moebius_euler r hr hsf χ]
  exact congrArg (fun P : Finset (Ideal (𝓞 F)) => ∏ p ∈ P,
    (1 - χ p / (Real.sqrt (ExplicitTerms.norm p) : ℂ))) primeFactors_radical

lemma moebius_radical_reindex (c d : Ideal (𝓞 F)) (hc0 : c ≠ ⊥) (hd0 : d ≠ ⊥)
    (hd : Squarefree d) (hdc : d ⊔ c = ⊤) (χ : Ideal (𝓞 F) →* ℂ) :
    (∑ e ∈ idealDivisors (c*d).radical,
      (UniqueFactorizationMonoid.moebius e : ℂ) * χ e /
        (Real.sqrt (ExplicitTerms.norm e) : ℂ)) =
    (∑ t ∈ idealDivisors c.radical,
      (UniqueFactorizationMonoid.moebius t : ℂ) * χ t /
        (Real.sqrt (ExplicitTerms.norm t) : ℂ)) *
      Vendor.CutoffDifference.moebiusDivisorSum (Sieve.MainBoundary.idealSize F) χ d := by
  rw [radical_euler (c*d) (mul_ne_zero hc0 hd0) χ, radical_euler c hc0 χ,
    moebius_euler d hd0 hd χ]
  rw [primeFactors_mul_eq_union hc0 hd0,
    Finset.prod_union (disjoint_primeFactors (rel hdc).symm)]
end DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorBoundary

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F]

private lemma rel_of_sup {x y : Ideal (𝓞 F)} (h : x ⊔ y = ⊤) : IsRelPrime x y := by
  intro z hz hz'
  apply Ideal.isUnit_iff.mpr
  apply top_unique
  rw [← h]
  exact sup_le (Ideal.dvd_iff_le.mp hz) (Ideal.dvd_iff_le.mp hz')
private lemma rho_density (a : Ideal (𝓞 F)) :
    sigma4Rho a = Vendor.CutoffDifference.density (Sieve.MainBoundary.idealSize F) a := by
  unfold sigma4Rho badPrimes Vendor.CutoffDifference.density
  rw [UniqueFactorizationMonoid.factors_eq_normalizedFactors]
  apply Finset.prod_congr rfl
  intro p hp
  simp [Sieve.MainBoundary.idealSize]
private lemma rho_mul (a b : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : IsRelPrime a b) : sigma4Rho (a*b) = sigma4Rho a * sigma4Rho b := by
  unfold sigma4Rho badPrimes
  change (∏ p ∈ UniqueFactorizationMonoid.primeFactors (a*b),
    (1 - 1 / (Ideal.absNorm p : ℝ))) = _
  rw [UniqueFactorizationMonoid.primeFactors_mul_eq_union ha hb,
    Finset.prod_union (UniqueFactorizationMonoid.disjoint_primeFactors hab)]
  rfl
private lemma prime_size (p : Ideal (𝓞 F)) (hp : Prime p) :
    1 < ((Sieve.MainBoundary.idealSize F) p : ℝ) := by
  have h0 : Ideal.absNorm p ≠ 0 := fun h => hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm p ≠ 1 :=
    fun h => hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  have h2 : 1 < Ideal.absNorm p := by omega
  have h2' : (1 : ℝ) < (Ideal.absNorm p : ℝ) := by exact_mod_cast h2
  simpa [Sieve.MainBoundary.idealSize] using h2'

set_option backward.isDefEq.respectTransparency false in

theorem uncollected_boundary (c d j : Ideal (𝓞 F))
    (hc0 : c ≠ ⊥) (hd0 : d ≠ ⊥) (hj0 : j ≠ ⊥)
    (hd : Squarefree d) (hdc : d ⊔ c = ⊤) (hjcd : j ⊔ (c * d) = ⊤)
    (χ : Ideal (𝓞 F) →* ℂ)
    (hχ : ∀ l : Ideal (𝓞 F), Prime l → l ∣ d → χ l ^ 2 = 1)
    (hfixed :
      (∑ t ∈ idealDivisors c.radical, χ t / (Real.sqrt (ExplicitTerms.norm t) : ℂ)) *
      (∑ e ∈ idealDivisors c.radical,
        (UniqueFactorizationMonoid.moebius e : ℂ) * χ e /
          (Real.sqrt (ExplicitTerms.norm e) : ℂ)) = (sigma4Rho c : ℂ))
    (K : ℝ) (hK : 0 < K) :
    (sigma4Rho j : ℂ) *
      (∑ e ∈ idealDivisors (c * d).radical,
        (UniqueFactorizationMonoid.moebius e : ℂ) * χ e /
          (Real.sqrt (ExplicitTerms.norm e) : ℂ)) *
      (∑ t ∈ idealDivisors c.radical, χ t / (Real.sqrt (ExplicitTerms.norm t) : ℂ)) *
      (∑ a ∈ Sieve.idealAdmissibleFinset F c K,
        χ a / (Real.sqrt (ExplicitTerms.norm a) : ℂ)) -
    (sigma4Rho ((c * d) * j) : ℂ) *
      (∑ a ∈ Sieve.idealAdmissibleFinset F (c * d) K,
        χ a / (Real.sqrt (ExplicitTerms.norm a) : ℂ)) =
    (sigma4Rho (c * j) : ℂ) *
      ∑ b ∈ Vendor.CutoffDifference.boundaryElements
          (Sieve.idealAdmissibleFinset F (c * d) K) d,
        (Vendor.CutoffDifference.boundaryCoefficient
          (Sieve.MainBoundary.idealSize F) K
          (Sieve.idealAdmissibleFinset F (c * d) K) d b : ℂ) *
          χ b / (Real.sqrt (ExplicitTerms.norm b) : ℂ) := by
  let n := Sieve.MainBoundary.idealSize F
  let H := Sieve.idealAdmissibleFinset F (c*d) K
  have hH : ∀ a ∈ H, Squarefree a ∧ IsRelPrime a d := by
    intro a ha
    obtain ⟨hs,hcop,_⟩ := (Sieve.mem_idealAdmissibleFinset F (c*d) K a).mp ha
    exact ⟨hs, (rel_of_sup hcop).of_dvd_right (dvd_mul_left d c)⟩
  have hcol := Vendor.CutoffDifference.main_terms_difference_collected n χ prime_size
    d hd0 hd hχ K hK H hH
  have hbase : (∑ a ∈ H, χ a / (Real.sqrt (ExplicitTerms.norm a) : ℂ)) =
      Vendor.CutoffDifference.baseCutoffSum n χ K H := by
    unfold Vendor.CutoffDifference.baseCutoffSum
    apply Finset.sum_congr rfl
    intro a ha
    have haK := ((Sieve.mem_idealAdmissibleFinset F (c*d) K a).mp ha).2.2
    have hn : (n a : ℝ) = ExplicitTerms.norm a := by simp [n, Sieve.MainBoundary.idealSize, ExplicitTerms.norm]
    unfold Vendor.CutoffDifference.normalizedValue Vendor.CutoffDifference.cutoff
    change ExplicitTerms.norm a ≤ K at haK
    rw [hn, if_pos haK]
    simp
  have hjc : IsRelPrime j c := (rel_of_sup hjcd).of_dvd_right (dvd_mul_right c d)
  have hjd : IsRelPrime j d := (rel_of_sup hjcd).of_dvd_right (dvd_mul_left d c)
  have hdc' := rel_of_sup hdc
  have hfac : sigma4Rho ((c*d)*j) = sigma4Rho (c*j) *
      Vendor.CutoffDifference.density n d := by
    rw [rho_mul (c*d) j (mul_ne_zero hc0 hd0) hj0 ((rel_of_sup hjcd).symm)]
    rw [rho_mul c d hc0 hd0 hdc'.symm, rho_mul c j hc0 hj0 hjc.symm, ← rho_density]
    ring
  have hcj : sigma4Rho (c*j) = sigma4Rho c * sigma4Rho j :=
    rho_mul c j hc0 hj0 hjc.symm
  rw [DivisorBoundary.moebius_radical_reindex c d hc0 hd0 hd hdc χ,
    DivisorBoundary.admissible_normalized_reindex c d hd0 hd hdc K χ, hfac]
  change (sigma4Rho j : ℂ) * (_ * Vendor.CutoffDifference.moebiusDivisorSum n χ d) * _ *
      Vendor.CutoffDifference.divisorCutoffSum n χ K H d -
    ((sigma4Rho (c*j) * Vendor.CutoffDifference.density n d : ℝ) : ℂ) *
      (∑ a ∈ H, χ a / (Real.sqrt (ExplicitTerms.norm a) : ℂ)) = _
  rw [hbase]
  have hcol' : (∑ b ∈ Vendor.CutoffDifference.boundaryElements H d,
      (Vendor.CutoffDifference.boundaryCoefficient n K H d b : ℂ) *
      χ b / (Real.sqrt (ExplicitTerms.norm b) : ℂ)) =
      Vendor.CutoffDifference.divisorCutoffSum n χ K H d *
        Vendor.CutoffDifference.moebiusDivisorSum n χ d -
      Vendor.CutoffDifference.baseCutoffSum n χ K H *
        (Vendor.CutoffDifference.density n d : ℂ) := by
    rw [hcol]
    apply Finset.sum_congr rfl
    intro b hb
    unfold Vendor.CutoffDifference.normalizedValue
    have hn : (n b : ℝ) = ExplicitTerms.norm b := by simp [n, Sieve.MainBoundary.idealSize, ExplicitTerms.norm]
    rw [hn]
    ring
  change _ = (sigma4Rho (c*j) : ℂ) *
    (∑ b ∈ Vendor.CutoffDifference.boundaryElements H d,
      (Vendor.CutoffDifference.boundaryCoefficient n K H d b : ℂ) *
      χ b / (Real.sqrt (ExplicitTerms.norm b) : ℂ))
  rw [hcol', hcj]
  push_cast
  calc
    _ = (sigma4Rho j : ℂ) *
        ((∑ t ∈ idealDivisors c.radical, χ t / (Real.sqrt (ExplicitTerms.norm t) : ℂ)) *
        (∑ e ∈ idealDivisors c.radical, (UniqueFactorizationMonoid.moebius e : ℂ) * χ e /
          (Real.sqrt (ExplicitTerms.norm e) : ℂ))) *
        (Vendor.CutoffDifference.divisorCutoffSum n χ K H d *
          Vendor.CutoffDifference.moebiusDivisorSum n χ d) -
        (sigma4Rho c : ℂ) * (sigma4Rho j : ℂ) *
          Vendor.CutoffDifference.baseCutoffSum n χ K H *
          (Vendor.CutoffDifference.density n d : ℂ) := by ring
    _ = _ := by rw [hfixed]; ring
end DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary

end

end
