module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private theorem prod_dvd_of_pairwise_coprime {ι : Type*} (t : Finset ι) (f : ι → ℕ) (n : ℕ)
    (hcop : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (f i) (f j))
    (hdvd : ∀ i ∈ t, f i ∣ n) : (∏ i ∈ t, f i) ∣ n := by
  classical
  revert hcop hdvd
  refine Finset.induction_on t ?_ ?_
  · intro _ _
    simp
  · intro a s ha ih hcop hdvd
    rw [Finset.prod_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hdvd a (Finset.mem_insert_self a s)) ?_
    · rw [Nat.coprime_prod_right_iff]
      intro i hi
      exact hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h : a = i => ha (h.symm ▸ hi))
    · exact ih (fun i hi j hj hij =>
          hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))

theorem exists_rationalBertrand_sequence (x : ℝ) (hx : 2 ≤ x)
    (L : ℕ) (hL : 1 ≤ L) :
    ∃ p : Fin L → ℕ, Function.Injective p ∧
      ∀ i : Fin L, (p i).Prime ∧
        (2 : ℝ) ^ (i : ℕ) * x < (p i : ℝ) ∧
        (p i : ℝ) ≤ (2 : ℝ) ^ ((i : ℕ) + 1) * x := by
  classical
  have hmain : ∀ i : Fin L, ∃ q : ℕ, q.Prime ∧
      (2 : ℝ) ^ (i : ℕ) * x < (q : ℝ) ∧
      (q : ℝ) ≤ (2 : ℝ) ^ ((i : ℕ) + 1) * x := by
    intro i
    have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (i : ℕ) * x := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (i : ℕ) := one_le_pow₀ (by norm_num)
      have hx1 : (1 : ℝ) ≤ x := by linarith
      nlinarith
    have hfloor : ⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ :=
          Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (i : ℕ) * x by exact_mod_cast hge)
      omega
    obtain ⟨q, hqp, hqgt, hqle⟩ :=
      Nat.exists_prime_lt_and_le_two_mul ⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ hfloor
    refine ⟨q, hqp, ?_, ?_⟩
    · have h1 : (2 : ℝ) ^ (i : ℕ) * x < (⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h2 : (⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by
        have : ⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ + 1 ≤ q := hqgt
        exact_mod_cast this
      linarith
    · have h1 : (⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ : ℝ) ≤ (2 : ℝ) ^ (i : ℕ) * x :=
        Nat.floor_le (by positivity)
      have h2 : (q : ℝ) ≤ 2 * (⌊(2 : ℝ) ^ (i : ℕ) * x⌋₊ : ℝ) := by
        exact_mod_cast hqle
      have h3 : (2 : ℝ) ^ ((i : ℕ) + 1) * x = 2 * ((2 : ℝ) ^ (i : ℕ) * x) := by
        rw [pow_succ]
        ring
      linarith
  choose p hp using hmain
  refine ⟨p, ?_, fun i => hp i⟩
  have key : ∀ a b : Fin L, (a : ℕ) < (b : ℕ) → p a = p b → False := by
    intro a b hab hpeq
    have hb := (hp b).2.1
    have hale := (hp a).2.2
    rw [← hpeq] at hb
    have hmono : (2 : ℝ) ^ ((a : ℕ) + 1) ≤ (2 : ℝ) ^ (b : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hx0 : 0 < x := by linarith
    have h := mul_le_mul_of_nonneg_right hmono hx0.le
    linarith
  intro i j hij
  by_contra hne
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
  · exact key i j hlt hij
  · exact hne (Fin.ext heq)
  · exact key j i hgt hij.symm

theorem rationalPrime_divisor_incidence {ι : Type*} (S : Finset ι)
    (p : ι → ℕ) (hinj : Set.InjOn p (S : Set ι))
    (Z d δ : ℝ) (hZ : 2 ≤ Z) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hp : ∀ i ∈ S, (p i).Prime ∧ Z ^ (δ / d) < (p i : ℝ))
    (n : ℕ) (hn : 1 ≤ n) (hnZ : (n : ℝ) ≤ Z) :
    ((S.filter (fun i => p i ∣ n)).card : ℝ) ≤ d / δ := by
  classical
  set T : Finset ι := S.filter (fun i => p i ∣ n) with hT
  have hTS : T ⊆ S := by rw [hT]; exact Finset.filter_subset _ _
  have hprime : ∀ i ∈ T, (p i).Prime := fun i hi => (hp i (hTS hi)).1
  have hlarge : ∀ i ∈ T, Z ^ (δ / d) < (p i : ℝ) := fun i hi => (hp i (hTS hi)).2
  have hdvd : ∀ i ∈ T, p i ∣ n := fun i hi => (Finset.mem_filter.mp hi).2

  have hprod_dvd : (∏ i ∈ T, p i) ∣ n := by
    refine prod_dvd_of_pairwise_coprime T p n ?_ hdvd
    intro i hi j hj hij
    have hpi := hprime i hi
    have hpj := hprime j hj
    have hne : p i ≠ p j := fun h => hij (hinj (hTS hi) (hTS hj) h)
    exact (Nat.coprime_primes hpi hpj).mpr hne

  have hZ1 : (1 : ℝ) < Z := by linarith
  have hZpos : (0 : ℝ) < Z := by linarith
  have hdpos : (0 : ℝ) < d := by linarith
  have hδdpos : 0 < δ / d := div_pos hδ hdpos
  set t : ℝ := Z ^ (δ / d) with ht
  have ht1 : 1 < t := Real.one_lt_rpow hZ1 hδdpos
  have htpos : 0 < t := lt_trans zero_lt_one ht1
  have hprod_ge : t ^ T.card ≤ ∏ i ∈ T, (p i : ℝ) := by
    have h : (∏ i ∈ T, t) ≤ ∏ i ∈ T, (p i : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => htpos.le)
        (fun i hi => le_of_lt (hlarge i hi))
    rwa [Finset.prod_const] at h
  have hprod_le : (∏ i ∈ T, (p i : ℝ)) ≤ Z := by
    have hnat : (∏ i ∈ T, p i) ≤ n := Nat.le_of_dvd (by omega) hprod_dvd
    have hreal : (∏ i ∈ T, (p i : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hnat
    linarith
  have hkey : t ^ T.card ≤ Z := le_trans hprod_ge hprod_le
  have hrw : t ^ T.card = Z ^ ((δ / d) * (T.card : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hZpos.le]
  have hle : (δ / d) * (T.card : ℝ) ≤ 1 := by
    have h := hkey
    rw [hrw] at h
    have h' : Z ^ ((δ / d) * (T.card : ℝ)) ≤ Z ^ (1 : ℝ) := by simpa using h
    exact (Real.rpow_le_rpow_left_iff hZ1).mp h'
  show (T.card : ℝ) ≤ d / δ
  have hcard_eq : (T.card : ℝ) = (δ / d) * (T.card : ℝ) * (d / δ) := by
    field_simp
  calc (T.card : ℝ) = (δ / d) * (T.card : ℝ) * (d / δ) := hcard_eq
    _ ≤ 1 * (d / δ) := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = d / δ := one_mul _

end DedekindZetaZeroFree.LargeSieve.Sieve
