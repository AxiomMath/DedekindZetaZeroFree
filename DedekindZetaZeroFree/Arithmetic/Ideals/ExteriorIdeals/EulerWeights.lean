module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical
open UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]

def idealNorm (I : Ideal (𝓞 F)) : ℝ := (Ideal.absNorm I : ℝ)

def NonzeroIdeal (F : Type) [Field F] [NumberField F] :=
  { I : Ideal (𝓞 F) // I ≠ ⊥ }

def ExteriorIdeal (cS : Ideal (𝓞 F)) :=
  { I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I ⊔ cS = ⊤ }

def ExteriorSquarefreeIdeal (cS : Ideal (𝓞 F)) :=
  { I : ExteriorIdeal cS // Squarefree I.val }

def idealPrimeSupport (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (normalizedFactors I).toFinset

def idealPrimeExponent (p I : Ideal (𝓞 F)) : ℕ :=
  (normalizedFactors I).count p

def Powerful (h : Ideal (𝓞 F)) : Prop :=
  ∀ p : Ideal (𝓞 F), Prime p →
    idealPrimeExponent p h = 0 ∨ 2 ≤ idealPrimeExponent p h

def idealRadical (h : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ∏ p ∈ idealPrimeSupport h, p

def IdealSupportedOn (a f : Ideal (𝓞 F)) : Prop :=
  idealPrimeSupport a ⊆ idealPrimeSupport f

def betaLocal (Q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then Real.rpow Q (-(e / 3 : ℕ) : ℝ)
  else if e % 3 = 0 then Real.rpow Q ((1 / 2 : ℝ) - (e / 3 : ℕ))
  else 0

def betaIdeal {cS : Ideal (𝓞 F)} (f : ExteriorSquarefreeIdeal cS)
    (a : Ideal (𝓞 F)) : ℝ :=
  if a ≠ ⊥ ∧ a ⊔ cS = ⊤ ∧ IdealSupportedOn a f.val.val then
    ∏ p ∈ idealPrimeSupport f.val.val, betaLocal (idealNorm p) (idealPrimeExponent p a)
  else 0

def eulerLocal (Q σ : ℝ) : ℝ :=
  1 + (Real.rpow Q (-σ) + Real.rpow Q (-(1 / 2 : ℝ) - 3 * σ)) /
    (1 - Real.rpow Q (-1 - 3 * σ))

def eulerIdeal {cS : Ideal (𝓞 F)} (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) : ℝ :=
  ∏ p ∈ idealPrimeSupport f.val.val, eulerLocal (idealNorm p) σ

def rowNorm {cS : Ideal (𝓞 F)} (a c n : ExteriorIdeal cS) : ℝ :=
  idealNorm a.val * idealNorm c.val * idealNorm n.val ^ 3

theorem idealNorm_ge_one (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : 1 ≤ idealNorm I := by
  have hn : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change (1 : ℝ) ≤ (Ideal.absNorm I : ℝ)
  exact_mod_cast hn

theorem idealNorm_prime_ge_two (p : Ideal (𝓞 F)) (hp : Prime p) :
    2 ≤ idealNorm p := by
  have hn0 : Ideal.absNorm p ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have hn1 : Ideal.absNorm p ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr
    (fun ht => hp.not_isUnit (by simpa [ht] using (isUnit_one : IsUnit (1 : Ideal (𝓞 F)))))
  have hn : 2 ≤ Ideal.absNorm p := by omega
  change (2 : ℝ) ≤ (Ideal.absNorm p : ℝ)
  exact_mod_cast hn

private theorem radical_factors (h : Ideal (𝓞 F)) :
    normalizedFactors (idealRadical h) = (idealPrimeSupport h).val := by
  unfold idealRadical
  simp only [Finset.prod_eq_multiset_prod, Multiset.map_id']
  apply normalizedFactors_prod_of_prime
  intro p hp
  exact prime_of_normalized_factor p (by simpa only [idealPrimeSupport, Finset.mem_val, Multiset.mem_toFinset] using hp)

theorem idealPrimeExponent_radical (h : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    (p : Ideal (𝓞 F)) (hp : Prime p) :
    idealPrimeExponent p (idealRadical h) =
      if p ∈ idealPrimeSupport h then 1 else 0 := by
  unfold idealPrimeExponent
  rw [radical_factors]
  exact Multiset.count_eq_of_nodup (idealPrimeSupport h).nodup

theorem idealRadical_squarefree_nonzero (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) :
    Squarefree (idealRadical h) ∧ idealRadical h ≠ ⊥ := by
  have hn : idealRadical h ≠ 0 := by
    unfold idealRadical
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (prime_of_normalized_factor p (by
      simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)).ne_zero
  refine ⟨?_, hn⟩
  rw [squarefree_iff_nodup_normalizedFactors hn, radical_factors]
  exact (idealPrimeSupport h).nodup

theorem betaLocal_zero (Q : ℝ) : betaLocal Q 0 = 1 := by
  simp [betaLocal]

theorem betaLocal_one_add_three_mul (Q : ℝ) (hQ : 2 ≤ Q) (k : ℕ) :
    betaLocal Q (1 + 3 * k) = Real.rpow Q (-(k : ℝ)) := by
  have h0 : 1 + 3 * k ≠ 0 := by omega
  have hm : (1 + 3 * k) % 3 = 1 := by omega
  have hd : (1 + 3 * k) / 3 = k := by omega
  simp [betaLocal, h0, hm, hd]

theorem betaLocal_three_mul (Q : ℝ) (hQ : 2 ≤ Q) (k : ℕ) (hk : 1 ≤ k) :
    betaLocal Q (3 * k) = Real.rpow Q ((1 / 2 : ℝ) - k) := by
  have h0 : 3 * k ≠ 0 := by omega
  have hm : (3 * k) % 3 = 0 := by omega
  have hd : (3 * k) / 3 = k := by omega
  simp [betaLocal, h0, hm, hd]

theorem betaLocal_two_add_three_mul (Q : ℝ) (hQ : 2 ≤ Q) (k : ℕ) :
    betaLocal Q (2 + 3 * k) = 0 := by
  have h0 : 2 + 3 * k ≠ 0 := by omega
  have hm : (2 + 3 * k) % 3 = 2 := by omega
  simp [betaLocal, h0, hm]

theorem betaLocal_nonneg (Q : ℝ) (hQ : 2 ≤ Q) (e : ℕ) :
    0 ≤ betaLocal Q e := by
  unfold betaLocal
  split_ifs <;> first | positivity | exact Real.rpow_nonneg (by linarith) _

def exteriorSquarefreeTop (cS : Ideal (𝓞 F)) : ExteriorSquarefreeIdeal cS :=
  ⟨⟨⊤, by simp⟩, by simpa using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))⟩

end

end DedekindZetaZeroFree
