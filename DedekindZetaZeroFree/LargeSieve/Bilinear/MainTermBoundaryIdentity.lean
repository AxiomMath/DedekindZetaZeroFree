module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.BoundaryTerms.DivisorReindexingAndMoebiusSeparation

@[expose] public section

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators NNReal
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.BoundaryDyadicRows
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
private lemma sc_top (c : Ideal (𝓞 F)) : sc c ⊤ = 1 := by
  have hf : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
    simpa only [Ideal.one_eq_top] using (UniqueFactorizationMonoid.normalizedFactors_one (α := Ideal (𝓞 F)))
  simp [sc, primeToSquarefreeKernel, Sieve.squarefreeKernel, hf]
private lemma unit_eq (c m : Ideal (𝓞 F)) (K : ℝ) (hK : 1 ≤ K) :
    ReflectedSigma4.unitRows c m K = {⊤} := by
  ext a
  simp only [ReflectedSigma4.unitRows, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · intro h
    subst a
    refine ⟨rfl, ?_, by simp, ?_⟩
    · simpa only [← Ideal.one_eq_top] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))
    · simpa only [sc_top] using hK
private lemma clipped_succ (m : Ideal (𝓞 F)) (K : ℝ) (i : ℕ) :
    Sieve.clippedDyadicBlock F m K (i+1) = sigma4DyadicRows F m K ((2:ℝ)^i) := by
  ext a
  simp only [Sieve.clippedDyadicBlock, Sieve.idealDyadicBlock, sigma4DyadicRows,
    Finset.mem_inter, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1, ((Sieve.mem_idealAdmissibleFinset F m K a).mp h.2).2.2⟩
  · rintro ⟨ha, hnorm⟩
    obtain ⟨hsf, hcop, _, _⟩ := (Sieve.mem_paperShell F m _ a).mp ha
    exact ⟨ha, (Sieve.mem_idealAdmissibleFinset F m K a).mpr ⟨hsf,hcop,hnorm⟩⟩
private lemma clipped_zero (m : Ideal (𝓞 F)) (K : ℝ) (hK : 1 ≤ K) :
    Sieve.clippedDyadicBlock F m K 0 = {⊤} := by
  ext a
  simp only [Sieve.clippedDyadicBlock, Sieve.idealDyadicBlock, Finset.mem_inter,
    Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · intro h
    subst a
    refine ⟨rfl, (Sieve.mem_idealAdmissibleFinset F m K ⊤).mpr ⟨?_, by simp, ?_⟩⟩
    · simpa only [← Ideal.one_eq_top] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))
    · simpa using hK
set_option backward.isDefEq.respectTransparency false in
private lemma row_partition (c m : Ideal (𝓞 F)) (K : ℝ) (hK : 1 ≤ K)
    (f : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ ReflectedSigma4.unitRows c m K, f a) +
      (∑ B ∈ (Finset.range (Vendor.dyadicLength K)).image (fun i => (2:ℝ)^i),
        ∑ a ∈ sigma4DyadicRows F m K B, f a) =
      ∑ a ∈ Sieve.idealAdmissibleFinset F m K, f a := by
  rw [Finset.sum_image]
  · have hsum := (Finset.sum_biUnion
      (Sieve.pairwiseDisjoint_clippedDyadicBlock F m K hK) (f := f)).symm
    rw [Sieve.biUnion_clippedDyadicBlock F m K hK, Finset.sum_range_succ'] at hsum
    simpa only [clipped_succ, clipped_zero m K hK, unit_eq c m K hK, add_comm] using hsum
  · intro i hi j hj heq
    exact pow_right_injective₀ (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ) ≠ 1) heq

lemma original_partition (C : Context Q) (hK : 1 ≤ C.K) (f : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ C.originalRows 1 true, f a) +
      (∑ B ∈ dyadicScales C, ∑ a ∈ C.originalRows B, f a) =
        ∑ a ∈ Sieve.idealAdmissibleFinset F (c*C.d) C.K, f a := by
  exact row_partition c (c*C.d) C.K hK f

lemma core_partition (C : Context Q) (hK : 1 ≤ C.K) (f : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ C.reflectedCoreRows 1 true, f a) +
      (∑ B ∈ dyadicScales C, ∑ a ∈ C.reflectedCoreRows B, f a) =
        ∑ a ∈ Sieve.idealAdmissibleFinset F c C.K, f a := by
  exact row_partition c c C.K hK f
private lemma sup_top_of_rel {x y : Ideal (𝓞 F)} (h : IsRelPrime x y) : x ⊔ y = ⊤ :=
  Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
private lemma rel_of_sup {x y : Ideal (𝓞 F)} (h : x ⊔ y = ⊤) : IsRelPrime x y := by
  intro z hz hz'
  apply Ideal.isUnit_iff.mpr
  apply top_unique
  rw [← h]
  exact sup_le (Ideal.dvd_iff_le.mp hz) (Ideal.dvd_iff_le.mp hz')
private lemma supported_core_rel (hc : c ≠ ⊥) {t r : Ideal (𝓞 F)}
    (ht : t ∈ squarefreeBadPool c) (hr : Squarefree r ∧ r ⊔ c = ⊤) :
    IsRelPrime t r := by
  obtain ⟨ht0, hts, htq⟩ := (mem_squarefreeBadPool hc).mp ht
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ht0).mpr
  intro p hpt hpr hp
  exact hp.not_isUnit ((rel_of_sup hr.2) hpr (htq p hp hpt))
private lemma core_row_spec (C : Context Q) (hK : 1 ≤ C.K) (B : ℝ) (unit : Bool)
    {r : Ideal (𝓞 F)} (hr : r ∈ C.reflectedCoreRows B unit) :
    Squarefree r ∧ r ⊔ c = ⊤ := by
  cases unit with
  | false => exact ((Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1).1
      |> fun hsf => ⟨hsf, ((Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1).2.1⟩
  | true =>
    change r ∈ ReflectedSigma4.unitRows c c C.K at hr
    rw [unit_eq c c C.K hK, Finset.mem_singleton] at hr
    subst r
    exact ⟨by simpa only [← Ideal.one_eq_top] using (squarefree_one : Squarefree (1 : Ideal (𝓞 F))), by simp⟩
private lemma indices_eq (C : Context Q) (hK : 1 ≤ C.K) (B : ℝ) (unit : Bool) :
    C.reflectedRowIndices B unit = squarefreeBadPool c ×ˢ C.reflectedCoreRows B unit := by
  apply Finset.filter_eq_self.mpr
  intro tr htr
  obtain ⟨ht,hr⟩ := Finset.mem_product.mp htr
  have hc : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
  have hrel := supported_core_rel hc ht (core_row_spec C hK B unit hr)
  have hs := (mem_squarefreeBadPool hc).mp ht
  exact ⟨sup_top_of_rel hrel, squarefree_mul_iff.mpr ⟨hrel, hs.2.1,
    (core_row_spec C hK B unit hr).1⟩, mul_ne_zero hs.1 (core_row_spec C hK B unit hr).1.ne_zero⟩
set_option backward.isDefEq.respectTransparency false in

lemma reflected_block_sum (C : Context Q) (hK : 1 ≤ C.K) (B : ℝ) (unit : Bool)
    (f : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ C.reflectedRows B unit, f a) =
      ∑ t ∈ squarefreeBadPool c, ∑ r ∈ C.reflectedCoreRows B unit, f (t*r) := by
  unfold Context.reflectedRows
  rw [indices_eq C hK B unit, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro tr htr zs hzs heq
    obtain ⟨ht,hr⟩ := Finset.mem_product.mp htr
    obtain ⟨hz,hs⟩ := Finset.mem_product.mp hzs
    have hc : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
    have ht' := (mem_squarefreeBadPool hc).mp ht
    have hz' := (mem_squarefreeBadPool hc).mp hz
    have hr' := core_row_spec C hK B unit hr
    have hs' := core_row_spec C hK B unit hs
    have hne : tr.1 * tr.2 ≠ ⊥ := mul_ne_zero ht'.1 hr'.1.ne_zero
    have hu := bad_good_unique hc hne ht'.1 hr'.1.ne_zero rfl hr'.2 ht'.2.2
    have hv := bad_good_unique hc hne hz'.1 hs'.1.ne_zero heq hs'.2 hz'.2.2
    exact Prod.ext (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm)

lemma reflected_partition (C : Context Q) (hK : 1 ≤ C.K) (f : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ C.reflectedRows 1 true, f a) +
      (∑ B ∈ dyadicScales C, ∑ a ∈ C.reflectedRows B, f a) =
        ∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K, f (t*r) := by
  simp_rw [reflected_block_sum C hK]
  rw [Finset.sum_comm (s := dyadicScales C) (t := squarefreeBadPool c)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t ht => core_partition C hK (fun r => f (t*r)))
end DedekindZetaZeroFree.LargeSieve.Bilinear.BoundaryDyadicRows

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators NNReal Function
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary
open ExplicitTerms
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def character (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) : Ideal (𝓞 F) →* ℂ where
  toFun := C.primitive p hp
  map_one' := by simpa only [Ideal.one_eq_top] using (C.primitive p hp).map_top'
  map_mul' := (C.primitive p hp).map_mul'

def pairBlock (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) (B : ℝ) (unit : Bool := false) : ℂ :=
  (∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
    ∑ a ∈ C.reflectedRows B unit,
      C.primitive p hp a * C.kappa *
        (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
        (sigma4Rho (p.1 * p.2) : ℂ)) -
  (∑ a ∈ C.originalRows B unit,
    C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass *
      (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ))

def pairScalar (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) : ℂ :=
  pairBlock C p hp 1 true + ∑ B ∈ dyadicScales C, pairBlock C p hp B

private theorem sqrt_prefactor (M e j a : ℝ)
    (hM : 0 < M) (he : 0 < e) (hj : 0 < j) (ha : 0 < a) :
    M / (e * Real.sqrt j) * Real.sqrt ((e*j/M)/a) =
      Real.sqrt M / Real.sqrt e / Real.sqrt a := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity), Real.sqrt_mul he.le]
  have hsM := Real.sq_sqrt hM.le
  have hse := Real.sq_sqrt he.le
  have hsj := Real.sq_sqrt hj.le
  have hMa := Real.sqrt_pos.mpr hM
  have hea := Real.sqrt_pos.mpr he
  have hja := Real.sqrt_pos.mpr hj
  have haa := Real.sqrt_pos.mpr ha
  field_simp
  nlinarith

private theorem norm_pos {a : Ideal (𝓞 F)} (ha : a ≠ ⊥) : 0 < norm a := by
  unfold ExplicitTerms.norm
  exact_mod_cast Nat.pos_of_ne_zero (fun h => ha (Ideal.absNorm_eq_zero_iff.mp h))

private theorem prefactor_main (C : Context Q) (hM : 1 ≤ C.M)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (e a : Ideal (𝓞 F)) (he : e ≠ ⊥) (ha : a ≠ ⊥) :
    C.prefactor e p hp *
      (C.primitive p hp a * C.kappa *
        (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
        (sigma4Rho (p.1 * p.2) : ℂ)) =
    C.kappa * (Real.sqrt C.M : ℂ) * C.mass * (sigma4Rho (p.1 * p.2) : ℂ) *
      ((UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e /
        (Real.sqrt (norm e) : ℂ)) *
      (C.primitive p hp a / (Real.sqrt (norm a) : ℂ)) := by
  have huv0 := mul_ne_zero hp.hu0 hp.hv0
  have hs := sqrt_prefactor C.M (norm e) (norm (p.1 * p.2)) (norm a)
    (by linarith) (norm_pos he) (norm_pos huv0) (norm_pos ha)
  have hs' : (C.M : ℂ) / ((norm e : ℂ) * (Real.sqrt (norm (p.1 * p.2)) : ℂ)) *
      (Real.sqrt (C.dualScale e p / norm a) : ℂ) =
      (Real.sqrt C.M : ℂ) / (Real.sqrt (norm e) : ℂ) / (Real.sqrt (norm a) : ℂ) := by
    exact_mod_cast hs
  unfold Context.prefactor
  calc
    _ = ((UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e) *
      (C.primitive p hp a * C.kappa * C.mass * (sigma4Rho (p.1 * p.2) : ℂ)) *
      ((C.M : ℂ) / ((norm e : ℂ) * (Real.sqrt (norm (p.1 * p.2)) : ℂ)) *
        (Real.sqrt (C.dualScale e p / norm a) : ℂ)) := by ring
    _ = _ := by rw [hs']; ring

private theorem pairScalar_partition (C : Context Q) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    pairScalar C p hp =
    (∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K,
        C.primitive p hp (t*r) * C.kappa *
          (Real.sqrt (C.dualScale e p / norm (t*r)) : ℂ) * C.mass *
          (sigma4Rho (p.1 * p.2) : ℂ)) -
    (∑ a ∈ (Sieve.idealAdmissibleFinset F (c * C.d) C.K),
      C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass *
        (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ)) := by
  unfold pairScalar pairBlock
  rw [Finset.sum_sub_distrib]
  have hswap := Finset.sum_comm (s := dyadicScales C) (t := C.mobiusDivisors)
    (f := fun B e => C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B,
        C.primitive p hp a * C.kappa *
          (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
          (sigma4Rho (p.1 * p.2) : ℂ))
  rw [hswap]
  rw [show ∀ A B D E : ℂ, (A-B)+(D-E) = (A+D)-(B+E) by intros; ring]
  rw [← Finset.sum_add_distrib]
  have hleft : ∀ e, C.prefactor e p hp *
      (∑ a ∈ C.reflectedRows 1 true,
        C.primitive p hp a * C.kappa *
          (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
          (sigma4Rho (p.1 * p.2) : ℂ)) +
      (∑ B ∈ dyadicScales C, C.prefactor e p hp *
        ∑ a ∈ C.reflectedRows B,
          C.primitive p hp a * C.kappa *
            (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
            (sigma4Rho (p.1 * p.2) : ℂ)) =
      C.prefactor e p hp *
      (∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K,
        C.primitive p hp (t*r) * C.kappa *
          (Real.sqrt (C.dualScale e p / norm (t*r)) : ℂ) * C.mass *
          (sigma4Rho (p.1 * p.2) : ℂ)) := by
    intro e
    rw [← Finset.mul_sum, ← mul_add, BoundaryDyadicRows.reflected_partition C hK]
  simp_rw [hleft]
  rw [BoundaryDyadicRows.original_partition C hK]

private theorem pairScalar_normalized (C : Context Q) (hM : 1 ≤ C.M) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    pairScalar C p hp = C.kappa * (Real.sqrt C.M : ℂ) * C.mass *
      ((sigma4Rho (p.1 * p.2) : ℂ) *
        (∑ e ∈ C.mobiusDivisors,
          (UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e /
            (Real.sqrt (norm e) : ℂ)) *
        (∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K,
          C.primitive p hp (t*r) / (Real.sqrt (norm (t*r)) : ℂ)) -
      (sigma4Rho ((c*C.d)*(p.1*p.2)) : ℂ) *
        (∑ a ∈ (Sieve.idealAdmissibleFinset F (c * C.d) C.K), C.primitive p hp a / (Real.sqrt (norm a) : ℂ))) := by
  rw [pairScalar_partition C hK p hp]
  have hmain : ∀ e ∈ C.mobiusDivisors, ∀ t ∈ squarefreeBadPool c,
      ∀ r ∈ Sieve.idealAdmissibleFinset F c C.K,
      C.prefactor e p hp *
      (C.primitive p hp (t*r) * C.kappa *
        (Real.sqrt (C.dualScale e p / norm (t*r)) : ℂ) * C.mass *
        (sigma4Rho (p.1 * p.2) : ℂ)) =
      C.kappa * (Real.sqrt C.M : ℂ) * C.mass * (sigma4Rho (p.1 * p.2) : ℂ) *
        ((UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e /
          (Real.sqrt (norm e) : ℂ)) *
        (C.primitive p hp (t*r) / (Real.sqrt (norm (t*r)) : ℂ)) := by
    intro e he t ht r hr
    have hc0 : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
    exact prefactor_main C hM p hp e (t*r) (ne_bot_of_mem_idealDivisors he)
      (mul_ne_zero ((mem_squarefreeBadPool hc0).mp ht).1
        ((Sieve.mem_idealAdmissibleFinset F c C.K r).mp hr).1.ne_zero)
  have horig : ∀ a ∈ (Sieve.idealAdmissibleFinset F (c * C.d) C.K),
      C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass *
        (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ) =
      C.kappa * (Real.sqrt C.M : ℂ) * C.mass *
        (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ) *
        (C.primitive p hp a / (Real.sqrt (norm a) : ℂ)) := by
    intro a ha
    rw [Real.sqrt_div (by linarith : 0 ≤ C.M), Complex.ofReal_div]
    ring
  have href : (∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
      ∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K,
        C.primitive p hp (t*r) * C.kappa *
          (Real.sqrt (C.dualScale e p / norm (t*r)) : ℂ) * C.mass *
          (sigma4Rho (p.1 * p.2) : ℂ)) =
      C.kappa * (Real.sqrt C.M : ℂ) * C.mass * (sigma4Rho (p.1 * p.2) : ℂ) *
        (∑ e ∈ C.mobiusDivisors,
          (UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e /
            (Real.sqrt (norm e) : ℂ)) *
        (∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K,
          C.primitive p hp (t*r) / (Real.sqrt (norm (t*r)) : ℂ)) := by
    rw [Finset.mul_sum (s := C.mobiusDivisors), Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e he => Finset.sum_congr rfl
      (fun t ht => Finset.sum_congr rfl (fun r hr => hmain e he t ht r hr)))
  rw [href, Finset.sum_congr rfl horig]
  rw [← Finset.mul_sum]
  ring

private theorem supported_normalized_factor (C : Context Q)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    (∑ t ∈ squarefreeBadPool c, ∑ r ∈ Sieve.idealAdmissibleFinset F c C.K,
      C.primitive p hp (t*r) / (Real.sqrt (norm (t*r)) : ℂ)) =
    (∑ t ∈ squarefreeBadPool c,
      C.primitive p hp t / (Real.sqrt (norm t) : ℂ)) *
    (∑ r ∈ Sieve.idealAdmissibleFinset F c C.K,
      C.primitive p hp r / (Real.sqrt (norm r) : ℂ)) := by
  have hn : ∀ a : Ideal (𝓞 F), ((Sieve.MainBoundary.idealSize F) a : ℝ) = norm a := by
    intro a
    simp [Sieve.MainBoundary.idealSize, ExplicitTerms.norm]
  have hmul : ∀ a b : Ideal (𝓞 F),
      C.primitive p hp (a*b) / (Real.sqrt (norm (a*b)) : ℂ) =
      (C.primitive p hp a / (Real.sqrt (norm a) : ℂ)) *
      (C.primitive p hp b / (Real.sqrt (norm b) : ℂ)) := by
    intro a b
    have h := Vendor.CutoffDifference.SplitData.normalizedValue_mul
      (Sieve.MainBoundary.idealSize F) (character C p hp) a b
    change (character C p hp) (a*b) / (Real.sqrt (norm (a*b)) : ℂ) =
      ((character C p hp) a / (Real.sqrt (norm a) : ℂ)) *
      ((character C p hp) b / (Real.sqrt (norm b) : ℂ))
    simpa only [Vendor.CutoffDifference.SplitData.normalizedValue, hn] using h
  simp_rw [hmul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun t ht => (Finset.mul_sum _ _ _).symm)

private theorem idealRadical_eq_ufmRadical (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) :
    Ideal.radical q = UniqueFactorizationMonoid.radical q := by
  have hset : ({J : Ideal (𝓞 F) | q ≤ J ∧ J.IsPrime} : Set (Ideal (𝓞 F))) =
      ↑(UniqueFactorizationMonoid.primeFactors q) := by
    ext J
    rw [Set.mem_setOf_eq, Finset.mem_coe, UniqueFactorizationMonoid.primeFactors,
      Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hq]
    tauto
  have hsInf : sInf (↑(UniqueFactorizationMonoid.primeFactors q) : Set (Ideal (𝓞 F))) =
      ⨅ p ∈ UniqueFactorizationMonoid.primeFactors q, p := by
    refine le_antisymm ?_ ?_
    · exact le_iInf fun p => le_iInf fun hp => sInf_le (Finset.mem_coe.mpr hp)
    · exact le_sInf fun J hJ => iInf_le_of_le J (iInf_le _ (Finset.mem_coe.mp hJ))
  have hpair : ((UniqueFactorizationMonoid.primeFactors q : Finset (Ideal (𝓞 F))) :
      Set (Ideal (𝓞 F))).Pairwise (IsCoprime on id) := by
    intro p hp r hr hpr
    show IsCoprime p r
    rw [Finset.mem_coe, UniqueFactorizationMonoid.primeFactors, Multiset.mem_toFinset] at hp hr
    obtain ⟨hpp, hpq⟩ := (Ideal.mem_normalizedFactors_iff hq).mp hp
    obtain ⟨hrp, hrq⟩ := (Ideal.mem_normalizedFactors_iff hq).mp hr
    have hpbot : p ≠ ⊥ := fun h => hq (le_bot_iff.mp (h ▸ hpq))
    have hrbot : r ≠ ⊥ := fun h => hq (le_bot_iff.mp (h ▸ hrq))
    haveI := Ideal.IsPrime.isMaximal hpp hpbot
    haveI := Ideal.IsPrime.isMaximal hrp hrbot
    exact Ideal.isCoprime_of_isMaximal hpr
  rw [Ideal.radical_eq_sInf, hset, hsInf, UniqueFactorizationMonoid.radical,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := UniqueFactorizationMonoid.primeFactors q) (J := id) hpair]
  rfl

private theorem primeFactors_ufmRadical (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) :
    UniqueFactorizationMonoid.primeFactors (UniqueFactorizationMonoid.radical q) =
      UniqueFactorizationMonoid.primeFactors q := by
  have hR0 : UniqueFactorizationMonoid.radical q ≠ ⊥ :=
    UniqueFactorizationMonoid.radical_ne_zero
  have hEq : Ideal.radical q = UniqueFactorizationMonoid.radical q :=
    idealRadical_eq_ufmRadical q hq
  ext J
  rw [UniqueFactorizationMonoid.primeFactors, Multiset.mem_toFinset,
    Ideal.mem_normalizedFactors_iff hR0, UniqueFactorizationMonoid.primeFactors,
    Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hq]
  constructor
  · rintro ⟨hp, hle⟩
    exact ⟨hp, (hEq ▸ Ideal.le_radical).trans hle⟩
  · rintro ⟨hp, hle⟩
    exact ⟨hp, hEq ▸ (Ideal.IsPrime.radical_le_iff hp).mpr hle⟩

private theorem pool_eq_divisors (c : Ideal (𝓞 F)) (hc0 : c ≠ ⊥) :
    squarefreeBadPool c = idealDivisors c.radical := by
  rw [idealRadical_eq_ufmRadical c hc0]
  have hr0 : UniqueFactorizationMonoid.radical c ≠ ⊥ :=
    UniqueFactorizationMonoid.radical_ne_zero
  have hsf := UniqueFactorizationMonoid.squarefree_radical (a := c)
  have hd := Vendor.CutoffDifference.squarefree_divisor_dictionary
    (UniqueFactorizationMonoid.radical c) hr0 hsf
  have hdiv : idealDivisors (UniqueFactorizationMonoid.radical c) =
      Vendor.CutoffDifference.divisors (UniqueFactorizationMonoid.radical c) := by
    ext e
    rw [mem_idealDivisors hr0]
    exact (hd.2.2.2.2.2 e).symm
  rw [hdiv]
  change squarefreeBadPool c = Vendor.CutoffDifference.SplitData.divisors
    (UniqueFactorizationMonoid.radical c)
  rw [hd.2.2.1, UniqueFactorizationMonoid.factors_eq_normalizedFactors]
  change squarefreeBadPool c =
    (UniqueFactorizationMonoid.primeFactors (UniqueFactorizationMonoid.radical c)).powerset.image
      (fun S => ∏ p ∈ S, p)
  rw [primeFactors_ufmRadical c hc0]
  rfl

theorem pair_scalar_uncollected (C : Context Q) (hM : 1 ≤ C.M) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    pairScalar C p hp = C.kappa * (Real.sqrt C.M : ℂ) * C.mass *
      ((sigma4Rho (p.1 * p.2) : ℂ) *
        (∑ e ∈ idealDivisors (c * C.d).radical,
          (UniqueFactorizationMonoid.moebius e : ℂ) * (character C p hp) e /
            (Real.sqrt (norm e) : ℂ)) *
        (∑ t ∈ idealDivisors c.radical,
          (character C p hp) t / (Real.sqrt (norm t) : ℂ)) *
        (∑ a ∈ Sieve.idealAdmissibleFinset F c C.K,
          (character C p hp) a / (Real.sqrt (norm a) : ℂ)) -
       (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ) *
        (∑ a ∈ Sieve.idealAdmissibleFinset F (c * C.d) C.K,
          (character C p hp) a / (Real.sqrt (norm a) : ℂ))) := by
  rw [pairScalar_normalized C hM hK p hp, supported_normalized_factor C p hp]
  have hc0 : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
  rw [pool_eq_divisors c hc0]
  simp only [Context.mobiusDivisors, character, MonoidHom.coe_mk, OneHom.coe_mk]
  ring
end DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators NNReal Function

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

namespace MainBoundary

def character (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) : Ideal (𝓞 F) →* ℂ where
  toFun := C.primitive p hp
  map_one' := by simpa only [Ideal.one_eq_top] using (C.primitive p hp).map_top'
  map_mul' := (C.primitive p hp).map_mul'

def base (C : Context Q) : Finset (Ideal (𝓞 F)) :=
  Sieve.idealAdmissibleFinset F (c * C.d) C.K

def beta (C : Context Q) (b : Ideal (𝓞 F)) : ℤ :=
  Vendor.CutoffDifference.boundaryCoefficient (Sieve.MainBoundary.idealSize F)
    C.K (base C) C.d b

def boundary (C : Context Q) : Finset (Ideal (𝓞 F)) :=
  Vendor.CutoffDifference.boundaryElements (base C) C.d

def pairBlock (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) (B : ℝ) (unit : Bool := false) : ℂ :=
  (∑ e ∈ C.mobiusDivisors, C.prefactor e p hp *
    ∑ a ∈ C.reflectedRows B unit,
      C.primitive p hp a * C.kappa *
        (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
        (sigma4Rho (p.1 * p.2) : ℂ)) -
  (∑ a ∈ C.originalRows B unit,
    C.primitive p hp a * C.kappa * (Real.sqrt (C.M / norm a) : ℂ) * C.mass *
      (sigma4Rho ((c * C.d) * (p.1 * p.2)) : ℂ))

def pairScalar (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F))
    (hp : C.ValidPair p) : ℂ :=
  pairBlock C p hp 1 true + ∑ B ∈ dyadicScales C, pairBlock C p hp B

def mainDifference (C : Context Q) : ℂ :=
  (T C 1 true - Tprime C 1 true) +
    ∑ B ∈ dyadicScales C, (T C B - Tprime C B)

private theorem isRelPrime_of_sup_eq_top' {x y : Ideal (𝓞 F)} (h : x ⊔ y = ⊤) :
    IsRelPrime x y := by
  intro z hzx hzy
  rw [Ideal.isUnit_iff]
  exact le_antisymm le_top
    (h ▸ sup_le (Ideal.dvd_iff_le.mp hzx) (Ideal.dvd_iff_le.mp hzy))

private theorem one_lt_idealSize_prime (p : Ideal (𝓞 F)) (hp : Prime p) :
    1 < ((Sieve.MainBoundary.idealSize F) p : ℝ) := by
  have h0 : Ideal.absNorm p ≠ 0 := fun h => hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm p ≠ 1 :=
    fun h => hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  have h2 : 1 < Ideal.absNorm p := by omega
  have h2' : (1 : ℝ) < (Ideal.absNorm p : ℝ) := by exact_mod_cast h2
  simpa [Sieve.MainBoundary.idealSize] using h2'

private theorem base_squarefree_isRelPrime (C : Context Q) :
    ∀ h ∈ base C, Squarefree h ∧ IsRelPrime h C.d := by
  intro h hh
  have hh' := (Sieve.mem_idealAdmissibleFinset F (c * C.d) C.K h).mp hh
  refine ⟨hh'.1, ?_⟩
  intro z hzh hzd
  have hzcd : z ∣ c * C.d := dvd_mul_of_dvd_right hzd c
  have hz : z ∣ h ⊔ (c * C.d) := by
    rw [← Ideal.gcd_eq_sup]; exact dvd_gcd hzh hzcd
  rw [hh'.2.1] at hz
  exact Ideal.isUnit_iff.mpr (le_antisymm le_top (Ideal.dvd_iff_le.mp hz))

private theorem sup_c_eq_top_of_beta_ne_zero (C : Context Q)
    (b : Ideal (𝓞 F)) (hb : beta C b ≠ 0) : b ⊔ c = ⊤ := by
  have hex : ∃ h ∈ base C, ∃ d ∈ Vendor.CutoffDifference.divisors C.d,
      ∃ e ∈ Vendor.CutoffDifference.divisors C.d, h * d * e = b := by
    by_contra hnone
    apply hb
    unfold beta Vendor.CutoffDifference.boundaryCoefficient
    apply Finset.sum_eq_zero
    intro h hh
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro e he
    exact if_neg (fun heq => hnone ⟨h, hh, d, hd, e, he, heq⟩)
  obtain ⟨h, hh, d, hd, e, he, rfl⟩ := hex
  have hhd : h ⊔ (c * C.d) = ⊤ :=
    (Sieve.mem_idealAdmissibleFinset F (c * C.d) C.K h).mp hh |>.2.1
  have hdvd : ∀ x ∈ Vendor.CutoffDifference.divisors C.d, x ∣ C.d := by
    intro x hx
    exact ((Vendor.CutoffDifference.squarefree_divisor_dictionary C.d C.hd0 C.hd).2.2.2.2.2 x).mp hx
  have hrel_h : IsRelPrime h c :=
    (IsRelPrime.of_dvd_right (isRelPrime_of_sup_eq_top' hhd) (dvd_mul_right c C.d))
  have hrel_d : IsRelPrime d c :=
    IsRelPrime.of_dvd_left (isRelPrime_of_sup_eq_top' C.hdc) (hdvd d hd)
  have hrel_e : IsRelPrime e c :=
    IsRelPrime.of_dvd_left (isRelPrime_of_sup_eq_top' C.hdc) (hdvd e he)
  have hrel : IsRelPrime (h * d * e) c :=
    (hrel_h.mul_left hrel_d).mul_left hrel_e
  exact Ideal.isUnit_iff.mp (hrel (Ideal.dvd_iff_le.mpr le_sup_left)
    (Ideal.dvd_iff_le.mpr le_sup_right))

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

theorem double_divisor_local_product (q : Ideal (𝓞 F)) (hq : q ≠ ⊥)
    (χ : Ideal (𝓞 F) →* ℂ) :
    (∑ r ∈ idealDivisors q.radical,
      χ r / (Real.sqrt (norm r) : ℂ)) *
    (∑ e ∈ idealDivisors q.radical,
      (UniqueFactorizationMonoid.moebius e : ℂ) * χ e /
        (Real.sqrt (norm e) : ℂ)) =
    ∏ l ∈ (UniqueFactorizationMonoid.normalizedFactors q).toFinset,
      (1 - χ l ^ 2 / (norm l : ℂ)) := by
  classical
  rw [ideal_radical_eq q hq]
  let r := UniqueFactorizationMonoid.radical q
  have hr : r ≠ ⊥ := radical_ne_zero
  obtain ⟨hp, hprod, hd, hi, hmu, hmem⟩ :=
    Vendor.CutoffDifference.squarefree_divisor_dictionary r hr squarefree_radical
  let P := (factors r).toFinset
  let n := Sieve.MainBoundary.idealSize F
  let v := Vendor.CutoffDifference.SplitData.normalizedValue n χ
  have hdiv : idealDivisors r = Vendor.CutoffDifference.SplitData.divisors r := by
    ext d
    rw [mem_idealDivisors hr, hmem]
  have hsum1 : (∑ d ∈ idealDivisors r, v d) = ∏ p ∈ P, (1 + v p) := by
    rw [hdiv, hd, Finset.sum_image hi, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro S hS
    exact nv_prod n χ S
  have hsum2 : (∑ d ∈ idealDivisors r, (moebius d : ℂ) * v d) =
      ∏ p ∈ P, (1 - v p) := by
    rw [hdiv, hd, Finset.sum_image hi]
    rw [show (∏ p ∈ P, (1 - v p)) = ∏ p ∈ P, (1 + (-v p)) by
      apply Finset.prod_congr rfl; intro p hp; ring]
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro S hS
    rw [hmu S hS, show v (∏ p ∈ S, p) = ∏ p ∈ S, v p from nv_prod n χ S,
      Finset.prod_neg]
    push_cast
    rfl
  change (∑ d ∈ idealDivisors r, v d) *
    (∑ d ∈ idealDivisors r, (moebius d : ℂ) * χ d / (Real.sqrt (norm d) : ℂ)) = _
  simp_rw [mul_div_assoc]
  change (∑ d ∈ idealDivisors r, v d) *
    (∑ d ∈ idealDivisors r, (moebius d : ℂ) * v d) = _
  rw [hsum1, hsum2, ← Finset.prod_mul_distrib]
  have hP : P = (normalizedFactors q).toFinset := by
    change (factors (UniqueFactorizationMonoid.radical q)).toFinset = _
    rw [factors_eq_normalizedFactors]
    exact primeFactors_radical
  rw [hP]
  apply Finset.prod_congr rfl
  intro l hl
  have hs : (Real.sqrt (norm l) : ℂ) ^ 2 = (norm l : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt]
    unfold norm
    positivity
  change (1 + χ l / (Real.sqrt (norm l) : ℂ)) *
    (1 - χ l / (Real.sqrt (norm l) : ℂ)) = _
  rw [show (1 + χ l / (Real.sqrt (norm l) : ℂ)) *
      (1 - χ l / (Real.sqrt (norm l) : ℂ)) =
      1 - (χ l / (Real.sqrt (norm l) : ℂ)) ^ 2 by ring, div_pow, hs]

theorem fixed_prime_product (C : Context Q)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    (∑ r ∈ idealDivisors c.radical,
      C.primitive p hp r / (Real.sqrt (norm r) : ℂ)) *
    (∑ e ∈ idealDivisors c.radical,
      (UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e /
        (Real.sqrt (norm e) : ℂ)) = (sigma4Rho c : ℂ) := by
  have hc0 : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
  have hprod := double_divisor_local_product c hc0 (character C p hp)
  change (∑ r ∈ idealDivisors c.radical,
      (character C p hp) r / (Real.sqrt (norm r) : ℂ)) *
    (∑ e ∈ idealDivisors c.radical,
      (moebius e : ℂ) * (character C p hp) e / (Real.sqrt (norm e) : ℂ)) = _
  rw [hprod]
  unfold sigma4Rho badPrimes
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro l hl
  have hlp : Prime l := prime_of_normalized_factor l (Multiset.mem_toFinset.mp hl)
  have hlc : l ∣ c := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hl)
  have hrel : IsRelPrime l (p.1 * p.2) :=
    ((isRelPrime_of_sup_eq_top' hp.huc).symm.of_dvd_left hlc).mul_right
      ((isRelPrime_of_sup_eq_top' hp.hvc).symm.of_dvd_left hlc)
  have hsup : l ⊔ (p.1 * p.2) = ⊤ := Ideal.isUnit_iff.mp
    (hrel (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
  have hchi : (character C p hp) l ^ 2 = 1 :=
    (primitiveProductQuadratic Q hp.hu0 hp.hv0 hp.hu hp.hv hp.huc hp.hvc hp.huv
      hp.hquotientClass (C.primitive p hp) (C.primitive_spec p hp).2.1).2 l hlp.ne_zero hsup
  rw [hchi]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, norm]

theorem pair_scalar_boundary (C : Context Q)
    (hM : 1 ≤ C.M) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    pairScalar C p hp =
      C.kappa * (Real.sqrt C.M : ℂ) * (sigma4Rho (c * p.1 * p.2) : ℂ) * C.mass *
        ∑ b ∈ boundary C,
          (beta C b : ℂ) * C.primitive p hp b / (Real.sqrt (norm b) : ℂ) := by
  have hχ : ∀ l : Ideal (𝓞 F), Prime l → l ∣ C.d →
      (character C p hp) l ^ 2 = 1 := by
    intro l hl hld
    have hsup : l ⊔ (p.1 * p.2) = ⊤ := Ideal.isUnit_iff.mp
      (((isRelPrime_of_sup_eq_top' hp.hduv).of_dvd_left hld)
        (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    exact (primitiveProductQuadratic Q hp.hu0 hp.hv0 hp.hu hp.hv hp.huc hp.hvc hp.huv
      hp.hquotientClass (C.primitive p hp) (C.primitive_spec p hp).2.1).2 l hl.ne_zero hsup
  have hc0 : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
  have hjcd : (p.1 * p.2) ⊔ (c * C.d) = ⊤ := by
    have hrelc := (isRelPrime_of_sup_eq_top' hp.huc).mul_left (isRelPrime_of_sup_eq_top' hp.hvc)
    have hreld := (isRelPrime_of_sup_eq_top' hp.hduv).symm
    have hrel := hrelc.mul_right hreld
    exact Ideal.isUnit_iff.mp (hrel (Ideal.dvd_iff_le.mpr le_sup_left)
      (Ideal.dvd_iff_le.mpr le_sup_right))
  have hfinite := DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary.uncollected_boundary
    c C.d (p.1 * p.2) hc0 C.hd0 (mul_ne_zero hp.hu0 hp.hv0) C.hd C.hdc hjcd
    (character C p hp) hχ (fixed_prime_product C p hp) C.K (by linarith)
  change DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary.pairScalar C p hp = _
  rw [DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary.pair_scalar_uncollected C hM hK p hp]
  change C.kappa * (Real.sqrt C.M : ℂ) * C.mass * _ = _
  change _ = (sigma4Rho (c * (p.1 * p.2)) : ℂ) *
    ∑ b ∈ boundary C, (beta C b : ℂ) * C.primitive p hp b /
      (Real.sqrt (norm b) : ℂ) at hfinite
  simp only [DedekindZetaZeroFree.LargeSieve.Bilinear.MainBoundary.character, character] at hfinite ⊢
  rw [hfinite]
  simp only [← mul_assoc]
  ring

private theorem sup_mul_eq_top {a u v : Ideal (𝓞 F)}
    (hu : a ⊔ u = ⊤) (hv : a ⊔ v = ⊤) : a ⊔ (u * v) = ⊤ := by
  rw [Ideal.sup_mul_eq_of_coprime_left hu, hv]

private theorem primitive_eq_pair_on_core (C : Context Q)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p)
    (a : Ideal (𝓞 F)) (hac : a ⊔ c = ⊤) :
    character C p hp a = Sieve.MainBoundary.pairCharacter Q p.1 p.2 a := by
  change C.primitive p hp a = (Q.χ p.1) a * star ((Q.χ p.2) a)
  by_cases ha0 : a = ⊥
  · subst a
    simp [RayOperations.map_bot]
  have hupper : ∀ u, Squarefree u → u ⊔ c = ⊤ →
      a ⊔ u = ⊤ → a ⊔ Q.cond u = ⊤ := by
    intro u hu huc hau
    have h : Q.cond u ∣ u * c := by
      simpa only [C.core] using C.D.all_conductor_dvd u hu huc
    exact top_unique ((sup_mul_eq_top hau hac).symm.trans_le
      (sup_le_sup_left (Ideal.dvd_iff_le.mp h) a))
  have hlower : ∀ u, Squarefree u → u ⊔ c = ⊤ →
      a ⊔ u ≠ ⊤ → a ⊔ Q.cond u ≠ ⊤ := by
    intro u hu huc hau hcond
    have h : u ∣ Q.cond u := C.D.index_dvd_conductor u hu (by simpa [C.core] using huc)
    exact hau (top_unique (hcond.symm.trans_le
      (sup_le_sup_left (Ideal.dvd_iff_le.mp h) a)))
  by_cases hauv : a ⊔ (p.1 * p.2) = ⊤
  · have hau : a ⊔ p.1 = ⊤ := top_unique (hauv.symm.trans_le
        (sup_le_sup_left Ideal.mul_le_left a))
    have hav : a ⊔ p.2 = ⊤ := top_unique (hauv.symm.trans_le
        (sup_le_sup_left Ideal.mul_le_right a))
    exact (C.primitive_spec p hp).2.1 a
      (sup_mul_eq_top (hupper _ hp.hu hp.huc hau) (hupper _ hp.hv hp.hvc hav))
  · have hzero : C.primitive p hp a = 0 :=
      ((C.primitive p hp).eq_zero_iff' a).mpr (Or.inr hauv)
    have hor : a ⊔ p.1 ≠ ⊤ ∨ a ⊔ p.2 ≠ ⊤ := by
      by_contra h
      push Not at h
      exact hauv (sup_mul_eq_top h.1 h.2)
    rcases hor with hu | hv
    · have hz := ((Q.χ p.1).eq_zero_iff' a).mpr
        (Or.inr (hlower _ hp.hu hp.huc hu))
      simp [hzero, hz]
    · have hz := ((Q.χ p.2).eq_zero_iff' a).mpr
        (Or.inr (hlower _ hp.hv hp.hvc hv))
      simp [hzero, hz]

set_option maxHeartbeats 800000 in
private theorem cutoff_pair_boundary (C : Context Q) (hK : 1 ≤ C.K)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    Sieve.MainBoundary.cutoffDifference c C.d C.K
      (Sieve.MainBoundary.pairCharacter Q p.1 p.2) =
      ∑ b ∈ boundary C,
        (beta C b : ℂ) * C.primitive p hp b / (Real.sqrt (norm b) : ℂ) := by
  let χ := Sieve.MainBoundary.pairCharacter Q p.1 p.2
  have hχ : ∀ l : Ideal (𝓞 F), Prime l → l ∣ C.d → χ l ^ 2 = 1 := by
    intro l hl hld
    have hcop : l ⊔ c = ⊤ := Ideal.isUnit_iff.mp
      (((isRelPrime_of_sup_eq_top' C.hdc).of_dvd_left hld)
        (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    have hcopuv : l ⊔ (p.1 * p.2) = ⊤ := Ideal.isUnit_iff.mp
      ((isRelPrime_of_sup_eq_top' hp.hduv).of_dvd_left hld
        (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))
    rw [← primitive_eq_pair_on_core C p hp l hcop]
    exact (primitiveProductQuadratic Q hp.hu0 hp.hv0 hp.hu hp.hv hp.huc hp.hvc hp.huv
      hp.hquotientClass (C.primitive p hp) (C.primitive_spec p hp).2.1).2
        l hl.ne_zero hcopuv
  have hcol := Vendor.CutoffDifference.main_terms_difference_collected
    (Sieve.MainBoundary.idealSize F) χ one_lt_idealSize_prime C.d
      C.hd0 C.hd hχ C.K (by linarith) (base C) (base_squarefree_isRelPrime C)
  change Sieve.MainBoundary.cutoffDifference c C.d C.K χ = _
  unfold Sieve.MainBoundary.cutoffDifference
  change Vendor.CutoffDifference.divisorCutoffSum (Sieve.MainBoundary.idealSize F) χ
      C.K (base C) C.d *
    Vendor.CutoffDifference.moebiusDivisorSum (Sieve.MainBoundary.idealSize F) χ C.d -
    Vendor.CutoffDifference.baseCutoffSum (Sieve.MainBoundary.idealSize F) χ
      C.K (base C) *
      (Vendor.CutoffDifference.density (Sieve.MainBoundary.idealSize F) C.d : ℂ) = _
  rw [hcol]
  apply Finset.sum_congr rfl
  intro b hb
  change (beta C b : ℂ) *
    Vendor.CutoffDifference.normalizedValue (Sieve.MainBoundary.idealSize F) χ b = _
  by_cases hβ : beta C b = 0
  · simp [hβ]
  have hbc := sup_c_eq_top_of_beta_ne_zero C b hβ
  have heq := primitive_eq_pair_on_core C p hp b hbc
  change C.primitive p hp b = χ b at heq
  have hn : ((Sieve.MainBoundary.idealSize F) b : ℝ) = norm b := by
    simp [Sieve.MainBoundary.idealSize, norm]
  unfold Vendor.CutoffDifference.normalizedValue
  rw [← heq, hn]
  ring

private theorem columns_eq (C : Context Q) :
    C.columns = Sieve.MainBoundary.quotientColumns Q c C.d C.N C.g := by
  ext u
  simp only [Context.columns, Sieve.MainBoundary.quotientColumns, norm, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hs, hg⟩
    have hsdu := ((Sieve.mem_paperShell F c C.N _).mp hs).1
    have hrel := (IsRelPrime.of_squarefree_mul hsdu).symm
    exact ⟨hu, Ideal.isUnit_iff.mp (hrel (Ideal.dvd_iff_le.mpr le_sup_left)
      (Ideal.dvd_iff_le.mpr le_sup_right)), hs, hg⟩
  · rintro ⟨hu, _, hs, hg⟩
    exact ⟨hu, hs, hg⟩

private theorem validPair_iff (C : Context Q) (u v : Ideal (𝓞 F))
    (hu : u ∈ C.columns) (hv : v ∈ C.columns) :
    C.ValidPair (u, v) ↔ u ⊔ v = ⊤ ∧ u * v ≠ ⊤ := by
  constructor
  · intro hp
    exact ⟨hp.huv, hp.offDiagonal⟩
  · rintro ⟨huv, hne⟩
    obtain ⟨hu', hsu, hgu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv', hsv, hgv⟩ := Finset.mem_filter.mp hv
    obtain ⟨husf, huc, _⟩ := (Sieve.mem_idealAdmissibleFinset F c _ u).mp hu'
    obtain ⟨hvsf, hvc, _⟩ := (Sieve.mem_idealAdmissibleFinset F c _ v).mp hv'
    obtain ⟨hdusf, hduc, _⟩ := (Sieve.mem_paperShell F c C.N _).mp hsu
    obtain ⟨hdvsf, hdvc, _⟩ := (Sieve.mem_paperShell F c C.N _).mp hsv
    have hrel := (IsRelPrime.of_squarefree_mul hdusf).mul_right
      (IsRelPrime.of_squarefree_mul hdvsf)
    have hclass := hgu.trans hgv.symm
    exact ⟨husf.ne_zero, hvsf.ne_zero, husf, hvsf, huc, hvc, hdusf, hdvsf,
      hduc, hdvc, huv, Ideal.isUnit_iff.mp (hrel (Ideal.dvd_iff_le.mpr le_sup_left)
        (Ideal.dvd_iff_le.mpr le_sup_right)), hclass,
      (ClassTwists.cls_mul_eq_iff Q C.d u v C.hdc huc hvc hduc hdvc).mp hclass, hne⟩

private theorem mainDifference_pairSum (C : Context Q) :
    mainDifference C = C.pairSum (fun p hp => C.coefficient p * pairScalar C p hp) := by
  unfold mainDifference T Tprime Context.pairSum pairScalar
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum,
    mul_add, mul_sub]
  rw [Finset.sum_comm (s := dyadicScales C), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hv : C.ValidPair p
  · simp only [dif_pos hv, pairBlock, mul_sub, Finset.mul_sum]
  · simp [hv]

end MainBoundary

theorem bilinear_main_boundary_identity (C : Context Q)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hK : 1 ≤ C.K) :
    MainBoundary.mainDifference C =
      Sieve.MainBoundary.cancelledMainTerms Q c C.W C.kappa
        C.M C.N C.K C.d C.g C.lam := by
  rw [MainBoundary.mainDifference_pairSum]
  unfold Context.pairSum Context.pairs
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  unfold Sieve.MainBoundary.cancelledMainTerms
  rw [← MainBoundary.columns_eq C]
  have hmass : C.mass = ((∫ t in Set.Ioi (0 : ℝ), C.W (t ^ 2)) : ℂ) := by
    rfl
  rw [← hmass]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hp : C.ValidPair (u,v)
  · have hcond := (MainBoundary.validPair_iff C u v hu hv).mp hp
    simp only [dif_pos hp, if_pos hp, if_pos hcond]
    rw [MainBoundary.pair_scalar_boundary C hM hK _ hp,
      ← MainBoundary.cutoff_pair_boundary C hK _ hp]
    have hdensity : Vendor.CutoffDifference.density
        (Sieve.MainBoundary.idealSize F) (c * u * v) = sigma4Rho (c * u * v) := by
      simp [Vendor.CutoffDifference.density, Sieve.MainBoundary.idealSize,
        sigma4Rho, badPrimes, UniqueFactorizationMonoid.factors_eq_normalizedFactors]
    rw [hdensity]
    unfold Context.coefficient
    ring
  · have hcond : ¬ (u ⊔ v = ⊤ ∧ u * v ≠ ⊤) :=
      fun h => hp ((MainBoundary.validPair_iff C u v hu hv).mpr h)
    simp [hp, hcond]

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

end

end
