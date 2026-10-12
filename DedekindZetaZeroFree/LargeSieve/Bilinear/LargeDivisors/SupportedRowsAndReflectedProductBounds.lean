module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.DualDyadicRectangles
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.PrimitivePairPhaseSeparation
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Divisors.CoreEnergyAndPairMasks
public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.ReflectedCoreRowPrefix

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

theorem reflected_weighted_sum_le (C : Context Q) (B : ℝ) (unit : Bool)
    (hunit : unit = true → B = 1) (hB : 1 ≤ B)
    (g : Ideal (𝓞 F) → ℝ) (hg : ∀ a, 0 ≤ g a) :
    (∑ a ∈ C.reflectedRows B unit, Real.sqrt (B / norm a) * g a) ≤
      ∑ t ∈ squarefreeBadPool c, ∑ r ∈ C.reflectedCoreRows B unit, g (t * r) := by
  have hweight : ∀ a ∈ C.reflectedRows B unit, Real.sqrt (B / norm a) ≤ 1 := by
    intro a ha
    obtain ⟨⟨t, r⟩, htr, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hprod, hmask⟩ := Finset.mem_filter.mp htr
    have hr := (Finset.mem_product.mp hprod).2
    have ht0 : t ≠ ⊥ := by
      intro ht0
      exact hmask.2.2 (by simp [ht0])
    have htn : 1 ≤ norm t := by
      dsimp [norm]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ht0)
    have hrn : B ≤ norm r := by
      cases unit with
      | false =>
        exact ((Sieve.mem_paperShell F c B r).mp (Finset.mem_filter.mp hr).1).2.2.1.le
      | true =>
        have heq : r = ⊤ := Finset.mem_singleton.mp (Finset.mem_filter.mp hr).1
        rw [heq, hunit rfl]
        simp [norm]
    have han : B ≤ norm (t * r) := by
      have hnorm : norm (t * r) = norm t * norm r := by simp [norm, map_mul]
      rw [hnorm]
      exact hrn.trans (le_mul_of_one_le_left (by dsimp [norm]; positivity) htn)
    apply Real.sqrt_le_one.mpr
    exact (div_le_one (lt_of_lt_of_le zero_lt_one (hB.trans han))).mpr han
  calc
    _ ≤ ∑ a ∈ C.reflectedRows B unit, g a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_of_le_one_left (hg a) (hweight a ha)
    _ ≤ ∑ tr ∈ C.reflectedRowIndices B unit, g (tr.1 * tr.2) :=
      Finset.sum_image_le_of_nonneg (fun a _ => hg a)
    _ ≤ ∑ tr ∈ (squarefreeBadPool c) ×ˢ C.reflectedCoreRows B unit,
        g (tr.1 * tr.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun tr _ _ => hg _)
    _ = _ := Finset.sum_product _ _ _

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorEnergy (C : Context Q) (f : Ideal (𝓞 F)) : ℝ :=
  ∑ u ∈ C.columns,
    if f ∣ u then
      (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
        ‖C.lam (C.d * u)‖ ^ 2
    else 0

def rowDivisorBlock (C : Context Q) (e f₁ f₂ a : Ideal (𝓞 F)) : ℂ :=
  C.pairSum fun p hp =>
    if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
      C.coefficient p * C.primitive p hp e * C.primitive p hp a
    else 0

theorem chosen_primitive_on_core (C : Context Q)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : Context.ValidPair C p)
    (r : Ideal (𝓞 F)) (hrc : r ⊔ c = ⊤) :
    C.primitive p hp r = (Q.χ p.1) r * star ((Q.χ p.2) r) := by
  have hnorm := DedekindZetaZeroFree.LargeSieve.algebra_normalized_reciprocity F c Q C.D.bad
    C.D.bad_ne_bot C.D.original_dvd_bad
    (fun a ha hac => ⟨C.D.index_dvd_conductor a ha hac,
      C.D.conductor_dvd_index_bad a ha hac⟩)
  have huc : p.1 ⊔ C.D.bad = ⊤ := by simpa only [C.core] using hp.huc
  have hvc : p.2 ⊔ C.D.bad = ⊤ := by simpa only [C.core] using hp.hvc
  obtain ⟨φ, -, hφ⟩ := hnorm.2.2 p.1 p.2 hp.hu huc hp.hv hvc hp.huv
    hp.hquotientClass
  have hmod : p.1 * p.2 ≠ ⊥ := mul_ne_zero hp.hu0 hp.hv0
  have hq : c * (Q.cond p.1 * Q.cond p.2) ≠ ⊥ := by
    exact mul_ne_zero C.D.original_ne_bot
      (mul_ne_zero (Q.primitive p.1 hp.hu hp.huc).1
        (Q.primitive p.2 hp.hv hp.hvc).1)
  have heq : ∀ I, C.primitive p hp I = φ I := by
    apply DedekindZetaZeroFree.LargeSieve.RayComparison.away_uniqueness hmod hq
    intro I _ hI
    have hcop : I ⊔ p.1 * p.2 = ⊤ ∧ I ⊔ c = ⊤ ∧
        I ⊔ (Q.cond p.1 * Q.cond p.2) = ⊤ := by
      simpa only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff,
        and_assoc] using hI
    rw [(C.primitive_spec p hp).2.1 I hcop.2.2,
      hφ I (by simpa only [C.core] using hcop.2.1),
      DedekindZetaZeroFree.LargeSieve.quadraticFamily_conj Q hp.hv hp.hvc I]
  rw [heq r, hφ r (by simpa only [C.core] using hrc)]
  change _ = (Q.χ p.1) r * starRingEnd ℂ ((Q.χ p.2) r)
  rw [DedekindZetaZeroFree.LargeSieve.quadraticFamily_conj Q hp.hv hp.hvc r]

theorem chosen_primitive_phase_core (C : Context Q) :
    ∃ phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ,
      (∀ u ∈ C.columns, ∀ z, ‖phase u z‖ ≤ 1) ∧
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p,
      ∀ z, z ≠ ⊥ → (∀ u ∈ C.columns, z ⊔ u = ⊤) →
      ∀ r, r ⊔ c = ⊤ →
        C.primitive p hp z * C.primitive p hp r =
          (phase p.1 z * (Q.χ p.1) r) *
            star (phase p.2 z * (Q.χ p.2) r) := by
  have hcols : ∀ u ∈ C.columns, Squarefree u ∧ u ⊔ c = ⊤ := by
    intro u hu
    have h := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1
    exact ⟨h.1, h.2.1⟩
  have hclass : ∀ u ∈ C.columns, ∀ v ∈ C.columns, Q.cls u = Q.cls v := by
    intro u hu v hv
    letI := Q.instGroup
    have hum := (Finset.mem_filter.mp hu).2.2
    have hvm := (Finset.mem_filter.mp hv).2.2
    have hh : Q.cls (C.d * u) = Q.cls (C.d * v) := hum.trans hvm.symm
    rw [Q.cls_mul C.d u C.hdc (hcols u hu).2,
      Q.cls_mul C.d v C.hdc (hcols v hv).2] at hh
    exact mul_left_cancel hh
  obtain ⟨phase, hphase, hsplit⟩ := PrimitivePhases.primitive_pair_phase_separation Q
    C.D.original_ne_bot C.columns hcols hclass
  refine ⟨phase, hphase, ?_⟩
  intro p hpairs hp z hz hzc r hrc
  have hpcols := Finset.mem_product.mp (Finset.mem_filter.mp hpairs).1
  rw [hsplit p.1 hpcols.1 p.2 hpcols.2 hp.huv (C.primitive p hp)
    (C.primitive_spec p hp).2.1 z hz hzc, chosen_primitive_on_core C p hp r hrc,
    star_mul]
  ring

theorem mobius_divisor_coprime_columns (C : Context Q)
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors) :
    e ≠ ⊥ ∧ ∀ u ∈ C.columns, e ⊔ u = ⊤ := by
  have hcd : c * C.d ≠ ⊥ := mul_ne_zero C.D.original_ne_bot C.hd0
  have hrad : (c * C.d).radical ≠ ⊥ := by
    intro hh
    exact hcd (bot_unique (hh ▸ Ideal.le_radical))
  have hediv : e ∣ c * C.d := by
    exact Ideal.dvd_iff_le.mpr (le_trans Ideal.le_radical
      (Ideal.dvd_iff_le.mp ((mem_idealDivisors hrad).mp he)))
  refine ⟨ne_bot_of_mem_idealDivisors he, ?_⟩
  intro u hu
  have h := (Sieve.mem_idealAdmissibleFinset _ _ _ _).mp (Finset.mem_filter.mp hu).1
  have hdu : Squarefree (C.d * u) :=
    ((Sieve.mem_paperShell _ _ _ _).mp (Finset.mem_filter.mp hu).2.1).1
  have hrel : IsRelPrime C.d u := (squarefree_mul_iff.mp hdu).1
  have hdcoprime : C.d ⊔ u = ⊤ := by
    rw [← Ideal.gcd_eq_sup]
    exact Ideal.isUnit_iff.mp (gcd_isUnit_iff_isRelPrime.mpr hrel)
  have hcu : c ⊔ u = ⊤ := by simpa only [sup_comm] using h.2.1
  have hmult : c * C.d ⊔ u = ⊤ :=
    ((Ideal.isCoprime_iff_sup_eq.mpr hcu).mul_left
      (Ideal.isCoprime_iff_sup_eq.mpr hdcoprime)).sup_eq
  apply top_unique
  rw [← hmult]
  exact sup_le_sup_right (Ideal.dvd_iff_le.mp hediv) u

theorem finite_coprime_sum_bound
    (R U V : Finset (Ideal (𝓞 F)))
    (hU : ∀ u ∈ U, u ≠ ⊥) (hV : ∀ v ∈ V, v ≠ ⊥)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUA : ∀ z : Ideal (𝓞 F) → ℂ, (∑ r ∈ R, ‖∑ u ∈ U, z u * (Q.χ u) r‖^2) ≤ A * ∑ u ∈ U, ‖z u‖^2)
    (hVB : ∀ z : Ideal (𝓞 F) → ℂ, (∑ r ∈ R, ‖∑ v ∈ V, z v * (Q.χ v) r‖^2) ≤ B * ∑ v ∈ V, ‖z v‖^2)
    (x y : Ideal (𝓞 F) → ℂ) :
    (∑ r ∈ R, ‖∑ u ∈ U, ∑ v ∈ V, if u ⊔ v = ⊤ then
      x u * star (y v) * (Q.χ u) r * star ((Q.χ v) r) else 0‖) ≤
      Real.sqrt (A*B) * Real.sqrt
        ((∑ u ∈ U, (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors u).toFinset.card * ‖x u‖^2) *
         (∑ v ∈ V, (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors v).toFinset.card * ‖y v‖^2)) := by
  have h := Sieve.DivisorSeparation.rectangle_operator_bound Q
    {⊤} {⊤} R U V hU hV A B hA hB
    (by intro d hd z; have hd' : d = ⊤ := Finset.mem_singleton.mp hd; subst d; simpa using hUA z)
    (by intro d hd z; have hd' : d = ⊤ := Finset.mem_singleton.mp hd; subst d; simpa using hVB z) x y
  simp only [Sieve.DivisorSeparation.idealDivisorRectangle, Finset.sum_singleton,
    Finset.card_singleton, Nat.cast_one, one_mul] at h
  have htop : ∀ u : Ideal (𝓞 F), (⊤ : Ideal (𝓞 F)) ∣ u := fun u =>
    by simpa only [← Ideal.one_eq_top] using one_dvd u
  have hfilter : ∀ u : Ideal (𝓞 F), ({⊤} : Finset (Ideal (𝓞 F))).filter (fun d => d ∣ u) = {⊤} := by
    intro u; apply Finset.filter_eq_self.mpr
    intro d hd; rw [Finset.mem_singleton.mp hd]; exact htop u
  simp only [htop, and_true, hfilter, Finset.card_singleton,
    Nat.cast_one, mul_one, starRingEnd_apply] at h
  rw [mul_assoc (A*B)] at h
  have hs := Real.le_sqrt_of_sq_le h
  simpa only [Real.sqrt_mul (mul_nonneg hA hB)] using hs

theorem supported_factor_coprime_columns (C : Context Q)
    (t : Ideal (𝓞 F)) (ht : t ∈ squarefreeBadPool c) :
    t ≠ ⊥ ∧ ∀ u ∈ C.columns, t ⊔ u = ⊤ := by
  obtain ⟨ht0, -, hsupp⟩ := (mem_squarefreeBadPool C.D.original_ne_bot).mp ht
  refine ⟨ht0, ?_⟩
  intro u hu
  have huc := ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
    (Finset.mem_filter.mp hu).1).2.1
  by_contra hne
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (t ⊔ u) hne
  have hpt : p ∣ t := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
  have hp0 : p ≠ ⊥ := by
    intro heq
    exact ht0 (eq_bot_iff.mpr (heq ▸ Ideal.dvd_iff_le.mp hpt))
  have hpc : p ∣ c := hsupp p (Ideal.prime_of_isPrime hp0 hp.isPrime) hpt
  exact hp.ne_top (top_unique (huc ▸ sup_le
    (le_trans le_sup_right hle) (Ideal.dvd_iff_le.mp hpc)))

theorem supported_primitive_phase_core (C : Context Q) :
    ∃ phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ,
      (∀ u ∈ C.columns, ∀ z, ‖phase u z‖ ≤ 1) ∧
      ∀ e ∈ C.mobiusDivisors, ∀ t ∈ squarefreeBadPool c,
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p,
      ∀ r, r ⊔ c = ⊤ →
        C.primitive p hp e * C.primitive p hp (t * r) =
          (phase p.1 (e * t) * (Q.χ p.1) r) *
            star (phase p.2 (e * t) * (Q.χ p.2) r) := by
  obtain ⟨phase, hphase, hsplit⟩ := chosen_primitive_phase_core C
  refine ⟨phase, hphase, ?_⟩
  intro e he t ht p hpairs hp r hrc
  obtain ⟨he0, hecols⟩ := mobius_divisor_coprime_columns C e he
  obtain ⟨ht0, htcols⟩ := supported_factor_coprime_columns C t ht
  have hetcols : ∀ u ∈ C.columns, e * t ⊔ u = ⊤ := by
    intro u hu
    exact ((Ideal.isCoprime_iff_sup_eq.mpr (hecols u hu)).mul_left
      (Ideal.isCoprime_iff_sup_eq.mpr (htcols u hu))).sup_eq
  have hh := hsplit p hpairs hp (e * t) (mul_ne_zero he0 ht0) hetcols r hrc
  rw [(C.primitive p hp).map_mul' e t] at hh
  rw [(C.primitive p hp).map_mul' t r]
  simpa only [mul_assoc] using hh

theorem rowDivisorBlock_eq_phase_sum (C : Context Q)
    (phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hphase : ∀ e ∈ C.mobiusDivisors, ∀ t ∈ squarefreeBadPool c,
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p,
      ∀ r, r ⊔ c = ⊤ → C.primitive p hp e * C.primitive p hp (t*r) =
        (phase p.1 (e*t) * (Q.χ p.1) r) * star (phase p.2 (e*t) * (Q.χ p.2) r))
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
    (t : Ideal (𝓞 F)) (ht : t ∈ squarefreeBadPool c)
    (f₁ f₂ r : Ideal (𝓞 F)) (hrc : r ⊔ c = ⊤) :
    rowDivisorBlock C e f₁ f₂ (t*r) =
      ∑ p ∈ C.pairs, if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
        (C.lam (C.d*p.1) * phase p.1 (e*t)) *
          star (C.lam (C.d*p.2) * phase p.2 (e*t)) *
          (Q.χ p.1) r * star ((Q.χ p.2) r)
      else 0 := by
  unfold rowDivisorBlock Context.pairSum
  apply Finset.sum_congr rfl
  intro p hp
  have hpvalid : Context.ValidPair C p := (Finset.mem_filter.mp hp).2
  rw [dif_pos hpvalid]
  dsimp only
  split_ifs with h
  · rw [mul_assoc, hphase e he t ht p hp hpvalid r hrc]
    simp only [Context.coefficient, star_mul]
    ring
  · rfl

theorem supported_divisible_pair_bound
    (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∃ H : ℝ, 0 < H ∧
      ∀ (C : Context Q), C.D = D →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
      ∀ e ∈ C.mobiusDivisors,
      ∀ (P : ℝ × ℝ), P ∈ admissibleRectangles C B →
      ∀ f₁ f₂ : Ideal (𝓞 F),
        ErrorRectangles.InBin P.1 f₁ → ErrorRectangles.InBin P.2 f₂ →
        (∑ a ∈ C.reflectedRows B unit,
            Real.sqrt (B / norm a) * ‖rowDivisorBlock C e f₁ f₂ a‖) ≤
          H * Real.sqrt
            (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
             ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
            Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) := by
  obtain ⟨A, hA, hcore⟩ := SupportedRows.core_divisible_pair_bound D
  let n : ℝ := (squarefreeBadPool c).card
  refine ⟨(n + 1) * A, mul_pos (by dsimp [n]; positivity) hA, ?_⟩
  intro C hCD B unit hunit hM hN hB hBK hKM hn hnN e he P hP f₁ f₂ hf₁ hf₂
  obtain ⟨phase, hphase, hsplit⟩ := supported_primitive_phase_core C
  have hends := ErrorRectangles.rectangle_endpoints C P (Finset.mem_filter.mp hP).1
  have hPf₁ : P.1 ≤ norm f₁ := by
    have hh := hf₁.2.1
    split_ifs at hh with hp
    · simpa only [hp] using hh
    · exact hh.le
  have hPf₂ : P.2 ≤ norm f₂ := by
    have hh := hf₂.2.1
    split_ifs at hh with hp
    · simpa only [hp] using hh
    · exact hh.le
  have hrows := SupportedRows.reflected_core_rows_subset C B unit hunit hB
  have hlocal : ∀ t ∈ squarefreeBadPool c,
      (∑ r ∈ C.reflectedCoreRows B unit, ‖rowDivisorBlock C e f₁ f₂ (t * r)‖) ≤
        A * Real.sqrt
          (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
           ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
          Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) := by
    intro t ht
    let x : Ideal (𝓞 F) → ℂ := fun u => C.lam (C.d * u) * phase u (e * t)
    have hx : ∀ u ∈ C.columns, ‖x u‖ ≤ ‖C.lam (C.d * u)‖ := by
      intro u hu
      dsimp [x]
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hphase u hu (e * t))
    have hh := hcore C hCD hN B P.1 P.2 hB hends.1 hends.2.1 f₁ f₂
      hf₁.1 hf₂.1 hPf₁ hPf₂ (C.reflectedCoreRows B unit) hrows x x hx hx
    have heq : ∀ r ∈ C.reflectedCoreRows B unit,
        rowDivisorBlock C e f₁ f₂ (t * r) =
          SupportedRows.coreBlock C f₁ f₂ x x r := by
      intro r hr
      have hrc := ((Sieve.mem_idealAdmissibleFinset F c (2 * B) r).mp (hrows hr)).2.1
      simpa only [SupportedRows.coreBlock, x] using
        rowDivisorBlock_eq_phase_sum C phase hsplit e he t ht f₁ f₂ r hrc
    calc
      _ = ∑ r ∈ C.reflectedCoreRows B unit,
          ‖SupportedRows.coreBlock C f₁ f₂ x x r‖ := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [heq r hr]
      _ ≤ _ := by simpa only [SupportedRows.energy, divisorEnergy] using hh
  calc
    _ ≤ ∑ t ∈ squarefreeBadPool c, ∑ r ∈ C.reflectedCoreRows B unit,
        ‖rowDivisorBlock C e f₁ f₂ (t * r)‖ :=
      SupportedRows.reflected_weighted_sum_le C B unit hunit hB
        (fun a => ‖rowDivisorBlock C e f₁ f₂ a‖) (fun a => norm_nonneg _)
    _ ≤ ∑ t ∈ squarefreeBadPool c,
        A * Real.sqrt
          (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
           ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
          Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) :=
      Finset.sum_le_sum hlocal
    _ = n * A * Real.sqrt
          (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
           ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
          Real.sqrt (divisorEnergy C f₁ * divisorEnergy C f₂) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      dsimp [n]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith : n ≤ n + 1) hA.le

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

end

end
