module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdeals.EulerWeights

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

def CRTLocalHigherUnits (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (u : (v.adicCompletion F)ˣ) : Prop :=
  ∃ a : (v.adicCompletionIntegers F)ˣ,
    Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom a = u ∧
      (a : v.adicCompletionIntegers F) - 1 ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ k

theorem CRTLocalHigherUnits_zero_iff (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    CRTLocalHigherUnits F v 0 u ↔
      ∃ a : (v.adicCompletionIntegers F)ˣ,
        Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom a = u := by
  simp [CRTLocalHigherUnits]

def CRTIdealSupport (m : Ideal (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (idealPrimeSupport m).preimage
    HeightOneSpectrum.asIdeal (fun _ _ _ _ h => HeightOneSpectrum.ext h)

def CRTIntegralLocalUnit (v : HeightOneSpectrum (𝓞 F)) (α : 𝓞 F) (hα : α ≠ 0) :
    (v.adicCompletion F)ˣ :=
  Units.map (NumberField.FinitePlace.embedding v).toMonoidHom
    (Units.mk0 (α : F) (by exact_mod_cast hα))

open Valuation UniqueFactorizationMonoid

theorem CRT_completed_power_mem_iff (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (n : ℕ) :
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n ↔ a ∈ v.asIdeal ^ n := by
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  let π := algebraMap (𝓞 F) (v.adicCompletionIntegers F) p
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1) := by
    exact (v.valuedAdicCompletion_eq_valuation p).trans ((v.valuation_of_algebraMap p).trans hp)
  have hπunif : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π : v.adicCompletion F) := by
    rw [Valuation.IsUniformizer.iff, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective (v.valuedAdicCompletion_surjective F)]
    exact hπval
  have hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπunif.is_generator
  have heq := (HeightOneSpectrum.adicCompletionIntegers.integers F v).maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow hπirr n
  change algebraMap (𝓞 F) (v.adicCompletionIntegers F) a ∈ (↑(IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n) : Set _) ↔ _
  rw [heq]
  change Valued.v ((algebraMap (𝓞 F) (v.adicCompletion F)) a) ≤ Valued.v (π : v.adicCompletion F) ^ n ↔ _
  rw [hπval, ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  have hval : Valued.v ((algebraMap (𝓞 F) (v.adicCompletion F)) a) = v.intValuation a :=
    (v.valuedAdicCompletion_eq_valuation (K := F) a).trans (v.valuation_of_algebraMap (K := F) a)
  rw [hval]
  exact v.intValuation_le_pow_iff_mem a n

theorem CRT_exists_smaller_exponent (m f : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hf : m < f) :
    ∃ v : ↥(CRTIdealSupport F m), idealPrimeExponent v.val.asIdeal f < idealPrimeExponent v.val.asIdeal m := by
  have hf0 : f ≠ ⊥ := ne_bot_of_le_ne_bot hm hf.le
  have hnot : ¬ normalizedFactors m ≤ normalizedFactors f := by
    intro h
    have hfm := Ideal.dvd_iff_le.mp ((dvd_iff_normalizedFactors_le_normalizedFactors hm hf0).mpr h)
    exact hf.not_ge hfm
  obtain ⟨p, hp⟩ : ∃ p, (normalizedFactors f).count p < (normalizedFactors m).count p := by
    simpa only [Multiset.le_iff_count, not_forall, not_le] using hnot
  have hpm : p ∈ normalizedFactors m := Multiset.count_pos.mp (by omega)
  have hprime := prime_of_normalized_factor p hpm
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
  have hv : v ∈ CRTIdealSupport F m := by
    simpa only [CRTIdealSupport, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hpm
  exact ⟨⟨v, hv⟩, hp⟩

private theorem CRT_power_criterion (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletionIntegers F) (n : ℕ) :
 b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n ↔
 Valued.v (b : v.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
 obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
 let π := algebraMap (𝓞 F) (v.adicCompletionIntegers F) p
 have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1) :=
  (v.valuedAdicCompletion_eq_valuation p).trans ((v.valuation_of_algebraMap p).trans hp)
 have hπunif : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π : v.adicCompletion F) := by
  rw [Valuation.IsUniformizer.iff, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective (v.valuedAdicCompletion_surjective F)]
  exact hπval
 have hπirr := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπunif.is_generator
 have heq := (HeightOneSpectrum.adicCompletionIntegers.integers F v).maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow hπirr n
 change b ∈ (↑(IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n) : Set _) ↔ _
 rw [heq]
 change Valued.v (b : v.adicCompletion F) ≤ Valued.v (π : v.adicCompletion F) ^ n ↔ _
 rw [hπval, ← WithZero.exp_nsmul]
 simp

theorem CRT_completed_residue_representative (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletionIntegers F) (n : ℕ) :
 ∃ a : 𝓞 F, algebraMap (𝓞 F) (v.adicCompletionIntegers F) a - b ∈
 IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n := by
 obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
 let z : v.adicCompletion F := algebraMap (𝓞 F) (v.adicCompletion F) p ^ n
 have hz : Valued.v z = WithZero.exp (-(n : ℤ)) := by
  dsimp [z]
  rw [map_pow]
  have hp' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) p) = WithZero.exp (-1) :=
   (v.valuedAdicCompletion_eq_valuation p).trans ((v.valuation_of_algebraMap p).trans hp)
  rw [hp', ← WithZero.exp_nsmul]
  simp
 have hopen : IsOpen {x : v.adicCompletion F | Valued.v (x - b) < Valued.v z} := by
  have hc : IsOpen {x : (v.valuation F).Completion | Valued.v (x - (b : v.adicCompletion F).toCompletion) < Valued.v z.toCompletion} := by
   simpa only [Valuation.restrict_lt_iff, Set.preimage_setOf_eq, Pi.sub_apply, id_eq] using
    (Valued.isOpen_ball ((v.valuation F).Completion) (Valued.v.restrict z.toCompletion)).preimage (continuous_id.sub continuous_const)
  exact hc.preimage (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v)
 obtain ⟨q, hq⟩ := (v.denseRange_algebraMap F).exists_mem_open hopen ⟨b, by simp [hz]⟩
 have hq' : Valued.v (algebraMap F (v.adicCompletion F) q - b) < WithZero.exp (-(n : ℤ)) := by simpa [hz] using hq
 have hn1 : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega
 have hqi : v.valuation F q ≤ 1 := by
  have hval : Valued.v (algebraMap F (v.adicCompletion F) q) = v.valuation F q := HeightOneSpectrum.adicCompletion.valued_coe F v q
  rw [← hval]
  have hb : Valued.v (b : v.adicCompletion F) ≤ 1 := b.2
  have heq : algebraMap F (v.adicCompletion F) q = (algebraMap F (v.adicCompletion F) q - b) + b := by ring
  rw [heq]
  exact (Valued.v.map_add _ _).trans (max_le (hq'.le.trans hn1) hb)
 obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hqi (Units.mk0 (WithZero.exp (-(n : ℤ))) (by simp))
 refine ⟨a, (CRT_power_criterion F v _ n).mpr ?_⟩
 have ha' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) q) < WithZero.exp (-(n : ℤ)) := by
  have heq : algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) q =
   algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a - q) := by
   rw [_root_.map_sub, ← IsScalarTower.algebraMap_apply]
  rw [heq]
  exact (HeightOneSpectrum.adicCompletion.valued_coe F v (algebraMap (𝓞 F) F a - q)).symm ▸ ha
 change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a - b) ≤ _
 have heq : algebraMap (𝓞 F) (v.adicCompletion F) a - b =
  (algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) q) +
  (algebraMap F (v.adicCompletion F) q - b) := by ring
 rw [heq]
 exact (Valued.v.map_add _ _).trans (max_le ha'.le hq'.le)

theorem CRT_congruent_isUnit (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : n ≠ 0)
 (a : v.adicCompletionIntegers F) (b : (v.adicCompletionIntegers F)ˣ)
 (hab : a - b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n) :
 IsUnit a := by
 by_contra ha
 have ha' : a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  simpa [IsLocalRing.mem_maximalIdeal] using ha
 have hd := Ideal.pow_le_self hn hab
 have hb : (b : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  simpa using (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).sub_mem ha' hd
 simpa [IsLocalRing.mem_maximalIdeal] using hb

theorem CRT_global_mem (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (a : 𝓞 F)
    (h : ∀ v ∈ CRTIdealSupport F I, a ∈ v.asIdeal ^ idealPrimeExponent v.asIdeal I) : a ∈ I := by
  have heq : I = (idealPrimeSupport I).inf (fun p => p ^ idealPrimeExponent p I) := by
    rw [IsDedekindDomain.inf_pow_eq_prod_of_prime]
    · symm
      exact (Finset.prod_multiset_count _).symm.trans (Ideal.prod_normalizedFactors_eq_self hI)
    · intro p hp
      exact prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
    · intro p _ q _ hpq
      exact hpq
  rw [heq]
  rw [Finset.inf_eq_iInf]
  simp only [Submodule.mem_iInf]
  intro p hp
  have hprime := prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
  apply h v
  simpa only [CRTIdealSupport, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using (Multiset.mem_toFinset.mp hp)

theorem CRT_global_coprime (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (a : 𝓞 F)
    (h : ∀ v ∈ CRTIdealSupport F I, a ∉ v.asIdeal) : Ideal.span {a} ⊔ I = ⊤ := by
  by_contra hne
  obtain ⟨v, hv⟩ := (HeightOneSpectrum.ideal_ne_top_iff_exists (NumberField.RingOfIntegers.not_isField F) _).mp hne
  have hvI : I ≤ v.asIdeal := le_sup_right.trans hv
  have hvm : v ∈ CRTIdealSupport F I := by
    have hd : v.asIdeal ∣ I := Ideal.dvd_iff_le.mpr hvI
    have hp := (dvd_iff_normalizedFactors_le_normalizedFactors v.ne_bot hI).mp hd
    have hmem : v.asIdeal ∈ normalizedFactors I := (Multiset.subset_of_le hp) (by simp [normalizedFactors_irreducible v.irreducible, normalize_eq])
    simpa only [CRTIdealSupport, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using hmem
  exact h v hvm ((le_sup_left.trans hv) (Ideal.subset_span (by simp)))

theorem CRT_character_eq_of_congruence (v : HeightOneSpectrum (𝓞 F)) (e : ℕ)
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u, CRTLocalHigherUnits F v e u → χ u = 1)
    (a b : (v.adicCompletionIntegers F)ˣ)
    (hab : (a : v.adicCompletionIntegers F) - b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ e) :
    χ (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom a) =
      χ (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom b) := by
  have hcong : ((a * b⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ e := by
    have heq : ((a * b⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) - 1 =
      ((a : v.adicCompletionIntegers F) - b) * ↑(b⁻¹) := by simp [sub_mul]
    rw [heq]
    exact Ideal.mul_mem_right _ _ hab
  have hh := hχ _ ⟨a * b⁻¹, rfl, hcong⟩
  simpa only [map_mul, _root_.map_inv, mul_inv_eq_one] using hh

private theorem CRT_global_lift (m : Ideal (𝓞 F))
 (b : (v : ↥(CRTIdealSupport F m)) → (v.val.adicCompletionIntegers F)ˣ) :
 ∃ a : 𝓞 F, ∀ v : ↥(CRTIdealSupport F m),
 algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) a - b v ∈
 IsLocalRing.maximalIdeal (v.val.adicCompletionIntegers F) ^ idealPrimeExponent v.val.asIdeal m := by
 choose x hx using fun v : ↥(CRTIdealSupport F m) =>
  CRT_completed_residue_representative F v.val (b v) (idealPrimeExponent v.val.asIdeal m)
 obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
  (s := CRTIdealSupport F m) HeightOneSpectrum.asIdeal
  (fun v => idealPrimeExponent v.asIdeal m) (fun v _ => v.prime)
  (fun v _ w _ h => fun heq => h (HeightOneSpectrum.ext heq)) x
 refine ⟨a, fun v => ?_⟩
 have hc := (CRT_completed_power_mem_iff F v.val (a - x v) _).mpr (ha v.val v.property)
 have hd := (IsLocalRing.maximalIdeal (v.val.adicCompletionIntegers F) ^ idealPrimeExponent v.val.asIdeal m).add_mem hc (hx v)
 simpa only [_root_.map_sub, sub_add_sub_cancel] using hd

private theorem CRT_global_nonmembership (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F)
 (hu : IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a)) : a ∉ v.asIdeal := by
 intro ha
 have hm := (CRT_completed_power_mem_iff F v a 1).mpr (by simpa using ha)
 have hm' : algebraMap (𝓞 F) (v.adicCompletionIntegers F) a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by simpa using hm
 simpa [IsLocalRing.mem_maximalIdeal, hu] using hm'

private theorem CRT_exponent_le (m f : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hf : m ≤ f) :
 ∀ v : HeightOneSpectrum (𝓞 F), idealPrimeExponent v.asIdeal f ≤ idealPrimeExponent v.asIdeal m := by
 have hf0 : f ≠ ⊥ := ne_bot_of_le_ne_bot hm hf
 have hn := (dvd_iff_normalizedFactors_le_normalizedFactors hf0 hm).mp (Ideal.dvd_iff_le.mpr hf)
 intro v
 exact (Multiset.le_iff_count.mp hn) _

private theorem CRT_support_subset (m f : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hf : m ≤ f) :
 CRTIdealSupport F f ⊆ CRTIdealSupport F m := by
 intro v hv
 have hf0 : f ≠ ⊥ := ne_bot_of_le_ne_bot hm hf
 have hn := (dvd_iff_normalizedFactors_le_normalizedFactors hf0 hm).mp (Ideal.dvd_iff_le.mpr hf)
 simp only [CRTIdealSupport, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] at hv ⊢
 exact Multiset.subset_of_le hn hv

theorem primitive_of_exact_local_exponents
    (htc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : RayClassCharacter F m)
    (lambda : (v : ↥(CRTIdealSupport F m)) → (v.val.adicCompletion F)ˣ →* ℂˣ)
    (hcontinuous : ∀ v, Continuous (lambda v))
    (htrivial : ∀ v, ∀ u, CRTLocalHigherUnits F v.val (idealPrimeExponent v.val.asIdeal m) u →
      lambda v u = 1)
    (hexact : ∀ v, ∀ k < idealPrimeExponent v.val.asIdeal m,
      ∃ u, CRTLocalHigherUnits F v.val k u ∧ lambda v u ≠ 1)
    (hprincipal : ∀ (α : 𝓞 F) (hα : α ≠ 0), Ideal.span {α} ⊔ m = ⊤ →
      η (Ideal.span {α}) =
        (((∏ v : ↥(CRTIdealSupport F m),
          lambda v (CRTIntegralLocalUnit F v.val α hα)) : ℂˣ) : ℂ)⁻¹) :
    η.IsPrimitive := by
  letI := htc
  intro f hf
  obtain ⟨v₀, hv₀⟩ := CRT_exists_smaller_exponent F m f hm hf
  obtain ⟨u, ⟨c, hcu, hc⟩, hu⟩ := hexact v₀ _ hv₀
  let b : (v : ↥(CRTIdealSupport F m)) → (v.val.adicCompletionIntegers F)ˣ := fun v => by
    by_cases h : v = v₀
    · subst v; exact c
    · exact 1
  have hb₀ : b v₀ = c := by simp [b]
  have hbother : ∀ v, v ≠ v₀ → b v = 1 := by
    intro v hv; simp [b, hv]
  have hbcong : ∀ v : ↥(CRTIdealSupport F m),
      (b v : v.val.adicCompletionIntegers F) - 1 ∈
        IsLocalRing.maximalIdeal (v.val.adicCompletionIntegers F) ^ idealPrimeExponent v.val.asIdeal f := by
    intro v
    by_cases hv : v = v₀
    · subst v; simpa only [hb₀] using hc
    · simp [hbother v hv]
  obtain ⟨a, ha⟩ := CRT_global_lift F m b
  have he : ∀ v : ↥(CRTIdealSupport F m), idealPrimeExponent v.val.asIdeal m ≠ 0 := by
    intro v
    apply Nat.ne_of_gt
    apply Multiset.count_pos.mpr
    simpa only [CRTIdealSupport, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using v.property
  have hai : ∀ v : ↥(CRTIdealSupport F m),
      IsUnit (algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) a) := by
    intro v
    exact CRT_congruent_isUnit F v.val _ (he v) _ (b v) (ha v)
  have ha0 : a ≠ 0 := by
    intro hz
    have h := (hai v₀).ne_zero
    simp [hz] at h
  have haf : a - 1 ∈ f := by
    apply CRT_global_mem F f (ne_bot_of_le_ne_bot hm hf.le)
    intro v hv
    let w : ↥(CRTIdealSupport F m) := ⟨v, CRT_support_subset F m f hm hf.le hv⟩
    apply (CRT_completed_power_mem_iff F v (a - 1) _).mp
    have h1 := Ideal.pow_le_pow_right (CRT_exponent_le F m f hm hf.le v) (ha w)
    have h2 := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ idealPrimeExponent v.asIdeal f).add_mem h1 (hbcong w)
    simpa only [_root_.map_sub, map_one, sub_add_sub_cancel] using h2
  have hcop : Ideal.span {a} ⊔ m = ⊤ := by
    apply CRT_global_coprime F m hm a
    intro v hv
    exact CRT_global_nonmembership F v a (hai ⟨v, hv⟩)
  let A : (v : ↥(CRTIdealSupport F m)) → (v.val.adicCompletionIntegers F)ˣ := fun v => (hai v).unit
  have hA : ∀ v, (A v : v.val.adicCompletionIntegers F) = algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) a := by
    intro v; exact IsUnit.unit_spec (hai v)
  have hmap : ∀ v, Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom (A v) = CRTIntegralLocalUnit F v.val a ha0 := by
    intro v
    apply Units.ext
    change ((A v : v.val.adicCompletionIntegers F) : v.val.adicCompletion F) = _
    rw [hA]
    rfl
  have hval : ∀ v, lambda v (CRTIntegralLocalUnit F v.val a ha0) =
      lambda v (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom (b v)) := by
    intro v
    rw [← hmap]
    apply CRT_character_eq_of_congruence F v.val _ (lambda v) (htrivial v)
    simpa only [hA] using ha v
  have hprod : (∏ v : ↥(CRTIdealSupport F m), lambda v (CRTIntegralLocalUnit F v.val a ha0)) = lambda v₀ u := by
    rw [Finset.prod_eq_single v₀]
    · rw [hval, hb₀, hcu]
    · intro v _ hv
      rw [hval, hbother v hv, map_one, map_one]
    · simp
  refine ⟨a, ha0, haf, ?_, hcop, ?_⟩
  · intro φ
    exfalso
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    simp [NumberField.ComplexEmbedding.conjugate]
  · rw [hprincipal a ha0 hcop, hprod]
    intro h
    apply hu
    apply Units.ext
    simpa only [inv_eq_one, Units.val_one] using h

end
end DedekindZetaZeroFree
