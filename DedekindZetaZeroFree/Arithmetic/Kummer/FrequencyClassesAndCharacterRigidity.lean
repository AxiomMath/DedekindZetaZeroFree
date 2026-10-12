module

public import DedekindZetaZeroFree.Arithmetic.Kummer.CofiniteResiduePowerDetection
public import DedekindZetaZeroFree.Arithmetic.Kummer.Sextic.ArithmeticArtinCharacter
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex

@[expose] public section

section

open scoped NumberField Classical
open IsDedekindDomain
namespace DedekindZetaZeroFree.Detector.FrequencyCharacterRigidity
variable {F : Type} [Field F] [NumberField F]

private theorem character_one_of_factors (m : Ideal (𝓞 F)) (χ : RayClassCharacter F m)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ I → χ v.asIdeal = 1) : χ I = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hI rfl).elim
  | h₂ I hu =>
    have he : I = ⊤ := by simpa using (isUnit_iff_eq_one.mp hu)
    rw [he, χ.map_top']
  | h₃ I p hI0 hp ih =>
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    rw [χ.map_mul', h v (dvd_mul_right p I), ih hI0 (fun w hw =>
      h w (dvd_mul_of_dvd_right hw p)), one_mul]

theorem prime_witness (m : Ideal (𝓞 F)) (p : HeightOneSpectrum (𝓞 F))
    (hp : ¬ m ≤ p.asIdeal) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ a - 1 ∈ m ∧ a ∈ p.asIdeal ∧ a ∉ p.asIdeal ^ 2 ∧
      ∀ v ∈ T, v ≠ p → ¬ m ≤ v.asIdeal → a ∉ v.asIdeal := by
  classical
  let B := (insert p T).filter (fun v => ¬ m ≤ v.asIdeal)
  have hpB : p ∈ B := by simp [B, hp]
  obtain ⟨b, hb, hb2⟩ := Ideal.exists_mem_pow_notMem_pow_succ p.asIdeal p.ne_bot
    p.isMaximal.ne_top 1
  simp only [pow_one] at hb
  let J : Option B → Ideal (𝓞 F) := fun i => match i with
    | none => m
    | some v => v.val.asIdeal ^ (if v.val = p then 2 else 1)
  let x : Option B → 𝓞 F := fun i => match i with
    | none => 1
    | some v => if v.val = p then b else 1
  have hpair : Pairwise (Function.onFun IsCoprime J) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some v =>
        have hv : ¬ m ≤ v.val.asIdeal := (Finset.mem_filter.mp v.property).2
        have hc : m ⊔ v.val.asIdeal = ⊤ := by
          rw [sup_comm]
          exact v.val.isMaximal.out.2 _
            (lt_of_le_of_ne le_sup_left (fun h => hv (h ▸ le_sup_right)))
        exact (Ideal.isCoprime_iff_sup_eq.mpr hc).pow_right
    | some v =>
      cases j with
      | none =>
        have hv : ¬ m ≤ v.val.asIdeal := (Finset.mem_filter.mp v.property).2
        have hc : v.val.asIdeal ⊔ m = ⊤ := v.val.isMaximal.out.2 _
          (lt_of_le_of_ne le_sup_left (fun h => hv (h ▸ le_sup_right)))
        exact (Ideal.isCoprime_iff_sup_eq.mpr hc).pow_left
      | some w =>
        apply HeightOneSpectrum.isCoprime_pow_of_ne
        intro he
        exact hij (congrArg some (Subtype.ext he))
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hpair x
  have ham : a - 1 ∈ m := ha none
  have hap : a - b ∈ p.asIdeal ^ 2 := by
    simpa [J, x] using ha (some ⟨p, hpB⟩)
  have ha2 : a ∉ p.asIdeal ^ 2 := by
    intro h
    apply hb2
    simpa only [sub_sub_cancel] using (p.asIdeal ^ 2).sub_mem h hap
  have ha0 : a ≠ 0 := by intro h; exact ha2 (h ▸ Submodule.zero_mem _)
  have ha1 : a ∈ p.asIdeal := by
    have hh := p.asIdeal.add_mem (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0) hap) hb
    simpa only [sub_add_cancel] using hh
  refine ⟨a, ha0, ham, ha1, ha2, ?_⟩
  intro v hv hne hm
  have hvB : v ∈ B := by simp [B, hv, hm]
  have hh : a - 1 ∈ v.asIdeal := by simpa [J, x, hne] using ha (some ⟨v, hvB⟩)
  intro hav
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    simpa only [sub_sub_cancel] using v.asIdeal.sub_mem hav hh
  exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem prime_values_one_of_cofinite [NumberField.IsTotallyComplex F]
    (m : Ideal (𝓞 F)) (χ : RayClassCharacter F m)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, χ v.asIdeal = 1)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal ⊔ m = ⊤) : χ p.asIdeal = 1 := by
  classical
  let T := (Filter.eventually_cofinite.mp h).toFinset
  have hpm : ¬ m ≤ p.asIdeal := by
    intro hh
    have he : p.asIdeal ⊔ m = p.asIdeal := sup_eq_left.mpr hh
    exact p.isMaximal.ne_top (he.symm.trans hp)
  obtain ⟨a, ha, ham, hap, hap2, haT⟩ := prime_witness m p hpm T
  have hpdiv : p.asIdeal ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr hap
  obtain ⟨I, hI⟩ := hpdiv
  have hI0 : I ≠ ⊥ := by
    intro hh
    rw [hh, Ideal.mul_bot] at hI
    exact ha (Ideal.span_singleton_eq_bot.mp hI)
  have hpI : ¬ p.asIdeal ∣ I := by
    intro hh
    apply hap2
    apply Ideal.dvd_span_singleton.mp
    rw [hI, pow_two]
    exact mul_dvd_mul_left p.asIdeal hh
  have hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ I → χ v.asIdeal = 1 := by
    intro v hv
    have hdiv : v.asIdeal ∣ Ideal.span {a} := hI ▸ dvd_mul_of_dvd_right hv p.asIdeal
    have hav : a ∈ v.asIdeal := Ideal.dvd_span_singleton.mp hdiv
    have hne : v ≠ p := by intro hh; subst v; exact hpI hv
    have hm : ¬ m ≤ v.asIdeal := by
      intro hh
      have hsub : a - 1 ∈ v.asIdeal := hh ham
      have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
        simpa only [sub_sub_cancel] using v.asIdeal.sub_mem hav hsub
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have hvT : v ∉ T := fun hh => haT v hh hne hm hav
    simpa [T] using hvT
  have hχI := character_one_of_factors m χ I hI0 hgood
  have hpos : ∀ φ : F →+* ℝ, 0 < φ (a : F) := by
    intro φ
    exfalso
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    simp [NumberField.ComplexEmbedding.conjugate]
  have he := χ.map_span' a ha ham hpos
  rw [hI, χ.map_mul', hχI, mul_one] at he
  exact he

theorem principal_of_cofinite_prime_values [NumberField.IsTotallyComplex F]
    (m : Ideal (𝓞 F)) (χ : RayClassCharacter F m)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, χ v.asIdeal = 1) :
    χ.IsPrincipal := by
  intro I hI hcop
  apply character_one_of_factors m χ I hI
  intro v hv
  apply prime_values_one_of_cofinite m χ h v
  apply top_le_iff.mp
  rw [← hcop]
  exact sup_le_sup_right (Ideal.dvd_iff_le.mp hv) m

end DedekindZetaZeroFree.Detector.FrequencyCharacterRigidity

end

section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector

noncomputable def frequencyGamma (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (S.unit F).map (powMonoidHom 6)

def frequencyEquivalent (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (x y : Fˣ) : Prop :=
  x / y ∈ frequencyGamma F S

def sixthPowerFreeFrequency (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (u : Fˣ) : Prop :=
  (u : F) ∈ S.integer F ∧
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∃ e : Fin 6, v.valuation F (u : F) = WithZero.exp (-(e.val : ℤ))

structure FrequencyRepresentatives (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) where
  carrier : Set Fˣ
  one_mem : (1 : Fˣ) ∈ carrier
  power_free : ∀ u ∈ carrier, sixthPowerFreeFrequency F S u
  represents : ∀ x : Fˣ, sixthPowerFreeFrequency F S x →
    ∃! u : carrier, frequencyEquivalent F S x u.val

theorem frequency_representatives_power_injective
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (U : FrequencyRepresentatives F S) (u v : U.carrier)
    (hPower : ∃ x : Fˣ, u.val / v.val = x ^ (6 : ℕ)) :
    u = v := by
  obtain ⟨x, hx⟩ := hPower
  have hxS : x ∈ S.unit F := by
    change ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w.valuation F (x : F) = 1
    intro w hw
    obtain ⟨a, ha⟩ := (U.power_free u.val u.property).2 w hw
    obtain ⟨b, hb⟩ := (U.power_free v.val v.property).2 w hw
    have heq := congrArg (fun y : Fˣ => w.valuation F (y : F)) hx
    simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      map_div₀, map_pow, ha, hb] at heq
    have hlog := congrArg WithZero.log heq
    rw [WithZero.log_div WithZero.exp_ne_zero WithZero.exp_ne_zero,
      WithZero.log_exp, WithZero.log_exp, WithZero.log_pow] at hlog
    have hz : WithZero.log (w.valuation F (x : F)) = 0 := by
      simp only [nsmul_eq_mul] at hlog
      have ha' := a.isLt
      have hb' := b.isLt
      omega
    have hn : w.valuation F (x : F) ≠ 0 := by
      exact (map_ne_zero (w.valuation F)).mpr x.ne_zero
    rw [← WithZero.exp_log hn, hz, WithZero.exp_zero]
  have huv : frequencyEquivalent F S u.val v.val := by
    change u.val / v.val ∈ (S.unit F).map (powMonoidHom 6)
    exact ⟨x, hxS, hx.symm⟩
  obtain ⟨w, hw, huniq⟩ := U.represents u.val (U.power_free u.val u.property)
  have hu : frequencyEquivalent F S u.val u.val := by
    change u.val / u.val ∈ frequencyGamma F S
    simp
  exact (huniq u hu).trans (huniq v huv).symm

private theorem ratio_sixth (G : Type*) [CommGroup G] (u v x r s a b : G)
    (ha : x / (u * r ^ 6) = a ^ 6)
    (hb : x / (v * s ^ 6) = b ^ 6) :
    u / v = (b * s / (a * r)) ^ 6 := by
  have hu : u = x / (a ^ 6 * r ^ 6) := by
    have ha' := congrArg (fun z : G => z * (u * r ^ 6)) ha
    simp only [div_mul_cancel] at ha'
    apply (eq_div_iff_mul_eq'').mpr
    calc
      (a ^ 6 * r ^ 6) * u = a ^ 6 * (u * r ^ 6) := by ac_rfl
      _ = x := ha'.symm
  have hv : v = x / (b ^ 6 * s ^ 6) := by
    have hb' := congrArg (fun z : G => z * (v * s ^ 6)) hb
    simp only [div_mul_cancel] at hb'
    apply (eq_div_iff_mul_eq'').mpr
    calc
      (b ^ 6 * s ^ 6) * v = b ^ 6 * (v * s ^ 6) := by ac_rfl
      _ = x := hb'.symm
  rw [hu, hv]
  simp only [mul_pow, div_pow]
  simp [div_div_div_cancel_left]
private theorem unit_of_sixth {F : Type} [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (y : Fˣ)
    (hy : y ^ 6 ∈ S.unit F) : y ∈ S.unit F := by
  intro w hw
  have h := hy w hw
  simp only [Units.val_pow_eq_pow_val, map_pow] at h
  have hn : w.valuation F (y : F) ≠ 0 := (map_ne_zero (w.valuation F)).mpr y.ne_zero
  have hz := congrArg WithZero.log h
  rw [WithZero.log_pow] at hz
  simp only [WithZero.log_one, nsmul_eq_mul] at hz
  have hh : WithZero.log (w.valuation F (y : F)) = 0 := by omega
  rw [← WithZero.exp_log hn, hh, WithZero.exp_zero]

private theorem frequency_presentation_unique
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (U : FrequencyRepresentatives F S) (x : Fˣ)
    (p q : U.carrier × {J : Ideal (S.integer F) // J ≠ ⊥})
    (hp : ∃ r : S.integer F, r ≠ 0 ∧ Ideal.span {r} = p.2.val ∧
        ∃ rF : Fˣ, (rF : F) = (r : F) ∧ frequencyEquivalent F S x (p.1.val * rF ^ 6))
    (hq : ∃ r : S.integer F, r ≠ 0 ∧ Ideal.span {r} = q.2.val ∧
        ∃ rF : Fˣ, (rF : F) = (r : F) ∧ frequencyEquivalent F S x (q.1.val * rF ^ 6)) : p = q := by
  obtain ⟨r, hr, hrJ, rF, hrF, heqr⟩ := hp
  obtain ⟨s, hs, hsJ, sF, hsF, heqs⟩ := hq
  obtain ⟨a, haS, ha⟩ := heqr
  obtain ⟨b, hbS, hb⟩ := heqs
  change a ^ 6 = x / (p.1.val * rF ^ 6) at ha
  change b ^ 6 = x / (q.1.val * sF ^ 6) at hb
  have heq := ratio_sixth Fˣ p.1.val q.1.val x rF sF a b ha.symm hb.symm
  have huv : p.1 = q.1 := frequency_representatives_power_injective F S U p.1 q.1
    ⟨b * sF / (a * rF), heq⟩
  have hy6 : (b * sF / (a * rF)) ^ 6 = 1 := by
    rw [← heq, huv]
    simp
  have hyS := unit_of_sixth S (b * sF / (a * rF)) (hy6.symm ▸ (S.unit F).one_mem)
  have hsr : sF / rF ∈ S.unit F := by
    have hh : sF / rF = (b * sF / (a * rF)) * a / b := by
      symm
      calc
        (b * sF / (a * rF)) * a / b = (sF / rF) * (a * a⁻¹) * (b * b⁻¹) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ac_rfl
        _ = sF / rF := by simp
    rw [hh]
    exact (S.unit F).div_mem ((S.unit F).mul_mem hyS haS) hbS
  let t : (S.integer F)ˣ := Set.unitEquivUnitsInteger S F ⟨sF / rF, hsr⟩
  have ht : (t : S.integer F) * r = s := by
    apply Subtype.ext
    change ((sF / rF : Fˣ) : F) * (r : F) = (s : F)
    rw [Units.val_div_eq_div_val, ← hrF, ← hsF]
    exact div_mul_cancel₀ _ rF.ne_zero
  have hJ : p.2 = q.2 := by
    apply Subtype.ext
    rw [← hrJ, ← hsJ, ← ht]
    exact (Ideal.span_singleton_mul_left_unit t.isUnit r).symm
  exact Prod.ext huv hJ

noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable (S : Set (HeightOneSpectrum (𝓞 F))) [IsPrincipalIdealRing (S.integer F)]

 def frequencyExteriorPrime (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) : Ideal (S.integer F) where
  carrier := {a | v.valuation F (a : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change v.valuation F ((a + b : S.integer F) : F) < 1
    change v.valuation F ((a : F) + (b : F)) < 1
    exact lt_of_le_of_lt (ValuationClass.map_add_le_max _ _ _) (max_lt ha hb)
  smul_mem' := by
    intro a b hb
    change v.valuation F ((a * b : S.integer F) : F) < 1
    change v.valuation F ((a : F) * (b : F)) < 1
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (a.property v hv) zero_le) (by simpa using hb)

private theorem frequency_exists_exterior_generator (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    ∃ p : S.integer F, p ≠ 0 ∧
      v.valuation F (p : F) = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v →
        w.valuation F (p : F) = 1 := by
  let P := frequencyExteriorPrime S v hv
  let p := Submodule.IsPrincipal.generator P
  have hP : Ideal.span {p} = P := Submodule.IsPrincipal.span_singleton_generator P
  have hpP : p ∈ P := by rw [← hP]; exact Ideal.subset_span (by simp)
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  let πR : S.integer F := ⟨(π : F), fun w _ => w.valuation_le_one π⟩
  have hvπ : v.valuation F (πR : F) = WithZero.exp (-1 : ℤ) := by
    simpa [πR, HeightOneSpectrum.valuation_of_algebraMap] using hπ
  have hπP : πR ∈ P := by
    change v.valuation F (πR : F) < 1
    rw [hvπ]
    simp
  have hdvd : p ∣ πR := by
    rw [← Ideal.mem_span_singleton, hP]
    exact hπP
  have hp0 : p ≠ 0 := by
    intro h
    have : πR = 0 := zero_dvd_iff.mp (h ▸ hdvd)
    have hh := congrArg (fun a : S.integer F => v.valuation F (a : F)) this
    simp [hvπ] at hh
  have hval : v.valuation F (p : F) = WithZero.exp (-1 : ℤ) := by
    have hlt : v.valuation F (p : F) < 1 := hpP
    obtain ⟨a, ha⟩ := hdvd
    have hh := congrArg (fun z : S.integer F => v.valuation F (z : F)) ha
    simp only [map_mul, Subalgebra.coe_mul] at hh
    have ha1 := Set.integer_valuation_le_one S F a hv
    have hpne : v.valuation F (p : F) ≠ 0 :=
      (map_ne_zero (v.valuation F)).mpr (by exact_mod_cast hp0)
    have hle : WithZero.exp (-1 : ℤ) ≤ v.valuation F (p : F) := by
      rw [← hvπ, hh]
      exact mul_le_of_le_one_right zero_le ha1
    apply le_antisymm ?_ hle
    rw [← WithZero.exp_log hpne, WithZero.exp_le_exp]
    have hz : WithZero.log (v.valuation F (p : F)) < 0 := by
      exact (WithZero.log_lt_iff_lt_exp hpne).mpr (by simpa using hlt)
    omega
  refine ⟨p, hp0, hval, ?_⟩
  intro w hw hwv
  have hvw : ¬ v.asIdeal ≤ w.asIdeal := by
    intro h
    exact hwv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h).symm)
  obtain ⟨a, hav, haw⟩ := SetLike.not_le_iff_exists.mp hvw
  let aR : S.integer F := ⟨(a : F), fun z _ => z.valuation_le_one a⟩
  have haP : aR ∈ P := by
    change v.valuation F (a : F) < 1
    exact (v.valuation_lt_one_iff_mem a).mpr hav
  have hpa : p ∣ aR := by rw [← Ideal.mem_span_singleton, hP]; exact haP
  obtain ⟨b, hb⟩ := hpa
  have ha1 : w.valuation F (aR : F) = 1 := by
    exact w.valuation_eq_one_iff_notMem.mpr haw
  have hh := congrArg (fun z : S.integer F => w.valuation F (z : F)) hb
  simp only [map_mul, Subalgebra.coe_mul, ha1] at hh
  have hb1 := Set.integer_valuation_le_one S F b hw
  have hp1 := Set.integer_valuation_le_one S F p hw
  have : 1 ≤ w.valuation F (p : F) := by
    rw [hh]
    exact mul_le_of_le_one_right zero_le hb1
  exact le_antisymm hp1 this

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem frequency_sixth_free_decomposition (x : S.integer F) (hx : x ≠ 0) :
    ∃ y r : S.integer F, y ≠ 0 ∧ r ≠ 0 ∧ x = y * r ^ 6 ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        ∃ e : Fin 6, v.valuation F (y : F) = WithZero.exp (-(e.val : ℤ)) := by
  classical
  induction x using (wellFounded_dvdNotUnit (α := S.integer F)).induction with
  | h x ih =>
    by_cases hfree : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        ∃ e : Fin 6, v.valuation F (x : F) = WithZero.exp (-(e.val : ℤ))
    · exact ⟨x, 1, hx, one_ne_zero, by simp, hfree⟩
    · push_neg at hfree
      obtain ⟨v, hv, hbad⟩ := hfree
      obtain ⟨p, hp0, hpv, hpw⟩ := frequency_exists_exterior_generator S v hv
      have hxF : (x : F) ≠ 0 := by exact_mod_cast hx
      have hpF : (p : F) ≠ 0 := by exact_mod_cast hp0
      have hvalne : v.valuation F (x : F) ≠ 0 := (map_ne_zero _).mpr hxF
      have hlog : WithZero.log (v.valuation F (x : F)) ≤ -6 := by
        have hle : WithZero.log (v.valuation F (x : F)) ≤ 0 :=
          (WithZero.log_le_iff_le_exp hvalne).mpr (by simpa using x.property v hv)
        by_contra hh
        have hn : 0 ≤ -WithZero.log (v.valuation F (x : F)) ∧
            -WithZero.log (v.valuation F (x : F)) < 6 := by omega
        let e : Fin 6 := ⟨(-WithZero.log (v.valuation F (x : F))).toNat, by omega⟩
        apply hbad e
        rw [← WithZero.exp_log hvalne]
        congr 1
        dsimp [e]
        omega
      have hqint : (x : F) / (p : F) ^ 6 ∈ S.integer F := by
        intro w hw
        rw [map_div₀, map_pow]
        by_cases hwv : w = v
        · subst w
          rw [hpv, ← WithZero.exp_log hvalne, ← WithZero.exp_nsmul,
            ← WithZero.exp_sub]
          simp only [nsmul_eq_mul]
          rw [WithZero.exp_le_one_iff]
          omega
        · rw [hpw w hw hwv]
          simpa using x.property w hw
      let q : S.integer F := ⟨(x : F) / (p : F) ^ 6, hqint⟩
      have hq0 : q ≠ 0 := by
        intro hh
        have := congrArg (fun a : S.integer F => (a : F)) hh
        exact (div_ne_zero hxF (pow_ne_zero _ hpF)) this
      have hxq : x = q * p ^ 6 := by
        apply Subtype.ext
        exact (div_mul_cancel₀ (x : F) (pow_ne_zero 6 hpF)).symm
      have hpnu : ¬ IsUnit (p ^ 6) := by
        intro hu
        have hpu : IsUnit p := (isUnit_pow_iff (by omega)).mp hu
        obtain ⟨pu, hpu⟩ := hpu
        have hone : v.valuation F (pu : F) = 1 := by
          have ha := (pu.val).property v hv
          have hb := (pu.inv).property v hv
          have heq : v.valuation F (pu : F) * v.valuation F (pu.inv : F) = 1 := by
            rw [← map_mul]
            change v.valuation F ((pu.val * pu.inv : S.integer F) : F) = 1
            rw [pu.val_inv]
            exact map_one _
          exact eq_one_of_one_le_mul_left ha hb heq.ge
        rw [hpu, hpv] at hone
        simpa using hone
      obtain ⟨y, r, hy0, hr0, hqy, hy⟩ := ih q ⟨hq0, p ^ 6, hpnu, hxq⟩ hq0
      refine ⟨y, r * p, hy0, mul_ne_zero hr0 hp0, ?_, hy⟩
      rw [hxq, hqy, mul_pow, mul_assoc]
private theorem frequency_presentation_exists
    (U : FrequencyRepresentatives F S) (x : Fˣ)
    (hx : (x : F) ∈ S.integer F) :
    ∃ p : U.carrier × {J : Ideal (S.integer F) // J ≠ ⊥},
      ∃ r : S.integer F, r ≠ 0 ∧ Ideal.span {r} = p.2.val ∧
        ∃ rF : Fˣ, (rF : F) = (r : F) ∧
          frequencyEquivalent F S x (p.1.val * rF ^ (6 : ℕ)) := by
  let xR : S.integer F := ⟨(x : F), hx⟩
  have hxR : xR ≠ 0 := by
    intro h
    have hh := congrArg (fun a : S.integer F => (a : F)) h
    exact x.ne_zero (by simpa [xR] using hh)
  obtain ⟨y, r, hy0, hr0, hxy, hy⟩ := frequency_sixth_free_decomposition S xR hxR
  let yF : Fˣ := Units.mk0 (y : F) (by exact_mod_cast hy0)
  let rF : Fˣ := Units.mk0 (r : F) (by exact_mod_cast hr0)
  have hyF : sixthPowerFreeFrequency F S yF := by
    refine ⟨y.property, ?_⟩
    intro v hv
    simpa [yF] using hy v hv
  obtain ⟨u, hu, _⟩ := U.represents yF hyF
  obtain ⟨a, haS, ha⟩ := hu
  have hxyF : x = yF * rF ^ 6 := by
    apply Units.ext
    have hh := congrArg (fun a : S.integer F => (a : F)) hxy
    simpa [xR, yF, rF] using hh
  let J : Ideal (S.integer F) := Ideal.span {r}
  have hJ : J ≠ ⊥ := by
    intro hh
    have hr : r ∈ (⊥ : Ideal (S.integer F)) := by
      rw [← hh]
      exact Ideal.subset_span (by simp)
    exact hr0 (by simpa using hr)
  refine ⟨⟨u, ⟨J, hJ⟩⟩, r, hr0, rfl, rF, by simp [rF], ?_⟩
  change x / (u.val * rF ^ 6) ∈ (S.unit F).map (powMonoidHom 6)
  refine ⟨a, haS, ?_⟩
  rw [ha, hxyF]
  simp only [div_eq_mul_inv, mul_inv_rev]
  symm
  calc
    yF * rF ^ 6 * ((rF ^ 6)⁻¹ * u.val⁻¹) =
        (yF * u.val⁻¹) * (rF ^ 6 * (rF ^ 6)⁻¹) := by ac_rfl
    _ = yF * u.val⁻¹ := by simp

end

theorem frequency_unique_presentation
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    [IsPrincipalIdealRing (S.integer F)]
    (U : FrequencyRepresentatives F S) (x : Fˣ)
    (hx : (x : F) ∈ S.integer F) :
    ∃! p : U.carrier × {J : Ideal (S.integer F) // J ≠ ⊥},
      ∃ r : S.integer F, r ≠ 0 ∧ Ideal.span {r} = p.2.val ∧
        ∃ rF : Fˣ, (rF : F) = (r : F) ∧
          frequencyEquivalent F S x (p.1.val * rF ^ (6 : ℕ)) := by
  have hexists : ∃ p : U.carrier × {J : Ideal (S.integer F) // J ≠ ⊥},
      ∃ r : S.integer F, r ≠ 0 ∧ Ideal.span {r} = p.2.val ∧
        ∃ rF : Fˣ, (rF : F) = (r : F) ∧
          frequencyEquivalent F S x (p.1.val * rF ^ (6 : ℕ)) := by
    exact frequency_presentation_exists S U x hx
  obtain ⟨p, hp⟩ := hexists
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact frequency_presentation_unique F S U x q p hq hp

structure PrimitiveFrequencyCharacter (F : Type) [Field F] [NumberField F] where
  conductor : Ideal (𝓞 F)
  conductor_ne_zero : conductor ≠ ⊥
  character : RayClassCharacter F conductor
  primitive : character.IsPrimitive

def samePrimitiveFrequencyCharacter (F : Type) [Field F] [NumberField F]
    (χ ψ : PrimitiveFrequencyCharacter F) : Prop :=
  ∀ n : Ideal (𝓞 F), χ.character n = ψ.character n

def IsKummerFrequencyCharacter (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (ι : F →+* ℂ) (S : Set (HeightOneSpectrum (𝓞 F)))
    (u : Fˣ) (χ : PrimitiveFrequencyCharacter F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F (u : F) = 1 →
    v.asIdeal ⊔ χ.conductor = ⊤ ∧
      ∃ j : Fin 6,
        v.valuation F ((u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
          (ζ12 ^ (2 : ℕ)) ^ j.val) < 1 ∧
        χ.character v.asIdeal = ι ((ζ12 ^ (2 : ℕ)) ^ j.val)

structure KummerFrequencyFamily (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (ι : F →+* ℂ) (S : Set (HeightOneSpectrum (𝓞 F)))
    (U : FrequencyRepresentatives F S) where
  numerator : U.carrier → PrimitiveFrequencyCharacter F
  kummer : ∀ u : U.carrier,
    IsKummerFrequencyCharacter F ζ12 ι S u.val (numerator u)

theorem kummer_frequency_family_exists
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (U : FrequencyRepresentatives F S) :
    Nonempty (KummerFrequencyFamily F ζ12 ι S U) := by
  classical
  let hc := primitive12_totallyComplex F ζ12 hζ12
  have hex : ∀ u : U.carrier, ∃ χ : PrimitiveFrequencyCharacter F,
      IsKummerFrequencyCharacter F ζ12 ι S u.val χ := by
    intro u
    obtain ⟨m, hm, ρ, χ, hp, _, _, hχ, _⟩ := PrimitiveRay.primitiveRay_exists hc
      (PrimitiveRay.arithmeticSexticArtinCharacter ζ12 hζ12 ι u.val)
      ⟨6, by norm_num, PrimitiveRay.arithmeticSexticArtinCharacter_pow_six ζ12 hζ12 ι u.val⟩
    refine ⟨⟨m, hm, χ, hp⟩, ?_⟩
    intro v hv hu
    have h6 : (Ideal.absNorm v.asIdeal).Coprime 6 := by
      by_contra h
      exact hv (hSix v h)
    have hn := PrimitiveRay.arithmeticSextic_primitiveRay_support ζ12 hζ12 ι u.val
      hc m hm χ hp hχ v h6 hu
    have hcop : v.asIdeal ⊔ m = ⊤ := by
      exact v.isMaximal.out.2 _
        (lt_of_le_of_ne le_sup_left (fun h => hn (h ▸ le_sup_right)))
    refine ⟨hcop, ?_⟩
    obtain ⟨j, hj, he⟩ := PrimitiveRay.arithmeticSexticArtinCharacter_prime
      ζ12 hζ12 ι u.val v h6 hu
    refine ⟨j, hj, ?_⟩
    have hv' : v ∉ (RayClassBridge.narrowIdealModulus F m hm).finitePart.support := by
      simpa only [← Finset.mem_coe, RayClassBridge.narrowIdealModulus_support,
        Set.mem_setOf_eq] using hn
    rw [← RayClassBridge.ideleClassCharacter_finitePrimeIdele F hc m hm χ v hv', hχ]
    exact he
  exact ⟨⟨fun u => (hex u).choose, fun u => (hex u).choose_spec⟩⟩

def IsPrimitiveFrequencyTwist (F : Type) [Field F] [NumberField F]
    (η χ ψ : PrimitiveFrequencyCharacter F) : Prop :=
  ∀ n : Ideal (𝓞 F), n ≠ ⊥ →
    n ⊔ (η.conductor * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character n = η.character n * (starRingEnd ℂ) (χ.character n)

structure TwistedFrequencyFamily (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (ι : F →+* ℂ) (S : Set (HeightOneSpectrum (𝓞 F)))
    (U : FrequencyRepresentatives F S)
    (K : KummerFrequencyFamily F ζ12 ι S U) (η : PrimitiveFrequencyCharacter F) where
  denominator : U.carrier → PrimitiveFrequencyCharacter F
  induces : ∀ u : U.carrier,
    IsPrimitiveFrequencyTwist F η (K.numerator u) (denominator u)

theorem twisted_frequency_family_exists
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
    (η : PrimitiveFrequencyCharacter F) :
    Nonempty (TwistedFrequencyFamily F ζ12 ι S U K η) := by
  classical
  let hc := primitive12_totallyComplex F ζ12 hζ12
  let lift (χ : PrimitiveFrequencyCharacter F) : IdeleClassGroup F →ₜ* ℂˣ :=
    ⟨RayClassBridge.ideleClassCharacter F hc χ.conductor χ.conductor_ne_zero χ.character,
      RayClassBridge.ideleClassCharacter_continuous F hc χ.conductor
        χ.conductor_ne_zero χ.character⟩
  let exponent (χ : PrimitiveFrequencyCharacter F) : ℕ :=
    Nat.card (ClassFieldTheory.RayClassGroup
      (RayClassBridge.narrowIdealModulus F χ.conductor χ.conductor_ne_zero))
  have hexpos (χ : PrimitiveFrequencyCharacter F) : 0 < exponent χ :=
    RayClassBridge.ideleClassCharacter_exponent_pos F χ.conductor χ.conductor_ne_zero
  have hexpow (χ : PrimitiveFrequencyCharacter F) (c : IdeleClassGroup F) :
      lift χ c ^ exponent χ = 1 :=
    RayClassBridge.ideleClassCharacter_pow_card F hc χ.conductor χ.conductor_ne_zero
      χ.character c
  have hex : ∀ u : U.carrier, ∃ ψ : PrimitiveFrequencyCharacter F,
      IsPrimitiveFrequencyTwist F η (K.numerator u) ψ := by
    intro u
    let χ := K.numerator u
    let Φ : IdeleClassGroup F →ₜ* ℂˣ := lift η * (lift χ)⁻¹
    have hpow : ∀ c : IdeleClassGroup F,
        Φ c ^ (exponent η * exponent χ) = 1 := by
      intro c
      change (lift η c * (lift χ c)⁻¹) ^ (exponent η * exponent χ) = 1
      rw [mul_pow, pow_mul, hexpow, one_pow, inv_pow,
        Nat.mul_comm, pow_mul, hexpow, one_pow, inv_one, one_mul]
    obtain ⟨m, hm, ρ, ψ, hp, _, _, hψ, _⟩ := PrimitiveRay.primitiveRay_exists hc Φ
      ⟨exponent η * exponent χ, Nat.mul_pos (hexpos η) (hexpos χ), hpow⟩
    refine ⟨⟨m, hm, ψ, hp⟩, ?_⟩
    intro I hI hcop
    have hηcop : I ⊔ η.conductor = ⊤ := by
      apply top_le_iff.mp
      rw [← hcop]
      exact sup_le_sup_left (le_trans Ideal.mul_le_left Ideal.mul_le_left) I
    have hχcop : I ⊔ χ.conductor = ⊤ := by
      apply top_le_iff.mp
      rw [← hcop]
      exact sup_le_sup_left (le_trans Ideal.mul_le_left Ideal.mul_le_right) I
    have hψcop : I ⊔ m = ⊤ := by
      apply top_le_iff.mp
      rw [← hcop]
      exact sup_le_sup_left Ideal.mul_le_right I
    let c : IdeleClassGroup F := QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
      (RayClassBridge.idealIdele F I hI)
    have eη : (lift η c : ℂ) = η.character I :=
      RayClassBridge.ideleClassCharacter_idealIdele F hc η.conductor η.conductor_ne_zero
        η.character I hI hηcop
    have eχ : (lift χ c : ℂ) = χ.character I :=
      RayClassBridge.ideleClassCharacter_idealIdele F hc χ.conductor χ.conductor_ne_zero
        χ.character I hI hχcop
    have en : ‖(lift χ c : ℂ)‖ = 1 :=
      RayClassBridge.ideleClassCharacter_norm F hc χ.conductor χ.conductor_ne_zero
        χ.character c
    rw [← RayClassBridge.ideleClassCharacter_idealIdele F hc m hm ψ I hI hψcop]
    change (RayClassBridge.ideleClassCharacter F hc m hm ψ c : ℂ) = _
    rw [hψ]
    change ((lift η c * (lift χ c)⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Complex.inv_eq_conj en, eη, eχ]
  exact ⟨⟨fun u => (hex u).choose, fun u => (hex u).choose_spec⟩⟩

private theorem frequency_ratio_residue
    {F : Type} [Field F] [NumberField F]
    (ζ12 : F) (ι : F →+* ℂ) (S : Set (HeightOneSpectrum (𝓞 F)))
    (u w : Fˣ) (χ ψ : PrimitiveFrequencyCharacter F)
    (hχ : IsKummerFrequencyCharacter F ζ12 ι S u χ)
    (hψ : IsKummerFrequencyCharacter F ζ12 ι S w ψ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (hu : v.valuation F (u : F) = 1) (hw : v.valuation F (w : F) = 1)
    (heq : χ.character v.asIdeal = ψ.character v.asIdeal) :
    v.valuation F (((u / w : Fˣ) : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1) < 1 := by
  obtain ⟨_, i, hi, hci⟩ := hχ v hv hu
  obtain ⟨_, j, hj, hcj⟩ := hψ v hv hw
  have hij : (ζ12 ^ 2) ^ i.val = (ζ12 ^ 2) ^ j.val := by
    apply ι.injective
    exact hci.symm.trans (heq.trans hcj)
  rw [← hij] at hj
  have hd : v.valuation F ((u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
      (w : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) < 1 := by
    convert (v.valuation F).map_sub_lt hi hj using 1
    congr 1
    ring
  have hn : (w : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) ≠ 0 := pow_ne_zero _ w.ne_zero
  have he : (((u / w : Fˣ) : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1) =
      ((u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
        (w : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) /
          (w : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    simp only [Units.val_div_eq_div_val, div_pow]
    rw [sub_div, div_self hn]
  rw [he, map_div₀, map_pow, hw, one_pow, div_one]
  exact hd

private theorem frequency_injective_of_cofinite_prime_equality
    {F : Type} [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
    (u w : U.carrier)
    (heq : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (K.numerator u).character v.asIdeal = (K.numerator w).character v.asIdeal) : u = w := by
  have hmu : (primitiveRoots 6 F).Nonempty :=
    ⟨ζ12 ^ 2, (mem_primitiveRoots (by norm_num : 0 < 6)).mpr
      (IsPrimitiveRoot.pow (by norm_num : 0 < 12) hζ12 (by norm_num : 12 = 2 * 6))⟩
  have hs : ∀ᶠ v in Filter.cofinite, v ∉ S := Filter.eventually_cofinite.mpr (by simpa using hS)
  have hr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.valuation F (((u.val / w.val : Fˣ) : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1) < 1 := by
    filter_upwards [hs, FrequencyDetection.valuation_unit_cofinite u.val,
      FrequencyDetection.valuation_unit_cofinite w.val, heq] with v hv hu hw he
    exact frequency_ratio_residue ζ12 ι S u.val w.val (K.numerator u) (K.numerator w)
      (K.kummer u) (K.kummer w) v hv hu hw he
  obtain ⟨x, hx⟩ := FrequencyDetection.global_power_of_cofinite_residue (6 : ℕ+) hmu
    (u.val / w.val) hr
  exact frequency_representatives_power_injective F S U u w ⟨x, hx.symm⟩

private theorem frequency_coprime_cofinite
    {F : Type} [Field F] [NumberField F] (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.asIdeal ⊔ m = ⊤ := by
  apply Filter.eventually_cofinite.mpr
  apply (Ideal.finite_factors hm).subset
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  apply Ideal.dvd_iff_le.mpr
  have hvmax : v.asIdeal.IsMaximal := v.isMaximal
  exact (hvmax.eq_of_le hv (show v.asIdeal ≤ v.asIdeal ⊔ m from le_sup_left)).symm ▸
    (show m ≤ v.asIdeal ⊔ m from le_sup_right)

theorem twisted_frequency_character_injective
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
    (η : PrimitiveFrequencyCharacter F) (T : TwistedFrequencyFamily F ζ12 ι S U K η)
    (u v : U.carrier)
    (hψ : samePrimitiveFrequencyCharacter F (T.denominator u) (T.denominator v)) :
    u = v := by
  apply frequency_injective_of_cofinite_prime_equality ζ12 hζ12 ι S hS U K u v
  filter_upwards [frequency_coprime_cofinite η.conductor η.conductor_ne_zero,
    frequency_coprime_cofinite (K.numerator u).conductor (K.numerator u).conductor_ne_zero,
    frequency_coprime_cofinite (K.numerator v).conductor (K.numerator v).conductor_ne_zero,
    frequency_coprime_cofinite (T.denominator u).conductor (T.denominator u).conductor_ne_zero,
    frequency_coprime_cofinite (T.denominator v).conductor (T.denominator v).conductor_ne_zero]
    with w hη hKu hKv hTu hTv
  have hm₁ : w.asIdeal ⊔ (η.conductor * (K.numerator u).conductor *
      (T.denominator u).conductor) = ⊤ := by
    rw [mul_assoc, Ideal.sup_mul_eq_of_coprime_left hη,
      Ideal.sup_mul_eq_of_coprime_left hKu, hTu]
  have hm₂ : w.asIdeal ⊔ (η.conductor * (K.numerator v).conductor *
      (T.denominator v).conductor) = ⊤ := by
    rw [mul_assoc, Ideal.sup_mul_eq_of_coprime_left hη,
      Ideal.sup_mul_eq_of_coprime_left hKv, hTv]
  have hη0 : η.character w.asIdeal ≠ 0 := by
    intro hz
    rcases (η.character.eq_zero_iff' w.asIdeal).mp hz with hz | hz
    · exact w.ne_bot hz
    · exact hz hη
  have heq : (starRingEnd ℂ) ((K.numerator u).character w.asIdeal) =
      (starRingEnd ℂ) ((K.numerator v).character w.asIdeal) := by
    apply mul_left_cancel₀ hη0
    exact (T.induces u w.asIdeal w.ne_bot hm₁).symm.trans
      ((hψ w.asIdeal).trans (T.induces v w.asIdeal w.ne_bot hm₂))
  simpa using congrArg (starRingEnd ℂ) heq

theorem twisted_frequency_at_most_one_principal
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (ι : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F), ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)]
    (U : FrequencyRepresentatives F S) (K : KummerFrequencyFamily F ζ12 ι S U)
    (η : PrimitiveFrequencyCharacter F) (T : TwistedFrequencyFamily F ζ12 ι S U K η)
    (u v : U.carrier) (hu : (T.denominator u).character.IsPrincipal)
    (hv : (T.denominator v).character.IsPrincipal) : u = v := by
  have htop : ∀ (χ : PrimitiveFrequencyCharacter F),
      χ.character.IsPrincipal → χ.conductor = ⊤ := by
    intro χ hχ
    by_contra h
    obtain ⟨α, hα, _, _, hprime, hne⟩ :=
      χ.primitive ⊤ (lt_top_iff_ne_top.mpr h)
    exact hne (hχ _ (by simpa using hα) hprime)
  have huc := htop (T.denominator u) hu
  have hvc := htop (T.denominator v) hv
  apply twisted_frequency_character_injective F ζ12 hζ12 ι S hS hSix U K η T u v
  intro n
  by_cases hn : n = ⊥
  · subst n
    have h0u := ((T.denominator u).character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
    have h0v := ((T.denominator v).character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
    exact h0u.trans h0v.symm
  · exact (hu n hn (by simp [huc])).trans (hv n hn (by simp [hvc])).symm

end DedekindZetaZeroFree.Detector

end
