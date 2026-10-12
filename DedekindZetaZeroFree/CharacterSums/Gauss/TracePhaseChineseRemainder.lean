module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PrincipalPrimePowerChineseRemainder

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization
open LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

 theorem prime_outside (p : ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have hc : A.cS ≤ p.val.asIdeal := Ideal.IsPrime.prod_le p.val.isPrime |>.mpr ⟨p.val, hp, le_rfl⟩
  apply p.val.isPrime.ne_top
  apply top_le_iff.mp
  calc
    ⊤ = p.val.asIdeal ⊔ A.cS := p.property.symm
    _ ≤ p.val.asIdeal := sup_le le_rfl hc

 def boundIdeal (p : ExteriorPrime A) (n : ℕ) : Ideal A.R where
  carrier := {a | p.val.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change p.val.valuation F ((a : F) + (b : F)) ≤ _
    exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha hb)
  smul_mem' := by
    intro a b hb
    change p.val.valuation F ((a : F) * (b : F)) ≤ _
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (a.property p.val (prime_outside p)) zero_le).trans (by simpa using hb)

private theorem generates_valuation (p : ExteriorPrime A)
    (I : A.Exterior) (r : A.R) (hr : A.Generates I r) :
    p.val.valuation F (r : F) = WithZero.exp (-(exponent p I : ℤ)) := by
  let n := exponent p I
  have hdvd (k : ℕ) : p.val.asIdeal ^ k ∣ I.val ↔ k ≤ n := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors p.val.irreducible I.property.1]
    simp [n, exponent, idealPrimeExponent]
  have hIn : I.val ≤ p.val.asIdeal ^ n := Ideal.dvd_iff_le.mp ((hdvd n).mpr le_rfl)
  have hnot : ¬ I.val ≤ p.val.asIdeal ^ (n + 1) := by
    rw [← Ideal.dvd_iff_le, hdvd]; omega
  have hmap : A.extendIdeal I ≤ boundIdeal p n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change p.val.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))
    rw [p.val.valuation_of_algebraMap]
    exact (p.val.intValuation_le_pow_iff_mem a n).mpr (hIn ha)
  have hrv : p.val.valuation F (r : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply hmap
    rw [← hr.2]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨a, ha, han⟩ : ∃ a : 𝓞 F, a ∈ I.val ∧ a ∉ p.val.asIdeal ^ (n + 1) := by
    contrapose! hnot
    exact hnot
  have ham : algebraMap (𝓞 F) A.R a ∈ Ideal.span ({r} : Set A.R) := by
    rw [hr.2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ham
  have hav : p.val.valuation F (a : F) ≤ p.val.valuation F (r : F) := by
    have hh := congrArg (fun t : A.R => (t : F)) hy
    change (a : F) = (r : F) * (y : F) at hh
    rw [hh, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property p.val (prime_outside p)) zero_le).trans (by simp)
  have hrv' : ¬ p.val.valuation F (r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro h
    apply han
    apply (p.val.intValuation_le_pow_iff_mem a (n + 1)).mp
    rw [← p.val.valuation_of_algebraMap (K := F)]
    exact hav.trans h
  have hnz : p.val.valuation F (r : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hr.1)
  rw [← WithZero.exp_log hnz, WithZero.exp_le_exp] at hrv hrv'
  have hv : WithZero.log (p.val.valuation F (r : F)) = -(n : ℤ) := by
    push_cast at hrv'
    omega
  rw [← WithZero.exp_log hnz, hv]

private theorem fieldTrace_eq_exterior_product (hS : A.ContainsTraceBadPlaces)
    (P : Finset (ExteriorPrime A)) (x : F)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      (∀ p ∈ P, p.val ≠ v) →
      algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F) :
    A.fieldTraceCharacter x =
      ∏ p ∈ P, negativeTrace p (algebraMap F (LocalField p) x) := by
  let f := fun v : HeightOneSpectrum (𝓞 F) =>
    ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) x)
  let Q := P.image (fun p => p.val)
  have hdisj : Disjoint Q A.Sf := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    have hc : A.cS ≤ p.val.asIdeal := Ideal.IsPrime.prod_le p.val.isPrime |>.mpr ⟨p.val, hvS, le_rfl⟩
    apply p.val.isPrime.ne_top
    exact ((sup_eq_left.mpr hc).symm.trans p.property)
  have hprod : (∏ᶠ v, f v) = (∏ v ∈ Q, f v) * ∏ v ∈ A.Sf, f v := by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := Q ∪ A.Sf), Finset.prod_union hdisj]
    intro v hv
    by_contra hn
    have hvs : v ∉ A.Sf := fun h => hn (Finset.mem_union_right Q h)
    have hvq : ∀ p ∈ P, p.val ≠ v := by
      intro p hp he
      exact hn (Finset.mem_union_left A.Sf (Finset.mem_image.mpr ⟨p, hp, he⟩))
    have h := (hS v hvs _).2 (hx v hvs hvq)
    exact hv (by simpa [f] using h (1 : v.adicCompletionIntegers F))
  have hglobal := ResidueTrace.diagonal_product_formula x
  rw [hprod] at hglobal
  have hfield : A.fieldTraceCharacter x = (∏ v ∈ Q, f v)⁻¹ := by
    change (∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion x)) *
      (∏ v : A.Sf, f v.val) = _
    rw [Finset.prod_coe_sort]
    apply (eq_inv_iff_mul_eq_one).mpr
    convert hglobal using 1 <;> ac_rfl
  rw [hfield, ← Finset.prod_inv_distrib]
  change (∏ v ∈ Q, (f v)⁻¹) = _
  rw [Finset.prod_image (fun p hp q hq he => Subtype.ext he)]
  apply Finset.prod_congr rfl
  intro p hp
  simp [f, negativeTrace, AddChar.map_neg_eq_inv]

private theorem phase_integral_outside_support (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia : A.Exterior) (s a : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a)
    (P : Finset (ExteriorPrime A))
    (hSupportS : ∀ p : ExteriorPrime A, exponent p Is ≠ 0 → p ∈ P)
    (hSupportA : ∀ p : ExteriorPrime A, exponent p Ia ≠ 0 → p ∈ P)
    (n : A.R) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (hvP : ∀ p ∈ P, p.val ≠ v) :
    algebraMap F (v.adicCompletion F) ((n : F) / ((s : F) * (a : F))) ∈
      v.adicCompletionIntegers F := by
  have hc : v.asIdeal ⊔ A.cS = ⊤ := by
    apply Ideal.sup_prod_eq_top
    intro w hw
    exact (HeightOneSpectrum.isCoprime_of_ne v w (fun h => hv (h.symm ▸ hw))).sup_eq
  let p : ExteriorPrime A := ⟨v, hc⟩
  have hp : p ∉ P := fun h => hvP p h rfl
  have hs0 : exponent p Is = 0 := by
    by_contra hn
    exact hp (hSupportS p hn)
  have ha0 : exponent p Ia = 0 := by
    by_contra hn
    exact hp (hSupportA p hn)
  have hvs := generates_valuation p Is s hs
  have hva := generates_valuation p Ia a ha
  simp only [hs0, ha0, Nat.cast_zero, neg_zero, WithZero.exp_zero] at hvs hva
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  change p.val.valuation F ((n : F) / ((s : F) * (a : F))) ≤ 1
  rw [map_div₀, map_mul, hvs, hva, one_mul, div_one]
  exact n.property v hv

private lemma uniformizer_ne_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : uniformizer C p ≠ 0 := by
  rw [uniformizer]
  exact (map_ne_zero (algebraMap F (LocalField p))).mpr
    (by exact_mod_cast (generator_generates C p).1)

private lemma congruent_of_residueMap_eq_generator (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x y : A.R)
    (h : residueMap C p n x = residueMap C p n y) :
    CompatiblePrimeRawLocal.Congruent C p n (algebraMap F (LocalField p) (x : F))
      (algebraMap F (LocalField p) (y : F)) := by
  have hmem : x - y ∈ Ideal.span ({generator C p ^ n} : Set A.R) :=
    Ideal.Quotient.eq.mp h
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨⟨algebraMap F (LocalField p) (r : F),
    CompatiblePrimeRawLocal.sInteger_local_integral p r⟩, ?_⟩
  simp only [Subtype.coe_mk]
  rw [← map_sub, ← Subalgebra.coe_sub, hr, Subalgebra.coe_mul, Subalgebra.coe_pow,
    map_mul, map_pow, uniformizer]

private lemma negTrace_congr (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) {x y : LocalField p}
    (h : x - y ∈ p.val.adicCompletionIntegers F) :
    negativeTrace p x = negativeTrace p y := by
  have hxy : x = y + (x - y) := by ring
  rw [hxy, AddChar.map_add_eq_mul,
    CompatiblePrimeRawLocal.negativeTrace_integer C p ⟨x - y, h⟩, mul_one]

private lemma unit_val_inv_mem (p : ExteriorPrime A) (u : (LocalIntegers p)ˣ) :
    ((u.val : LocalField p))⁻¹ ∈ p.val.adicCompletionIntegers F := by
  have hmul : (u.val : LocalField p) * ((u⁻¹).val : LocalField p) = 1 := by
    exact congrArg (fun z : LocalIntegers p => (z : LocalField p)) (Units.mul_inv u)
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact ((u⁻¹).val).2

theorem phase_crt (C : A.GeneralArithmeticContext σ η hS)
    (Is Ia Ih : A.Exterior) (s a h : A.R)
    (hs : A.Generates Is s) (ha : A.Generates Ia a)
    (P : Finset (ExteriorPrime A))
    (hSupportS : ∀ p : ExteriorPrime A, exponent p Is ≠ 0 → p ∈ P)
    (hSupportA : ∀ p : ExteriorPrime A, exponent p Ia ≠ 0 → p ∈ P)
    (Es : FiniteTransform.Residue A.R.toSubring s ≃+* PrimePowerProduct C Is P)
    (Ea : FiniteTransform.Residue A.R.toSubring a ≃+* PrimePowerProduct C Ia P)
    (hEs : ∀ (r : A.R) (p : P),
      Es (FiniteTransform.residueMap A.R.toSubring s r) p =
        LocalFiniteSums.residueMap C p.val (exponent p.val Is) r)
    (hEa : ∀ (r : A.R) (p : P),
      Ea (FiniteTransform.residueMap A.R.toSubring a r) p =
        LocalFiniteSums.residueMap C p.val (exponent p.val Ia) r)
    (sU aU hU : (p : P) → (LocalIntegers p.val)ˣ)
    (hsU : ∀ p : P, ((sU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (s : F) / uniformizer C p.val ^ exponent p.val Is)
    (haU : ∀ p : P, ((aU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (a : F) / uniformizer C p.val ^ exponent p.val Ia)
    (hhU : ∀ p : P, ((hU p).val : LocalField p.val) =
      algebraMap F (LocalField p.val) (h : F) / uniformizer C p.val ^ exponent p.val Ih)
    (d : FiniteTransform.Residue A.R.toSubring s)
    (v : FiniteTransform.Residue A.R.toSubring a)
    (hc : FiniteTransform.residueMap A.R.toSubring s h =
      FiniteTransform.residueMap A.R.toSubring s a * d) :
    (Circle.coeHom.compAddChar A.fieldTraceCharacter)
      (((h : F) - (a : F) * ((FiniteTransform.canonicalLifts A.R.toSubring s).val d : F)) *
        ((FiniteTransform.canonicalLifts A.R.toSubring a).val v : F) /
        ((s : F) * (a : F))) =
      ∏ p : P, CompatiblePrimeRawLocal.rawPhase C p.val
        (exponent p.val Ia) (exponent p.val Is) (exponent p.val Ih)
        (sU p) (aU p) (hU p)
        (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val (exponent p.val Is) (Es d p))
        (CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val (exponent p.val Ia) (Ea v p)) := by
  classical
  set d' : A.R := (FiniteTransform.canonicalLifts A.R.toSubring s).val d with hd'def
  set v' : A.R := (FiniteTransform.canonicalLifts A.R.toSubring a).val v with hv'def
  let X : F := (((h : F) - (a : F) * (d' : F)) * (v' : F)) / ((s : F) * (a : F))
  change (Circle.coeHom.compAddChar A.fieldTraceCharacter) X = _
  have hx : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ A.Sf → (∀ p ∈ P, p.val ≠ w) →
      algebraMap F (w.adicCompletion F) X ∈ w.adicCompletionIntegers F := by
    intro w hw hwP
    have h := phase_integral_outside_support C Is Ia s a hs ha P hSupportS hSupportA
      ((h - a * d') * v') w hw hwP
    dsimp only [X]
    exact h
  have hfield := fieldTrace_eq_exterior_product hS P X hx
  change (Circle.coeHom (A.fieldTraceCharacter X)) = _
  rw [hfield, map_prod, ← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  set π := uniformizer C p.val with hπdef
  set H : LocalField p.val := algebraMap F (LocalField p.val) (h : F) with hHdef
  set A' : LocalField p.val := algebraMap F (LocalField p.val) (a : F) with hA'def
  set S : LocalField p.val := algebraMap F (LocalField p.val) (s : F) with hSdef
  set Dp : LocalField p.val := CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val
      (exponent p.val Is) (Es d p) with hDpdef
  set Vp : LocalField p.val := CompatiblePrimeRawLocal.canonicalLocalRepresentative C p.val
      (exponent p.val Ia) (Ea v p) with hVpdef
  set D'' : LocalField p.val := algebraMap F (LocalField p.val) (d' : F) with hD''def
  set V'' : LocalField p.val := algebraMap F (LocalField p.val) (v' : F) with hV''def
  have hπ : π ≠ 0 := by rw [hπdef]; exact uniformizer_ne_zero C p.val
  have hsU' : ((sU p).val : LocalField p.val) = S / π ^ exponent p.val Is := by
    rw [hsU p]
  have haU' : ((aU p).val : LocalField p.val) = A' / π ^ exponent p.val Ia := by
    rw [haU p]
  have hhU' : ((hU p).val : LocalField p.val) = H / π ^ exponent p.val Ih := by
    rw [hhU p]
  have hraw : CompatiblePrimeRawLocal.rawPhase C p.val (exponent p.val Ia) (exponent p.val Is)
      (exponent p.val Ih) (sU p) (aU p) (hU p) Dp Vp
      = (negativeTrace p.val ((H - A' * Dp) * Vp / (S * A')) : ℂ) := by
    have harg : (((hU p).val : LocalField p.val) * π ^ exponent p.val Ih -
          ((aU p).val : LocalField p.val) * π ^ exponent p.val Ia * Dp) * Vp /
          (((sU p).val : LocalField p.val) * ((aU p).val : LocalField p.val) *
            π ^ (exponent p.val Is + exponent p.val Ia))
        = (H - A' * Dp) * Vp / (S * A') := by
      rw [hsU', haU', hhU']
      rw [div_mul_cancel₀ _ (pow_ne_zero _ hπ)]
      rw [div_mul_cancel₀ _ (pow_ne_zero _ hπ)]
      have hden : (S / π ^ exponent p.val Is) * (A' / π ^ exponent p.val Ia) *
            π ^ (exponent p.val Is + exponent p.val Ia) = S * A' := by
        rw [div_mul_div_comm, ← pow_add, div_mul_cancel₀ _ (pow_ne_zero _ hπ)]
      rw [hden]
    simp only [CompatiblePrimeRawLocal.rawPhase]
    exact congrArg (fun z : LocalField p.val => (negativeTrace p.val z : ℂ)) harg
  rw [hraw]
  have hX : algebraMap F (LocalField p.val) X = (H - A' * D'') * V'' / (S * A') := by
    dsimp only [X]
    simp only [map_div₀, map_mul, map_sub]
    rfl
  rw [hX]
  have hEsd : Es d p = LocalFiniteSums.residueMap C p.val (exponent p.val Is) d' :=
    (congrArg (fun z => Es z p)
      ((FiniteTransform.canonicalLifts A.R.toSubring s).property d)).symm.trans (hEs d' p)
  have hEav : Ea v p = LocalFiniteSums.residueMap C p.val (exponent p.val Ia) v' :=
    (congrArg (fun z => Ea z p)
      ((FiniteTransform.canonicalLifts A.R.toSubring a).property v)).symm.trans (hEa v' p)
  obtain ⟨e, he⟩ : ∃ e : LocalIntegers p.val,
      Dp - D'' = π ^ exponent p.val Is * (e : LocalField p.val) :=
    congruent_of_residueMap_eq_generator C p.val (exponent p.val Is)
      ((lifts C p.val (exponent p.val Is)).val (Es d p)) d'
      (((lifts C p.val (exponent p.val Is)).property (Es d p)).trans hEsd)
  obtain ⟨w, hw⟩ : ∃ w : LocalIntegers p.val,
      Vp - V'' = π ^ exponent p.val Ia * (w : LocalField p.val) :=
    congruent_of_residueMap_eq_generator C p.val (exponent p.val Ia)
      ((lifts C p.val (exponent p.val Ia)).val (Ea v p)) v'
      (((lifts C p.val (exponent p.val Ia)).property (Ea v p)).trans hEav)
  obtain ⟨c, hc'⟩ : ∃ c : A.R, h - a * d' = s * c := by
    have hres : FiniteTransform.residueMap A.R.toSubring s (h - a * d') = 0 := by
      rw [map_sub, map_mul,
        (FiniteTransform.canonicalLifts A.R.toSubring s).property d, hc, sub_self]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hres)
  have hHAD : H - A' * D'' = S * (algebraMap F (LocalField p.val) (c : F)) := by
    have h1 := congrArg (fun z : A.R => algebraMap F (LocalField p.val) (z : F)) hc'
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, map_sub, map_mul] at h1
    exact h1
  have hA'mul : ((aU p).val : LocalField p.val) * π ^ exponent p.val Ia = A' := by
    rw [haU', div_mul_cancel₀ _ (pow_ne_zero _ hπ)]
  have hSmul : ((sU p).val : LocalField p.val) * π ^ exponent p.val Is = S := by
    rw [hsU', div_mul_cancel₀ _ (pow_ne_zero _ hπ)]
  have hZ : (H - A' * D'') * V'' / (S * A') - (H - A' * Dp) * Vp / (S * A')
      = -(algebraMap F (LocalField p.val) (c : F) * (w : LocalField p.val)) *
          ((aU p).val : LocalField p.val)⁻¹ +
        ((e : LocalField p.val) * Vp) * ((sU p).val : LocalField p.val)⁻¹ := by
    rw [← sub_div]
    have hnum : (H - A' * D'') * V'' - (H - A' * Dp) * Vp
        = -S * (algebraMap F (LocalField p.val) (c : F)) * π ^ exponent p.val Ia *
            (w : LocalField p.val) +
          A' * π ^ exponent p.val Is * (e : LocalField p.val) * Vp := by
      have h2 : H - A' * Dp =
          S * (algebraMap F (LocalField p.val) (c : F)) -
            A' * (π ^ exponent p.val Is * (e : LocalField p.val)) := by
        have h4 : H - A' * Dp = (H - A' * D'') - A' * (Dp - D'') := by ring
        rw [h4, hHAD, he]
      have h3 : V'' = Vp - π ^ exponent p.val Ia * (w : LocalField p.val) := by
        rw [← hw]; ring
      rw [hHAD, h2, h3]
      ring
    rw [hnum, ← hA'mul, ← hSmul]
    have haU0 : ((aU p).val : LocalField p.val) ≠ 0 := by
      intro h0; exact (aU p).ne_zero (Subtype.coe_injective h0)
    have hsU0 : ((sU p).val : LocalField p.val) ≠ 0 := by
      intro h0; exact (sU p).ne_zero (Subtype.coe_injective h0)
    field_simp [hπ, haU0, hsU0]
  have hdiff : (H - A' * D'') * V'' / (S * A') - (H - A' * Dp) * Vp / (S * A') ∈
      LocalIntegers p.val := by
    rw [hZ]
    have hCmem : algebraMap F (LocalField p.val) (c : F) ∈ LocalIntegers p.val :=
      CompatiblePrimeRawLocal.sInteger_local_integral p.val c
    have hwmem : (w : LocalField p.val) ∈ LocalIntegers p.val := w.2
    have hemem : (e : LocalField p.val) ∈ LocalIntegers p.val := e.2
    have hVpmem : Vp ∈ LocalIntegers p.val := by
      rw [hVpdef]
      exact CompatiblePrimeRawLocal.sInteger_local_integral p.val
        ((lifts C p.val (exponent p.val Ia)).val (Ea v p))
    exact add_mem (mul_mem (neg_mem (mul_mem hCmem hwmem)) (unit_val_inv_mem p.val (aU p)))
      (mul_mem (mul_mem hemem hVpmem) (unit_val_inv_mem p.val (sU p)))
  rw [negTrace_congr C p.val hdiff]
  rfl

end DedekindZetaZeroFree.MaskedPrimePowerCRTFactorization

end
