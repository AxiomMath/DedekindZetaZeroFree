module

public import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators
public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData

@[expose] public section

open scoped NumberField nonZeroDivisors Classical

namespace DedekindZetaZeroFree
noncomputable section

namespace GeneratorInvariance

def transportCharacter {T : Type*} [CommRing T] (I J : Ideal T)
    (h : I = J) (χ : MulChar (T ⧸ I) ℂ) : MulChar (T ⧸ J) ℂ :=
  h ▸ χ

 def quotientEq {T : Type*} [CommRing T] (I J : Ideal T)
    (h : I = J) : T ⧸ I ≃+* T ⧸ J := h ▸ RingEquiv.refl _

private theorem quotientEq_mk {T : Type*} [CommRing T] (I J : Ideal T)
    (h : I = J) (x : T) :
    quotientEq I J h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x := by
  subst J
  rfl

private theorem transport_apply {T : Type*} [CommRing T] (I J : Ideal T)
    (h : I = J) (χ : MulChar (T ⧸ I) ℂ) (x : T ⧸ I) :
    transportCharacter I J h χ (quotientEq I J h x) = χ x := by
  subst J
  rfl

private theorem sixth_character {T : Type*} [CommRing T]
    (χ : MulChar T ℂ) (hχ : χ ^ 6 = 1) (u : Tˣ) :
    χ ((u ^ 6 : Tˣ) : T) = 1 := by
  rw [Units.val_pow_eq_pow_val, map_pow, ← χ.pow_apply_coe 6 u, hχ,
    MulChar.one_apply_coe]

variable {K : Type*} [Field K]

theorem finiteCoefficient_first_sixth_unit (R : Subring K) (s a h : R)
    (hs : s ≠ 0) (ha : a ≠ 0) (ε : Rˣ)
    [Fintype (FiniteTransform.Residue R s)]
    [Fintype (FiniteTransform.Residue R a)]
    [Fintype (FiniteTransform.Residue R (((ε ^ 6 : Rˣ) : R) * s))]
    (χs : MulChar (FiniteTransform.Residue R s) ℂ)
    (χa : MulChar (FiniteTransform.Residue R a) ℂ)
    (hχs : χs ^ 6 = 1) (hχa : χa ^ 6 = 1)
    (e : AddChar K ℂ) (he : FiniteTransform.IsTrivialOn R e) :
    FiniteTransform.finiteCoefficient R (((ε ^ 6 : Rˣ) : R) * s) a h
      (transportCharacter _ _
        (Ideal.span_singleton_mul_left_unit (ε ^ 6).isUnit s).symm χs) χa e =
      FiniteTransform.finiteCoefficient R s a h χs χa e := by
  let c := ε ^ 6
  let E := quotientEq _ _ (Ideal.span_singleton_mul_left_unit c.isUnit s).symm
  let ca : (FiniteTransform.Residue R a)ˣ :=
    Units.map (FiniteTransform.residueMap R a).toMonoidHom c
  let ds : FiniteTransform.ResidueLifts R ((c : R) * s) :=
    ⟨fun d => (FiniteTransform.canonicalLifts R s).val (E.symm d), by
      intro d
      change Ideal.Quotient.mk _ _ = d
      rw [← quotientEq_mk _ _ (Ideal.span_singleton_mul_left_unit c.isUnit s).symm]
      change E (FiniteTransform.residueMap R s
        ((FiniteTransform.canonicalLifts R s).val (E.symm d))) = d
      rw [(FiniteTransform.canonicalLifts R s).property, E.apply_symm_apply]⟩
  let va : FiniteTransform.ResidueLifts R a :=
    ⟨fun v => (c : R) * (FiniteTransform.canonicalLifts R a).val (ca.mulLeft.symm v), by
      intro v
      rw [map_mul, (FiniteTransform.canonicalLifts R a).property]
      exact ca.mulLeft.apply_symm_apply v⟩
  rw [← FiniteTransform.finiteCoefficient_lifts_independent R _ a h
    (mul_ne_zero c.ne_zero hs) ha _ χa e he ds va]
  unfold FiniteTransform.finiteCoefficient FiniteTransform.finiteCoefficientWithLifts
  symm
  apply Fintype.sum_equiv E.toEquiv
  intro d
  simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
  have hm (x : R) : FiniteTransform.residueMap R ((c : R) * s) x =
      E (FiniteTransform.residueMap R s x) :=
    (quotientEq_mk _ _ (Ideal.span_singleton_mul_left_unit c.isUnit s).symm x).symm
  have hc : FiniteTransform.residueMap R ((c : R) * s) h =
      FiniteTransform.residueMap R ((c : R) * s) a * E d ↔
      FiniteTransform.residueMap R s h = FiniteTransform.residueMap R s a * d := by
    rw [hm, hm, ← map_mul]
    exact E.injective.eq_iff
  by_cases hd : FiniteTransform.residueMap R s h = FiniteTransform.residueMap R s a * d
  · rw [if_pos hd, if_pos (hc.mpr hd)]
    rw [transport_apply]
    congr 1
    apply Fintype.sum_equiv ca.mulLeft
    intro v
    have hca : χa (ca : FiniteTransform.Residue R a) = 1 := by
      have H := sixth_character χa hχa
        (Units.map (FiniteTransform.residueMap R a).toMonoidHom ε)
      simpa only [ca, c, map_pow] using H
    change χa v * e _ = χa ((ca : FiniteTransform.Residue R a) * v) * e _
    rw [map_mul, hca, one_mul]
    congr 1
    apply congrArg e
    change _ = (((h : K) - (a : K) *
      ((FiniteTransform.canonicalLifts R s).val (E.symm (E d)) : K)) *
      (((c : R) * (FiniteTransform.canonicalLifts R a).val
        (ca.mulLeft.symm (ca.mulLeft v)) : R) : K) /
      ((((c : R) * s : R) : K) * (a : K)))
    rw [E.symm_apply_apply, ca.mulLeft.symm_apply_apply]
    push_cast
    have hc0 : ((c : R) : K) ≠ 0 := by exact_mod_cast c.ne_zero
    field_simp
    <;> ring
  · rw [if_neg hd, if_neg (fun hn => hd (hc.mp hn))]

theorem finiteCoefficient_second_sixth_unit (R : Subring K) (s a h : R)
    (hs : s ≠ 0) (ha : a ≠ 0) (ε : Rˣ)
    [Fintype (FiniteTransform.Residue R s)]
    [Fintype (FiniteTransform.Residue R a)]
    [Fintype (FiniteTransform.Residue R (((ε ^ 6 : Rˣ) : R) * a))]
    (χs : MulChar (FiniteTransform.Residue R s) ℂ)
    (χa : MulChar (FiniteTransform.Residue R a) ℂ)
    (hχs : χs ^ 6 = 1) (hχa : χa ^ 6 = 1)
    (e : AddChar K ℂ) (he : FiniteTransform.IsTrivialOn R e) :
    FiniteTransform.finiteCoefficient R s (((ε ^ 6 : Rˣ) : R) * a) h χs
      (transportCharacter _ _
        (Ideal.span_singleton_mul_left_unit (ε ^ 6).isUnit a).symm χa) e =
      FiniteTransform.finiteCoefficient R s a h χs χa e := by
  let c := ε ^ 6
  let E := quotientEq _ _ (Ideal.span_singleton_mul_left_unit c.isUnit a).symm
  let cs : (FiniteTransform.Residue R s)ˣ :=
    Units.map (FiniteTransform.residueMap R s).toMonoidHom c⁻¹
  let ca : (FiniteTransform.Residue R a)ˣ :=
    Units.map (FiniteTransform.residueMap R a).toMonoidHom c
  let ds : FiniteTransform.ResidueLifts R s :=
    ⟨fun d => ((c⁻¹ : Rˣ) : R) *
      (FiniteTransform.canonicalLifts R s).val (cs.mulLeft.symm d), by
      intro d
      rw [map_mul, (FiniteTransform.canonicalLifts R s).property]
      exact cs.mulLeft.apply_symm_apply d⟩
  let va : FiniteTransform.ResidueLifts R ((c : R) * a) :=
    ⟨fun v => (c : R) * (FiniteTransform.canonicalLifts R a).val
      (ca.mulLeft.symm (E.symm v)), by
      intro v
      change Ideal.Quotient.mk _ _ = v
      rw [← quotientEq_mk _ _ (Ideal.span_singleton_mul_left_unit c.isUnit a).symm]
      change E (FiniteTransform.residueMap R a ((c : R) * _)) = v
      rw [map_mul, (FiniteTransform.canonicalLifts R a).property]
      change E (ca.mulLeft (ca.mulLeft.symm (E.symm v))) = v
      rw [ca.mulLeft.apply_symm_apply, E.apply_symm_apply]⟩
  rw [← FiniteTransform.finiteCoefficient_lifts_independent R s _ h hs
    (mul_ne_zero c.ne_zero ha) χs _ e he ds va]
  unfold FiniteTransform.finiteCoefficient FiniteTransform.finiteCoefficientWithLifts
  symm
  apply Fintype.sum_equiv cs.mulLeft
  intro d
  have hc : FiniteTransform.residueMap R s h =
      FiniteTransform.residueMap R s ((c : R) * a) * cs.mulLeft d ↔
      FiniteTransform.residueMap R s h = FiniteTransform.residueMap R s a * d := by
    simp only [map_mul, Units.mulLeft_apply]
    have hi : FiniteTransform.residueMap R s (c : R) *
        (cs : FiniteTransform.Residue R s) = 1 := by
      change FiniteTransform.residueMap R s (c : R) *
        FiniteTransform.residueMap R s ((c⁻¹ : Rˣ) : R) = 1
      rw [← map_mul, c.mul_inv, map_one]
    rw [mul_mul_mul_comm, hi, one_mul]
  by_cases hd : FiniteTransform.residueMap R s h = FiniteTransform.residueMap R s a * d
  · rw [if_pos hd, if_pos (hc.mpr hd)]
    have hcs : χs (cs : FiniteTransform.Residue R s) = 1 := by
      have H := sixth_character χs hχs
        (Units.map (FiniteTransform.residueMap R s).toMonoidHom ε⁻¹)
      simpa only [cs, c, map_inv, map_pow, inv_pow] using H
    simp only [Units.mulLeft_apply, map_mul, hcs, one_mul]
    congr 1
    apply Fintype.sum_equiv (ca.mulLeft.trans E.toEquiv)
    intro v
    simp only [Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
    rw [transport_apply]
    have hca : χa (ca : FiniteTransform.Residue R a) = 1 := by
      have H := sixth_character χa hχa
        (Units.map (FiniteTransform.residueMap R a).toMonoidHom ε)
      simpa only [ca, c, map_pow] using H
    simp only [Units.mulLeft_apply, map_mul, hca, one_mul]
    congr 1
    apply congrArg e
    rw [← E.map_mul]
    change _ = (((h : K) - (((c : R) * a : R) : K) *
      ((((c⁻¹ : Rˣ) : R) * (FiniteTransform.canonicalLifts R s).val
        (cs.mulLeft.symm (cs.mulLeft d)) : R) : K)) *
      (((c : R) * (FiniteTransform.canonicalLifts R a).val
        (ca.mulLeft.symm (E.symm (E (ca.mulLeft v)))) : R) : K) /
      ((s : K) * (((c : R) * a : R) : K)))
    rw [cs.mulLeft.symm_apply_apply, E.symm_apply_apply, ca.mulLeft.symm_apply_apply]
    push_cast
    have hi : ((c : R) : K) * (((c⁻¹ : Rˣ) : R) : K) = 1 := by
      exact_mod_cast c.mul_inv
    have hc0 : ((c : R) : K) ≠ 0 := by exact_mod_cast c.ne_zero
    have hs0 : (s : K) ≠ 0 := by exact_mod_cast hs
    have ha0 : (a : K) ≠ 0 := by exact_mod_cast ha
    field_simp
    linear_combination ((a : K) *
      ((FiniteTransform.canonicalLifts R s).val d : K) *
      ((FiniteTransform.canonicalLifts R a).val v : K)) * hi
  · rw [if_neg hd, if_neg (fun hn => hd (hc.mp hn))]

variable {F : Type} [Field F] [NumberField F]

def HasCompatibleCharacters (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) : Prop :=
  FiniteTransform.IsTrivialOn A.R.toSubring D.additiveCharacter ∧
  (∀ (a : A.R), a ≠ 0 → D.character a ^ 6 = 1) ∧
  (∀ (a b : A.R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Ideal.span ({a} : Set A.R) = Ideal.span {b}),
      D.character b = transportCharacter _ _ hab (D.character a))

def coefficient (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (s a h : A.R) (hs : s ≠ 0) (ha : a ≠ 0) : ℂ := by
  letI := D.finiteResidue s hs
  letI := D.finiteResidue a ha
  exact FiniteTransform.finiteCoefficient A.R.toSubring s a h
    (D.character s) (D.character a) D.additiveCharacter

theorem coefficient_sixth_sUnit_invariant (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (hD : HasCompatibleCharacters A D)
    (s a h : A.R) (hs : s ≠ 0) (ha : a ≠ 0) (ε : A.U) :
    let v : A.Rˣ := A.unitEquiv ε ^ 6
    coefficient A D ((v : A.R) * s) a h (mul_ne_zero v.ne_zero hs) ha =
        coefficient A D s a h hs ha ∧
    coefficient A D s ((v : A.R) * a) h hs (mul_ne_zero v.ne_zero ha) =
        coefficient A D s a h hs ha ∧
    coefficient A D s a ((v : A.R) * h) hs ha =
        coefficient A D s a h hs ha := by
  dsimp only
  let v : A.Rˣ := A.unitEquiv ε ^ 6
  letI := D.finiteResidue s hs
  letI := D.finiteResidue a ha
  letI := D.finiteResidue ((v : A.R) * s) (mul_ne_zero v.ne_zero hs)
  letI := D.finiteResidue ((v : A.R) * a) (mul_ne_zero v.ne_zero ha)
  have cs := hD.2.2 s ((v : A.R) * s) hs (mul_ne_zero v.ne_zero hs)
    (Ideal.span_singleton_mul_left_unit v.isUnit s).symm
  have ca := hD.2.2 a ((v : A.R) * a) ha (mul_ne_zero v.ne_zero ha)
    (Ideal.span_singleton_mul_left_unit v.isUnit a).symm
  unfold coefficient
  refine ⟨?_, ?_, ?_⟩
  · rw [cs]
    exact finiteCoefficient_first_sixth_unit A.R.toSubring s a h hs ha
      (A.unitEquiv ε) (D.character s) (D.character a) (hD.2.1 s hs)
      (hD.2.1 a ha) D.additiveCharacter hD.1
  · rw [ca]
    exact finiteCoefficient_second_sixth_unit A.R.toSubring s a h hs ha
      (A.unitEquiv ε) (D.character s) (D.character a) (hD.2.1 s hs)
      (hD.2.1 a ha) D.additiveCharacter hD.1
  · exact FiniteTransform.finiteCoefficient_sixth_unit_invariant A.R.toSubring
      s a h hs ha (D.character s) (D.character a) (hD.2.1 s hs)
      (hD.2.1 a ha) D.additiveCharacter hD.1 (A.unitEquiv ε)

theorem coefficient_eq_comparison (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n s : A.Exterior) (h : A.R) :
    coefficient A D (D.generator s) (D.generator c.val * D.generator n ^ 3) h
      (D.generates s).1
      (mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)) =
      comparisonPoissonFiniteCoefficient F A D c n s h := by
  rfl

private theorem allowed_translate (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (I : A.Exterior) (r r' : A.R) (hr : A.Generates I r) (hr' : A.Generates I r')
    (a a' : Fˣ) (ha : (a : F) = (r : F)) (ha' : (a' : F) = (r' : F))
    (hal : A.IsAllowed B a) (hal' : A.IsAllowed B a') :
    ∃ ε : A.U, r' = (((A.unitEquiv ε ^ 6 : A.Rˣ) : A.R) * r) := by
  have heq : FractionalIdeal.spanSingleton A.R⁰ (a' : F) =
      FractionalIdeal.spanSingleton A.R⁰ (a : F) := by
    rw [ha, ha']
    change FractionalIdeal.spanSingleton A.R⁰ (algebraMap A.R F r') =
      FractionalIdeal.spanSingleton A.R⁰ (algebraMap A.R F r)
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_span_singleton, hr'.2, hr.2]
  have hmem := A.allowed_generator_unique_mod_sixth hCl H B hB
    (FractionalIdeal.spanSingleton A.R⁰ (a : F)) a' a ⟨heq.symm, hal'⟩ ⟨rfl, hal⟩
  obtain ⟨ε, hε, he⟩ := hmem
  refine ⟨⟨ε, hε⟩, ?_⟩
  have hv : (ε : F) ^ 6 * (a : F) = (a' : F) := by
    have hh := congrArg (fun x : Fˣ => (x : F)) he
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val] at hh
    exact (eq_div_iff a.ne_zero).mp hh
  apply Subtype.ext
  change (r' : F) = _
  rw [← ha']
  exact hv.symm.trans (by rw [ha]; rfl)

theorem coefficient_allowed_generator_replacement (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (hD : HasCompatibleCharacters A D)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (hB : A.IsSUnitIsotropicComplement H B)
    (Ic In Is Ir : A.Exterior) (c n s r c' n' s' r' u : A.R)
    (hc : A.Generates Ic c) (hn : A.Generates In n)
    (hs : A.Generates Is s) (hr : A.Generates Ir r)
    (hc' : A.Generates Ic c') (hn' : A.Generates In n')
    (hs' : A.Generates Is s') (hr' : A.Generates Ir r')
    (ac an as_ ar ac' an' as' ar' : Fˣ)
    (hac : (ac : F) = (c : F)) (han : (an : F) = (n : F))
    (has : (as_ : F) = (s : F)) (har : (ar : F) = (r : F))
    (hac' : (ac' : F) = (c' : F)) (han' : (an' : F) = (n' : F))
    (has' : (as' : F) = (s' : F)) (har' : (ar' : F) = (r' : F))
    (hallowed : A.IsAllowed B ac ∧ A.IsAllowed B an ∧
      A.IsAllowed B as_ ∧ A.IsAllowed B ar)
    (hallowed' : A.IsAllowed B ac' ∧ A.IsAllowed B an' ∧
      A.IsAllowed B as' ∧ A.IsAllowed B ar') :
    coefficient A D s' (c' * n' ^ 3) (u * r' ^ 6) hs'.1
        (mul_ne_zero hc'.1 (pow_ne_zero _ hn'.1)) =
      coefficient A D s (c * n ^ 3) (u * r ^ 6) hs.1
        (mul_ne_zero hc.1 (pow_ne_zero _ hn.1)) := by
  obtain ⟨εc, ec⟩ := allowed_translate A hCl H B hB Ic c c' hc hc'
    ac ac' hac hac' hallowed.1 hallowed'.1
  obtain ⟨εn, en⟩ := allowed_translate A hCl H B hB In n n' hn hn'
    an an' han han' hallowed.2.1 hallowed'.2.1
  obtain ⟨εs, es⟩ := allowed_translate A hCl H B hB Is s s' hs hs'
    as_ as' has has' hallowed.2.2.1 hallowed'.2.2.1
  obtain ⟨εr, er⟩ := allowed_translate A hCl H B hB Ir r r' hr hr'
    ar ar' har har' hallowed.2.2.2 hallowed'.2.2.2
  have ea : c' * n' ^ 3 =
      (((A.unitEquiv (εc * εn ^ 3) ^ 6 : A.Rˣ) : A.R) * (c * n ^ 3)) := by
    rw [ec, en]
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have eh : u * r' ^ 6 =
      (((A.unitEquiv (εr ^ 6) ^ 6 : A.Rˣ) : A.R) * (u * r ^ 6)) := by
    rw [er]
    simp only [map_pow, Units.val_pow_eq_pow_val]
    ring
  have hanon : c * n ^ 3 ≠ 0 := mul_ne_zero hc.1 (pow_ne_zero _ hn.1)
  have hsnon : (((A.unitEquiv εs ^ 6 : A.Rˣ) : A.R) * s) ≠ 0 :=
    mul_ne_zero (A.unitEquiv εs ^ 6).ne_zero hs.1
  have e1 := (coefficient_sixth_sUnit_invariant A D hD s (c' * n' ^ 3)
    (u * r' ^ 6) hs.1 (mul_ne_zero hc'.1 (pow_ne_zero _ hn'.1)) εs).1
  have e2 := (coefficient_sixth_sUnit_invariant A D hD s (c * n ^ 3)
    (u * r' ^ 6) hs.1 hanon (εc * εn ^ 3)).2.1
  have e3 := (coefficient_sixth_sUnit_invariant A D hD s (c * n ^ 3)
    (u * r ^ 6) hs.1 hanon (εr ^ 6)).2.2
  have e1' : coefficient A D s' (c' * n' ^ 3) (u * r' ^ 6) hs'.1
      (mul_ne_zero hc'.1 (pow_ne_zero _ hn'.1)) =
      coefficient A D s (c' * n' ^ 3) (u * r' ^ 6) hs.1
        (mul_ne_zero hc'.1 (pow_ne_zero _ hn'.1)) := by
    simpa only [← es] using e1
  have e2' : coefficient A D s (c' * n' ^ 3) (u * r' ^ 6) hs.1
      (mul_ne_zero hc'.1 (pow_ne_zero _ hn'.1)) =
      coefficient A D s (c * n ^ 3) (u * r' ^ 6) hs.1 hanon := by
    simpa only [← ea] using e2
  have e3' : coefficient A D s (c * n ^ 3) (u * r' ^ 6) hs.1 hanon =
      coefficient A D s (c * n ^ 3) (u * r ^ 6) hs.1 hanon := by
    simpa only [← eh] using e3
  exact e1'.trans (e2'.trans e3')

end GeneratorInvariance
end
end DedekindZetaZeroFree
