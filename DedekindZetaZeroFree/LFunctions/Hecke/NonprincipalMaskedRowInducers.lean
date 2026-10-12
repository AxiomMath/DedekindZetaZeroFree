module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.MaskedPrimitiveInducers
public import DedekindZetaZeroFree.LFunctions.Hecke.FiniteDeletedSeriesContinuation

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem exteriorPrime_notMem_Sf {A : SArithmeticData F}
    (p : LocalFiniteSums.ExteriorPrime A) : p.val ∉ A.Sf := by
  intro hp
  have h := (A.exterior_iff ⟨p.val.asIdeal, p.val.ne_bot⟩).mp p.property p.val hp
  exact p.val.isMaximal.ne_top (by simpa using h)

 def boundIdealRaw (A : SArithmeticData F)
    (p : ThetaBranch.ExteriorPrime A) (n : ℕ) : Ideal A.R where
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
    exact (mul_le_mul_of_nonneg_right (a.property p.val p.property) zero_le).trans (by simpa using hb)

private theorem order_eq_exponent (A : SArithmeticData F) (r : A.R)
    (I : A.Exterior) (hgen : A.Generates I r) (p : ThetaBranch.ExteriorPrime A) :
    ThetaBranch.order p.val (Units.mk0 (r : F) (by exact_mod_cast hgen.1)) =
      (idealPrimeExponent p.val.asIdeal I.val : ℤ) := by
  classical
  let n := idealPrimeExponent p.val.asIdeal I.val
  have hdvd (k : ℕ) : p.val.asIdeal ^ k ∣ I.val ↔ k ≤ n := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors p.val.irreducible I.property.1]
    simp [n, idealPrimeExponent]
  have hIn : I.val ≤ p.val.asIdeal ^ n := Ideal.dvd_iff_le.mp ((hdvd n).mpr le_rfl)
  have hnot : ¬ I.val ≤ p.val.asIdeal ^ (n + 1) := by
    rw [← Ideal.dvd_iff_le, hdvd]; omega
  have hmap : A.extendIdeal I ≤ boundIdealRaw A p n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change p.val.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))
    rw [p.val.valuation_of_algebraMap]
    exact (p.val.intValuation_le_pow_iff_mem a n).mpr (hIn ha)
  have hrv : p.val.valuation F (r : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply hmap
    rw [← hgen.2]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨a, ha, han⟩ : ∃ a : 𝓞 F, a ∈ I.val ∧ a ∉ p.val.asIdeal ^ (n + 1) := by
    contrapose! hnot
    exact hnot
  have ham : algebraMap (𝓞 F) A.R a ∈ Ideal.span ({r} : Set A.R) := by
    rw [hgen.2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ham
  have hav : p.val.valuation F (a : F) ≤ p.val.valuation F (r : F) := by
    have hh := congrArg (fun t : A.R => (t : F)) hy
    change (a : F) = (r : F) * (y : F) at hh
    rw [hh, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property p.val p.property) zero_le).trans (by simp)
  have hrv' : ¬ p.val.valuation F (r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro h
    apply han
    apply (p.val.intValuation_le_pow_iff_mem a (n + 1)).mp
    rw [← p.val.valuation_of_algebraMap (K := F)]
    exact hav.trans h
  have hnz : p.val.valuation F (r : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hgen.1 : (r : F) ≠ 0)
  rw [← WithZero.exp_log hnz, WithZero.exp_le_exp] at hrv hrv'
  change -WithZero.log (p.val.valuation F (r : F)) = (n : ℤ)
  push_cast at hrv'
  omega

 def recipeArithmeticContext (R : PrincipalMellin.ActualRecipe S η) :
    R.A.GeneralArithmeticContext R.σ R.target R.traceBad := by
  let A := R.A
  let D := R.probe.correction
  letI : Subsingleton (ClassGroup A.R) := R.classKilled
  have hl := ArithmeticContext.actual_hilbert_lagrangian_properties
    A R.classKilled D.H D.B D.H_actual D.B_complement
  exact {
    principal := A.principalIdealRing_of_classGroup_subsingleton R.classKilled
    classGroup_trivial := R.classKilled
    fractional_principal := fun I hI => exists_unit_of_isPrincipal I
      (ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI) hI.ne_zero
    unit_injective := A.unitQuotientClass_injective R.classKilled
    unit_image := A.unitQuotientClass_range
    correction := D
    units_lagrangian := hl.1
    primary_two := hl.2.1
    primary_three := hl.2.2
    reciprocity := ArithmeticContext.actual_hilbert_sextic_reciprocity
      A D.H D.B D.H_actual D.B_complement
    allowed_integral := fun I =>
      A.exists_allowed_integral_generator R.classKilled D.H D.B D.B_complement I
    allowed_unique := fun I a b ha hb =>
      A.allowed_generator_unique_mod_sixth R.classKilled D.H D.B D.B_complement I a b ha hb
    normOne_compact := ArithmeticContext.normOne_sixth_unit_quotient_compact A
    prime_target := fun I v hIv p hp a ha hap x hx =>
      D.prime_theta I v hIv p hp a ha hap x hx }

theorem actual_context_and_raw_frequencies
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
      (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A),
      R.probe.correction = C.correction ∧
      ∀ u : Frequency R, (U u).u = u.val.val := by
  classical
  have hU : ∀ u : Frequency R, ∃ U : AllRowEuler.InitialSeparation.RawFrequency R.A,
      U.u = u.val.val := by
    intro u
    let r : R.A.R := u.val.val
    have hr : r ≠ 0 := u.val.property
    let I : R.A.Exterior :=
      R.A.exteriorIdealEquiv.symm ⟨Ideal.span {r}, by simpa using hr⟩
    have hIgen : R.A.Generates I r := by
      refine ⟨hr, ?_⟩
      rw [← R.A.exteriorIdealEquiv_apply]
      exact (congrArg Subtype.val (R.A.exteriorIdealEquiv.apply_symm_apply
        ⟨Ideal.span {r}, by simpa using hr⟩)).symm
    refine ⟨⟨r, I, hIgen, ?_⟩, rfl⟩
    intro p
    have hpS : p.val ∉ R.A.Sf := exteriorPrime_notMem_Sf p
    have hrow : ThetaReflectionData.rowUnit R.A u.val =
        Units.mk0 (r : F) (by exact_mod_cast hIgen.1) := Units.ext rfl
    have h6 := (R.probe.frequencies.sixthFree u.val u.property ⟨p.val, hpS⟩).2
    rw [hrow, order_eq_exponent R.A r I hIgen ⟨p.val, hpS⟩] at h6
    simp only [Subtype.coe_mk] at h6
    omega
  choose U hUeq using hU
  exact ⟨recipeArithmeticContext R, U, rfl, hUeq⟩

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

open IsDedekindDomain

 def valuationIdeal (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) : Ideal A.R where
  carrier := {r | v.valuation F (r : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change v.valuation F ((x : F) + (y : F)) < 1
    exact (ValuationClass.map_add_le_max _ _ _).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro x y hy
    change v.valuation F ((x : F) * (y : F)) < 1
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (x.property v hv) zero_le).trans_lt (by simpa using hy)

private lemma residueCoefficient_eq_one (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (x : A.R)
    (h : AllRowEuler.UnitCovariance.residueCoefficient σ I x = 1) :
    A.sexticResidue I x = 1 := by
  have h2 := AllRowEuler.UnitCovariance.residueCoefficient_eq (A := A) (σ := σ) I x
  rw [h2] at h
  exact σ.injective (by simpa using h)

private lemma coprime_conductor_cofinite (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.asIdeal ⊔ m = ⊤ := by
  apply Filter.eventually_cofinite.mpr
  apply (Ideal.finite_factors hm).subset
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  apply Ideal.dvd_iff_le.mpr
  have hvmax : v.asIdeal.IsMaximal := v.isMaximal
  exact (hvmax.eq_of_le hv (show v.asIdeal ≤ v.asIdeal ⊔ m from le_sup_left)).symm ▸
    (show m ≤ v.asIdeal ⊔ m from le_sup_right)

private lemma sexticResidue_one_valuation (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) (x : A.R)
    (h : A.sexticResidue (ThetaBranch.primeIdeal A ⟨v, hv⟩) x = 1) :
    v.valuation F ((x : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1) < 1 := by
  set I := ThetaBranch.primeIdeal A ⟨v, hv⟩ with hIdef
  have hIval : I.val = v.asIdeal := rfl
  have h' : MulChar.ofUnitHom (A.sexticResidueFamily I)
      (Ideal.Quotient.mk (A.extendIdeal I) x) = 1 := h
  have hunit : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x) := by
    by_contra hx
    rw [MulChar.map_nonunit _ hx] at h'
    exact one_ne_zero h'.symm
  let q : (A.R ⧸ A.extendIdeal I)ˣ := hunit.unit
  have hq : ((A.sexticResidueFamily I) q : F) = 1 := by
    have hq' := h'
    rw [← hunit.unit_spec] at hq'
    rw [MulChar.ofUnitHom_coe] at hq'
    exact hq'
  obtain ⟨j, hj, he, hr⟩ := A.sexticResidueFamily_normalized.2.1 I v hIval q
  have hz : A.zeta12 ^ (2 * j) = 1 := by rw [← he, hq]
  have hz2 : IsPrimitiveRoot (A.zeta12 ^ 2) 6 :=
    A.primitive_zeta12.pow (by decide) (by decide : 12 = 2 * 6)
  have hj0 : j = 0 := by
    have h6 : 6 ∣ j := by
      apply (hz2.pow_eq_one_iff_dvd j).mp
      simpa [pow_mul] using hz
    omega
  have hcard : Nat.card (A.R ⧸ A.extendIdeal I) = Ideal.absNorm v.asIdeal := by
    rw [A.exteriorResidue_card I, hIval]
  have hq1 : q ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hcard]
    rw [hj0] at hr
    simp only [mul_zero, pow_zero, map_one] at hr
    exact hr.symm
  have hmk : Ideal.Quotient.mk (A.extendIdeal I)
      (x ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) = 1 := by
    have h1 := congrArg Units.val hq1
    rw [Units.val_pow_eq_pow_val, hunit.unit_spec, ← map_pow] at h1
    exact h1
  have hmem : x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1 ∈ A.extendIdeal I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hmk, map_one, sub_self]
  have hmap : A.extendIdeal I ≤ valuationIdeal A v hv := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change v.valuation F (((algebraMap (𝓞 F) A.R) a : A.R) : F) < 1
    have hcoe : (((algebraMap (𝓞 F) A.R) a : A.R) : F) = algebraMap (𝓞 F) F a := rfl
    rw [hcoe]
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr (hIval ▸ ha)
  have hval2 : v.valuation F
      ((x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1 : A.R) : F) < 1 :=
    hmap hmem
  simpa [map_sub, map_pow] using hval2

private lemma eventually_coefficient_of_principal
    (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A)
    (ν : Detector.PrimitiveFrequencyCharacter F) (hν : ν.character.IsPrincipal)
    (hcoeff : ∀ I : R.A.Exterior,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ U I =
        Detector.deletedPrimitiveIdealCoefficient F ν (rawDeletionSet U) I.val) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ (hv : v ∉ R.A.Sf),
        AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ U
          (ThetaBranch.primeIdeal R.A ⟨v, hv⟩) = 1 := by
  have hSf : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ R.A.Sf :=
    Filter.eventually_cofinite.mpr (by simpa using R.A.Sf.finite_toSet)
  have hcop : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.asIdeal ⊔ U.ideal.val = ⊤ :=
    coprime_conductor_cofinite U.ideal.val U.ideal.property.1
  have hcopc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.asIdeal ⊔ ν.conductor = ⊤ :=
    coprime_conductor_cofinite ν.conductor ν.conductor_ne_zero
  filter_upwards [hSf, hcop, hcopc] with v hvSf h1 h2
  intro hv
  have hdel : Detector.deletedPrimitiveIdealCoefficient F ν (rawDeletionSet U) v.asIdeal =
      ν.character v.asIdeal := by
    unfold Detector.deletedPrimitiveIdealCoefficient
    rw [if_neg]
    rintro ⟨w, hw, hle⟩
    simp only [rawDeletionSet, Set.mem_union, Set.mem_setOf_eq] at hw
    have hwv : w = v :=
      (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isMaximal.ne_top hle)).symm
    rw [hwv] at hw
    rcases hw with hwSf | hwU
    · exact hvSf hwSf
    · have hsup : v.asIdeal ⊔ U.ideal.val = v.asIdeal := sup_eq_left.mpr hwU
      rw [h1] at hsup
      exact v.isMaximal.ne_top hsup.symm
  rw [hcoeff (ThetaBranch.primeIdeal R.A ⟨v, hv⟩)]
  rw [show (ThetaBranch.primeIdeal R.A ⟨v, hv⟩).val = v.asIdeal from rfl, hdel]
  exact hν v.asIdeal v.ne_bot h2

private lemma eventually_coefficient_of_principal_target
    (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A)
    (ν : Detector.PrimitiveFrequencyCharacter F) (hν : ν.character.IsPrincipal)
    (hcoeff : ∀ I : R.A.Exterior,
      AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
        Detector.deletedPrimitiveIdealCoefficient F ν (rawDeletionSet U) I.val) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ (hv : v ∉ R.A.Sf),
        AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ U
          (ThetaBranch.primeIdeal R.A ⟨v, hv⟩) = 1 := by
  have hSf : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ R.A.Sf :=
    Filter.eventually_cofinite.mpr (by simpa using R.A.Sf.finite_toSet)
  have hcop : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.asIdeal ⊔ U.ideal.val = ⊤ :=
    coprime_conductor_cofinite U.ideal.val U.ideal.property.1
  have hcopc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.asIdeal ⊔ ν.conductor = ⊤ :=
    coprime_conductor_cofinite ν.conductor ν.conductor_ne_zero
  filter_upwards [hSf, hcop, hcopc] with v hvSf h1 h2
  intro hv
  have hdel : Detector.deletedPrimitiveIdealCoefficient F ν (rawDeletionSet U) v.asIdeal =
      ν.character v.asIdeal := by
    unfold Detector.deletedPrimitiveIdealCoefficient
    rw [if_neg]
    rintro ⟨w, hw, hle⟩
    simp only [rawDeletionSet, Set.mem_union, Set.mem_setOf_eq] at hw
    have hwv : w = v :=
      (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isMaximal.ne_top hle)).symm
    rw [hwv] at hw
    rcases hw with hwSf | hwU
    · exact hvSf hwSf
    · have hsup : v.asIdeal ⊔ U.ideal.val = v.asIdeal := sup_eq_left.mpr hwU
      rw [h1] at hsup
      exact v.isMaximal.ne_top hsup.symm
  have hmod' : ¬ R.A.modulus ≤ v.asIdeal := fun hle => hvSf (R.A.modulus_support v hle)
  have hmod : v.asIdeal ⊔ R.A.modulus = ⊤ :=
    v.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left (fun h => hmod' (h ▸ le_sup_right)))
  have htarget : R.target v.asIdeal = 1 := R.probe.principal v.asIdeal v.ne_bot hmod
  have hmain : R.target v.asIdeal *
      star (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ U
        (ThetaBranch.primeIdeal R.A ⟨v, hv⟩)) = 1 := by
    have hthis := hcoeff (ThetaBranch.primeIdeal R.A ⟨v, hv⟩)
    simp only [AllRowEuler.InitialSeparation.minusExteriorCoefficient] at hthis
    rw [show (ThetaBranch.primeIdeal R.A ⟨v, hv⟩).val = v.asIdeal from rfl, hdel,
      hν v.asIdeal v.ne_bot h2] at hthis
    exact hthis
  rw [htarget, one_mul] at hmain
  simpa using congrArg star hmain

private lemma nonprincipal_of_eventually
    (R : PrincipalMellin.ActualRecipe S η)
    (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : U.u = u.val.val) (hu : u ≠ principalFrequency R)
    (hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ (hv : v ∉ R.A.Sf),
        AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ U
          (ThetaBranch.primeIdeal R.A ⟨v, hv⟩) = 1) : False := by
  have hSf : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ R.A.Sf :=
    Filter.eventually_cofinite.mpr (by simpa using R.A.Sf.finite_toSet)
  have hev3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      v.valuation F ((U.u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1) < 1 := by
    filter_upwards [hSf, hev] with v hvSf hv
    have h1 : R.A.sexticResidue (ThetaBranch.primeIdeal R.A ⟨v, hvSf⟩) U.u = 1 :=
      residueCoefficient_eq_one R.A R.σ (ThetaBranch.primeIdeal R.A ⟨v, hvSf⟩) U.u (hv hvSf)
    exact sexticResidue_one_valuation R.A v hvSf U.u h1
  have hne : (U.u : F) ≠ 0 := fun h => U.generates.1 (ZeroMemClass.coe_eq_zero.mp h)
  obtain ⟨x, hx⟩ := Detector.FrequencyDetection.global_power_of_cofinite_residue (6 : ℕ+)
    R.A.primitive_sixth_root (Units.mk0 (U.u : F) hne) (by
      filter_upwards [hev3] with v hv
      simpa using hv)
  have hx6 : (x : F) ^ 6 = (U.u : F) := by
    have hh := congrArg Units.val hx
    simpa using hh
  have hbrow : Units.mk0 (U.u : F) hne = ThetaReflectionData.rowUnit R.A u.val := by
    apply Units.ext
    simp only [Units.val_mk0, ThetaReflectionData.rowUnit]
    rw [hU]
  have hxU : x ∈ R.A.U := by
    intro v hv
    have hord : ThetaBranch.order v (ThetaReflectionData.rowUnit R.A u.val) =
        6 * ThetaBranch.order v x := by
      rw [← hbrow, show Units.mk0 (U.u : F) hne = x ^ 6 from hx.symm]
      unfold ThetaBranch.order
      rw [Units.val_pow_eq_pow_val, map_pow, WithZero.log_pow]
      ring
    have h0 : 0 ≤ ThetaBranch.order v (ThetaReflectionData.rowUnit R.A u.val) := by
      simpa using (R.probe.frequencies.sixthFree u.val u.property ⟨v, hv⟩).1
    have hlt : ThetaBranch.order v (ThetaReflectionData.rowUnit R.A u.val) < 6 := by
      simpa using (R.probe.frequencies.sixthFree u.val u.property ⟨v, hv⟩).2
    have hox : ThetaBranch.order v x = 0 := by omega
    have hlog : WithZero.log (v.valuation F (x : F)) = 0 := by
      have hh := hox
      unfold ThetaBranch.order at hh
      linarith
    have hxn : v.valuation F (x : F) ≠ 0 := (map_ne_zero (v.valuation F)).mpr x.ne_zero
    rw [← WithZero.exp_log hxn, hlog, WithZero.exp_zero]
  let x0 : R.A.U := ⟨x, hxU⟩
  let I0 : R.A.Exterior := ExteriorIdealEuler.one R.A.cS
  obtain ⟨r, hgenr, hgencoe⟩ := R.probe.allowed.generates I0
  have hrunit : IsUnit r := by
    rw [← Ideal.span_singleton_eq_top]
    rw [hgenr.2]
    simp [SArithmeticData.extendIdeal, I0, ExteriorIdealEuler.one, Ideal.map_top]
  let gU : R.A.U := R.A.unitEquiv.symm hrunit.unit
  have hgU : ((gU : R.A.U) : Fˣ) = R.probe.allowed.generator I0 := by
    apply Units.ext
    rw [hgencoe]
    simp [gU, SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
  obtain ⟨w, hw, huniqw⟩ := R.probe.frequencies.factorization u.val
  have hpv : ThetaReflectionData.rowUnit R.A (principalFrequency R).val = 1 := by
    apply Units.ext
    simp [ThetaReflectionData.rowUnit, principalFrequency]
  have hA : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A u.val =
      ThetaReflectionData.rowUnit R.A (principalFrequency R).val *
        R.probe.allowed.generator I0 ^ 6 * γ.val ^ 6 := by
    refine ⟨x0 * gU⁻¹, ?_⟩
    have hcoe : (((x0 * gU⁻¹ : R.A.U)) : Fˣ) = x * ((gU : R.A.U) : Fˣ)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [hpv, hcoe, hgU, hbrow.symm, ← show x ^ 6 = Units.mk0 (U.u : F) hne from hx]
    rw [one_mul, mul_pow, inv_pow, ← mul_assoc,
      mul_comm (R.probe.allowed.generator I0 ^ 6) (x ^ 6), mul_assoc, mul_inv_cancel, mul_one]
  have hB : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A u.val =
      ThetaReflectionData.rowUnit R.A u.val *
        R.probe.allowed.generator I0 ^ 6 * γ.val ^ 6 := by
    refine ⟨gU⁻¹, ?_⟩
    have hcoe : (((gU⁻¹ : R.A.U)) : Fˣ) = ((gU : R.A.U) : Fˣ)⁻¹ := by
      simp only [Subgroup.coe_inv]
    rw [hcoe, hgU, inv_pow, mul_assoc, mul_inv_cancel, mul_one]
  have h1 := huniqw (u, I0) hB
  have h2 := huniqw (principalFrequency R, I0) hA
  have heq : u = principalFrequency R := congrArg Prod.fst (h1.trans h2.symm)
  exact hu heq

theorem actual_raw_inducers_nonprincipal
    (R : PrincipalMellin.ActualRecipe S η)
    (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : U.u = u.val.val) (hu : u ≠ principalFrequency R)
    (P M : Detector.PrimitiveFrequencyCharacter F)
    (hP : ∀ I : R.A.Exterior,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ U I =
        Detector.deletedPrimitiveIdealCoefficient F P (rawDeletionSet U) I.val)
    (hM : ∀ I : R.A.Exterior,
      AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
        Detector.deletedPrimitiveIdealCoefficient F M (rawDeletionSet U) I.val) :
    ¬ P.character.IsPrincipal ∧ ¬ M.character.IsPrincipal := by
  refine ⟨fun hp => ?_, fun hm => ?_⟩
  · exact nonprincipal_of_eventually R u U hU hu
      (eventually_coefficient_of_principal R U P hp hP)
  · exact nonprincipal_of_eventually R u U hU hu
      (eventually_coefficient_of_principal_target R U M hm hM)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_raw_hecke_rows
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
      (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
      (plus minus : Frequency R → ℂ → ℂ),
      R.probe.correction = C.correction ∧
      (∀ u : Frequency R, (U u).u = u.val.val) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R →
        DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re}) ∧
      (∀ u : Frequency R, u ≠ principalFrequency R →
        DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re}) ∧
      (∀ (u : Frequency R) (s : ℂ), 1 < s.re →
        plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s) ∧
      (∀ (u : Frequency R) (s : ℂ), 1 < s.re →
        minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s) := by
  obtain ⟨C, U, hC, hU⟩ := RawHeckeRows.actual_context_and_raw_frequencies R
  obtain ⟨P, M, hfinite, hP, hM⟩ :=
    RawHeckeRows.actual_raw_masked_inducers R C hC U hU
  have hSD (u : Frequency R) :
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆
        RawHeckeRows.rawDeletionSet (U u) :=
    Set.subset_union_left
  have hplus (u : Frequency R) :=
    RawHeckeRows.deleted_exterior_series_continuation R.A (P u)
      (RawHeckeRows.rawDeletionSet (U u)) (hfinite u) (hSD u)
      (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u)) (hP u)
  have hminus (u : Frequency R) :=
    RawHeckeRows.deleted_exterior_series_continuation R.A (M u)
      (RawHeckeRows.rawDeletionSet (U u)) (hfinite u) (hSD u)
      (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u)) (hM u)
  choose plus hpDiff hpEq using hplus
  choose minus hmDiff hmEq using hminus
  refine ⟨C, U, plus, minus, hC, hU, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact hpDiff u (RawHeckeRows.actual_raw_inducers_nonprincipal
      R u (U u) (hU u) hu (P u) (M u) (hP u) (hM u)).1
  · intro u hu
    exact hmDiff u (RawHeckeRows.actual_raw_inducers_nonprincipal
      R u (U u) (hU u) hu (P u) (M u) (hP u) (hM u)).2
  · intro u s hs
    exact hpEq u s hs
  · intro u s hs
    exact hmEq u s hs

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
