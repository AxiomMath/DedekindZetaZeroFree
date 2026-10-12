module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

noncomputable section

namespace ClassKillProof
variable (F : Type) [Field F] [NumberField F]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
 abbrev extHom : FractionalIdeal (𝓞 F)⁰ F →+* FractionalIdeal (S.integer F)⁰ F :=
  FractionalIdeal.extendedHom (K := F) F (S.integer F)
private lemma map_id : IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 F) (S.integer F)) = RingHom.id F := by
  apply IsLocalization.ringHom_ext (𝓞 F)⁰
  ext a
  simp [IsFractionRing.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply]
private lemma ext_span (x : F) : extHom F S (FractionalIdeal.spanSingleton (𝓞 F)⁰ x) =
    FractionalIdeal.spanSingleton (S.integer F)⁰ x := by
  rw [extHom, FractionalIdeal.extendedHom_spanSingleton, map_id]
  rfl
private lemma ext_coe (I : FractionalIdeal (𝓞 F)⁰ F) :
    (extHom F S I : Submodule (S.integer F) F) = Submodule.span (S.integer F) (I : Set F) := by
  simp only [extHom, FractionalIdeal.extendedHom, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.coe_extended_eq_span]
  change Submodule.span (S.integer F) ((IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 F) (S.integer F))) '' (I : Set F)) = _
  rw [map_id]
  simp
private lemma same_class (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (h : ClassGroup.mk F I = ClassGroup.mk F J) :
    ∃ x : Fˣ, I * toPrincipalIdeal (𝓞 F) F x = J := by
  have h' := congrArg (ClassGroup.equiv F) h
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl] at h'
  change (QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range) I =
    (QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range) J at h'
  rw [QuotientGroup.mk'_eq_mk'] at h'
  rcases h' with ⟨z, hz, h⟩
  rcases hz with ⟨x, rfl⟩
  exact ⟨x, h⟩
private lemma descent (I : FractionalIdeal (S.integer F)⁰ F) (hI : IsUnit I) :
    ∃ J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, extHom F S J = I := by
  classical
  obtain ⟨s, hs⟩ := I.fg_of_isUnit hI
  let J := FractionalIdeal.spanFinset (𝓞 F) s id
  have hext : extHom F S J = I := by
    apply FractionalIdeal.coeToSubmodule_injective
    change (extHom F S J : Submodule (S.integer F) F) = (I : Submodule (S.integer F) F)
    rw [ext_coe]
    change Submodule.span (S.integer F) (Submodule.span (𝓞 F) ((id : F → F) '' (s : Set F)) : Set F) = _
    rw [Submodule.span_span_of_tower]
    simpa using hs
  have hJ : J ≠ 0 := by
    intro h
    rw [h, map_zero] at hext
    exact hI.ne_zero hext.symm
  exact ⟨Units.mk0 J hJ, hext⟩
private lemma inv_mem (a : 𝓞 F) (hS : ∀ v : HeightOneSpectrum (𝓞 F), a ∈ v.asIdeal → v ∈ S) :
    (algebraMap (𝓞 F) F a)⁻¹ ∈ S.integer F := by
  intro v hv
  have h : v.valuation F (algebraMap (𝓞 F) F a) = 1 :=
    (v.valuation_eq_one_iff_notMem).mpr (fun ha => hv (hS v ha))
  simp [map_inv₀, h]
private lemma kill (J : Ideal (𝓞 F)) (a : 𝓞 F) (ha : a ∈ J) (ha0 : a ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), a ∈ v.asIdeal → v ∈ S) :
    extHom F S (J : FractionalIdeal (𝓞 F)⁰ F) = 1 := by
  apply le_antisymm
  · exact FractionalIdeal.extended_le_one_of_le_one _ _ _ FractionalIdeal.coeIdeal_le_one
  · rw [FractionalIdeal.one_le]
    rw [← FractionalIdeal.mem_coe, ext_coe]
    have hm : algebraMap (𝓞 F) F a ∈ Submodule.span (S.integer F) ((J : FractionalIdeal (𝓞 F)⁰ F) : Set F) :=
      Submodule.subset_span ((FractionalIdeal.mem_coeIdeal (𝓞 F)⁰).mpr ⟨a, ha, rfl⟩)
    have := (Submodule.span (S.integer F) ((J : FractionalIdeal (𝓞 F)⁰ F) : Set F)).smul_mem
      (⟨(algebraMap (𝓞 F) F a)⁻¹, inv_mem F S a hS⟩ : S.integer F) hm
    have haF : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
    simpa [Algebra.smul_def, inv_mul_cancel₀ haF] using this
private lemma principalize (J : FractionalIdeal (𝓞 F)⁰ F) (a : Fˣ)
    (h : extHom F S J * FractionalIdeal.spanSingleton (S.integer F)⁰ (a : F) = 1) :
    extHom F S J = FractionalIdeal.spanSingleton (S.integer F)⁰ ((a⁻¹ : Fˣ) : F) := by
  have h' := congrArg (fun I => I * FractionalIdeal.spanSingleton (S.integer F)⁰ ((a⁻¹ : Fˣ) : F)) h
  simpa only [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
    Units.mul_inv, FractionalIdeal.spanSingleton_one, mul_one, one_mul] using h'
private lemma principal_of_reps
    (rep : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰)
    (hrep : ∀ C, ClassGroup.mk0 (rep C) = C)
    (hkill : ∀ C, extHom F S (rep C : Ideal (𝓞 F)) = 1)
    (I : FractionalIdeal (S.integer F)⁰ F) (hI : IsUnit I) :
    ∃ x : Fˣ, I = FractionalIdeal.spanSingleton (S.integer F)⁰ (x : F) := by
  obtain ⟨J, hJ⟩ := descent F S I hI
  let C := ClassGroup.mk F J
  have hclass : ClassGroup.mk F J = ClassGroup.mk F (FractionalIdeal.mk0 F (rep C)) := by
    rw [ClassGroup.mk_mk0, hrep]
  obtain ⟨x, hx⟩ := same_class F J (FractionalIdeal.mk0 F (rep C)) hclass
  have hx' := congrArg (fun J : (FractionalIdeal (𝓞 F)⁰ F)ˣ => extHom F S (J : FractionalIdeal (𝓞 F)⁰ F)) hx
  simp only [Units.val_mul, coe_toPrincipalIdeal, map_mul, ext_span, FractionalIdeal.coe_mk0] at hx'
  rw [hkill] at hx'
  exact ⟨x⁻¹, hJ ▸ principalize F S J x hx'⟩
end ClassKillProof

open ClassKillProof

lemma exists_unit_of_isPrincipal {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K]
    [IsLocalization R⁰ K] (I : FractionalIdeal R⁰ K)
    (h : (I : Submodule R K).IsPrincipal) (h0 : I ≠ 0) :
    ∃ x : Kˣ, I = FractionalIdeal.spanSingleton R⁰ (x : K) := by
  obtain ⟨x, hx⟩ := h.principal
  have hIeq : I = FractionalIdeal.spanSingleton R⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.val_eq_coe, hx, FractionalIdeal.coe_spanSingleton]
  have hx0 : x ≠ 0 := fun hxz => h0 (by rw [hIeq, hxz, FractionalIdeal.spanSingleton_zero])
  exact ⟨Units.mk0 x hx0, by rw [hIeq, Units.val_mk0]⟩

theorem exists_principalizing_finite_set (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ Sf : Finset (HeightOneSpectrum (𝓞 F)),
      S₀ ⊆ Sf ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → v ∈ Sf) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v ∈ Sf) ∧
      (∀ I : FractionalIdeal ((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F)⁰ F,
        IsUnit I → ∃ x : Fˣ,
          I = FractionalIdeal.spanSingleton
            ((Sf : Set (HeightOneSpectrum (𝓞 F))).integer F)⁰ (x : F)) := by
  classical
  choose rep hrep using (fun C : ClassGroup (𝓞 F) => ClassGroup.mk0_surjective C)
  have hnz (C : ClassGroup (𝓞 F)) : (rep C : Ideal (𝓞 F)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp (rep C).property
  choose a ha ha0 using fun C => (Submodule.ne_bot_iff (rep C : Ideal (𝓞 F))).mp (hnz C)
  let supp (x : 𝓞 F) (hx : x ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
    (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hx)).toFinset
  let six := supp 6 (by norm_num)
  let modSupp := (Ideal.finite_factors h𝔪).toFinset
  let classSupp := Finset.univ.biUnion (fun C => supp (a C) (ha0 C))
  let Sf := S₀ ∪ six ∪ modSupp ∪ classSupp
  have hbad : S₀ ⊆ Sf := by intro v hv; simp [Sf, hv]
  have hsix : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → v ∈ Sf := by
    intro v hv
    have hv' : v ∈ six := by simpa [six, supp, Ideal.dvd_span_singleton] using hv
    simp [Sf, hv']
  have hmod : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v ∈ Sf := by
    intro v hv
    have hv' : v ∈ modSupp := by simpa [modSupp, Ideal.dvd_iff_le] using hv
    simp [Sf, hv']
  refine ⟨Sf, hbad, hsix, hmod, ?_⟩
  apply principal_of_reps F (Sf : Set _) rep hrep
  intro C
  apply kill F (Sf : Set _) (rep C) (a C) (ha C) (ha0 C)
  intro v hv
  have hv' : v ∈ supp (a C) (ha0 C) := by simpa [supp, Ideal.dvd_span_singleton] using hv
  have hv'' : v ∈ classSupp := Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ _, hv'⟩
  simp [Sf, hv'']

theorem exists_principalizing_sArithmeticData (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (zeta12 : F) (hzeta12 : IsPrimitiveRoot zeta12 12) :
    ∃ A : SArithmeticData F,
      A.S₀ = S₀ ∧ A.modulus = 𝔪 ∧ A.zeta12 = zeta12 ∧
      (∀ I : FractionalIdeal A.R⁰ F, IsUnit I →
        ∃ x : Fˣ, I = FractionalIdeal.spanSingleton A.R⁰ (x : F)) := by
  obtain ⟨Sf, hbad, hsix, hmod, hprincipal⟩ :=
    exists_principalizing_finite_set F S₀ 𝔪 h𝔪
  let A : SArithmeticData F :=
    { zeta12 := zeta12
      primitive_zeta12 := hzeta12
      Sf := Sf
      S₀ := S₀
      bad_subset := hbad
      modulus := 𝔪
      modulus_ne_zero := h𝔪
      above_six := hsix
      modulus_support := hmod }
  exact ⟨A, rfl, rfl, rfl, hprincipal⟩

end

end DedekindZetaZeroFree
