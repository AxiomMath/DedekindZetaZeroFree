module

public import DedekindZetaZeroFree.LFunctions.Hecke.LocalComponentUniqueness
public import DedekindZetaZeroFree.Adeles.Characters.IdelicLocalRestriction

@[expose] public section

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.Conductor

namespace LocalCertification

theorem idealAwayPrimePart_coprime (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) :
    v.asIdeal ⊔ Raw.idealAwayPrimePart F v I = ⊤ := by
  classical
  apply Ideal.sup_multiset_prod_eq_top
  intro p hp
  obtain ⟨hpf, hpv⟩ := Multiset.mem_filter.mp hp
  have hpprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hpf
  exact v.isMaximal.coprime_of_ne
    ((Ideal.isPrime_of_prime hpprime).isMaximal hpprime.ne_zero) hpv.symm

private theorem exists_sub_mem_pair {R : Type*} [CommRing R] (I J : Ideal R) (h : I ⊔ J = ⊤) (b : R) :
    ∃ a : R, a - b ∈ I ∧ a - 1 ∈ J := by
  obtain ⟨i, hi, j, hj, hij⟩ := (Ideal.isCoprime_iff_sup_eq.mpr h).exists
  refine ⟨b * j + i, ?_, ?_⟩
  · have heq : b * j + i - b = (1 - b) * i := by linear_combination b * hij
    rw [heq]
    exact I.mul_mem_left _ hi
  · have heq : b * j + i - 1 = (b - 1) * j := by linear_combination hij
    rw [heq]
    exact J.mul_mem_left _ hj

theorem exists_integral_away_congruent
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) (n : ℕ)
    (b : 𝓞 F) : ∃ a : 𝓞 F,
      a - b ∈ v.asIdeal ^ n ∧ a - 1 ∈ Raw.idealAwayPrimePart F v I := by
  have h : v.asIdeal ^ n ⊔ Raw.idealAwayPrimePart F v I = ⊤ :=
    Ideal.pow_sup_eq_top (idealAwayPrimePart_coprime F v I)
  exact exists_sub_mem_pair (v.asIdeal ^ n) (Raw.idealAwayPrimePart F v I) h b

end LocalCertification

private theorem idelic_hom_ext_at_modulus
    {F : Type} [Field F] [NumberField F] (m : RayClass.Modulus F)
    (f g : IdeleClassGroup F →* ℂˣ)
    (hf : m.congruenceSubgroup ≤ f.ker) (hg : m.congruenceSubgroup ≤ g.ker)
    (hp : ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ m.finitePart.support),
      f (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) (IdeleGroup.finitePrimeIdele v)) =
      g (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) (IdeleGroup.finitePrimeIdele v))) : f = g := by
  let fl := QuotientGroup.lift m.congruenceSubgroup f hf
  let gl := QuotientGroup.lift m.congruenceSubgroup g hg
  have hl : fl = gl := by
    apply GlobalClassFieldTheory.GlobalClassFields.rayClassGroup_hom_ext_finitePrime m
    intro v hv
    exact hp v hv
  apply MonoidHom.ext
  intro c
  exact DFunLike.congr_fun hl (QuotientGroup.mk' m.congruenceSubgroup c)

theorem canonical_idelic_primitive_twist
    (F : Type) [Field F] [NumberField F] (hc : NumberField.IsTotallyComplex F)
    (η χ ψ : PrimitiveFrequencyCharacter F)
    (htw : IsPrimitiveFrequencyTwist F η χ ψ)
    (c : IdeleClassGroup F) :
    RayClassBridge.ideleClassCharacter F hc ψ.conductor ψ.conductor_ne_zero
        ψ.character c =
      RayClassBridge.ideleClassCharacter F hc η.conductor η.conductor_ne_zero
          η.character c /
        RayClassBridge.ideleClassCharacter F hc χ.conductor χ.conductor_ne_zero
          χ.character c := by
  classical
  let me := RayClassBridge.narrowIdealModulus F η.conductor η.conductor_ne_zero
  let mx := RayClassBridge.narrowIdealModulus F χ.conductor χ.conductor_ne_zero
  let mp := RayClassBridge.narrowIdealModulus F ψ.conductor ψ.conductor_ne_zero
  let orig := ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
  let M : RayClass.Modulus F :=
    { finitePart := me.finitePart + mx.finitePart + mp.finitePart
      infinitePart := Finset.univ }
  have he : orig me ≤ M := ⟨by intro v; change me.finitePart v ≤ me.finitePart v + mx.finitePart v + mp.finitePart v; omega, by simp [M]⟩
  have hx : orig mx ≤ M := ⟨by intro v; change mx.finitePart v ≤ me.finitePart v + mx.finitePart v + mp.finitePart v; omega, by simp [M]⟩
  have hp : orig mp ≤ M := ⟨by intro v; change mp.finitePart v ≤ me.finitePart v + mx.finitePart v + mp.finitePart v; omega, by simp [M]⟩
  let E := RayClassBridge.ideleClassCharacter F hc η.conductor η.conductor_ne_zero η.character
  let X := RayClassBridge.ideleClassCharacter F hc χ.conductor χ.conductor_ne_zero χ.character
  let P := RayClassBridge.ideleClassCharacter F hc ψ.conductor ψ.conductor_ne_zero ψ.character
  have hE : M.congruenceSubgroup ≤ E.ker :=
    (RayClass.Modulus.congruenceSubgroup_antitone he).trans
      (RayClassBridge.ideleClassCharacter_congruenceSubgroup_le_ker F hc η.conductor η.conductor_ne_zero η.character)
  have hX : M.congruenceSubgroup ≤ X.ker :=
    (RayClass.Modulus.congruenceSubgroup_antitone hx).trans
      (RayClassBridge.ideleClassCharacter_congruenceSubgroup_le_ker F hc χ.conductor χ.conductor_ne_zero χ.character)
  have hP : M.congruenceSubgroup ≤ P.ker :=
    (RayClass.Modulus.congruenceSubgroup_antitone hp).trans
      (RayClassBridge.ideleClassCharacter_congruenceSubgroup_le_ker F hc ψ.conductor ψ.conductor_ne_zero ψ.character)
  have hEX : M.congruenceSubgroup ≤ (E / X).ker := by
    intro z hz
    change E z / X z = 1
    rw [MonoidHom.mem_ker.mp (hE hz), MonoidHom.mem_ker.mp (hX hz), one_div, inv_one]
  have hall : P = E / X := by
    apply idelic_hom_ext_at_modulus M P (E / X) hP hEX
    intro v hv
    have hve : v ∉ me.finitePart.support := by
      intro h
      apply hv
      simp only [Finsupp.mem_support_iff] at h ⊢
      change me.finitePart v + mx.finitePart v + mp.finitePart v ≠ 0
      omega
    have hvx : v ∉ mx.finitePart.support := by
      intro h
      apply hv
      simp only [Finsupp.mem_support_iff] at h ⊢
      change me.finitePart v + mx.finitePart v + mp.finitePart v ≠ 0
      omega
    have hvp : v ∉ mp.finitePart.support := by
      intro h
      apply hv
      simp only [Finsupp.mem_support_iff] at h ⊢
      change me.finitePart v + mx.finitePart v + mp.finitePart v ≠ 0
      omega
    have coprime (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
        (hv : v ∉ (RayClassBridge.narrowIdealModulus F m hm).finitePart.support) : v.asIdeal ⊔ m = ⊤ := by
      have hn : ¬ m ≤ v.asIdeal := by
        intro h
        apply hv
        change v ∈ (↑(RayClassBridge.narrowIdealModulus F m hm).finitePart.support : Set _)
        rw [RayClassBridge.narrowIdealModulus_support F m hm]
        exact h
      exact (Ideal.isMaximal_def.mp v.isMaximal).2 _
        (lt_of_le_of_ne le_sup_left (fun he => hn (he ▸ le_sup_right)))
    have hce := coprime η.conductor η.conductor_ne_zero hve
    have hcx := coprime χ.conductor χ.conductor_ne_zero hvx
    have hcp := coprime ψ.conductor ψ.conductor_ne_zero hvp
    have hcommon : v.asIdeal ⊔ (η.conductor * χ.conductor * ψ.conductor) = ⊤ := by
      rw [Ideal.sup_mul_eq_of_coprime_left ((Ideal.sup_mul_eq_of_coprime_left hce).trans hcx), hcp]
    apply Units.ext
    simp only [MonoidHom.div_apply, Units.val_div_eq_div_val]
    change (P _ : ℂ) = (E _ : ℂ) / (X _ : ℂ)
    rw [RayClassBridge.ideleClassCharacter_finitePrimeIdele F hc ψ.conductor ψ.conductor_ne_zero ψ.character v hvp,
      RayClassBridge.ideleClassCharacter_finitePrimeIdele F hc η.conductor η.conductor_ne_zero η.character v hve,
      RayClassBridge.ideleClassCharacter_finitePrimeIdele F hc χ.conductor χ.conductor_ne_zero χ.character v hvx]
    rw [htw v.asIdeal v.ne_bot hcommon, div_eq_mul_inv,
      Complex.inv_eq_conj (RayClassBridge.rayClassCharacter_norm_of_primeTo F hc χ.conductor χ.conductor_ne_zero χ.character v.asIdeal v.ne_bot hcx)]
  exact DFunLike.congr_fun hall c

end DedekindZetaZeroFree.Detector.Conductor
