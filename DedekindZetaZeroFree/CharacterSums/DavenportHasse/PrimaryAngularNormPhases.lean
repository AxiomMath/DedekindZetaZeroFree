module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.CharacterSums.Cubic.JacobiPrimaryGeneratorValue
public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.LiftingFormula
public import DedekindZetaZeroFree.CharacterSums.Gauss.NormalizedSexticPowerIdentities

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.DHCubic.ResidueFields

noncomputable section

abbrev Residue (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) := 𝓞 F ⧸ v.asIdeal

instance residueField (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Field (Residue F v) := Ideal.Quotient.field _

instance residueFintype (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Fintype (Residue F v) := Fintype.ofFinite _

end
end DedekindZetaZeroFree.DHCubic.ResidueFields

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.DHCubic.ResidueFields

theorem exists_prime_below_exterior
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F]
    [Algebra E F] (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    ∃ q : HeightOneSpectrum (𝓞 E), v.asIdeal.LiesOver q.asIdeal ∧
      q.asIdeal ⊔ Ideal.span {(6 : 𝓞 E)} = ⊤ := by
  let q : Ideal (𝓞 E) := v.asIdeal.under (𝓞 E)
  have hq_ne : q ≠ ⊥ := Ideal.IsIntegral.under_ne_bot (𝓞 E) v.ne_bot
  have hq_prime : q.IsPrime := Ideal.IsPrime.under (𝓞 E) v.asIdeal
  have hq_max : q.IsMaximal := Ideal.IsMaximal.under (𝓞 E) v.asIdeal
  refine ⟨⟨q, hq_prime, hq_ne⟩, ?_, ?_⟩
  · exact Ideal.over_under (A := 𝓞 E) v.asIdeal
  · by_contra h
    have heq : q = q ⊔ Ideal.span {(6 : 𝓞 E)} :=
      Ideal.IsMaximal.eq_of_le hq_max h le_sup_left
    have hle : Ideal.span {(6 : 𝓞 E)} ≤ q := heq ▸ le_sup_right
    have h6 : (6 : 𝓞 E) ∈ q := hle (Ideal.subset_span (by simp))
    have h6v : (6 : 𝓞 F) ∈ v.asIdeal := by
      have := (Ideal.mem_under (𝓞 E) v.asIdeal).mp h6
      simpa only [map_ofNat] using this
    exact hv (A.above_six v h6v)

end DedekindZetaZeroFree.DHCubic.ResidueFields

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.DHCubic.ResidueFields

theorem primary_power_div_sqrt_residue_card
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F]
    [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (ι : E →+* ℂ) (v : HeightOneSpectrum (𝓞 F))
    (q : HeightOneSpectrum (𝓞 E)) (hq : v.asIdeal.LiesOver q.asIdeal)
    (hq6 : q.asIdeal ⊔ Ideal.span {(6 : 𝓞 E)} = ⊤) :
    letI := hq
    Eisenstein.ιR E ι
        (Eisenstein.primaryGenerator E (Eisenstein.q3 E q.asIdeal q.ne_bot hq6)) ^
          Module.finrank (Residue E q) (Residue F v) /
            (Real.sqrt (Fintype.card (Residue F v)) : ℂ) =
      if hI : Ideal.relNorm (𝓞 E) v.asIdeal ∈ Eisenstein.I3 E then
        Eisenstein.ιR E ι
            (Eisenstein.primaryGenerator E ⟨Ideal.relNorm (𝓞 E) v.asIdeal, hI⟩) /
          (‖Eisenstein.ιR E ι
            (Eisenstein.primaryGenerator E ⟨Ideal.relNorm (𝓞 E) v.asIdeal, hI⟩)‖ : ℂ)
      else 0 := by
  classical
  letI := hq
  let A := Eisenstein.q3 E q.asIdeal q.ne_bot hq6
  let f := Module.finrank (Residue E q) (Residue F v)
  have hrel : Ideal.relNorm (𝓞 E) v.asIdeal = q.asIdeal ^ f := by
    rw [Ideal.relNorm_eq_pow_of_isMaximal v.asIdeal q.asIdeal,
      Ideal.inertiaDeg_eq_of_isMaximal q.asIdeal v.asIdeal]
  have hI : Ideal.relNorm (𝓞 E) v.asIdeal ∈ Eisenstein.I3 E := by
    rw [hrel]
    exact (A ^ f).property
  rw [dif_pos hI]
  have hA : (⟨Ideal.relNorm (𝓞 E) v.asIdeal, hI⟩ : Eisenstein.I3 E) = A ^ f := by
    apply Subtype.ext
    exact hrel
  have hpow : ∀ n : ℕ, Eisenstein.primaryGenerator E (A ^ n) =
      Eisenstein.primaryGenerator E A ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]
  rw [hA, hpow, map_pow]
  have hn : ‖Eisenstein.ιR E ι (Eisenstein.primaryGenerator E A) ^ f‖ =
      Real.sqrt (Fintype.card (Residue F v)) := by
    have habs := Eisenstein.absNorm_span_eq_normSq E ι
      (Eisenstein.primaryGenerator E (A ^ f))
    rw [Eisenstein.span_primaryGenerator] at habs
    have hcard : Ideal.absNorm ((A ^ f : Eisenstein.I3 E) : Ideal (𝓞 E)) =
        Fintype.card (Residue F v) := by
      change Ideal.absNorm (q.asIdeal ^ f) = _
      rw [← hrel, Ideal.absNorm_relNorm]
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      exact Nat.card_eq_fintype_card
    rw [hcard, hpow, map_pow, ← Complex.sq_norm] at habs
    rw [habs, Real.sqrt_sq (norm_nonneg _)]
  rw [hn]

end DedekindZetaZeroFree.DHCubic.ResidueFields

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.DHCubic

noncomputable section

def angular (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem angular_mul (x y : ℂ) : angular (x * y) = angular x * angular y := by
  rw [angular, angular, angular, norm_mul, Complex.ofReal_mul, div_mul_div_comm]

theorem angular_smul_ofReal (z : ℂ) {r : ℝ} (hr : 0 < r) :
    angular ((r : ℂ) * z) = angular z := by
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  rw [angular, angular]
  have hnorm : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
    rw [norm_mul]
    congr 1
    exact_mod_cast (abs_of_pos hr : |r| = r)
  rw [hnorm, Complex.ofReal_mul]
  rw [mul_div_mul_left z (‖z‖ : ℂ) hrne]

theorem star_angular (z : ℂ) (hz : z ≠ 0) :
    star (angular z) = angular z ^ (-1 : ℤ) := by
  have hz' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr hz
  rw [angular, zpow_neg_one, Complex.star_def, map_div₀, Complex.conj_ofReal, inv_div]
  rw [div_eq_div_iff hz' hz]
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  ring

def lambdaBase (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ι : E →+* ℂ)
    (I : Ideal (𝓞 E)) : ℂ :=
  if hI : I ∈ Eisenstein.I3 E then
    angular (Eisenstein.ιR E ι (Eisenstein.primaryGenerator E ⟨I, hI⟩))
  else 0

theorem lambdaBase_mul (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ι : E →+* ℂ) (I J : Ideal (𝓞 E)) :
    lambdaBase E ι (I * J) = lambdaBase E ι I * lambdaBase E ι J := by
  have key : ∀ A B : Ideal (𝓞 E), A * B ∈ Eisenstein.I3 E → A ∈ Eisenstein.I3 E := by
    intro A B h
    rw [Eisenstein.mem_I3] at h ⊢
    have h' : ¬(A = ⊥ ∨ B = ⊥) := fun hc => h.1 (Ideal.mul_eq_bot.mpr hc)
    refine ⟨fun hA => h' (Or.inl hA), ?_⟩
    refine le_antisymm le_top ?_
    rw [← h.2]
    exact sup_le_sup_right (Ideal.mul_le_left (I := A) (J := B)) _
  by_cases hI : I ∈ Eisenstein.I3 E
  · by_cases hJ : J ∈ Eisenstein.I3 E
    · have hIJ : I * J ∈ Eisenstein.I3 E := (Eisenstein.I3 E).mul_mem hI hJ
      unfold lambdaBase
      rw [dif_pos hIJ, dif_pos hI, dif_pos hJ]
      have hsub : (⟨I, hI⟩ : Eisenstein.I3 E) * ⟨J, hJ⟩ = ⟨I * J, hIJ⟩ := Subtype.ext rfl
      have hmul := Eisenstein.primaryGenerator_mul E ⟨I, hI⟩ ⟨J, hJ⟩
      rw [hsub] at hmul
      rw [hmul, map_mul, angular_mul]
    · unfold lambdaBase
      rw [dif_pos hI, dif_neg hJ, mul_zero]
      rw [dif_neg]
      exact fun hIJ => hJ (key J I (by rwa [mul_comm] at hIJ))
  · unfold lambdaBase
    rw [dif_neg hI, zero_mul]
    rw [dif_neg]
    exact fun hIJ => hI (key I J hIJ)

def lambdaF (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F]
    [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (ι : E →+* ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  lambdaBase E ι (Ideal.relNorm (𝓞 E) I)

def infinityComponent (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [Algebra E F]
    (ι : E →+* ℂ) (w : InfinitePlace F) (z : ℂ) : ℂ :=
  if w.embedding.comp (algebraMap E F) = ι then angular z else star (angular z)

abbrev E0 (F : Type) [Field F] [NumberField F] (A : SArithmeticData F) : Type :=
  ↥(IntermediateField.adjoin ℚ ({A.zeta12 ^ 4} : Set F))

instance e0Cyclotomic (F : Type) [Field F] [NumberField F] (A : SArithmeticData F) :
    IsCyclotomicExtension {3} ℚ (E0 F A) :=
  (A.primitive_zeta12.pow (by decide) (by decide : 12 = 4 * 3)).intermediateField_adjoin_isCyclotomicExtension ℚ

def omega0 (F : Type) [Field F] [NumberField F] (A : SArithmeticData F) : E0 F A :=
  ⟨A.zeta12 ^ 4, IntermediateField.mem_adjoin_simple_self ℚ _⟩

theorem omega0_primitive (F : Type) [Field F] [NumberField F] (A : SArithmeticData F) :
    IsPrimitiveRoot (omega0 F A) 3 := by
  apply (IsPrimitiveRoot.map_iff_of_injective
    (RingHom.injective (algebraMap (E0 F A) F))).mp
  exact A.primitive_zeta12.pow (by decide) (by decide : 12 = 4 * 3)

def lambda (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (ι : E0 F A →+* ℂ) (I : Ideal (𝓞 F)) : ℂ := lambdaF (E0 F A) F ι I

abbrev Residue (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) := 𝓞 F ⧸ v.asIdeal

instance residueField (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Field (Residue F v) :=
  Ideal.Quotient.field _

instance residueFintype (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Fintype (Residue F v) := Fintype.ofFinite _

def IsNormalizedSextic (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (χ : MulChar (Residue F v) (𝓞 F)) : Prop :=
  ∀ x : Residue F v, x ≠ 0 →
    (∃ j : ℕ, j < 6 ∧ χ x = A.primitive_zeta12.toInteger ^ (2 * j)) ∧
      Ideal.Quotient.mk v.asIdeal (χ x) = x ^ ((Fintype.card (Residue F v) - 1) / 6)

def gammaTwo (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (σ : F →+* ℂ)
    (χ : MulChar (Residue F v) (𝓞 F)) (ψ : AddChar (Residue F v) ℂ) : ℂ :=
  FiniteGauss.normalizedGaussPower
    (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) ψ 2

private theorem red_sextic_primitive (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal (A.primitive_zeta12.toInteger ^ 2)) 6 := by
  let r := Ideal.Quotient.mk v.asIdeal
  let z := A.primitive_zeta12.toInteger ^ 2
  have hp : IsPrimitiveRoot z 6 := A.primitive_zeta12.toInteger_isPrimitiveRoot.pow
    (by decide) (by decide : 12 = 2 * 6)
  have h6 : (6 : Residue F v) ≠ 0 := by
    intro h
    apply hv
    apply A.above_six v
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using h)
  have h2 : (2 : Residue F v) ≠ 0 := by
    intro h
    apply h6
    linear_combination 3 * h
  have h3 : (3 : Residue F v) ≠ 0 := by
    intro h
    apply h6
    linear_combination 2 * h
  have hc : z ^ 3 = -1 := (hp.pow (by decide) (by decide : 6 = 3 * 2)).eq_neg_one_of_two_right
  have hr3 : IsPrimitiveRoot ((r z) ^ 3) 2 := by
    rw [← map_pow, hc, map_neg, map_one]
    apply (IsPrimitiveRoot.iff (by decide : 0 < 2)).mpr
    refine ⟨by simp, ?_⟩
    intro l hl hlt
    have : l = 1 := by omega
    subst l
    intro h
    apply h2
    simp only [pow_one] at h
    linear_combination -h
  have hr2 : IsPrimitiveRoot ((r z) ^ 2) 3 := by
    have hp2 := hp.pow (by decide) (by decide : 6 = 2 * 3)
    have hpow : ((r z) ^ 2) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hp2.pow_eq_one, map_one]
    have hne : (r z) ^ 2 ≠ 1 := by
      intro h
      have hg := congrArg r (hp2.geom_sum_eq_zero (by decide : 1 < 3))
      simp [Finset.sum_range_succ, map_add, map_pow, h] at hg
      exact h3 (by linear_combination hg)
    exact isPrimitiveRoot_of_mem_nthRootsFinset (by decide : Nat.Prime 3)
      ((Polynomial.mem_nthRootsFinset (by decide : 0 < 3) 1).mpr hpow) hne
  apply (IsPrimitiveRoot.iff_def _ _).mpr
  refine ⟨by rw [← map_pow, hp.pow_eq_one, map_one], ?_⟩
  intro l hl
  have hd2 : 2 ∣ l := hr3.dvd_of_pow_eq_one l (by rw [pow_right_comm, hl, one_pow])
  have hd3 : 3 ∣ l := hr2.dvd_of_pow_eq_one l (by rw [pow_right_comm, hl, one_pow])
  exact Nat.lcm_dvd hd2 hd3
private theorem sextic_roots_red_bijective (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    Function.Bijective (restrictRootsOfUnity (Ideal.Quotient.mk v.asIdeal) 6) := by
  let r := Ideal.Quotient.mk v.asIdeal
  let z := A.primitive_zeta12.toInteger ^ 2
  have hp : IsPrimitiveRoot z 6 := A.primitive_zeta12.toInteger_isPrimitiveRoot.pow
    (by decide) (by decide : 12 = 2 * 6)
  have hr : IsPrimitiveRoot (r z) 6 := red_sextic_primitive F A v hv
  constructor
  · intro a b hab
    obtain ⟨i, hi, hai⟩ := hp.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' 6 a.val).mp a.prop)
    obtain ⟨j, hj, hbj⟩ := hp.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' 6 b.val).mp b.prop)
    have he : i = j := hr.pow_inj hi hj (by
      have hv := congrArg (fun z : rootsOfUnity 6 (Residue F v) => (z.val : Residue F v)) hab
      change r (a.val : 𝓞 F) = r (b.val : 𝓞 F) at hv
      simpa only [← hai, ← hbj, map_pow] using hv)
    apply rootsOfUnity.coe_injective
    simpa only [← hai, ← hbj, he]
  · intro a
    obtain ⟨i, hi, hai⟩ := hr.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' 6 a.val).mp a.prop)
    refine ⟨rootsOfUnity.mkOfPowEq (z ^ i) ?_, ?_⟩
    · rw [← pow_mul, Nat.mul_comm i 6, pow_mul, hp.pow_eq_one, one_pow]
    · apply rootsOfUnity.coe_injective
      change r (z ^ i) = (a.val : Residue F v)
      simpa only [map_pow] using hai

theorem existsUnique_normalizedSextic (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    ∃! χ : MulChar (Residue F v) (𝓞 F), IsNormalizedSextic F A v χ := by
  let r := Ideal.Quotient.mk v.asIdeal
  let z := A.primitive_zeta12.toInteger ^ 2
  let n := (Fintype.card (Residue F v) - 1) / 6
  have hp : IsPrimitiveRoot z 6 := A.primitive_zeta12.toInteger_isPrimitiveRoot.pow
    (by decide) (by decide : 12 = 2 * 6)
  have hr : IsPrimitiveRoot (r z) 6 := red_sextic_primitive F A v hv
  have hd : 6 ∣ Fintype.card (Residue F v) - 1 :=
    hr.dvd_of_pow_eq_one _ (FiniteField.pow_card_sub_one_eq_one _ (hr.ne_zero (by decide)))
  let e := MulEquiv.ofBijective (restrictRootsOfUnity r 6)
    (sextic_roots_red_bijective F A v hv)
  let f : (Residue F v)ˣ →* rootsOfUnity 6 (Residue F v) := {
    toFun := fun x => ⟨x ^ n, by
      rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel hd]
      apply Units.ext
      exact FiniteField.pow_card_sub_one_eq_one (x : Residue F v) x.ne_zero⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intros; apply Subtype.ext; simp [mul_pow] }
  let g : (Residue F v)ˣ →* (𝓞 F)ˣ :=
    (rootsOfUnity 6 (𝓞 F)).subtype.comp (e.symm.toMonoidHom.comp f)
  let χ := MulChar.ofUnitHom g
  have hred (x : (Residue F v)ˣ) : r (χ x) = (x : Residue F v) ^ n := by
    have he := e.apply_symm_apply (f x)
    have hv := congrArg (fun z : rootsOfUnity 6 (Residue F v) => (z.val : Residue F v)) he
    change r (g x : 𝓞 F) = (x : Residue F v) ^ n at hv
    simpa only [χ, MulChar.ofUnitHom_coe] using hv
  have hpow (x : (Residue F v)ˣ) : χ x ^ 6 = 1 := by
    change (MulChar.ofUnitHom g) x ^ 6 = 1
    rw [MulChar.ofUnitHom_coe]
    exact (mem_rootsOfUnity' 6 (e.symm (f x)).val).mp (e.symm (f x)).prop
  refine ⟨χ, ?_, ?_⟩
  · intro x hx
    lift x to (Residue F v)ˣ using (isUnit_iff_ne_zero.mpr hx)
    obtain ⟨i, hi, hei⟩ := hp.eq_pow_of_pow_eq_one (hpow x)
    refine ⟨⟨i, hi, ?_⟩, hred x⟩
    simpa only [z, ← pow_mul] using hei.symm
  · intro χ' hχ'
    apply MulChar.ext
    intro x
    obtain ⟨⟨j, hj, hval⟩, hred'⟩ := hχ' x x.ne_zero
    have hpow' : χ' x ^ 6 = 1 := by
      rw [hval, ← pow_mul]
      have : 2 * j * 6 = 12 * j := by omega
      rw [this, pow_mul, A.primitive_zeta12.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    have he : restrictRootsOfUnity r 6 (rootsOfUnity.mkOfPowEq (χ' x) hpow') =
        restrictRootsOfUnity r 6 (rootsOfUnity.mkOfPowEq (χ x) (hpow x)) := by
      apply rootsOfUnity.coe_injective
      exact hred'.trans (hred x).symm
    exact congrArg (fun z : rootsOfUnity 6 (𝓞 F) => (z.val : 𝓞 F))
      ((sextic_roots_red_bijective F A v hv).1 he)

theorem orderOf_normalizedSextic (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (χ : MulChar (Residue F v) (𝓞 F)) (hχ : IsNormalizedSextic F A v χ) :
    orderOf χ = 6 := by
  let q := Fintype.card (Residue F v) - 1
  let n := q / 6
  have hd : 6 ∣ q := by
    have hm := A.exterior_norm_mod_twelve v hv
    have ha : Ideal.absNorm v.asIdeal = Fintype.card (Residue F v) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [ha] at hm
    omega
  have hqpos : 0 < q := by
    have := Fintype.one_lt_card (α := Residue F v)
    dsimp [q]; omega
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hqpos hd) (by decide)
  have he : n * 6 = q := Nat.div_mul_cancel hd
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  constructor
  · apply MulChar.ext
    intro x
    obtain ⟨⟨j, hj, hv⟩, _⟩ := hχ x x.ne_zero
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hv, ← pow_mul]
    have he : 2 * j * 6 = 12 * j := by omega
    rw [he, pow_mul, A.primitive_zeta12.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  · intro m hm hmpos h
    have hpow : ∀ x : (Residue F v)ˣ, x ^ (n * m) = 1 := by
      intro x
      apply Units.ext
      have hred := (hχ x x.ne_zero).2
      have hval := congrArg (fun c : MulChar (Residue F v) (𝓞 F) => c x) h
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hval
      have hmap := congrArg (Ideal.Quotient.mk v.asIdeal) hval
      simpa only [map_pow, map_one, hred, ← pow_mul, Units.val_pow_eq_pow_val, Units.val_one] using hmap
    have hl := Nat.le_of_dvd (Nat.mul_pos hn hmpos)
      ((FiniteField.forall_pow_eq_one_iff (Residue F v) _).mp hpow)
    change q ≤ n * m at hl
    nlinarith
theorem orderOf_normalizedSextic_complex (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (σ : F →+* ℂ) (χ : MulChar (Residue F v) (𝓞 F))
    (hχ : IsNormalizedSextic F A v χ) :
    orderOf (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) = 6 := by
  rw [← orderOf_normalizedSextic F A v hv χ hχ]
  exact (orderOf_injective (MulChar.ringHomCompHom (σ.comp (algebraMap (𝓞 F) F)))
    (MulChar.injective_ringHomComp (σ.injective.comp NumberField.RingOfIntegers.coe_injective)) χ)

theorem gammaTwo_cube_eq_jacobi (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (σ : F →+* ℂ) (χ : MulChar (Residue F v) (𝓞 F))
    (hχ : IsNormalizedSextic F A v χ) (ψ : AddChar (Residue F v) ℂ) (hψ : ψ ≠ 1) :
    gammaTwo F v σ χ ψ ^ 3 =
      jacobiSum ((χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) ^ 2)
        ((χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) ^ 2) /
          (Real.sqrt (Fintype.card (Residue F v)) : ℂ) := by
  apply FiniteGauss.normalizedGaussPower_two_cube
  · have hm := A.exterior_norm_mod_twelve v hv
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hm
  · exact orderOf_normalizedSextic_complex F A v hv σ χ hχ
  · exact hψ

private theorem card_sub_one_dvd (k K : Type) [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K] :
    Fintype.card k - 1 ∣ Fintype.card K - 1 := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := kˣ)
  have ho : orderOf x = Fintype.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card, Fintype.card_units]
  let hom := Units.map (algebraMap k K).toMonoidHom
  have hi : Function.Injective hom := by
    intro a b h
    apply Units.ext
    exact (algebraMap k K).injective (by simpa [hom] using congrArg Units.val h)
  have he := orderOf_injective hom hi x
  have hd : orderOf (hom x) ∣ Fintype.card K - 1 := by
    rw [← Fintype.card_units]
    exact orderOf_dvd_card
  rwa [he, ho] at hd

theorem normalizedSextic_sq_norm_lift (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F]
    [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (A : SArithmeticData F) (ω : E) (hω : IsPrimitiveRoot ω 3)
    (hcompat : algebraMap E F ω = A.zeta12 ^ 4)
    (v : HeightOneSpectrum (𝓞 F)) (q : Ideal (𝓞 E))
    (hq0 : q ≠ ⊥) (hqp : q.IsPrime) (hq6 : q ⊔ Ideal.span {(6 : 𝓞 E)} = ⊤)
    [v.asIdeal.LiesOver q]
    (χ : MulChar (Residue F v) (𝓞 F)) (hχ : IsNormalizedSextic F A v χ)
    (h6 : 6 ∣ Fintype.card (Residue F v) - 1) :
    letI := Eisenstein.residueField E q hq0 hqp
    letI := Eisenstein.residueFintype E q hq0
    ∀ x : Residue F v, χ x ^ 2 = algebraMap (𝓞 E) (𝓞 F)
      (Eisenstein.ρq E ω hω q hq0 hqp hq6 (Algebra.norm (𝓞 E ⧸ q) x)) := by
  letI := Eisenstein.residueField E q hq0 hqp
  letI := Eisenstein.residueFintype E q hq0
  let k := 𝓞 E ⧸ q
  let K := Residue F v
  let r := Ideal.Quotient.mk v.asIdeal
  let z := A.primitive_zeta12.toInteger ^ 4
  have hz : algebraMap (𝓞 E) (𝓞 F) (Eisenstein.η E ω hω) = z := by
    apply NumberField.RingOfIntegers.coe_injective
    change algebraMap E F (hω.toInteger : E) = (A.primitive_zeta12.toInteger : F) ^ 4
    exact hcompat
  have hp : IsPrimitiveRoot (r z) 3 := by
    have hp := (Eisenstein.redq_η_isPrimitiveRoot E ω hω q hq0 hqp hq6).map_of_injective
      (algebraMap k K).injective
    simpa only [k, K, Eisenstein.redq, Ideal.Quotient.algebraMap_mk_of_liesOver, hz] using hp
  intro x
  by_cases hx : x = 0
  · subst x
    have hc0 : χ 0 = 0 := χ.map_nonunit (by simp)
    simp [hc0]
  have hnx : Algebra.norm k x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  obtain ⟨⟨j, hj, hjval⟩, hjred⟩ := hχ x hx
  have hh := Eisenstein.ρq_mem E ω hω q hq0 hqp hq6 (Algebra.norm k x) hnx
  have hpred := Eisenstein.redq_ρq E ω hω q hq0 hqp hq6 (Algebra.norm k x)
  have hexp : ((Fintype.card K - 1) / (Fintype.card k - 1)) *
      ((Fintype.card k - 1) / 3) = 2 * ((Fintype.card K - 1) / 6) := by
    have hd := card_sub_one_dvd k K
    have h3 : 3 ∣ Fintype.card k - 1 :=
      Eisenstein.three_dvd_residueCard_sub_one E q hq0 hqp hq6
    have hb : 0 < Fintype.card k - 1 := by have := Fintype.one_lt_card (α := k); omega
    apply Nat.eq_of_mul_eq_mul_right hb
    calc
      _ = ((Fintype.card K - 1) / (Fintype.card k - 1)) *
          (((Fintype.card k - 1) / 3) * (Fintype.card k - 1)) := by ring
      _ = ((Fintype.card K - 1) / (Fintype.card k - 1)) *
          ((Fintype.card k - 1) * ((Fintype.card k - 1) / 3)) := by ring
      _ = (Fintype.card K - 1) * ((Fintype.card k - 1) / 3) := by
        rw [← mul_assoc, Nat.div_mul_cancel hd]
      _ = 2 * ((Fintype.card K - 1) / 6) * (Fintype.card k - 1) := by
        have ha := Nat.div_mul_cancel h6
        have hc := Nat.div_mul_cancel h3
        nlinarith
  have hred : r (χ x ^ 2) = r (algebraMap (𝓞 E) (𝓞 F)
      (Eisenstein.ρq E ω hω q hq0 hqp hq6 (Algebra.norm k x))) := by
    rw [map_pow, hjred]
    change _ = algebraMap k K (Eisenstein.redq E q
      (Eisenstein.ρq E ω hω q hq0 hqp hq6 (Algebra.norm k x)))
    rw [hpred]
    rw [map_pow, FiniteField.algebraMap_norm_eq_pow, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, ← pow_mul]
    change x ^ (((Fintype.card K - 1) / 6) * 2) =
      (x ^ ((Fintype.card K - 1) / (Fintype.card k - 1))) ^
        ((Fintype.card k - 1) / 3)
    rw [← pow_mul, hexp]
    congr 1
    omega
  have hleft : χ x ^ 2 = z ^ (j % 3) := by
    rw [hjval]
    have hpow : (A.primitive_zeta12.toInteger ^ (2 * j)) ^ 2 = z ^ j := by
      dsimp [z]
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hpow]
    have hpz : IsPrimitiveRoot z 3 := by
      exact A.primitive_zeta12.toInteger_isPrimitiveRoot.pow
        (by decide : 0 < 12) (by decide : 12 = 4 * 3)
    simpa only [hpz.eq_orderOf] using (pow_mod_orderOf z j).symm
  obtain ⟨i, hi, hright⟩ : ∃ i : ℕ, i < 3 ∧
      algebraMap (𝓞 E) (𝓞 F)
        (Eisenstein.ρq E ω hω q hq0 hqp hq6 (Algebra.norm k x)) = z ^ i := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with h | h | h
    · exact ⟨0, by decide, by rw [h, map_one, pow_zero]⟩
    · exact ⟨1, by decide, by rw [h, hz, pow_one]⟩
    · exact ⟨2, by decide, by rw [h, map_pow, hz]⟩
  rw [hleft, hright]
  congr 1
  apply hp.pow_inj (Nat.mod_lt _ (by decide)) hi
  simpa only [hleft, hright, map_pow] using hred

theorem jacobiSum_norm_pullback
    (k K : Type) [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]
    (ρ : MulChar k ℂ) (ρK : MulChar K ℂ)
    (ψ : AddChar k ℂ) (ψK : AddChar K ℂ)
    (hρ : ρ * ρ ≠ 1) (hρK : ρK * ρK ≠ 1)
    (hψ : ψ ≠ 1) (hψK : ψK ≠ 1)
    (hnorm : ∀ x : K, ρK x = ρ (Algebra.norm k x))
    (htrace : ∀ x : K, ψK x = ψ (Algebra.trace k K x)) :
    jacobiSum ρK ρK = -(-jacobiSum ρ ρ) ^ Module.finrank k K := by
  have hex : ∃ x : k, ψ x ≠ 1 := by
    by_contra h
    apply hψ
    ext x
    simpa using (not_exists_not.mp h x)
  have hcard : (Fintype.card k : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardK : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg := DedekindZetaZeroFree.davenportHasse k K ρ ψ ρK ψK hex hnorm htrace
  have hh := DedekindZetaZeroFree.davenportHasse k K (ρ * ρ) ψ (ρK * ρK) ψK hex
    (fun x => by simp only [MulChar.mul_apply, hnorm]) htrace
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcardK hρK
    (AddChar.IsPrimitive.of_ne_one hψK),
    jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcard hρ
    (AddChar.IsPrimitive.of_ne_one hψ), hg, hh]
  rw [neg_mul_neg, div_neg, ← mul_pow, ← div_pow]
  congr 2
  ring

theorem gammaTwo_cube
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F]
    [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (A : SArithmeticData F) (ω : E) (hω : IsPrimitiveRoot ω 3)
    (hcompat : algebraMap E F ω = A.zeta12 ^ 4)
    (ι : E →+* ℂ) (σ : F →+* ℂ) (hσ : σ.comp (algebraMap E F) = ι)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (χ : MulChar (Residue F v) (𝓞 F)) (hχ : IsNormalizedSextic F A v χ)
    (ψ : AddChar (Residue F v) ℂ) (hψ : ψ ≠ 1) :
    gammaTwo F v σ χ ψ ^ 3 = -lambdaF E F ι v.asIdeal := by
  obtain ⟨q, hq, hq6⟩ := ResidueFields.exists_prime_below_exterior E F A v hv
  letI := hq
  letI := ResidueFields.residueField E q
  letI := ResidueFields.residueFintype E q
  let ρ := Eisenstein.ρqC E ω hω ι q.asIdeal q.ne_bot q.isPrime hq6
  let ρF := (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) ^ 2
  have h6 : 6 ∣ Fintype.card (Residue F v) - 1 := by
    have hm := A.exterior_norm_mod_twelve v hv
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hm
    change Fintype.card (Residue F v) % 12 = 1 at hm
    exact dvd_trans (by decide : 6 ∣ 12) (Nat.dvd_of_mod_eq_zero (by omega))
  have hint := normalizedSextic_sq_norm_lift E F A ω hω hcompat v q.asIdeal
    q.ne_bot q.isPrime hq6 χ hχ h6
  have hemb : (σ.comp (algebraMap (𝓞 F) F)).comp (algebraMap (𝓞 E) (𝓞 F)) =
      Eisenstein.ιR E ι := by
    ext x
    change σ (algebraMap E F (x : E)) = ι (x : E)
    exact DFunLike.congr_fun hσ (x : E)
  have hnorm : ∀ x : Residue F v, ρF x = ρ (Algebra.norm (Residue E q) x) := by
    intro x
    by_cases hx : x = 0
    · subst x
      have hc0 : ρF 0 = 0 := ρF.map_nonunit (by simp)
      have hρ0 : ρ 0 = 0 := ρ.map_nonunit (by simp)
      simp only [hc0, Algebra.norm_zero, hρ0]
    · lift x to (Residue F v)ˣ using isUnit_iff_ne_zero.mpr hx
      simp only [ρF, MulChar.pow_apply_coe, MulChar.ringHomComp_apply]
      rw [← map_pow, hint x]
      exact DFunLike.congr_fun hemb _
  have hρ : orderOf ρ = 3 :=
    (Eisenstein.ρqC_facts E ω hω ι q.asIdeal q.ne_bot q.isPrime hq6).1
  have hJ : jacobiSum ρF ρF =
      -(-jacobiSum ρ ρ) ^ Module.finrank (Residue E q) (Residue F v) := by
    obtain ⟨ψbase, hψbase1⟩ :=
      (AddChar.exists_apply_ne_zero (α := Residue E q) (a := 1)).mpr one_ne_zero
    have hψbase : ψbase ≠ 1 := by
      intro h
      simpa [h] using hψbase1
    let ψF := ψbase.compAddMonoidHom
      (Algebra.trace (Residue E q) (Residue F v)).toAddMonoidHom
    have hψF : ψF ≠ 1 := by
      obtain ⟨x, hx⟩ := Algebra.trace_surjective (Residue E q) (Residue F v) 1
      intro h
      have hh := DFunLike.congr_fun h x
      change ψbase (Algebra.trace (Residue E q) (Residue F v) x) = 1 at hh
      rw [hx] at hh
      exact hψbase1 hh
    have hρsq : ρ * ρ ≠ 1 := by
      intro h
      have hd := orderOf_dvd_of_pow_eq_one (show ρ ^ 2 = 1 by simpa [pow_two] using h)
      rw [hρ] at hd
      norm_num at hd
    have hρFsq : ρF * ρF ≠ 1 := by
      intro h
      apply hρsq
      apply MulChar.ext
      intro x
      obtain ⟨y, hy⟩ := FiniteField.norm_surjective (Residue E q) (Residue F v) (x : Residue E q)
      have hh := DFunLike.congr_fun h y
      have hyne : y ≠ 0 := by
        intro hzero
        have : (x : Residue E q) = 0 := by simpa [hzero] using hy.symm
        exact x.ne_zero this
      have hyunit : IsUnit y := isUnit_iff_ne_zero.mpr hyne
      simp only [MulChar.mul_apply, hnorm, hy, MulChar.one_apply hyunit] at hh
      simpa only [MulChar.mul_apply, MulChar.one_apply x.isUnit] using hh
    exact jacobiSum_norm_pullback (Residue E q) (Residue F v) ρ ρF ψbase ψF
      hρsq hρFsq hψbase hψF hnorm (fun _ => rfl)
  have hbase : jacobiSum ρ ρ =
      -Eisenstein.ιR E ι
        (Eisenstein.primaryGenerator E (Eisenstein.q3 E q.asIdeal q.ne_bot hq6)) := by
    exact Eisenstein.jacobiSum_ρqC_eq_neg_primaryGenerator E ω hω ι
      q.asIdeal q.ne_bot q.isPrime hq6
  rw [hbase, neg_neg] at hJ
  rw [gammaTwo_cube_eq_jacobi F A v hv σ χ hχ ψ hψ]
  change jacobiSum ρF ρF / (Real.sqrt (Fintype.card (Residue F v)) : ℂ) = _
  rw [hJ, neg_div]
  congr 1
  exact ResidueFields.primary_power_div_sqrt_residue_card E F ι v q hq hq6

theorem gammaTwo_cube_canonical
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (σ : F →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf)
    (χ : MulChar (Residue F v) (𝓞 F)) (hχ : IsNormalizedSextic F A v χ)
    (ψ : AddChar (Residue F v) ℂ) (hψ : ψ ≠ 1) :
    gammaTwo F v σ χ ψ ^ 3 =
      -lambda F A (σ.comp (algebraMap (E0 F A) F)) v.asIdeal := by
  exact gammaTwo_cube (E0 F A) F A (omega0 F A) (omega0_primitive F A)
    rfl (σ.comp (algebraMap (E0 F A) F)) σ rfl v hv χ hχ ψ hψ

theorem lambdaF_mul (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (ι : E →+* ℂ) (I J : Ideal (𝓞 F)) :
    lambdaF E F ι (I * J) = lambdaF E F ι I * lambdaF E F ι J := by
  unfold lambdaF
  rw [map_mul]
  exact lambdaBase_mul E ι _ _

private theorem lambdaF_prime_unitary (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (A : SArithmeticData F) (ι : E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    ‖lambdaF E F ι v.asIdeal‖ = 1 := by
  let q := v.asIdeal.under (𝓞 E)
  have hq0 : q ≠ ⊥ := Ideal.under_ne_bot (𝓞 E) v.ne_bot
  have hq3 : q ⊔ Ideal.span {(3 : 𝓞 E)} = ⊤ := by
    by_contra h
    have heq : q = q ⊔ Ideal.span {(3 : 𝓞 E)} :=
      Ideal.IsMaximal.eq_of_le (inferInstance : q.IsMaximal) h le_sup_left
    have hle : Ideal.span {(3 : 𝓞 E)} ≤ q := heq ▸ le_sup_right
    have h3 : (3 : 𝓞 E) ∈ q := hle (Ideal.subset_span (by simp))
    have h3v : (3 : 𝓞 F) ∈ v.asIdeal := by
      have := (Ideal.mem_under (𝓞 E) v.asIdeal).mp h3
      simpa only [map_ofNat] using this
    exact hv (A.above_six v (by convert v.asIdeal.mul_mem_left 2 h3v using 1 <;> norm_num))
  have hq : q ∈ Eisenstein.I3 E := (Eisenstein.mem_I3 E q).mpr ⟨hq0, hq3⟩
  have hn : q ^ v.asIdeal.inertiaDeg (𝓞 E) ∈ Eisenstein.I3 E :=
    (Eisenstein.I3 E).pow_mem hq _
  rw [lambdaF, Ideal.relNorm_eq_pow_of_isMaximal v.asIdeal q]
  rw [lambdaBase, dif_pos hn, angular, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self]
  apply norm_ne_zero_iff.mpr
  intro h
  apply Eisenstein.primaryGenerator_ne_zero E ⟨_, hn⟩
  apply ι.injective.comp NumberField.RingOfIntegers.coe_injective
  simpa only [Eisenstein.ιR, RingHom.comp_apply, Function.comp_apply, map_zero] using h

theorem lambdaF_exterior_norm (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (A : SArithmeticData F) (ι : E →+* ℂ) (I : A.Exterior) :
    ‖lambdaF E F ι I.val‖ = 1 := by
  have hfac : ∀ p ∈ normalizedFactors I.val, ‖lambdaF E F ι p‖ = 1 := by
    intro p hp
    have hp0 : p ≠ ⊥ := ne_zero_of_mem_normalizedFactors hp
    obtain ⟨hpp, hIp⟩ := (Ideal.mem_normalizedFactors_iff I.property.1).mp hp
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hpp, hp0⟩
    have hv : v ∉ A.Sf := by
      intro hmem
      have hc : A.cS ≤ v.asIdeal := by
        change (∏ w ∈ A.Sf, w.asIdeal) ≤ v.asIdeal
        rw [← Ideal.dvd_iff_le]
        exact Finset.dvd_prod_of_mem (fun w => w.asIdeal) hmem
      have ht : (⊤ : Ideal (𝓞 F)) ≤ p := by
        rw [← I.property.2]
        exact sup_le hIp hc
      exact hpp.ne_top (top_le_iff.mp ht)
    exact lambdaF_prime_unitary E F A ι v hv
  rw [← prod_normalizedFactors_eq_self I.property.1]
  generalize normalizedFactors I.val = ps at hfac ⊢
  induction ps using Multiset.induction_on with
  | empty =>
    have htop : (⊤ : Ideal (𝓞 E)) ∈ Eisenstein.I3 E := by
      simpa only [Ideal.one_eq_top] using (Eisenstein.I3 E).one_mem
    simp [lambdaF, lambdaBase, angular, Eisenstein.primaryGenerator_ne_zero E ⟨⊤, htop⟩]
  | cons p ps ih =>
    rw [Multiset.prod_cons, lambdaF_mul, norm_mul]
    rw [hfac p (Multiset.mem_cons_self p ps), ih]
    · simp
    · intro q hq
      exact hfac q (Multiset.mem_cons_of_mem hq)

theorem infinity_restriction (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (ι : E →+* ℂ) (w : InfinitePlace F) :
    w.embedding.comp (algebraMap E F) = ι ∨
      w.embedding.comp (algebraMap E F) = (starRingEnd ℂ).comp ι := by
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ E
    (show 3 ∈ ({3} : Set ℕ) by simp) (by decide)
  have hr : InfinitePlace.nrRealPlaces E = 0 :=
    InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide) hω
  have hf : Module.finrank ℚ E = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank 3 E]
    decide
  have hc : InfinitePlace.nrComplexPlaces E = 1 := by
    have h := InfinitePlace.card_add_two_mul_card_eq_rank E
    omega
  have hsub : Subsingleton (InfinitePlace E) :=
    Fintype.card_le_one_iff_subsingleton.mp
      (by rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc])
  have heq : InfinitePlace.mk (w.embedding.comp (algebraMap E F)) =
      InfinitePlace.mk ι := Subsingleton.elim _ _
  rcases InfinitePlace.mk_eq_iff.mp heq with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq])

theorem infinity_angular (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (A : SArithmeticData F) (ι : E →+* ℂ) (w : InfinitePlace F) :
    w.IsComplex ∧ ∃ n : ℤ, (n = 1 ∨ n = -1) ∧
      ∀ z : ℂ, z ≠ 0 → infinityComponent E F ι w z = angular z ^ n := by
  refine ⟨A.complex_place w, ?_⟩
  by_cases h : w.embedding.comp (algebraMap E F) = ι
  · exact ⟨1, Or.inl rfl, fun z _ => by rw [infinityComponent, if_pos h, zpow_one]⟩
  · exact ⟨-1, Or.inr rfl, fun z hz => by
      rw [infinityComponent, if_neg h, star_angular z hz]⟩

theorem infinity_no_radial (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [Algebra E F]
    (ι : E →+* ℂ) (w : InfinitePlace F) (z : ℂ)
    (r : ℝ) (hr : 0 < r) :
    infinityComponent E F ι w ((r : ℂ) * z) = infinityComponent E F ι w z := by
  unfold infinityComponent
  rw [angular_smul_ofReal z hr]

private theorem norm_primary_congruence (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (α : 𝓞 F) (hα3 : α - 1 ∈ Ideal.span {(3 : 𝓞 F)}) :
    Algebra.intNorm (𝓞 E) (𝓞 F) α - 1 ∈ Ideal.span {(3 : 𝓞 E)} := by
  haveI : IsPrincipalIdealRing (𝓞 E) := IsCyclotomicExtension.Rat.three_pid E
  letI : Module.Free (𝓞 E) (𝓞 F) := inferInstance
  rw [Algebra.intNorm_eq_norm]
  let b := Module.Free.chooseBasis (𝓞 E) (𝓞 F)
  let r := Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)})
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.mp hα3
  have hα : α = 1 + (3 : 𝓞 E) • β := by
    simpa only [Algebra.smul_def, map_ofNat] using (eq_add_of_sub_eq' hβ)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_one, Algebra.norm_eq_matrix_det b, r.map_det]
  have hm : r.mapMatrix (Algebra.leftMulMatrix b α) = 1 := by
    rw [hα, map_add, map_one, map_smul]
    ext i j
    have h3 : r (3 : 𝓞 E) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (show (3 : 𝓞 E) ∈ ({3} : Set (𝓞 E)) by simp))
    simp only [RingHom.mapMatrix_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, h3, zero_mul, add_zero]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, h3]
  rw [hm, Matrix.det_one, sub_self]
private theorem auxiliary_embedding_not_real (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (ι : E →+* ℂ) :
    ComplexEmbedding.conjugate ι ≠ ι := by
  intro h
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ E
    (Set.mem_singleton 3) (by decide : 3 ≠ 0)
  have hp : IsPrimitiveRoot (ι ω) 3 := hω.map_of_injective ι.injective
  have he : star (ι ω) = ι ω := by
    simpa [ComplexEmbedding.conjugate_coe_eq] using DFunLike.congr_fun h ω
  have hn : ‖ι ω‖ = 1 := hp.norm'_eq_one (by decide)
  have hc : (ι ω) ^ 2 = 1 := by
    calc
      (ι ω) ^ 2 = (ι ω) * star (ι ω) := by rw [he, pow_two]
      _ = 1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  have hd := hp.dvd_of_pow_eq_one 2 hc
  norm_num at hd

private theorem angular_norm_eq_infinity_product (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (ι : E →+* ℂ) (x : F) :
    angular (ι (Algebra.norm E x)) =
      ∏ w : InfinitePlace F, infinityComponent E F ι w (w.embedding x) := by
  letI : Algebra E ℂ := ι.toAlgebra
  let k : InfinitePlace F → (F →ₐ[E] ℂ) := fun w => {
    toRingHom := if w.embedding.comp (algebraMap E F) = ι then
      w.embedding else ComplexEmbedding.conjugate w.embedding
    commutes' := by
      intro y
      split_ifs with h
      · exact DFunLike.congr_fun h y
      · obtain h' | h' := infinity_restriction E F ι w
        · exact False.elim (h h')
        · have hy := DFunLike.congr_fun h' y
          simpa [ComplexEmbedding.conjugate_coe_eq, RingHom.algebraMap_toAlgebra] using congrArg star hy }
  have hkmk (w : InfinitePlace F) : InfinitePlace.mk (k w).toRingHom = w := by
    change InfinitePlace.mk (if _ then _ else _) = w
    split_ifs <;> simp
  have hkinj : Function.Injective k := by
    intro w w' h
    simpa only [hkmk] using congrArg (fun σ : F →ₐ[E] ℂ => InfinitePlace.mk σ.toRingHom) h
  have hksurj : Function.Surjective k := by
    intro σ
    refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
    apply AlgHom.ext
    have hmk : InfinitePlace.mk (k (InfinitePlace.mk σ.toRingHom)).toRingHom =
      InfinitePlace.mk σ.toRingHom := hkmk _
    obtain he | he := InfinitePlace.mk_eq_iff.mp hmk
    · intro y; exact DFunLike.congr_fun he y
    · exfalso
      apply auxiliary_embedding_not_real E ι
      ext y
      have hc := DFunLike.congr_fun he (algebraMap E F y)
      simpa [ComplexEmbedding.conjugate_coe_eq, RingHom.algebraMap_toAlgebra] using hc
  rw [show ι (Algebra.norm E x) = ∏ σ : F →ₐ[E] ℂ, σ x from Algebra.norm_eq_prod_embeddings E ℂ x]
  have hap : ∀ s : Finset (F →ₐ[E] ℂ), angular (∏ σ ∈ s, σ x) = ∏ σ ∈ s, angular (σ x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [angular]
    | @insert σ s hσ ih => simp only [Finset.prod_insert hσ, angular_mul, ih]
  rw [show angular (∏ σ : F →ₐ[E] ℂ, σ x) = ∏ σ : F →ₐ[E] ℂ, angular (σ x) from hap Finset.univ]
  symm
  apply Fintype.prod_bijective k ⟨hkinj, hksurj⟩
  intro w
  symm
  change angular ((if w.embedding.comp (algebraMap E F) = ι then w.embedding else
    ComplexEmbedding.conjugate w.embedding) x) = _
  split_ifs with h
  · simp [infinityComponent, h]
  · simp [infinityComponent, h, angular, ComplexEmbedding.conjugate_coe_eq,
      map_div₀, Complex.norm_conj]

theorem lambdaF_principal_congruence (E F : Type) [Field E] [NumberField E]
    [Field F] [NumberField F] [IsCyclotomicExtension {3} ℚ E] [Algebra E F]
    (ι : E →+* ℂ) (α : 𝓞 F) (hα : α ≠ 0)
    (hα3 : α - 1 ∈ Ideal.span {(3 : 𝓞 F)}) :
    lambdaF E F ι (Ideal.span {α}) =
      ∏ w : InfinitePlace F, infinityComponent E F ι w (w.embedding (α : F)) := by
  let β := Algebra.intNorm (𝓞 E) (𝓞 F) α
  have hβ : β ≠ 0 := Algebra.intNorm_ne_zero.mpr hα
  have hβ3 : Eisenstein.red3 E β = 1 := by
    have hm := norm_primary_congruence E F α hα3
    have hr := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    change Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) β = 1
    simpa only [β, map_sub, map_one, sub_eq_zero] using hr
  have hI := Eisenstein.span_mem_I3_of_red3_eq_one E β hβ hβ3
  rw [lambdaF, Ideal.relNorm_singleton, lambdaBase, dif_pos hI]
  have hgen : Eisenstein.primaryGenerator E ⟨Ideal.span {β}, hI⟩ = β :=
    Eisenstein.primaryGenerator_primaryPrincipalIdeal E β hβ hβ3
  rw [hgen]
  have hnorm : (β : E) = Algebra.norm E (α : F) := Algebra.algebraMap_intNorm (K := E) (L := F) α
  change angular (ι (β : E)) = _
  rw [hnorm]
  exact angular_norm_eq_infinity_product E F ι (α : F)

end
end DedekindZetaZeroFree.DHCubic

end
