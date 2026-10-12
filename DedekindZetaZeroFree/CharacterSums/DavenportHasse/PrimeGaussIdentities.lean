module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.PrimaryAngularNormPhases
public import DedekindZetaZeroFree.Metaplectic.Weil.GlobalPhaseExtension

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

private theorem bridge (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (χ : MulChar (DHCubic.Residue F v) (𝓞 F))
    (hχ : DHCubic.IsNormalizedSextic F A v χ) :
    ∀ x : DHCubic.Residue F v,
      A.sexticResiduePowerChar σ I 1
        ((((Ideal.quotientEquivAlgOfEq (𝓞 F) hIv.symm).toRingEquiv.trans
      (ArithGaussCRT.exteriorQuotientEquiv A I))) x) =
      σ (χ x) := by
  let e : DHCubic.Residue F v ≃+* (A.R ⧸ A.extendIdeal I) :=
    ((Ideal.quotientEquivAlgOfEq (𝓞 F) hIv.symm).toRingEquiv.trans
      (ArithGaussCRT.exteriorQuotientEquiv A I))
  letI : Nontrivial (A.R ⧸ A.extendIdeal I) := e.symm.toEquiv.nontrivial
  intro x
  change A.sexticResiduePowerChar σ I 1 (e x) = σ (χ x)
  by_cases hx : x = 0
  · rw [hx, e.map_zero, MulChar.map_zero, MulChar.map_zero]
    exact (map_zero σ).symm
  have hxu : IsUnit x := isUnit_iff_ne_zero.mpr hx
  let u : (DHCubic.Residue F v)ˣ := hxu.unit
  let eu := Units.map e.toMonoidHom u
  obtain ⟨i, hi, hci⟩ := (hχ x hx).1
  obtain ⟨j, hj, hcj, hrj⟩ := A.sexticResidueFamily_normalized.2.1 I v hIv eu
  have he_x : (eu : A.R ⧸ A.extendIdeal I) = e x := by simp [eu, u]
  have hiq : Ideal.Quotient.mk (A.extendIdeal I)
      (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * i))) =
      (e x) ^ ((Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6) := by
    have hh := congrArg e (hχ x hx).2
    rw [hci] at hh
    have hc : Nat.card (A.R ⧸ A.extendIdeal I) = Fintype.card (DHCubic.Residue F v) := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rw [hc]
    simpa [e, ← hIv] using hh
  have hji : j = i := by
    have hp := A.exterior_sextic_primitive I (hIv ▸ v.isPrime.ne_top)
    apply hp.pow_inj hj hi
    have hh := hrj.trans (he_x ▸ hiq.symm)
    simpa only [map_pow, pow_mul] using hh
  have hval : (A.sexticResidueFamily I eu : F) = (χ x : F) := by
    rw [hcj, hci, hji]
    rfl
  have hn : sexticExponent 1 = 1 := by decide
  rw [sexticResiduePowerChar, hn, pow_one, ← he_x, MulChar.ofUnitHom_coe]
  change σ (A.sexticResidueFamily I eu) = σ (χ x)
  exact congrArg σ hval

private theorem gaussBridge (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p)
    (χ : MulChar (DHCubic.Residue F v) (𝓞 F))
    (hχ : DHCubic.IsNormalizedSextic F A v χ) :
    let e := (Ideal.quotientEquivAlgOfEq (𝓞 F) hIv.symm).toRingEquiv.trans
      (ArithGaussCRT.exteriorQuotientEquiv A I)
    let ψ := (Circle.coeHom.compAddChar (A.residueTraceCharacter hS I p hp)).compAddMonoidHom
      e.toAddMonoidHom
    ∀ j : ℕ, j < 6 → A.idealGauss σ hS I p hp j =
      FiniteGauss.normalizedGaussPower
        (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) ψ j := by
  dsimp only
  let e := (Ideal.quotientEquivAlgOfEq (𝓞 F) hIv.symm).toRingEquiv.trans
      (ArithGaussCRT.exteriorQuotientEquiv A I)
  letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ A.extendIdeal I) := Fintype.ofFinite _
  intro j hj
  have hn : sexticExponent (j : ℤ) = j := by
    unfold sexticExponent
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg j) (by omega), Int.toNat_natCast]
  have hchar : (fun x => MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp
      (A.sexticResidueFamily I)) (e x)) =
      (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) := by
    funext x
    simpa only [sexticResiduePowerChar, show sexticExponent 1 = 1 from rfl,
      pow_one, MulChar.ringHomComp_apply, RingHom.comp_apply] using bridge A σ I v hIv χ hχ x
  have hpow (x : DHCubic.Residue F v) :
      A.sexticResiduePowerChar σ I j (e x) =
        (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F)) ^ j) x := by
    rw [sexticResiduePowerChar, hn]
    by_cases hx : IsUnit x
    · let u := hx.unit
      have hxu : (u : DHCubic.Residue F v) = x := hx.unit_spec
      have heu : (Units.map e.toMonoidHom u : A.R ⧸ A.extendIdeal I) = e x := by
        simp [hxu]
      rw [← heu, MulChar.pow_apply_coe, ← hxu, MulChar.pow_apply_coe]
      exact congrArg (fun z : ℂ => z ^ j) (congrFun hchar u)
    · have hex : ¬ IsUnit (e x) := fun h => hx (by simpa using h.map e.symm.toMonoidHom)
      rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit _ hex]
  have hc : A.exteriorNorm I = (Fintype.card (DHCubic.Residue F v) : ℝ) := by
    change (Ideal.absNorm I.val : ℝ) = _
    rw [← A.exteriorResidue_card I, ← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  unfold idealGauss FiniteGauss.normalizedGaussPower FiniteGauss.gaussPower gaussSum
  rw [hc, div_eq_mul_inv, mul_comm]
  congr 1
  rw [← e.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change A.sexticResiduePowerChar σ I j (e x) * _ = _
  rw [hpow]
  rfl

private theorem primeIdentities
    (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces) (σ : F →+* ℂ)
    (B : Subgroup A.V) (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F)) :
    A.idealGauss σ hS I p hp 2 ^ 3 =
      -DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val ∧
    A.idealGauss σ hS I p hp 1 * A.idealGauss σ hS I p hp 2 =
      star (σ (A.sexticResidue I (4 : A.R))) * A.idealGauss σ hS I p hp 3 *
        A.idealGauss σ hS I p hp 2 ^ 3 := by
  have hv : v ∉ A.Sf := by
    intro hv
    have h := (A.exterior_iff ⟨I.val, I.prop.1⟩).mp I.prop.2 v hv
    rw [hIv, sup_idem] at h
    exact v.isPrime.ne_top h
  obtain ⟨χ, hχ, _⟩ := DHCubic.existsUnique_normalizedSextic F A v hv
  let e := (Ideal.quotientEquivAlgOfEq (𝓞 F) hIv.symm).toRingEquiv.trans
      (ArithGaussCRT.exteriorQuotientEquiv A I)
  let ψ := (Circle.coeHom.compAddChar (A.residueTraceCharacter hS I p hp)).compAddMonoidHom
      e.toAddMonoidHom
  have hψ : ψ ≠ 1 := by
    intro h
    apply A.residueTraceCharacter_prime_ne_one hS B I (hIv ▸ v.isPrime) p hp a hap ha
    ext x
    have hh := congrArg (fun f : AddChar (DHCubic.Residue F v) ℂ => f (e.symm x)) h
    change Circle.coeHom ((A.residueTraceCharacter hS I p hp) (e (e.symm x))) = 1 at hh
    rw [e.apply_symm_apply] at hh
    exact hh
  have hg (j : ℕ) (hj : j < 6) : A.idealGauss σ hS I p hp j =
      FiniteGauss.normalizedGaussPower (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) ψ j :=
    gaussBridge A σ hS I v hIv p hp χ hχ j hj
  have hg1 := hg 1 (by decide)
  have hg2 := hg 2 (by decide)
  have hg3 := hg 3 (by decide)
  norm_num only [Nat.cast_ofNat] at hg1 hg2 hg3
  have hcub : A.idealGauss σ hS I p hp 2 ^ 3 =
      -DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val := by
    rw [hg2]
    exact hIv.symm ▸ DHCubic.gammaTwo_cube_canonical F A σ v hv χ hχ ψ hψ
  refine ⟨hcub, ?_⟩
  have hQ : Fintype.card (DHCubic.Residue F v) % 12 = 1 := by
    have hcard : Fintype.card (DHCubic.Residue F v) = Ideal.absNorm v.asIdeal := by
      rw [← Nat.card_eq_fintype_card]
      exact (Submodule.cardQuot_apply v.asIdeal).symm
    rw [hcard]
    exact A.exterior_norm_mod_twelve v hv
  have hdup := FiniteGauss.normalizedGaussPower_sextic_duplication
    (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) ψ hQ
      (DHCubic.orderOf_normalizedSextic_complex F A v hv σ χ hχ) hψ
  have hfour : (χ.ringHomComp (σ.comp (algebraMap (𝓞 F) F))) (4 : DHCubic.Residue F v) =
      σ (A.sexticResidue I (4 : A.R)) := by
    have hb := bridge A σ I v hIv χ hχ (4 : DHCubic.Residue F v)
    have he4 : e (4 : DHCubic.Residue F v) = 4 := map_ofNat e 4
    change A.sexticResiduePowerChar σ I 1 (e 4) = _ at hb
    rw [he4] at hb
    change σ (χ 4) = _
    rw [← hb]
    rw [sexticResiduePowerChar, show sexticExponent 1 = 1 from rfl, pow_one]
    change MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily I)) 4 =
      σ (MulChar.ofUnitHom (A.sexticResidueFamily I) 4)
    by_cases hu : IsUnit (4 : A.R ⧸ A.extendIdeal I)
    · let u := hu.unit
      have huu : (u : A.R ⧸ A.extendIdeal I) = 4 := hu.unit_spec
      rw [← huu, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
      rfl
    · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, map_zero]
  rw [hg1, hg2, hg3]
  rw [hfour] at hdup
  exact hdup

theorem primeGaussIdentities
    (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces) (σ : F →+* ℂ)
    (B : Subgroup A.V) (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F)) :
    A.idealGauss σ hS I p hp 2 ^ 3 =
      -DHCubic.lambda F A (σ.comp (algebraMap (DHCubic.E0 F A) F)) I.val ∧
    A.idealGauss σ hS I p hp 1 * A.idealGauss σ hS I p hp 2 =
      star (σ (A.sexticResidue I (4 : A.R))) * A.idealGauss σ hS I p hp 3 *
        A.idealGauss σ hS I p hp 2 ^ 3 :=
  primeIdentities A hS σ B I v hIv p hp a ha hap

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
