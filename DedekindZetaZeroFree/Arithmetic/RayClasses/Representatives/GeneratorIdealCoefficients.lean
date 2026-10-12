module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PerfectTraceQuotientPairing
public import DedekindZetaZeroFree.Theta.RayClasses.WeightedIdealBlocks
public import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteRings.PrimitiveCharacterFourierTransform
public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.RankOne
public import DedekindZetaZeroFree.Algebra.RankOneModules.GeneratorTorsor

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [nf : NumberField F]
include nf

private theorem generator_of_coprime
    {m : Ideal (𝓞 F)} (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (ξ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)})
    (hc : integralElementIdeal L ξ ⊔ m = ⊤) :
    Function.Surjective (fun k : 𝓞 F ⧸ m => k •
      fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ) := by
  have hs : (m : FractionalIdeal (𝓞 F)⁰ F) +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ.val * (L : FractionalIdeal (𝓞 F)⁰ F)⁻¹ = 1 := by
    have h := congrArg (fun a : Ideal (𝓞 F) => (a : FractionalIdeal (𝓞 F)⁰ F)) hc
    simpa only [FractionalIdeal.coeIdeal_sup, FractionalIdeal.coeIdeal_top,
      integralElementIdeal_coe, add_comm] using h
  have hs' := congrArg (fun J : FractionalIdeal (𝓞 F)⁰ F => J * L) hs
  rw [add_mul, mul_assoc, inv_mul_cancel₀ (Units.ne_zero L), mul_one, one_mul] at hs'
  intro q
  obtain ⟨x, rfl⟩ := fractionalIdealQuotientMk_surjective _ _ q
  have hx : x.val ∈ (m : FractionalIdeal (𝓞 F)⁰ F) * L +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ.val := by rw [hs']; exact x.property
  obtain ⟨a, ha, b, hb, hab⟩ := (FractionalIdeal.mem_add _ _ _).mp hx
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 F)⁰).mp hb
  refine ⟨Ideal.Quotient.mk m r, ?_⟩
  change Ideal.Quotient.mk m r • Submodule.Quotient.mk
    (p := fractionalResidueDenominator m (L : FractionalIdeal (𝓞 F)⁰ F)) ξ =
    Submodule.Quotient.mk x
  rw [fractionalResidueModule_mk_smul_mk]
  apply (Submodule.Quotient.eq _).mpr
  change r • ξ.val - x.val ∈ (m : FractionalIdeal (𝓞 F)⁰ F) * L
  have he : r • ξ.val - x.val = -a := by rw [← hr] at hab; rw [← hab]; abel
  rw [he]
  exact (((m : FractionalIdeal (𝓞 F)⁰ F) * L : FractionalIdeal (𝓞 F)⁰ F) :
    Submodule (𝓞 F) F).neg_mem ha

private theorem generator_injective
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (q : fractionalResidueModule m (L : FractionalIdeal (𝓞 F)⁰ F))
    (hq : Function.Surjective (fun k : 𝓞 F ⧸ m => k • q)) :
    Function.Injective (fun k : 𝓞 F ⧸ m => k • q) := by
  let e := fractionalResidueEquiv m (L : FractionalIdeal (𝓞 F)⁰ F) hm (Units.ne_zero L)
  obtain ⟨a, ha⟩ := hq (e 1)
  have hunit : IsUnit (e.symm q) := by
    have he : a * e.symm q = 1 := by
      simpa using congrArg e.symm ha
    exact ⟨⟨e.symm q, a, by simpa [mul_comm] using he, he⟩, rfl⟩
  intro a b hab
  have he : a * e.symm q = b * e.symm q := by
    simpa using congrArg e.symm hab
  exact hunit.mul_right_cancel he

theorem integralElementIdeal_generator_coprime
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (ξ₀ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)})
    (hgen : Function.Surjective (fun k : 𝓞 F ⧸ m =>
      k • fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ₀)) :
    ξ₀.val ≠ 0 ∧ integralElementIdeal L ξ₀ ≠ ⊥ ∧
      integralElementIdeal L ξ₀ ⊔ m = ⊤ := by
  have hne : (L : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := Units.ne_zero L
  obtain ⟨hξ, _, hb, _, hsum⟩ := fractionalResidueGenerator_lift_properties m
    (L : FractionalIdeal (𝓞 F)⁰ F) hm hmt hne _ hgen ξ₀.val ξ₀.property rfl
  have hcoe : (integralElementIdeal L ξ₀ : FractionalIdeal (𝓞 F)⁰ F) =
      fractionalResidueLiftIdeal (L : FractionalIdeal (𝓞 F)⁰ F) ξ₀.val :=
    integralElementIdeal_coe L ξ₀
  refine ⟨hξ, ?_, ?_⟩
  · intro hz
    apply hb
    rw [← hcoe, hz, FractionalIdeal.coeIdeal_bot]
  · apply FractionalIdeal.coeIdeal_injective (K := F)
    simpa only [FractionalIdeal.coeIdeal_sup, FractionalIdeal.coeIdeal_top, hcoe,
      add_comm] using hsum

private theorem coefficient_mul_numerator
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (ξ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)}) :
    (integralElementIdeal L ξ : FractionalIdeal (𝓞 F)⁰ F) *
      (L : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ.val := by
  rw [integralElementIdeal_coe, mul_assoc, inv_mul_cancel₀ (Units.ne_zero L), mul_one]

private theorem coefficient_scalar_comparison
    {m : Ideal (𝓞 F)} (hmt : m ≠ ⊤)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (ξ₀ ξ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)})
    (hξ₀ : ξ₀.val ≠ 0) (hc : integralElementIdeal L ξ₀ ⊔ m = ⊤)
    (a : 𝓞 F) (hcong : ξ.val - a • ξ₀.val ∈
      (m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ d γ : 𝓞 F, d ≠ 0 ∧ d - 1 ∈ m ∧
      Ideal.Quotient.mk m γ = Ideal.Quotient.mk m a ∧
      Ideal.span {d} * integralElementIdeal L ξ =
        Ideal.span {γ} * integralElementIdeal L ξ₀ := by
  obtain ⟨d, hd, e, he, hde⟩ :=
    Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hc)
  have hd1 : d - 1 ∈ m := by
    have heq : d - 1 = -e := by rw [← hde]; ring
    rw [heq]
    exact m.neg_mem he
  have hdne : d ≠ 0 := by
    intro hz
    have hone : (1 : 𝓞 F) ∈ m := by simpa [hz] using m.neg_mem hd1
    exact hmt ((Ideal.eq_top_iff_one _).mpr hone)
  have hdmem : (d : F) ∈ (integralElementIdeal L ξ₀ : FractionalIdeal (𝓞 F)⁰ F) :=
    FractionalIdeal.mem_coeIdeal_of_mem (𝓞 F)⁰ hd
  have hdx : (d : F) * ξ.val ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ₀.val := by
    rw [← coefficient_mul_numerator L ξ₀]
    exact FractionalIdeal.mul_mem_mul hdmem ξ.property
  obtain ⟨γ, hγ⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 F)⁰).mp hdx
  have hdiff : (d : F) * (ξ.val - a • ξ₀.val) ∈
      (m : FractionalIdeal (𝓞 F)⁰ F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ ξ₀.val := by
    rw [← coefficient_mul_numerator L ξ₀, mul_left_comm
      (m : FractionalIdeal (𝓞 F)⁰ F)]
    exact FractionalIdeal.mul_mem_mul hdmem hcong
  rw [mul_comm] at hdiff
  obtain ⟨r, hr, her⟩ := FractionalIdeal.mem_singleton_mul.mp hdiff
  obtain ⟨r', hr', hrr⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 F)⁰).mp hr
  have hγda : γ - d * a = r' := by
    apply IsFractionRing.injective (𝓞 F) F
    apply mul_right_cancel₀ hξ₀
    simp only [map_sub, map_mul]
    rw [← hrr] at her
    simp only [Algebra.smul_def] at hγ her
    linear_combination hγ + her
  have hγa : γ - a ∈ m := by
    have hh : γ - a = (γ - d * a) + (d - 1) * a := by ring
    rw [hh, hγda]
    exact m.add_mem hr' (m.mul_mem_right a hd1)
  refine ⟨d, γ, hdne, hd1,
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hγa, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := F)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
    integralElementIdeal_coe]
  rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
  congr 2
  simpa only [Algebra.smul_def] using hγ.symm

private theorem scalar_coprime_iff (m : Ideal (𝓞 F)) (a : 𝓞 F) :
    Ideal.span {a} ⊔ m = ⊤ ↔ IsUnit (Ideal.Quotient.mk m a) := by
  constructor
  · intro hc
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hc)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hb
    have hh : Ideal.Quotient.mk m a * Ideal.Quotient.mk m r = 1 := by
      rw [← map_mul]
      apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr
      have he : a * r - 1 = -c := by rw [← hbc]; ring
      rw [he]
      exact m.neg_mem hc
    exact ⟨⟨Ideal.Quotient.mk m a, Ideal.Quotient.mk m r, hh, by simpa [mul_comm] using hh⟩, rfl⟩
  · rintro ⟨u, hu⟩
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (𝓞 F ⧸ m)ˣ) : 𝓞 F ⧸ m)
    have hh : Ideal.Quotient.mk m (a * r) = 1 := by rw [map_mul, ← hu, hr]; exact u.val_inv
    have hm := (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hh
    apply (Ideal.eq_top_iff_one _).mpr
    have ha : a * r ∈ Ideal.span {a} ⊔ m :=
      Ideal.mem_sup_left (Ideal.mul_mem_right r _ (Ideal.mem_span_singleton_self a))
    simpa using (Ideal.span {a} ⊔ m).sub_mem ha (Ideal.mem_sup_right hm)

private theorem scalar_character_extend
    (hF : NumberField.IsTotallyComplex F) {m : Ideal (𝓞 F)}
    (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (a : 𝓞 F) :
    η (Ideal.span {a}) =
      unitCharExtend ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η))
        (Ideal.Quotient.mk m a) := by
  classical
  by_cases hu : IsUnit (Ideal.Quotient.mk m a)
  · obtain ⟨u, hu⟩ := hu
    have ha : a ≠ 0 := by
      intro hz
      letI : Nontrivial (𝓞 F ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hmt
      exact u.ne_zero (by simpa [hz] using hu)
    rw [← hu, unitCharExtend_coe]
    exact (residueRayCharacter_apply hF hm hmt η a ha
      ((scalar_coprime_iff m a).mpr ⟨u, hu⟩) u hu).symm
  · rw [unitCharExtend_nonunit _ hu]
    exact (η.eq_zero_iff' _).mpr (Or.inr (fun hc => hu ((scalar_coprime_iff m a).mp hc)))

private theorem scalar_positive (hF : NumberField.IsTotallyComplex F)
    (a : 𝓞 F) : ∀ φ : F →+* ℝ, 0 < φ (a : F) := by
  letI := hF
  intro φ
  exfalso
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  change star (Complex.ofRealHom.comp φ) = Complex.ofRealHom.comp φ
  ext x
  simp

theorem integralElementIdeal_residue_coefficient
    (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (ξ₀ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)})
    (hgen : Function.Surjective (fun k : 𝓞 F ⧸ m =>
      k • fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ₀))
    (ξ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)}) (k : 𝓞 F ⧸ m)
    (hcong : fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
      ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ =
      k • fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ₀) :
    η (integralElementIdeal L ξ) =
      unitCharExtend ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)) k *
        η (integralElementIdeal L ξ₀) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective k
  have hh : ξ.val - a • ξ₀.val ∈
      (m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F) := by
    change Submodule.Quotient.mk (p := fractionalResidueDenominator m
      (L : FractionalIdeal (𝓞 F)⁰ F)) ξ = Ideal.Quotient.mk m a •
      Submodule.Quotient.mk (p := fractionalResidueDenominator m
        (L : FractionalIdeal (𝓞 F)⁰ F)) ξ₀ at hcong
    rw [fractionalResidueModule_mk_smul_mk] at hcong
    have hd := (Submodule.Quotient.eq (fractionalResidueDenominator m
      (L : FractionalIdeal (𝓞 F)⁰ F))).mp hcong
    exact hd
  have hc := integralElementIdeal_generator_coprime hm hmt L ξ₀ hgen
  obtain ⟨d, γ, hd, hd1, hres, hid⟩ :=
    coefficient_scalar_comparison hmt L ξ₀ ξ hc.1 hc.2.2 a hh
  have heval := congrArg η hid
  rw [η.map_mul', η.map_mul',
    η.map_span' d hd hd1 (scalar_positive hF d), one_mul,
    scalar_character_extend hF hm hmt η γ, hres] at heval
  exact heval

theorem integralElementIdeal_residue_coprime_iff
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (ξ₀ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)})
    (hgen : Function.Surjective (fun k : 𝓞 F ⧸ m =>
      k • fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ₀))
    (ξ : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)}) (k : 𝓞 F ⧸ m)
    (hcong : fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
      ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ =
      k • fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ₀) :
    (integralElementIdeal L ξ ≠ ⊥ ∧ integralElementIdeal L ξ ⊔ m = ⊤) ↔
      IsUnit k := by
  let q₀ : fractionalResidueModule m (L : FractionalIdeal (𝓞 F)⁰ F) :=
    fractionalIdealQuotientMk _ _ ξ₀
  have hgen' : Function.Bijective (fun r : 𝓞 F ⧸ m => r • q₀) :=
    ⟨generator_injective hm L q₀ hgen, hgen⟩
  constructor
  · intro hc
    have hs := generator_of_coprime L ξ hc.2
    have hs' : Function.Bijective (fun r : 𝓞 F ⧸ m => r • (k • q₀)) := by
      rw [← hcong]
      exact ⟨generator_injective hm L _ hs, hs⟩
    exact (smul_mem_rankOneGenerators_iff q₀ hgen' k).mp hs'
  · intro hk
    have hs := (smul_mem_rankOneGenerators_iff q₀ hgen' k).mpr hk
    have hs' : Function.Surjective (fun r : 𝓞 F ⧸ m => r •
        fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
          ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) ξ) := by
      rw [hcong]
      exact hs.2
    exact (integralElementIdeal_generator_coprime hm hmt L ξ hs').2

theorem traceCoefficient_denominator_eq
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hL : (L : FractionalIdeal (𝓞 F)⁰ F) =
      (m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * codifferentFractionalIdeal F) :
    (m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F) =
      codifferentFractionalIdeal F := by
  rw [hL, ← mul_assoc, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hm),
    one_mul]

theorem integralElementIdeal_trace_coe
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hL : (L : FractionalIdeal (𝓞 F)⁰ F) =
      (m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * codifferentFractionalIdeal F)
    (β : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)}) :
    (integralElementIdeal L β : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ β.val *
        (m : FractionalIdeal (𝓞 F)⁰ F) * (codifferentFractionalIdeal F)⁻¹ := by
  rw [integralElementIdeal_coe]
  have hinv := congrArg Inv.inv hL
  rw [mul_inv, inv_inv] at hinv
  rw [hinv, mul_assoc]

theorem integralElementIdeal_trace_residue_coefficient
    (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hL : (L : FractionalIdeal (𝓞 F)⁰ F) =
      (m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * codifferentFractionalIdeal F)
    (β₀ β : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)})
    (k : 𝓞 F ⧸ m) :
    letI := rayTraceQuotientModule m hm
    let q₀ : rayTraceQuotient m := fractionalIdealQuotientMk _
      (codifferentFractionalIdeal F) ⟨β₀.val, by rw [← hL]; exact β₀.property⟩
    let q : rayTraceQuotient m := fractionalIdealQuotientMk _
      (codifferentFractionalIdeal F) ⟨β.val, by rw [← hL]; exact β.property⟩
    Function.Surjective (fun r : 𝓞 F ⧸ m => r • q₀) → q = k • q₀ →
      integralElementIdeal L β₀ ≠ ⊥ ∧ integralElementIdeal L β₀ ⊔ m = ⊤ ∧
      η (integralElementIdeal L β) =
        unitCharExtend ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)) k *
          η (integralElementIdeal L β₀) ∧
      ((integralElementIdeal L β ≠ ⊥ ∧ integralElementIdeal L β ⊔ m = ⊤) ↔
        IsUnit k) := by
  dsimp only
  intro hgen hcong
  have hden := traceCoefficient_denominator_eq hm L hL
  letI := rayTraceQuotientModule m hm
  have heq (r : 𝓞 F)
      (x y : {x : F // x ∈ (L : FractionalIdeal (𝓞 F)⁰ F)}) :
      (Ideal.Quotient.mk m r • fractionalIdealQuotientMk
        ((m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * codifferentFractionalIdeal F)
        (codifferentFractionalIdeal F) ⟨x.val, by rw [← hL]; exact x.property⟩ =
        fractionalIdealQuotientMk
          ((m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * codifferentFractionalIdeal F) (codifferentFractionalIdeal F)
          ⟨y.val, by rw [← hL]; exact y.property⟩) ↔
      (Ideal.Quotient.mk m r • fractionalIdealQuotientMk _
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) x =
        fractionalIdealQuotientMk _
          ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) y) := by
    let I := (m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * codifferentFractionalIdeal F
    let x' : I.coeToSubmodule := ⟨x.val, by dsimp [I]; rw [← hL]; exact x.property⟩
    let y' : I.coeToSubmodule := ⟨y.val, by dsimp [I]; rw [← hL]; exact y.property⟩
    change r • fractionalIdealQuotientMk I (codifferentFractionalIdeal F) x' =
      fractionalIdealQuotientMk I (codifferentFractionalIdeal F) y' ↔ _
    change fractionalIdealQuotientMk I (codifferentFractionalIdeal F) (r • x') =
      fractionalIdealQuotientMk I (codifferentFractionalIdeal F) y' ↔
      Ideal.Quotient.mk m r • Submodule.Quotient.mk
        (p := fractionalResidueDenominator m (L : FractionalIdeal (𝓞 F)⁰ F)) x =
        Submodule.Quotient.mk
          (p := fractionalResidueDenominator m (L : FractionalIdeal (𝓞 F)⁰ F)) y
    rw [fractionalResidueModule_mk_smul_mk]
    simp only [fractionalIdealQuotientMk, Submodule.mkQ_apply, Submodule.Quotient.eq,
      Submodule.mem_comap, Submodule.coe_sub, Submodule.coe_smul]
    rw [hden]
    rfl
  have hgen' : Function.Surjective (fun r : 𝓞 F ⧸ m => r •
      fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) β₀) := by
    intro q
    obtain ⟨y, rfl⟩ := fractionalIdealQuotientMk_surjective _ _ q
    obtain ⟨r, hr⟩ := hgen (fractionalIdealQuotientMk
          ((m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * codifferentFractionalIdeal F) (codifferentFractionalIdeal F)
      ⟨y.val, by rw [← hL]; exact y.property⟩)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨Ideal.Quotient.mk m r, (heq r β₀ y).mp hr⟩
  have hcong' : fractionalIdealQuotientMk (L : FractionalIdeal (𝓞 F)⁰ F)
      ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) β = k •
      fractionalIdealQuotientMk _ ((m : FractionalIdeal (𝓞 F)⁰ F) * (L : FractionalIdeal (𝓞 F)⁰ F)) β₀ := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective k
    exact ((heq r β₀ β).mp hcong.symm).symm
  obtain ⟨_, hb, hc⟩ := integralElementIdeal_generator_coprime hm hmt L β₀ hgen'
  exact ⟨hb, hc, integralElementIdeal_residue_coefficient hF hm hmt η L β₀ hgen' β k hcong',
    integralElementIdeal_residue_coprime_iff hm hmt L β₀ hgen' β k hcong'⟩

end DedekindZetaZeroFree.Hecke.Theta

end
