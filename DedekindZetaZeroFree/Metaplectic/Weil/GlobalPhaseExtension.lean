module

public import DedekindZetaZeroFree.Metaplectic.Weil.IsotropicComplementSignCharacter
public import DedekindZetaZeroFree.Adeles.Characters.LocalArithmeticLaws
public import DedekindZetaZeroFree.Metaplectic.Weil.NormalizedLocalIndicesAndProductFormula

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]
set_option backward.isDefEq.respectTransparency false

private lemma two_six_coeff (A : SArithmeticData F) (σ : F →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    σ (((A.actualLocalSymbol v 2 (Or.inl rfl) a b : Fˣ) : F)) =
    σ (((A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl)) a b : Fˣ) : F)) ^ 3 := by
  have he : ((A.actualLocalSymbol v 2 (Or.inl rfl) a b : Fˣ) : F) =
      ((A.actualLocalSymbol v 6 (Or.inr (Or.inr rfl)) a b : Fˣ) : F) ^ 3 := by
    apply (algebraMap F (v.adicCompletion F)).injective
    have h := congrArg Units.val (A.actualLocalSymbol_two_six v a b)
    simpa only [Units.val_pow_eq_pow_val, A.finiteRootsEquiv_apply, map_pow] using h
  rw [he, map_pow]

theorem actualWeilSStructuralLaws (A : SArithmeticData F) (σ : F →+* ℂ)
    (H : A.V → A.V → Fˣ)
    (hActual : ∀ x y : A.G, H (QuotientGroup.mk' A.sixthPowers x)
      (QuotientGroup.mk' A.sixthPowers y) = (A.H_S x y : Fˣ)) :
    A.WeilSStructuralLaws H σ A.complexWeilPhase (fun v => A.finiteWeilPhase v.val) := by
  refine ⟨A.complexWeilPhase_one, (fun v => A.finiteWeilPhase_one v.val),
    A.complexWeilPhase_mul_sq, (fun v => A.finiteWeilPhase_mul_sq v.val), ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective A.sixthPowers x
    rw [hActual, ← A.H_S6_on_representatives, A.H_S6_alternating]
    rfl
  · intro x y
    rw [hActual]
    have hloc (v : {v // v ∈ A.Sf}) :
        A.finiteWeilPhase v.val (x.2 v) * A.finiteWeilPhase v.val (y.2 v) =
        σ (((A.actualLocalSymbol v.val 6 (Or.inr (Or.inr rfl)) (x.2 v) (y.2 v) : Fˣ) : F)) ^ 3 *
          A.finiteWeilPhase v.val ((x * y).2 v) := by
      have h := A.finiteWeilIndex_mul σ v.val (x.2 v) (y.2 v)
      change A.finiteWeilPhase v.val (x.2 v) * A.finiteWeilPhase v.val (y.2 v) = _ at h
      rw [two_six_coeff] at h
      exact h
    simp only [weilSProduct, complexWeilPhase, complexGamma, div_self one_ne_zero,
      Finset.prod_const_one, one_mul]
    rw [← Finset.prod_mul_distrib]
    simp only [hloc, Finset.prod_mul_distrib]
    congr 1
    simp only [H_S, SubmonoidClass.coe_finsetProd, Units.coe_prod, map_prod, Finset.prod_pow]

theorem classCharacterExtension_infinity (A : SArithmeticData F) (B : Subgroup A.V)
    (φ : B →* ℂˣ) (D : A.ClassCharacterExtension B φ)
    (w : InfinitePlace F) (z : w.Completionˣ) :
    A.ideleInfiniteComponent D.ideleCharacter w z = 1 := by
  obtain ⟨t, ht⟩ := A.infinite_unit_isPower w 6 (Or.inr (Or.inr rfl)) z
  let y : A.G := (Pi.mulSingle w z, 1)
  have hy : QuotientGroup.mk' A.sixthPowers y = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨(Pi.mulSingle w t, 1), ?_⟩
    apply Prod.ext
    · funext u
      by_cases hu : u = w
      · subst u; simpa [y] using ht
      · simp [y, Pi.mulSingle_eq_of_ne hu]
    · simp [y]
  have h := D.local_split_value y (1, 1) (by simpa using hy)
  have h' := congrArg (fun u : ℂˣ => (u : ℂ)) h
  have he : A.ideleSInverseProduct D.ideleCharacter y = 1 := by
    apply Circle.ext
    simpa using h'
  have hx : A.ideleSInverseProduct D.ideleCharacter y =
      (A.ideleInfiniteComponent D.ideleCharacter w z)⁻¹ := by
    simp only [ideleSInverseProduct, y, map_one, inv_one, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single w]
    · simp
    · intro u _ huw
      simp [Pi.mulSingle_eq_of_ne huw]
    · simp
  rw [hx] at he
  exact inv_eq_one.mp he

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection

end
