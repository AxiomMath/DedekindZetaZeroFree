module

public import DedekindZetaZeroFree.Theta.Unfolding.RayClasses.DualGaussianNormalization
public import DedekindZetaZeroFree.CharacterSums.Gauss.RayClasses.NormalizedFactor
public import DedekindZetaZeroFree.Arithmetic.Ideals.RamifiedTraceDualClassPermutation

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [instNF : NumberField F]
variable {m : Ideal (𝓞 F)} {hm : m ≠ ⊥}
variable {η : DedekindZetaZeroFree.RayClassCharacter F m}

include instNF

 noncomputable def barData {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (χ : RayCharacterData F m hm η) : RayCharacterData F m hm (conjugateRayCharacter η) where
  ψ := (starRingEnd ℂ).toMonoidHom.comp χ.ψ
  descent := by
    intro I
    rw [conjugateRayCharacter_apply, χ.descent]
    cases rayIdealClass F m hm I <;> simp
  principal_iff := by
    rw [conjugateRayCharacter_isPrincipal_iff, χ.principal_iff]
    constructor
    · intro h
      simp [h]
    · intro h
      apply MonoidHom.ext
      intro c
      have hc := DFunLike.congr_fun h c
      simpa using congrArg (starRingEnd ℂ) hc

private theorem primal_sum (hF : NumberField.IsTotallyComplex F) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (χ : RayCharacterData F m hm η) (D : RayThetaRepresentatives F m hm)
    (u : ℝ) (hu : 0 < u) :
    letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
    letI : Fintype (ClassGroup (𝓞 F)) := Fintype.ofFinite _
    (∑ c, χ.ψ c * RayTheta.fδ (D.coset c) ∅ u) =
      ∑ C, weightedIdealBlock hF hm hmt η
        (FractionalIdeal.mk0 F (inverseOrdinaryClassCoprimeRepresentative F m hm C)) u := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  letI : Fintype (ClassGroup (𝓞 F)) := Fintype.ofFinite _
  rw [← Finset.sum_fiberwise Finset.univ (rayToOrdinary F m hm)]
  apply Finset.sum_congr rfl
  intro C hC
  let a := inverseOrdinaryClassCoprimeRepresentative F m hm C
  have ha : (a : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.ne_zero a.property
  have hclass : ClassGroup.mk F (rayIdealFractionalIdeal F (a : Ideal (𝓞 F)) ha) = C⁻¹ :=
    mk_inverseOrdinaryClassCoprimeRepresentative F m hm C
  have haeq : rayIdealFractionalIdeal F (a : Ideal (𝓞 F)) ha = FractionalIdeal.mk0 F a := by
    apply Units.ext
    rfl
  simpa only [haeq, a, mk_inverseOrdinaryClassCoprimeRepresentative, inv_inv] using
    rayTheta_primal_fiber_eq_weightedIdealBlock hF m (a : Ideal (𝓞 F)) hm ha
      (inverseOrdinaryClassCoprimeRepresentative_coprime F m hm C) hmt η χ D u hu

private theorem uniform_aux (hF : NumberField.IsTotallyComplex F) (hmt : m ≠ ⊤)
    {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (χ : RayCharacterData F m hm η) (hprim : η.IsPrimitive) :
    ∃ w : ℂ, w ≠ 0 ∧ ‖w‖ = 1 ∧
      ∀ (D : RayThetaRepresentatives F m hm) (t : ℝ), 0 < t →
        normalizedRayDualTheta D χ.ψ t = w * normalizedRayConjugateTheta D χ.ψ t := by
  classical
  letI : Finite (𝓞 F ⧸ m) := m.finiteQuotientOfFreeOfNeBot hm
  letI : Fintype (𝓞 F ⧸ m) := Fintype.ofFinite _
  letI := rayTraceQuotientModule m hm
  obtain ⟨β, b, hlift, hβ, hb, hcop, himage, _⟩ :=
    rayTraceQuotientGenerator_exists_coprime_lift m hm hmt
  have hgen : Function.Bijective (LinearMap.toSpanSingleton (𝓞 F ⧸ m)
      (rayTraceQuotient m) (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β)) := by
    rw [hlift]
    exact rayTraceQuotientGenerator_bijective m hm
  have hbimage : (b : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (β : F) *
        (m : FractionalIdeal (𝓞 F)⁰ F) * (codifferentFractionalIdeal F)⁻¹ := by
    simpa only [rayDifferentFrac, rayCodifferent, codifferentFractionalIdeal,
      traceDualFractionalIdeal] using himage
  let e := rayTraceGeneratorChar m hm
    (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β)
  let τ := finiteRingGaussSum e ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η))
  let w := rayNormalizedGaussFactor m η b τ
  have hw : ‖w‖ = 1 := rayNormalizedGaussFactor_norm_eq_one hF m hm hmt η hprim
    β hgen b hb hcop hbimage e rfl τ rfl
  refine ⟨w, norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero), hw, ?_⟩
  intro D t ht
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  letI : Fintype (ClassGroup (𝓞 F)) := Fintype.ofFinite _
  have hp : 0 < t / conductorScale F m := div_pos ht (conductorScale_pos hm)
  have hd : 0 < conductorScale F m * t := mul_pos (conductorScale_pos hm) ht
  have hparam : conductorScale F m * t / conductorNorm F m = t / conductorScale F m := by
    rw [← conductorScale_sq hm]
    field_simp
    <;> ring
  let B := fun C : ClassGroup (𝓞 F) => weightedIdealBlock hF hm hmt (conjugateRayCharacter η)
    (FractionalIdeal.mk0 F (inverseOrdinaryClassCoprimeRepresentative F m hm C))
    (t / conductorScale F m)
  have hprimal : normalizedRayConjugateTheta D χ.ψ t =
      (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F * ∑ C, B C := by
    unfold normalizedRayConjugateTheta
    rw [show (∑ c, (starRingEnd ℂ) (χ.ψ c) * RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m)) =
      ∑ C, B C from primal_sum hF hmt (conjugateRayCharacter η) (barData χ) D _ hp]
  have hdual : (∑ c, χ.ψ c * RayTheta.gδDual (D.coset c) ∅ (conductorScale F m * t)) =
      (τ * η b / (RayCoset.modulusCovolume F m : ℂ)) * ∑ C, B C := by
    rw [← Finset.sum_fiberwise Finset.univ (rayToOrdinary F m hm)]
    calc
      _ = ∑ C, (τ * η b / (RayCoset.modulusCovolume F m : ℂ)) *
          B (ramifiedTraceDualClassEquiv F m hm C) := by
        apply Finset.sum_congr rfl
        intro C hC
        let a := inverseOrdinaryClassCoprimeRepresentative F m hm C
        have ha : (a : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.ne_zero a.property
        have hclass : ClassGroup.mk F (rayIdealFractionalIdeal F (a : Ideal (𝓞 F)) ha) = C⁻¹ :=
          mk_inverseOrdinaryClassCoprimeRepresentative F m hm C
        have hfiber := rayTheta_dual_fiber_eq_conjugateWeightedIdealBlock hF m hm hmt η hprim
          β hgen b hb hcop hbimage e rfl τ rfl (a : Ideal (𝓞 F)) ha
          (inverseOrdinaryClassCoprimeRepresentative_coprime F m hm C) χ D _ hd
        rw [hclass, inv_inv, hparam] at hfiber
        rw [hfiber]
        congr 1
        exact weightedIdealBlock_class_invariant hF hm hmt (conjugateRayCharacter η) _ _
          (mk_traceDual_mul_modulus_inverseOrdinaryClassCoprimeRepresentative F m hm C) _ hp
      _ = _ := by
        rw [← Finset.mul_sum, (ramifiedTraceDualClassEquiv F m hm).sum_comp B]
  have hfactor : (conductorScale F m : ℂ) *
      (τ * η b / (RayCoset.modulusCovolume F m : ℂ)) = w := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) (conductorScale_div_modulusCovolume hF m hm)
    push_cast at hc
    dsimp [w, rayNormalizedGaussFactor]
    calc
      _ = (τ * η b) * ((conductorScale F m : ℂ) / (RayCoset.modulusCovolume F m : ℂ)) := by ring
      _ = _ := by rw [hc]; ring
  rw [hprimal]
  unfold normalizedRayDualTheta
  rw [hdual]
  calc
    _ = (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      ((conductorScale F m : ℂ) * (τ * η b / (RayCoset.modulusCovolume F m : ℂ))) * ∑ C, B C := by ring
    _ = _ := by rw [hfactor]; ring

theorem normalizedRayDualTheta_eq_ramified_conjugate
    (hF : NumberField.IsTotallyComplex F) (hmt : m ≠ ⊤)
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hprim : η.IsPrimitive) (hη : ¬ η.IsPrincipal) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ t : ℝ, 0 < t →
      normalizedRayDualTheta D χ.ψ t = w * normalizedRayConjugateTheta D χ.ψ t := by
  obtain ⟨w, hw, _, hdual⟩ := uniform_aux hF hmt χ hprim
  exact ⟨w, hw, hdual D⟩

end DedekindZetaZeroFree.Hecke.Theta

end
