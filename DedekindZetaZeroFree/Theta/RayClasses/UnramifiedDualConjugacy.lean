module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOfGroupCharacter
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterConjugation
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitivePrincipalCharacters
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarityAndOrthogonality
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualClassInvolution
public import DedekindZetaZeroFree.Theta.Periods.LogarithmicAveragePoissonInversion
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.UnitModulusClassGroupEquivalence
public import DedekindZetaZeroFree.Theta.Periods.UnramifiedRayThetaLogarithmicAverage
public import DedekindZetaZeroFree.Theta.RayClasses.WeightedClassInvolutionSums
public import DedekindZetaZeroFree.Theta.RayClasses.FunctionalEquationPair

@[expose] public section

noncomputable section

open scoped NumberField
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]
variable {m : Ideal (𝓞 F)} {hm : m ≠ ⊥}
variable {η : DedekindZetaZeroFree.RayClassCharacter F m}

theorem normalizedRayDualTheta_eq_unramified_conjugate
    (hF : NumberField.IsTotallyComplex F) (htop : m = ⊤)
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ t : ℝ, 0 < t →
      normalizedRayDualTheta D χ.ψ t = w * normalizedRayConjugateTheta D χ.ψ t := by
  classical
  subst m
  letI : Fintype (RayIdealClass F ⊤ hm) := Fintype.ofFinite _
  let E := topRayClassEquivClassGroup F hF hm
  let d := E.symm (DedekindZetaZeroFree.Hecke.principalTraceDualClass F)
  let I := fun c : RayIdealClass F ⊤ hm =>
    rayIdealFractionalIdeal F (D.coset c).a (D.coset c).ideal_ne_bot
  let B := fun (t : ℝ) (c : RayIdealClass F ⊤ hm) =>
    topLogIdealAverage F hm (I c) t
  let a := conductorScale F (⊤ : Ideal (𝓞 F))
  have ha : 0 < a := conductorScale_pos hm
  have hscale : a = Real.sqrt |(NumberField.discr F : ℝ)| := by
    simp [a, conductorScale, conductorNorm, Int.cast_abs]
  have hψ : ∀ c, ‖χ.ψ c‖ = 1 :=
    rayCharacterDescent_norm_eq_one hm η χ.ψ χ.descent
  refine ⟨χ.ψ (d⁻¹), weightedInvolution_factor_ne_zero χ.ψ hψ d, ?_⟩
  intro t ht
  have hprimal (c : RayIdealClass F ⊤ hm) (u : ℝ) (hu : 0 < u) :
      RayTheta.fδ (D.coset c) ∅ (u / a) = B u c := by
    rw [hscale]
    exact topPrimal_eq_topLogIdealAverage F (D.coset c) (D.modulus_eq c) hm u hu
  have hclass (c : RayIdealClass F ⊤ hm) :
      ClassGroup.mk F (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F (I c)) =
        ClassGroup.mk F (I (weightedInverseClassEquiv d c)) := by
    rw [DedekindZetaZeroFree.Hecke.mk_traceDualIdealUnit,
      topRayClassEquivClassGroup_representatives F hF hm D c,
      topRayClassEquivClassGroup_representatives F hF hm D
        (weightedInverseClassEquiv d c)]
    simp only [weightedInverseClassEquiv_apply, map_mul, map_inv, inv_inv, mul_inv_rev]
    have hd : E d = DedekindZetaZeroFree.Hecke.principalTraceDualClass F := E.apply_symm_apply _
    change DedekindZetaZeroFree.Hecke.principalTraceDualClass F * E c = E c * E d
    rw [hd, mul_comm]
  have hdual (c : RayIdealClass F ⊤ hm) :
      (a : ℂ) * RayTheta.gδDual (D.coset c) ∅ (a * t) =
        B t (weightedInverseClassEquiv d c) := by
    have hfe := RayTheta.fδ_one_div (D.coset c) ∅ (a * t) (mul_pos ha ht)
    simp only [RayParity.εδ, Finset.card_empty, pow_zero, one_mul,
      Complex.ofReal_mul] at hfe
    have harg : 1 / (a * t) = (1 / t) / a := by ring
    rw [harg, hprimal c (1 / t) (one_div_pos.mpr ht)] at hfe
    have hp := topLogIdealAverage_poisson F hm (I c) t ht
    have hi := topLogIdealAverage_class_invariant F hm
      (DedekindZetaZeroFree.AbelianQuotient.Theta.traceDualIdealUnit F (I c))
      (I (weightedInverseClassEquiv d c)) t ht (hclass c)
    rw [hi] at hp
    apply mul_left_cancel₀ (show (t : ℂ) ≠ 0 by exact_mod_cast ht.ne')
    calc
      (t : ℂ) * ((a : ℂ) * RayTheta.gδDual (D.coset c) ∅ (a * t)) = B (1 / t) c := by
        rw [hfe]
        ring
      _ = (t : ℂ) * B t (weightedInverseClassEquiv d c) := hp
  change (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F * (a : ℂ) *
      (∑ c, χ.ψ c * RayTheta.gδDual (D.coset c) ∅ (a * t)) =
    χ.ψ (d⁻¹) * ((4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      ∑ c, (starRingEnd ℂ) (χ.ψ c) * RayTheta.fδ (D.coset c) ∅ (t / a))
  rw [mul_assoc, Finset.mul_sum]
  simp_rw [← mul_assoc (a : ℂ), mul_comm (a : ℂ) (χ.ψ _),
    mul_assoc (χ.ψ _), hdual, hprimal _ t ht]
  rw [weightedInvolution_sum χ.ψ hψ d (B t)]
  ring

end DedekindZetaZeroFree.Hecke.Theta

end
