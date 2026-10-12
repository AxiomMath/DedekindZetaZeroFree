module

public import DedekindZetaZeroFree.Theta.RayClasses.NormalizedCharacterAggregates
public import DedekindZetaZeroFree.Theta.RayClasses.FunctionalEquationPair

@[expose] public section

noncomputable section

open scoped NumberField
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]
variable {m : Ideal (𝓞 F)} {hm : m ≠ ⊥}

theorem normalizedRayTheta_one_div
    (D : RayThetaRepresentatives F m hm) (ψ : RayIdealClass F m hm →* ℂ)
    (t : ℝ) (ht : 0 < t) :
    normalizedRayTheta D ψ t = (t : ℂ)⁻¹ * normalizedRayDualTheta D ψ t⁻¹ := by
  classical
  have ha := conductorScale_pos (F := F) hm
  have heq (c : RayIdealClass F m hm) :
      RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m) =
        (conductorScale F m : ℂ) * (t : ℂ)⁻¹ *
          RayTheta.gδDual (D.coset c) ∅ (conductorScale F m * t⁻¹) := by
    have h := RayTheta.fδ_one_div (D.coset c) ∅
      (conductorScale F m / t) (div_pos ha ht)
    have hid : 1 / (conductorScale F m / t) = t / conductorScale F m := by field_simp
    simpa [hid, RayParity.εδ, div_eq_mul_inv] using h
  unfold normalizedRayTheta normalizedRayDualTheta
  simp_rw [heq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

private lemma conj_fδ_empty (D : RayCoset.Data F) (t : ℝ) :
    (starRingEnd ℂ) (RayTheta.fδ D ∅ t) = RayTheta.fδ D ∅ t := by
  unfold RayTheta.fδ
  split_ifs with ht
  · rw [map_mul, map_inv₀]
    simp only [map_natCast]
    congr 1
    rw [← integral_conj]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with h
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro l
    simp [RayParity.gδ, Theta.latticeGaussian, ← Complex.exp_conj]
  · exact map_zero _

theorem normalizedRayConjugateTheta_eq_conj
    (D : RayThetaRepresentatives F m hm) (ψ : RayIdealClass F m hm →* ℂ)
    (t : ℝ) :
    normalizedRayConjugateTheta D ψ t = (starRingEnd ℂ) (normalizedRayTheta D ψ t) := by
  classical
  unfold normalizedRayConjugateTheta normalizedRayTheta
  simp only [map_mul, map_pow, map_ofNat, map_sum, conj_fδ_empty]

end DedekindZetaZeroFree.Hecke.Theta

end
