module

public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.HeightPermutationFubini
public import DedekindZetaZeroFree.Moments.Probes.TripleMellinAbsoluteConvergence

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin
open TripleMellinRaw
noncomputable section
open MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem kernel_eq_summed (P : PrincipalData A σ η hS) (X Y Z : ℝ)
    (t : ℝ × ℝ × ℝ) :
    principalTripleMellinHeights A σ η hS P X Y Z (heightEquiv.symm t) =
      ∑' i : MellinSeriesIndex P, initialTripleMellinSummand P X Y Z i t := by
  rw [show (∑' i : MellinSeriesIndex P, initialTripleMellinSummand P X Y Z i t) =
      tripleMellinWeight P X Y Z (initialMellinPoint t).1
        (initialMellinPoint t).2.1 (initialMellinPoint t).2.2 *
        ∑' i : MellinSeriesIndex P, weightedSeparatedSummand P i
          (initialMellinPoint t).1 (initialMellinPoint t).2.1 (initialMellinPoint t).2.2
      by simp only [initialTripleMellinSummand, tsum_mul_left]]
  rw [separatedSeries_eq_grouped P _ _ _ (by norm_num [initialMellinPoint])
    (by norm_num [initialMellinPoint]) (by norm_num [initialMellinPoint])]
  rfl

theorem heights_integrable (P : PrincipalData A σ η hS) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (principalTripleMellinHeights A σ η hS P X Y Z) := by
  have h := (tripleMellin_sum_integral_interchange P X Y Z hX hY hZ).1
  apply ((heightEquiv_preserving.symm heightEquiv).integrable_comp_emb
    heightEquiv.symm.measurableEmbedding (g := principalTripleMellinHeights A σ η hS P X Y Z)).mp
  simpa only [Function.comp_def, kernel_eq_summed] using h

theorem integral_eq_sum (P : PrincipalData A σ η hS) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    principalTripleMellinIntegral A σ η hS P X Y Z =
      tripleMellinNormalization * ∑' i : MellinSeriesIndex P,
        ∫ t : ℝ × ℝ × ℝ, initialTripleMellinSummand P X Y Z i t := by
  unfold principalTripleMellinIntegral
  rw [← (heightEquiv_preserving.symm heightEquiv).integral_comp'
    (principalTripleMellinHeights A σ η hS P X Y Z)]
  simp_rw [kernel_eq_summed]
  rw [(tripleMellin_sum_integral_interchange P X Y Z hX hY hZ).2]

theorem integral_eq_every_order (P : PrincipalData A σ η hS) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (order : Equiv.Perm (Fin 3)) :
    principalTripleMellinIntegral A σ η hS P X Y Z =
      iteratedTripleMellinIntegral (principalTripleMellinHeights A σ η hS P X Y Z) order := by
  unfold principalTripleMellinIntegral iteratedTripleMellinIntegral
  rw [integral_eq_order _ (heights_integrable P X Y Z hX hY hZ) order]

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin
