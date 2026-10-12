module

public import DedekindZetaZeroFree.Theta.Profiles.MixedThetaDefinitions
public import DedekindZetaZeroFree.Theta.Profiles.MixedGaussian

@[expose] public section

open NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

open Classical NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.AbelianQuotient.Theta

private theorem covariance_exp_add {F : Type} [Field F] [NumberField F]
    (x y : mixedEmbedding.realSpace F) :
    expMapBasis (x + y) = expMapBasis x * expMapBasis y := by
  simp only [expMapBasis_apply, map_add, expMap_add]

private theorem covariance_covolume_pos {F : Type} [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : 0 < mixedThetaCovolume F I := by
  apply mul_pos
  · exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _)
      (Ne.symm (fun h => Units.ne_zero I (FractionalIdeal.absNorm_eq_zero_iff.mp h)))
  · apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (by exact_mod_cast discr_ne_zero F)

private theorem covariance_reindex {F : Type} [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F))
    (f : F → ℂ) :
    (∑' x : ↥((J : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F), f (x : F)) =
    ∑' x : ↥((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F), f ((a : F) * x) := by
  have h := FractionalIdeal.eq_spanSingleton_mul.mp hJ
  let m : ↥((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) →
      ↥((J : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) :=
    fun x => ⟨(a : F) * x, h.2 x x.2⟩
  have hm : Function.Bijective m := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ (Units.ne_zero a) (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, he⟩ := h.1 y y.2
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  exact ((Equiv.ofBijective m hm).tsum_eq (fun x => f (x : F))).symm

theorem principalCenteredShapeCovariance (F : Type) [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ d : DedekindZetaZeroFree.AbelianQuotient.Theta.Angular F,
      ∀ t : ℝ, 0 < t →
        ∀ u : DedekindZetaZeroFree.AbelianQuotient.Theta.Angular F,
          DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta F J t u =
            DedekindZetaZeroFree.AbelianQuotient.Theta.mixedRadialTheta F I t (u + d) := by
  classical
  let A : mixedEmbedding.realSpace F := fun v => v (a : F)
  let L : mixedEmbedding.realSpace F := expMapBasis.symm A
  have hA : ∀ v, 0 < A v := by
    intro v
    exact InfinitePlace.pos_iff.mpr (Units.ne_zero a)
  have hL : expMapBasis L = A := by
    apply expMapBasis.right_inv
    change A ∈ expMap.target
    rw [expMap_target]
    exact Set.mem_univ_pi.mpr hA
  let N : ℝ := (|(Algebra.norm ℚ) (a : F)| : ℚ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (abs_pos.mpr
      (show (Algebra.norm ℚ) (a : F) ≠ 0 from Algebra.norm_ne_zero_iff.mpr (Units.ne_zero a)))
  have hrad : L w₀ = Real.log N / (Module.finrank ℚ F : ℝ) := by
    have hp := prod_expMapBasis_pow L
    rw [hL, prod_eq_abs_norm] at hp
    have hl := congrArg Real.log hp
    rw [Real.log_pow, Real.log_exp] at hl
    dsimp [N]
    exact (eq_div_iff (by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne')).mpr
      (by linarith)
  have hc : mixedThetaCovolume F J = N * mixedThetaCovolume F I := by
    unfold mixedThetaCovolume
    rw [hJ, map_mul, FractionalIdeal.absNorm_span_singleton]
    dsimp [N]
    push_cast
    ring
  let d : Angular F := fun v => L v
  refine ⟨d, ?_⟩
  intro t ht u
  have hcoords :
      angularLift F (u + d) + radialLift F
          ((Real.log t - Real.log (mixedThetaCovolume F I)) / (Module.finrank ℚ F : ℝ)) =
      (angularLift F u + radialLift F
          ((Real.log t - Real.log (mixedThetaCovolume F J)) / (Module.finrank ℚ F : ℝ))) + L := by
    have hlog : Real.log (mixedThetaCovolume F J) =
        Real.log N + Real.log (mixedThetaCovolume F I) := by
      rw [hc, Real.log_mul hN.ne' (covariance_covolume_pos I).ne']
    funext v
    by_cases hv : v = w₀
    · subst v
      simp only [Pi.add_apply, angularLift, radialLift, dite_true, ite_true]
      rw [hlog, hrad]
      ring
    · simp only [Pi.add_apply, angularLift, radialLift, dif_neg hv, if_neg hv,
        add_zero, d]
  have hs : mixedThetaShape F I t (u + d) =
      (fun v => mixedThetaShape F J t u v * v (a : F)) := by
    unfold mixedThetaShape
    rw [hcoords, covariance_exp_add, hL]
    rfl
  unfold mixedRadialTheta
  rw [fractionalShapeIdealTheta_eq_tsum_mixedGaussian,
    fractionalShapeIdealTheta_eq_tsum_mixedGaussian]
  rw [covariance_reindex I J a hJ (fun x => mixedGaussian F x (mixedThetaShape F J t u))]
  apply tsum_congr
  intro x
  unfold mixedGaussian
  congr 3
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul, hs]
  ring

end DedekindZetaZeroFree.Hecke
