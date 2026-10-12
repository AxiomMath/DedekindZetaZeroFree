module

public import DedekindZetaZeroFree.Theta.RayClasses.NormalizedCharacterAggregates

@[expose] public section

noncomputable section

open scoped NumberField
open DedekindZetaZeroFree.AbelianQuotient
open NumberField NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]
variable {m : Ideal (𝓞 F)} {hm : m ≠ ⊥}
variable {η : DedekindZetaZeroFree.RayClassCharacter F m}

 noncomputable instance zeroCancellationRayClassFintype :
    Fintype (RayIdealClass F m hm) := Fintype.ofFinite _

private theorem embedding_injective (D : RayCoset.Data F) :
    Function.Injective (RayCoset.normalizedEmbedding D) := by
  intro x y h
  have ht : Theta.traceEmbedding F (x : F) = Theta.traceEmbedding F (y : F) :=
    (smul_right_injective _ (RayCoset.normalizationScale_pos D).ne').eq_iff.mp h
  apply RingOfIntegers.coe_injective
  apply mixedEmbedding_injective F
  simpa [Theta.traceEmbedding] using congrArg (Theta.traceToMixed F) ht
private theorem origin_iff (D : RayCoset.Data F) :
    (0 : euclidean.mixedSpace F) ∈ RayCoset.normalizedAffineCoset D ↔ D.m = ⊤ := by
  constructor
  · intro h
    obtain ⟨α, hα, he⟩ := (RayCoset.normalizedEmbedding_bijOn D).2.2 h
    have hz : α = 0 := (embedding_injective D) (he.trans (map_zero (RayCoset.normalizedEmbedding D)).symm)
    subst α
    have hn := ((RayCoset.mem_C_iff D 0).mp hα).2
    apply (Ideal.eq_top_iff_one _).mpr
    simpa using D.m.neg_mem hn
  · intro hm
    have hzero : (0 : 𝓞 F) ∈ RayCoset.C D := by
      rw [RayCoset.mem_C_iff]
      simp [hm]
    simpa only [map_zero] using (RayCoset.normalizedEmbedding_bijOn D).1 hzero
private theorem primal_common (D : RayThetaRepresentatives F m hm)
    (c : RayIdealClass F m hm) :
    RayTheta.f0δ (D.coset c) ∅ =
      if m = ⊤ then (RayCoset.rayUnitDomainVolume F m hm : ℂ) /
        (RayCoset.rayUnitTorsionCard F m : ℂ) else 0 := by
  simp [RayTheta.f0δ, origin_iff, D.modulus_eq]

private theorem dual_common (D : RayThetaRepresentatives F m hm)
    (c : RayIdealClass F m hm) :
    RayTheta.g0δ (D.coset c) ∅ =
      (RayCoset.rayUnitDomainVolume F m hm : ℂ) /
        ((RayCoset.rayUnitTorsionCard F m : ℂ) *
          (RayCoset.modulusCovolume F m : ℂ)) := by
  simp [RayTheta.g0δ, D.modulus_eq]

private theorem sum_coeff (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) : ∑ c : RayIdealClass F m hm, χ.ψ c = 0 := by
  classical
  exact sum_hom_units_eq_zero χ.ψ (fun h => hη (χ.principal_iff.mpr h))

private theorem sum_conj_coeff (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) :
    ∑ c : RayIdealClass F m hm, (starRingEnd ℂ) (χ.ψ c) = 0 := by
  classical
  rw [← map_sum, sum_coeff χ hη, map_zero]

theorem sum_rayTheta_f0_eq_zero
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) :
    ∑ c : RayIdealClass F m hm, χ.ψ c * RayTheta.f0δ (D.coset c) ∅ = 0 := by
  classical
  simp_rw [primal_common D]
  rw [← Finset.sum_mul, sum_coeff χ hη, zero_mul]

theorem sum_rayTheta_g0_eq_zero
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) :
    ∑ c : RayIdealClass F m hm, χ.ψ c * RayTheta.g0δ (D.coset c) ∅ = 0 := by
  classical
  simp_rw [dual_common D]
  rw [← Finset.sum_mul, sum_coeff χ hη, zero_mul]

theorem sum_conjugate_rayTheta_f0_eq_zero
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) :
    ∑ c : RayIdealClass F m hm,
      (starRingEnd ℂ) (χ.ψ c) * RayTheta.f0δ (D.coset c) ∅ = 0 := by
  classical
  simp_rw [primal_common D]
  rw [← Finset.sum_mul, sum_conj_coeff χ hη, zero_mul]

theorem normalizedRayTheta_eq_sub_zero_modes
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) (t : ℝ) (ht : 0 < t) :
    normalizedRayTheta D χ.ψ t =
      (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        ∑ c : RayIdealClass F m hm, χ.ψ c *
          (RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m) -
            RayTheta.f0δ (D.coset c) ∅) := by
  classical
  simp only [normalizedRayTheta, mul_sub, Finset.sum_sub_distrib,
    sum_rayTheta_f0_eq_zero D χ hη, sub_zero]

theorem normalizedRayDualTheta_eq_sub_zero_modes
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) (t : ℝ) (ht : 0 < t) :
    normalizedRayDualTheta D χ.ψ t =
      (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        (conductorScale F m : ℂ) *
        ∑ c : RayIdealClass F m hm, χ.ψ c *
          (RayTheta.gδDual (D.coset c) ∅ (conductorScale F m * t) -
            RayTheta.g0δ (D.coset c) ∅) := by
  classical
  simp only [normalizedRayDualTheta, mul_sub, Finset.sum_sub_distrib,
    sum_rayTheta_g0_eq_zero D χ hη, sub_zero]

theorem normalizedRayConjugateTheta_eq_sub_zero_modes
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) (t : ℝ) (ht : 0 < t) :
    normalizedRayConjugateTheta D χ.ψ t =
      (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        ∑ c : RayIdealClass F m hm, (starRingEnd ℂ) (χ.ψ c) *
          (RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m) -
            RayTheta.f0δ (D.coset c) ∅) := by
  classical
  simp only [normalizedRayConjugateTheta, mul_sub, Finset.sum_sub_distrib,
    sum_conjugate_rayTheta_f0_eq_zero D χ hη, sub_zero]

end DedekindZetaZeroFree.Hecke.Theta

end
