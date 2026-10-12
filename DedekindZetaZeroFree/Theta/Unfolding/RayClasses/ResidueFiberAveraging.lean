module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.CoprimeResidues.OrdinaryClassFiberEquivalence
public import DedekindZetaZeroFree.Theta.Unfolding.RayClasses.RepresentativePacketAverages

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

theorem residueFiber_normalizers_ne_zero
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    (residueUnitImageCard F m : ℂ) ≠ 0 ∧
      (RayCoset.rayUnitTorsionCard F m : ℂ) ≠ 0 ∧
      (RayCoset.modulusCovolume F m : ℂ) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (residueUnitImageCard_pos hm).ne'
  · exact_mod_cast (RayCoset.rayUnitTorsionCard_pos F m).ne'
  · exact_mod_cast (RayCoset.modulusCovolume_pos m hm).ne'

section Coprime
variable (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
local notation "I" => rayIdealFractionalIdeal F a ha
local notation "R" => coprimeIdealResidue F m a hm ha
local notation "U" => coprimeIdealResidueUnits F m a hm ha hcop hmt
local notation "Fiber" => {c : RayIdealClass F m hm //
  rayToOrdinary F m hm c = (ClassGroup.mk F I)⁻¹}

theorem coprimeIdealResidueRayClass_sum_fiber (f : Fiber → ℂ) :
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI : Finite U := inferInstanceAs
      (Finite {q : R // IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q)})
    letI := Fintype.ofFinite U
    letI := Fintype.ofFinite Fiber
    (∑ q : U, f (coprimeIdealResidueRayClass hF m a hm ha hcop hmt q)) =
      (residueUnitImageCard F m : ℂ) * ∑ c : Fiber, f c := by
  classical
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI : Finite U := inferInstanceAs
    (Finite {q : R // IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q)})
  letI := Fintype.ofFinite U
  letI := Fintype.ofFinite Fiber
  rw [← Fintype.sum_fiberwise' (coprimeIdealResidueRayClass hF m a hm ha hcop hmt) f,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact_mod_cast (by
    rw [← Nat.card_eq_fintype_card]
    exact coprimeIdealResidueRayClass_fiber_card_all hF m a hm ha hcop hmt c)

variable (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η)
    (D : RayThetaRepresentatives F m hm) (u : ℝ) (hu : 0 < u)

private theorem sum_residue_eq_sum_units (B : R → ℂ) [Fintype R] [Fintype U] :
    (∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q * B q) =
      ∑ q : U, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q.val * B q.val := by
  classical
  unfold coprimeIdealResidueUnits at *
  have hz : (∑ q : {q : R // ¬ IsUnit
      (coprimeIdealResidueReduction F m a hm ha hcop q)},
      coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q.val * B q.val) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [coprimeIdealResidueCoefficient_eq_zero_of_not_isUnit
      hF m a hm ha hcop hmt η E q.val q.property, zero_mul]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun q : R => IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q))
    (fun q => coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q * B q)
  convert (by simpa only [hz, add_zero] using hs.symm) using 1
  congr 1
  ext q
  exact ⟨fun _ => @Finset.mem_univ _ (Subtype.fintype
    (fun q : R => IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q))) q,
    fun _ => @Finset.mem_univ _ _ q⟩

theorem coprimeIdealResidueAverage_sum_fiber :
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI := Fintype.ofFinite R
    letI := Fintype.ofFinite Fiber
    (∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
      coprimeIdealResidueAverage hF m a hm ha hcop u hu q) =
      (residueUnitImageCard F m : ℂ) *
        ∑ c : Fiber, E.ψ c.val *
          ((RayCoset.rayUnitTorsionCard F m : ℂ) *
            RayTheta.fδ (D.coset c.val) ∅ u) := by
  classical
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite R
  letI : Finite U := inferInstanceAs
    (Finite {q : R // IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q)})
  letI := Fintype.ofFinite U
  letI := Fintype.ofFinite Fiber
  rw [sum_residue_eq_sum_units hF m a hm ha hcop hmt η E]
  rw [← coprimeIdealResidueRayClass_sum_fiber hF m a hm ha hcop hmt
    (fun c => E.ψ c.val * ((RayCoset.rayUnitTorsionCard F m : ℂ) *
      RayTheta.fδ (D.coset c.val) ∅ u))]
  apply Finset.sum_congr rfl
  intro q _
  rw [coprimeIdealResidueCoefficient_eq_character hF m a hm ha hcop hmt η E q]
  congr 1
  obtain ⟨x, hx⟩ := fractionalIdealQuotientMk_surjective
    (I : FractionalIdeal (𝓞 F)⁰ F)
    ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F) q.val
  have ht := rayTheta_fδ_eq_affineResidueAverage hF m a hm ha hcop hmt D q x hx u hu
  dsimp only at ht
  rw [ht, ← hx, coprimeIdealResidueAverage_mk hF m a hm ha hcop u hu]
  rw [← mul_assoc, mul_inv_cancel₀ (residueFiber_normalizers_ne_zero m hm).2.1, one_mul]

theorem coprimeIdealResidueDualAverage_sum_fiber :
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI := Fintype.ofFinite R
    letI := Fintype.ofFinite Fiber
    (∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
      coprimeIdealResidueDualAverage hF m a hm ha hcop u hu q) =
      (residueUnitImageCard F m : ℂ) *
        ∑ c : Fiber, E.ψ c.val *
          (((RayCoset.rayUnitTorsionCard F m : ℂ) *
            (RayCoset.modulusCovolume F m : ℂ)) *
              RayTheta.gδDual (D.coset c.val) ∅ u) := by
  classical
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite R
  letI : Finite U := inferInstanceAs
    (Finite {q : R // IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q)})
  letI := Fintype.ofFinite U
  letI := Fintype.ofFinite Fiber
  rw [sum_residue_eq_sum_units hF m a hm ha hcop hmt η E]
  rw [← coprimeIdealResidueRayClass_sum_fiber hF m a hm ha hcop hmt
    (fun c => E.ψ c.val * (((RayCoset.rayUnitTorsionCard F m : ℂ) *
      (RayCoset.modulusCovolume F m : ℂ)) * RayTheta.gδDual (D.coset c.val) ∅ u))]
  apply Finset.sum_congr rfl
  intro q _
  rw [coprimeIdealResidueCoefficient_eq_character hF m a hm ha hcop hmt η E q]
  congr 1
  obtain ⟨x, hx⟩ := fractionalIdealQuotientMk_surjective
    (I : FractionalIdeal (𝓞 F)⁰ F)
    ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F) q.val
  have ht := rayTheta_gδDual_eq_affineResidueDualAverage hF m a hm ha hcop hmt D q x hx u hu
  dsimp only at ht
  rw [ht, ← hx, coprimeIdealResidueDualAverage_mk hF m a hm ha hcop u hu]
  rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero
    (residueFiber_normalizers_ne_zero m hm).2.1
    (residueFiber_normalizers_ne_zero m hm).2.2), one_mul]

end Coprime

end DedekindZetaZeroFree.Hecke.Theta

end
