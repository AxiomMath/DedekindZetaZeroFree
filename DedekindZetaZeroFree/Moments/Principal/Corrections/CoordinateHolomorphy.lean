module

public import DedekindZetaZeroFree.Moments.Principal.Corrections.NormalProductConvergence

@[expose] public section

open scoped NumberField Classical

noncomputable section
namespace DedekindZetaZeroFree.CorrectionFactors
set_option autoImplicit false

open LocalFiniteSums

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem localFactor_differentiableOn
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (p : ExteriorPrime A) :
    DifferentiableOn ℂ (fun x : Coordinates => localFactor C U p x.1 x.2.1 x.2.2)
      Omega := by
  by_cases hj : (U.j p).val = 0
  · have hu : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
      have heq : U.u = U.unitPart p := by
        simpa [hj] using (U.unitPart_spec p).1
      rw [heq]
      exact (U.unitPart_spec p).2
    simpa only [localFactor, if_pos hj] using good_correction_holomorphic C p U.u hu
  · simpa only [localFactor, if_neg hj] using
      bad_factor_holomorphic C p (U.j p) hj (U.theta p)

private theorem product_slice_differentiableOn
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C)
    (e : ℂ → Coordinates) (he : Differentiable ℂ e) :
    DifferentiableOn ℂ
      (fun t : ℂ => ∏' p : ExteriorPrime A, localFactor C U p (e t).1 (e t).2.1 (e t).2.2)
      (e ⁻¹' Omega) := by
  have hlim := (hasProdLocallyUniformlyOn_localFactor C U).comp e
    (fun _ ht => ht) he.continuous.continuousOn
  apply hlim.differentiableOn
  · apply Filter.Eventually.of_forall
    intro s
    simpa only [Finset.prod_fn, Function.comp_apply] using
      (DifferentiableOn.finset_prod (u := s) fun p _ =>
        (localFactor_differentiableOn C U p).comp he.differentiableOn (fun _ ht => ht))
  · exact isOpen_Omega.preimage he.continuous

theorem continuous_H_u
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C) :
    Continuous (fun x : Omega =>
      H_u C U x.val.1 x.val.2.1 x.val.2.2
        (multipliable_localFactor C U x.val x.property)) := by
  change Continuous (Omega.domRestrict (fun x : Coordinates =>
    ∏' p : ExteriorPrime A, localFactor C U p x.1 x.2.1 x.2.2))
  apply continuousOn_iff_continuous_restrict.mp
  apply (hasProdLocallyUniformlyOn_localFactor C U).continuousOn
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro s
  exact continuousOn_finsetProd s fun p _ =>
    (localFactor_differentiableOn C U p).continuousOn

theorem differentiableOn_H_u_xi
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C) (w z : ℂ) :
    DifferentiableOn ℂ
      (fun ξ : ℂ => ∏' p : ExteriorPrime A, localFactor C U p ξ w z)
      {ξ : ℂ | (ξ, w, z) ∈ Omega} := by
  exact product_slice_differentiableOn C U (fun ξ => (ξ, w, z))
    (differentiable_id.prodMk ((differentiable_const w).prodMk (differentiable_const z)))

theorem differentiableOn_H_u_w
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C) (ξ z : ℂ) :
    DifferentiableOn ℂ
      (fun w : ℂ => ∏' p : ExteriorPrime A, localFactor C U p ξ w z)
      {w : ℂ | (ξ, w, z) ∈ Omega} := by
  exact product_slice_differentiableOn C U (fun w => (ξ, w, z))
    ((differentiable_const ξ).prodMk (differentiable_id.prodMk (differentiable_const z)))

theorem differentiableOn_H_u_z
    (C : A.GeneralArithmeticContext σ η hS) (U : Frequency C) (ξ w : ℂ) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∏' p : ExteriorPrime A, localFactor C U p ξ w z)
      {z : ℂ | (ξ, w, z) ∈ Omega} := by
  exact product_slice_differentiableOn C U (fun z => (ξ, w, z))
    ((differentiable_const ξ).prodMk ((differentiable_const w).prodMk differentiable_id))

end DedekindZetaZeroFree.CorrectionFactors

end
