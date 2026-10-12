module

public import DedekindZetaZeroFree.LFunctions.Hecke.CompletionScaling
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TotallyComplexQuadraticSignature
public import DedekindZetaZeroFree.LFunctions.Hecke.AbsoluteEulerProducts
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticLocalEulerFactors

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

noncomputable section
open scoped NumberField Classical Topology
open Filter IsDedekindDomain

private theorem norm_le_one_of_cube {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I) (I : Ideal (𝓞 F)) : ‖η I‖ ≤ 1 := by
  have hfac : η I * (η I ^ 2 - 1) = 0 := by
    have : η I * (η I ^ 2 - 1) = η I ^ 3 - η I := by ring
    rw [this, hq I, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h1
  · simp [h0]
  · have hsq : η I ^ 2 = 1 := sub_eq_zero.mp h1
    have h2 : ‖η I‖ * ‖η I‖ = 1 := by
      rw [← norm_mul, ← pow_two, hsq]; simp
    nlinarith [norm_nonneg (η I)]

private theorem quadratic_idealHeckeL_factorization_aux
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬ η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η) (s : ℂ) (hs : 1 < s.re) :
    idealHeckeL (principalUnitRayCharacter d.extension) s =
      idealHeckeL (principalUnitRayCharacter F) s * idealHeckeL η s := by
  have hη : ∀ I, ‖η I‖ ≤ 1 := fun I => norm_le_one_of_cube η hq I
  have hgrouped := principal_idealHeckeL_euler_finite_fibers_grouped F d.extension s hs
  have hbase := (principal_idealHeckeL_absolute_euler_product F s hs).2.1
  have heta := (idealHeckeL_absolute_euler_product η s hf hη hs).2
  have hprod := hbase.mul heta
  have hfun : (fun p : HeightOneSpectrum (𝓞 F) =>
        ∏' Q : {Q : HeightOneSpectrum (𝓞 d.extension) //
          Q.asIdeal.LiesOver p.asIdeal},
          (1 - (Ideal.absNorm Q.val.asIdeal : ℂ) ^ (-s))⁻¹) =
      (fun p : HeightOneSpectrum (𝓞 F) =>
        (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹ *
          (1 - η p.asIdeal * (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))⁻¹) := by
    funext p
    exact quadratic_local_euler_factors F hF f hf η hq hn hp d p s hs
  exact HasProd.unique hgrouped.2 (hfun.symm ▸ hprod)

private theorem poleCleared_agrees_on_halfplane
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬ η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η)
    (pF : PrincipalHeckeWitness (principalUnitRayCharacter F))
    (pE : PrincipalHeckeWitness (principalUnitRayCharacter d.extension))
    (w : EntireHeckeWitness η) :
    ∀ s : ℂ, 1 < s.re →
      pE.Λ s = heckeCompletionFactor d.extension ⊤ s *
        idealHeckeL (principalUnitRayCharacter d.extension) s := by
  intro s hs
  refine HasSum.unique (pE.hasSum s hs) ?_
  exact ((principal_idealHeckeL_absolute_euler_product d.extension s hs).1.hasSum).mul_left _

private theorem poleCleared_base_series
    (F : Type) [Field F] [NumberField F]
    (pF : PrincipalHeckeWitness (principalUnitRayCharacter F)) :
    ∀ s : ℂ, 1 < s.re →
      pF.Λ s = heckeCompletionFactor F ⊤ s *
        idealHeckeL (principalUnitRayCharacter F) s := by
  intro s hs
  refine HasSum.unique (pF.hasSum s hs) ?_
  exact ((principal_idealHeckeL_absolute_euler_product F s hs).1.hasSum).mul_left _

private theorem poleCleared_eta_series
    {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hη : ∀ I, ‖η I‖ ≤ 1)
    (w : EntireHeckeWitness η) :
    ∀ s : ℂ, 1 < s.re →
      w.Λ s = heckeCompletionFactor F f s * idealHeckeL η s := by
  intro s hs
  refine HasSum.unique (w.hasSum s hs) ?_
  exact ((idealHeckeL_absolute_euler_product η s hf hη hs).1.hasSum).mul_left _

private theorem eq_of_agrees_on_halfplane {A B : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (h : ∀ s : ℂ, 1 < s.re → A s = B s) : ∀ s : ℂ, A s = B s := by
  have hA' : AnalyticOnNhd ℂ A Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hA
  have hB' : AnalyticOnNhd ℂ B Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hB
  have hU : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
  have hev : A =ᶠ[𝓝 (2 : ℂ)] B := by
    filter_upwards [hU.mem_nhds hmem] with s hs using h s hs
  have hEq := AnalyticOnNhd.eq_of_eventuallyEq hA' hB' hev
  exact fun s => congr_fun hEq s

theorem poleClearedHecke_factorization
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬ η.IsPrincipal) (hp : η.IsPrimitive)
    (d : QuadraticRayExtensionData η)
    (pF : PrincipalHeckeWitness (principalUnitRayCharacter F))
    (pE : PrincipalHeckeWitness (principalUnitRayCharacter d.extension))
    (w : EntireHeckeWitness η) :
    ∀ s : ℂ, pE.U s =
      Complex.exp ((heckeCompletionLogScale F d.extension f : ℂ) * s) *
        pF.U s * w.Λ s := by
  have hη : ∀ I, ‖η I‖ ≤ 1 := fun I => norm_le_one_of_cube η hq I
  have hsig := quadraticExtension_signature F d.extension hF d.degree_two
  have hexp : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((heckeCompletionLogScale F d.extension f : ℂ) * s)) :=
    Complex.differentiable_exp.comp
      ((differentiable_const (c := (heckeCompletionLogScale F d.extension f : ℂ))).mul
        differentiable_id)
  have hB : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((heckeCompletionLogScale F d.extension f : ℂ) * s) * pF.U s * w.Λ s) :=
    (hexp.mul pF.differentiable_U).mul w.differentiable
  refine eq_of_agrees_on_halfplane pE.differentiable_U hB ?_
  intro s hs
  have hE := poleCleared_agrees_on_halfplane F hF f hf η hq hn hp d pF pE w s hs
  have hFb := poleCleared_base_series F pF s hs
  have hW := poleCleared_eta_series hf η hη w s hs
  have hzeta := quadratic_idealHeckeL_factorization_aux F hF f hf η hq hn hp d s hs
  have hscale := heckeCompletionFactor_scaling F d.extension f hf hsig.2 s
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hU_E := pE.poleClearing s hs0 hs1
  have hU_F := pF.poleClearing s hs0 hs1
  rw [hU_E, hU_F, hE, hFb, hW, hzeta, hscale]
  ring

end

end DedekindZetaZeroFree.LargeSieve
