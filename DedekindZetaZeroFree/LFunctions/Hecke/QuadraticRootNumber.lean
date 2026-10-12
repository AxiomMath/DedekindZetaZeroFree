module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticSelfDualFunctionalEquation
public import DedekindZetaZeroFree.LFunctions.Hecke.PoleClearedQuadraticFactorization
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalNonvanishingAtTwo
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalPoleClearedReflection
public import DedekindZetaZeroFree.LFunctions.Hecke.RootNumberFromPositiveScaling

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem quadratic_entireHeckeWitness_root_number
    {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    {f : Ideal (𝓞 F)} (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hp : η.IsPrimitive)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬ η.IsPrincipal)
    (w : EntireHeckeWitness η) :
    w.Λdual = w.Λ ∧ w.W = 1 ∧
      (∀ s : ℂ, w.Λ s = w.Λ (1 - s)) ∧ w.Λ (2 : ℂ) ≠ 0 := by

  have hdual : w.Λdual = w.Λ := w.dual_eq_self hq

  obtain ⟨d⟩ := exists_quadraticRayExtensionData F hF f hf η hq hn

  have hsig := quadraticExtension_signature F d.extension hF d.degree_two
  haveI : NumberField.IsTotallyComplex d.extension := hsig.1

  obtain ⟨pF⟩ := exists_principalUnitHeckeWitness F hF
  obtain ⟨pE⟩ := exists_principalUnitHeckeWitness d.extension hsig.1

  have hfactor := poleClearedHecke_factorization F hF f hf η hq hn hp d pF pE w

  have hW1 : w.W = 1 :=
    rootNumber_eq_one_of_positive_scaling (heckeCompletionLogScale F d.extension f)
      pE.U pF.U w.Λ w.W
      (fun s => PrincipalHeckeWitness.U_reflection pE s)
      (fun s => PrincipalHeckeWitness.U_reflection pF s)
      hfactor
      (fun s => w.selfdual_functionalEquation hq s)
      w.norm_W
      (principalUnitHeckeWitness_U_two_ne_zero d.extension pE)

  have hL2 : w.Λ (2 : ℂ) ≠ 0 := by
    have hpE2 := principalUnitHeckeWitness_U_two_ne_zero d.extension pE
    intro hw0
    refine hpE2 ?_
    rw [hfactor 2, hw0]
    ring
  refine ⟨hdual, hW1, fun s => ?_, hL2⟩
  rw [w.selfdual_functionalEquation hq s, hW1, one_mul]

end DedekindZetaZeroFree.LargeSieve
