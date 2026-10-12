module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem weightedFractionalCharacter
    (K : Type) [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℂˣ) :
    ∃ H : ClassFieldTheory.NumberFieldFractionalIdealGroup K →* ℂˣ,
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        H (ClassFieldTheory.finitePrimeFractionalIdeal v) = w v := by
  classical

  let primeWeightHom (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      Multiplicative ℤ →* ℂˣ :=
    MonoidHom.mk' (fun n : Multiplicative ℤ => w v ^ n.toAdd)
      (fun m n => by simp only [toAdd_mul, zpow_add])

  let E : Multiplicative (IsDedekindDomain.HeightOneSpectrum (𝓞 K) →₀ ℤ) →* ℂˣ :=
    MonoidHom.mk' (fun exps => exps.toAdd.prod fun v n => primeWeightHom v (Multiplicative.ofAdd n))
      (fun a b => Finsupp.prod_hom_add_index (fun v => primeWeightHom v))
  refine ⟨E.comp ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv.symm.toMonoidHom, ?_⟩
  intro v

  have hfac : ClassFieldTheory.NumberFieldFractionalIdealGroup.factorization
      (Multiplicative.ofAdd (Finsupp.single v (1 : ℤ))) =
      ClassFieldTheory.finitePrimeFractionalIdeal v := by
    apply Units.ext
    rw [ClassFieldTheory.NumberFieldFractionalIdealGroup.factorization_val]
    simp only [toAdd_ofAdd]
    rw [Finsupp.prod_single_index (by simp only [zpow_zero])]
    simp [ClassFieldTheory.finitePrimeFractionalIdeal]
  have hsingle : ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv
      (Multiplicative.ofAdd (Finsupp.single v (1 : ℤ))) =
      ClassFieldTheory.finitePrimeFractionalIdeal v := hfac
  show E (ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv.symm
    (ClassFieldTheory.finitePrimeFractionalIdeal v)) = w v
  rw [← hsingle, MulEquiv.symm_apply_apply]
  show Finsupp.prod (Finsupp.single v (1 : ℤ))
    (fun v n => primeWeightHom v (Multiplicative.ofAdd n)) = w v
  rw [Finsupp.prod_single_index (by simp [primeWeightHom])]
  simp [primeWeightHom]

end DedekindZetaZeroFree.AbelianQuotient
