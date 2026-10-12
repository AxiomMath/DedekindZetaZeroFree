module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.SIntegerResidueCharacters
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveCharactersByCRT

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.Detector.FixedSInjectivity

noncomputable section

open FixedSResidue

variable {F : Type} [Field F] [NumberField F]

def ExteriorPrincipalization (A : SArithmeticData F) : Prop :=
  ∀ a : A.Exterior, ∃ n : NonzeroSInteger A,
    Ideal.span {n.val} = A.extendIdeal a

def SPrimeCompatibility (A : SArithmeticData F)
    (f : Ideal (𝓞 F)) (omega : RayClassCharacter F f)
    (sigma : FullLocalCharacters A) : Prop :=
  ∀ v : {v // v ∈ A.Sf},
    (∀ x : (v.val.adicCompletion F)ˣ,
      CRTLocalHigherUnits F v.val (idealPrimeExponent v.val.asIdeal f) x →
        sigma.2 v x = 1) ∧
    (∀ k : ℕ, k < idealPrimeExponent v.val.asIdeal f →
      ∃ x : (v.val.adicCompletion F)ˣ,
        CRTLocalHigherUnits F v.val k x ∧ sigma.2 v x ≠ 1) ∧
    (v.val.asIdeal ⊔ f = ⊤ →
      ∀ pi : (v.val.adicCompletion F)ˣ,
        ‖(pi : v.val.adicCompletion F)‖ = (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹ →
        omega v.val.asIdeal = (sigma.2 v pi : ℂ))

private theorem exponent_zero_iff (v : HeightOneSpectrum (𝓞 F))
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥) :
    idealPrimeExponent v.asIdeal f = 0 ↔ v.asIdeal ⊔ f = ⊤ := by
  rw [idealPrimeExponent, Multiset.count_eq_zero]
  rw [mem_normalizedFactors_iff hf]
  simp only [v.prime, true_and, Ideal.dvd_iff_le]
  constructor
  · intro h
    exact (Ideal.isMaximal_def.mp v.isMaximal).2 _ (show v.asIdeal < v.asIdeal ⊔ f from
      lt_of_le_of_ne le_sup_left (by
        intro he
        exact h (he ▸ le_sup_right)))
  · intro h hle
    have : v.asIdeal ⊔ f = v.asIdeal := sup_eq_left.mpr hle
    exact v.isPrime.ne_top (this.symm.trans h)

private theorem exponent_eq (A : SArithmeticData F) (sigma : FixedSResidue.FullLocalCharacters A)
    (f₁ f₂ : Ideal (𝓞 F)) (o₁ : RayClassCharacter F f₁) (o₂ : RayClassCharacter F f₂)
    (h₁ : SPrimeCompatibility A f₁ o₁ sigma) (h₂ : SPrimeCompatibility A f₂ o₂ sigma)
    (v : {v // v ∈ A.Sf}) :
    idealPrimeExponent v.val.asIdeal f₁ = idealPrimeExponent v.val.asIdeal f₂ := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨x, hx, hn⟩ := (h₁ v).2.1 _ h
    exact hn ((h₂ v).1 x hx)
  · by_contra! h
    obtain ⟨x, hx, hn⟩ := (h₂ v).2.1 _ h
    exact hn ((h₁ v).1 x hx)

private theorem uniformizer_exists (v : HeightOneSpectrum (𝓞 F)) :
    ∃ pi : (v.adicCompletion F)ˣ,
      ‖(pi : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer F
  have hr0 : r ≠ 0 := by
    intro h
    have hz : (v.valuation F) r = 0 := by simp [h]
    rw [hr] at hz
    exact WithZero.coe_ne_zero hz
  refine ⟨Units.map (FinitePlace.embedding v).toMonoidHom (Units.mk0 r hr0), ?_⟩
  change ‖FinitePlace.embedding v r‖ = _
  rw [FinitePlace.norm_embedding', hr]
  simp [WithZeroMulInt.toNNReal]

private theorem exterior_prime (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) : v.asIdeal ⊔ A.cS = ⊤ := by
  apply Ideal.sup_prod_eq_top
  intro w hw
  apply v.isMaximal.coprime_of_ne w.isMaximal
  intro he
  exact hv (HeightOneSpectrum.ext he ▸ hw)

private theorem s_prime_eq (A : SArithmeticData F) (sigma : FixedSResidue.FullLocalCharacters A)
    (f₁ f₂ : Ideal (𝓞 F)) (hf₁ : f₁ ≠ ⊥) (hf₂ : f₂ ≠ ⊥)
    (o₁ : RayClassCharacter F f₁) (o₂ : RayClassCharacter F f₂)
    (h₁ : SPrimeCompatibility A f₁ o₁ sigma) (h₂ : SPrimeCompatibility A f₂ o₂ sigma)
    (v : {v // v ∈ A.Sf}) : o₁ v.val.asIdeal = o₂ v.val.asIdeal := by
  have he := exponent_eq A sigma f₁ f₂ o₁ o₂ h₁ h₂ v
  have hc : v.val.asIdeal ⊔ f₁ = ⊤ ↔ v.val.asIdeal ⊔ f₂ = ⊤ := by
    rw [← exponent_zero_iff v.val f₁ hf₁, ← exponent_zero_iff v.val f₂ hf₂, he]
  by_cases hv : v.val.asIdeal ⊔ f₁ = ⊤
  · obtain ⟨pi, hpi⟩ := uniformizer_exists v.val
    rw [(h₁ v).2.2 hv pi hpi, (h₂ v).2.2 (hc.mp hv) pi hpi]
  · have hv₂ : v.val.asIdeal ⊔ f₂ ≠ ⊤ := fun h => hv (hc.mpr h)
    rw [(o₁.eq_zero_iff' _).mpr (Or.inr hv), (o₂.eq_zero_iff' _).mpr (Or.inr hv₂)]

 def charHom (f : Ideal (𝓞 F)) (o : RayClassCharacter F f) :
    Ideal (𝓞 F) →* ℂ where
  toFun := o.toFun
  map_one' := by simpa using o.map_top'
  map_mul' := o.map_mul'

theorem ideal_character_eq (A : SArithmeticData F)
    (hprincipal : ExteriorPrincipalization A)
    (sigma : FullLocalCharacters A) (hsigma : HasFiniteOrder A sigma)
    (f₁ f₂ fS₁ fS₂ qO : Ideal (𝓞 F))
    (omega₁ : RayClassCharacter F f₁) (omega₂ : RayClassCharacter F f₂)
    (hprimitive₁ : omega₁.IsPrimitive) (hprimitive₂ : omega₂.IsPrimitive)
    (hsplit₁ : ConductorSplit A f₁ fS₁ qO)
    (hsplit₂ : ConductorSplit A f₂ fS₂ qO)
    (hlocal₁ : SPrimeCompatibility A f₁ omega₁ sigma)
    (hlocal₂ : SPrimeCompatibility A f₂ omega₂ sigma)
    (lam₁ lam₂ : ResidueCharacter A (residueModulus A qO))
    (hbridge₁ : ExteriorDecomposition A f₁ omega₁ sigma (residueModulus A qO) lam₁)
    (hbridge₂ : ExteriorDecomposition A f₂ omega₂ sigma (residueModulus A qO) lam₂)
    (hlam : lam₁ = lam₂) :
    omega₁.toFun = omega₂.toFun := by
  subst lam₂
  have hp : ∀ p : Ideal (𝓞 F), Prime p → omega₁ p = omega₂ p := by
    intro p hp
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    by_cases hv : v ∈ A.Sf
    · exact s_prime_eq A sigma f₁ f₂ hsplit₁.1 hsplit₂.1 omega₁ omega₂ hlocal₁ hlocal₂ ⟨v, hv⟩
    · let a : A.Exterior := ⟨p, hp.ne_zero, exterior_prime A v hv⟩
      obtain ⟨n, hn⟩ := hprincipal a
      exact (hbridge₁ a n hn).trans (hbridge₂ a n hn).symm
  funext I
  by_cases hI : I = ⊥
  · subst I
    exact ((omega₁.eq_zero_iff' _).mpr (Or.inl rfl)).trans
      ((omega₂.eq_zero_iff' _).mpr (Or.inl rfl)).symm
  · have hprod : (normalizedFactors I).prod = I := by
      simpa using prod_normalizedFactors_eq hI
    change charHom f₁ omega₁ I = charHom f₂ omega₂ I
    rw [← hprod, map_multiset_prod, map_multiset_prod]
    congr 1
    apply Multiset.map_congr rfl
    intro p hpI
    exact hp p (prime_of_normalized_factor p hpI)

end
end DedekindZetaZeroFree.Detector.FixedSInjectivity
