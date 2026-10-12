module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseOperatorEvaluation
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.ProjectorGermsAndFrequencySupport

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorFrequency
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 def conjugate_root_map
    {G N V : Type*} [Group G] [Group N] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (n : N →* G) (e : N ≃* N) (g : G)
    (hconj : ∀ x, g * n x = n (e x) * g)
    (ψ χ : N →* ℂˣ) (hchar : ∀ x, χ (e x) = ψ x) :
    RootCoinvariants ρ n ψ →ₗ[ℂ] RootCoinvariants ρ n χ :=
  rootCoinvariantsLift ρ n ψ ⟨(rootCoinvariantsMk ρ n χ).comp (ρ g), by
    intro x v
    change rootCoinvariantsMk ρ n χ (ρ g (ρ (n x) v)) =
      (ψ x : ℂ) • rootCoinvariantsMk ρ n χ (ρ g v)
    rw [← Module.End.mul_apply, ← map_mul, hconj x, map_mul, Module.End.mul_apply,
      rootCoinvariantsMk_equivariant, hchar]⟩

 def conjugate_root_equiv
    {G N V : Type*} [Group G] [Group N] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (n : N →* G) (e : N ≃* N) (g : G)
    (hconj : ∀ x, g * n x = n (e x) * g)
    (ψ χ : N →* ℂˣ) (hchar : ∀ x, χ (e x) = ψ x) :
    RootCoinvariants ρ n ψ ≃ₗ[ℂ] RootCoinvariants ρ n χ := by
  have hinv : ∀ x, g⁻¹ * n x = n (e.symm x) * g⁻¹ := by
    intro x
    have H := congrArg (fun z => g⁻¹ * z * g⁻¹) (hconj (e.symm x))
    simpa [mul_assoc] using H.symm
  have hc : ∀ x, ψ (e.symm x) = χ x := by
    intro x
    simpa using (hchar (e.symm x)).symm
  exact
    { toLinearMap := conjugate_root_map ρ n e g hconj ψ χ hchar
      invFun := conjugate_root_map ρ n e.symm g⁻¹ hinv χ ψ hc
      left_inv := by
        intro x
        obtain ⟨v, rfl⟩ := rootCoinvariantsMk_surjective ρ n ψ x
        change rootCoinvariantsMk ρ n ψ (ρ g⁻¹ (ρ g v)) = _
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      right_inv := by
        intro x
        obtain ⟨v, rfl⟩ := rootCoinvariantsMk_surjective ρ n χ x
        change rootCoinvariantsMk ρ n χ (ρ g (ρ g⁻¹ v)) = _
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] }

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

 def scale_root (y : (LocalField F q)ˣ) :
    Multiplicative (LocalField F q) ≃* Multiplicative (LocalField F q) where
  toFun x := Multiplicative.ofAdd ((y : LocalField F q) * Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((y⁻¹ : (LocalField F q)ˣ) : LocalField F q) * Multiplicative.toAdd x)
  left_inv := by intro x; simp [← mul_assoc]
  right_inv := by intro x; simp [← mul_assoc]
  map_mul' := by intro x z; simp [mul_add]

 local instance sectionAdd (ε : Sign) : AddCommGroup (sectionSpace S.borel P ε 0) :=
  inferInstance

 def frequency_quotient_equiv
    (ε : Sign) (t : actualTorus F ζ hζ q) (a b : LocalField F q)
    (hab : b * (S.borel.coordinate t : LocalField F q) = a) :
    RootCoinvariants (principalSeries S.borel P ε 0) (S.borel.B.subtype.comp S.borel.upperRoot)
      (KPKirillovProjectorGerms.frequencyCharacter F q a) ≃ₗ[ℂ]
    RootCoinvariants (principalSeries S.borel P ε 0) (S.borel.B.subtype.comp S.borel.upperRoot)
      (KPKirillovProjectorGerms.frequencyCharacter F q b) := by
  apply conjugate_root_equiv _ _ (scale_root F q (S.borel.coordinate t))
    (S.borel.torus t : ActualCover F ζ hζ q)
  · intro x
    have H := CompactBorel.torus_root F ζ hζ q S P t (Multiplicative.toAdd x)
    have H' := congrArg (fun z => z * (S.borel.torus t : ActualCover F ζ hζ q)) H
    simpa [scale_root, mul_assoc] using H'
  · intro x
    apply Units.ext
    change (KPKirillovProjectorGerms.frequencyCharacter F q b
      (Multiplicative.ofAdd ((S.borel.coordinate t : LocalField F q) * Multiplicative.toAdd x)) : ℂ) =
      (KPKirillovProjectorGerms.frequencyCharacter F q a x : ℂ)
    change (Circle.toUnits ((localFiniteCharacter F q)
      (b * ((S.borel.coordinate t : LocalField F q) * Multiplicative.toAdd x))) : ℂ) =
      (Circle.toUnits ((localFiniteCharacter F q) (a * Multiplicative.toAdd x)) : ℂ)
    rw [← mul_assoc, hab]

private theorem actual_reverse_frequency_square
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (t : actualTorus F ζ hζ q) (a b : LocalField F q)
    (hab : b * (S.borel.coordinate t : LocalField F q) = a)
    (v : sectionSpace S.borel P .minus 0) :
    frequency_quotient_equiv F ζ hζ q S P .plus t a b hab
      (rootCoinvariantsMk (IPlus S.borel P) (S.borel.B.subtype.comp S.borel.upperRoot)
        (KPKirillovProjectorGerms.frequencyCharacter F q a)
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v)) =
    rootCoinvariantsMk (IPlus S.borel P) (S.borel.B.subtype.comp S.borel.upperRoot)
      (KPKirillovProjectorGerms.frequencyCharacter F q b)
      (actualCanonicalReverseMap F ζ hζ q S P μ hμ
        (IMinus S.borel P (S.borel.torus t : ActualCover F ζ hζ q) v)) := by
  change rootCoinvariantsMk (IPlus S.borel P) _ _
    (IPlus S.borel P (S.borel.torus t : ActualCover F ζ hζ q)
      (actualCanonicalReverseMap F ζ hζ q S P μ hμ v)) = _
  congr 1
  exact (actualCanonicalReverseLinear_intertwines F ζ hζ q S P μ hμ _ v).symm

theorem actual_reverse_frequency_pair_transport
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (t : actualTorus F ζ hζ q) (a b : LocalField F q)
    (hab : b * (S.borel.coordinate t : LocalField F q) = a)
    (v₁ v₂ : sectionSpace S.borel P .minus 0)
    (h : LinearIndependent ℂ ![
      rootCoinvariantsMk (IPlus S.borel P) (S.borel.B.subtype.comp S.borel.upperRoot)
        (KPKirillovProjectorGerms.frequencyCharacter F q a)
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₁),
      rootCoinvariantsMk (IPlus S.borel P) (S.borel.B.subtype.comp S.borel.upperRoot)
        (KPKirillovProjectorGerms.frequencyCharacter F q a)
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ v₂)]) :
    LinearIndependent ℂ ![
      rootCoinvariantsMk (IPlus S.borel P) (S.borel.B.subtype.comp S.borel.upperRoot)
        (KPKirillovProjectorGerms.frequencyCharacter F q b)
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ
          (IMinus S.borel P (S.borel.torus t : ActualCover F ζ hζ q) v₁)),
      rootCoinvariantsMk (IPlus S.borel P) (S.borel.B.subtype.comp S.borel.upperRoot)
        (KPKirillovProjectorGerms.frequencyCharacter F q b)
        (actualCanonicalReverseMap F ζ hζ q S P μ hμ
          (IMinus S.borel P (S.borel.torus t : ActualCover F ζ hζ q) v₂))] := by
  let E := frequency_quotient_equiv F ζ hζ q S P .plus t a b hab
  have H := h.map' E.toLinearMap (LinearMap.ker_eq_bot.mpr E.injective)
  convert H using 1
  funext i
  fin_cases i <;>
    exact (actual_reverse_frequency_square F ζ hζ q S P μ hμ t a b hab _).symm

end DedekindZetaZeroFree.ActualReverseMinorFrequency

end
