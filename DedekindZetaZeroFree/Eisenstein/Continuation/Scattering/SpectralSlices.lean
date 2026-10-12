module

public import DedekindZetaZeroFree.Eisenstein.Induction.LocalSpectralWeights
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.TraceHaarContraction

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLocalExceptionalConstruction KPLocalPrincipalSeries
open KPRankOneShellRepair KPAdelicCoverRestrictedProduct ThetaExpansion
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open _root_.DedekindZetaZeroFree.KPLocalStoneVonNeumann renaming inducedCosetEquiv → inducedCosetEquiv
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def integralCompactProfile (q : KPFinitePlace F)
    (f : Plus R.A P C (Sum.inr q)) (s : ℂ) :
    compactPicture (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus :=
  LocalCompactChange.correctedCompact F ζ hζ q (C.canonical q)
    (C.canonical q).iwasawa (finiteIntegralIwasawa R P C q) (C.polarization q) s
      ((compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus 0).symm f)

def integralSpectralSection (q : KPFinitePlace F)
    (f : Plus R.A P C (Sum.inr q)) (s : ℂ) :
    sectionSpace (C.canonical q).borel (C.polarization q) .plus s :=
  compactTrivialization (C.canonical q).borel (C.polarization q)
    (C.canonical q).iwasawa .plus s (integralCompactProfile R P C q f s)

theorem integralSpectralSection_value (q : KPFinitePlace F)
    (f : Plus R.A P C (Sum.inr q)) (s : ℂ) (g : ActualCover F ζ hζ q) :
    (integralSpectralSection R P C q f s).val g =
      Complex.exp (s * (Real.log (LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q)
        (finiteIntegralIwasawa R P C q) g) : ℂ)) • f.val g := by
  have h := LocalCompactChange.correctedCompact_displacement F ζ hζ q (C.canonical q)
    (C.canonical q).iwasawa (finiteIntegralIwasawa R P C q) (C.polarization q)
    ((compactTrivialization (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus 0).symm f) s g
  simpa only [integralSpectralSection, integralCompactProfile,
    LinearEquiv.apply_symm_apply] using h

theorem coreFlatInsertion_scattering_stage
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (g : Raw R.A)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (hg : ∀ v, v ∉ t.val → localValue R.A P C v (g v) (plusReference R.A P C v) = reference R.A P C v)
    (s : ℂ) (y : q.adicCompletion F) :
    (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ t
      (PiTensorProduct.tprod ℂ x))).val s
      (scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q) (finiteScatteringRaw R.A q y)) *
        scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
      Complex.exp (s * (awayHeight R P C q g : ℂ)) *
        rationalSlotContraction R.A P C t q hq
          (fun j => localValue R.A P C j.val (g j.val) (x j))
          ((integralSpectralSection R P C q (x ⟨Sum.inr q,hq⟩) s).val
            ((C.canonical q).borel.liftedW⁻¹ *
              (C.canonical q).borel.upperRoot (Multiplicative.ofAdd y) *
                KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q)))) := by
  simp only [coreFlatInsertion, scalarTwist, quotientCoreEvaluator,
    LinearMap.coe_mk, AddHom.coe_mk]
  change Complex.exp (s * (iwasawaLogHeight R _ : ℂ)) * quotientCoreValue R.A P C _ _ = _
  change Complex.exp (s * (iwasawaLogHeight R
    (scalarQuotient F ζ hζ (amalgamation F ζ hζ
      (localToRestricted F ζ hζ (Sum.inr q) (finiteScatteringRaw R.A q y))) *
        scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) : ℂ)) *
      quotientCoreValue R.A P C _
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ
          (localToRestricted F ζ hζ (Sum.inr q) (finiteScatteringRaw R.A q y))) *
            scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) = _
  simp only [← map_mul]
  rw [quotientCoreValue_raw,
    spectralWeight_local_left R P C q (finiteScatteringRaw R.A q y) g s]
  have hraw := rawCoreInsertion_scattering_stage R.A P C t x g q hq hg y
  simp only [rawCoreInsertion, LinearMap.coe_mk, AddHom.coe_mk] at hraw
  rw [hraw, integralSpectralSection_value, map_smul, smul_eq_mul]
  unfold rationalScatteringSlice
  rw [map_mul, finiteScatteringRaw_quotient]
  ring

theorem spectral_forward_contraction (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (q.adicCompletion F)).integer : Set _) = 1)
    (s : ℂ) (hs : KPRankOneShellContinuation.convergenceHalfPlane .plus s)
    (f : sectionSpace (C.canonical q).borel (C.polarization q) .plus s)
    (g : ActualCover F ζ hζ q)
    (L : LocalFiber F ζ hζ P C q →ₗ[ℂ] ℂ) :
    let out := KPRankOneShellContinuation.transportToSections (q.adicCompletion F)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
      (actualCanonicalContinued F q ζ hζ (C.canonical q) (C.polarization q) μ hμ .plus s) f
    Integrable (fun y => L (f.val ((C.canonical q).borel.liftedW⁻¹ *
      (C.canonical q).borel.upperRoot (Multiplicative.ofAdd y) * g))) μ ∧
    (∫ y, L (f.val ((C.canonical q).borel.liftedW⁻¹ *
      (C.canonical q).borel.upperRoot (Multiplicative.ofAdd y) * g)) ∂μ) = L (out.val g) := by
  dsimp only
  let J := actualTorus F ζ hζ q ⧸ (C.polarization q).L.comap (C.canonical q).heisenberg.π
  letI : Fintype J := Fintype.ofFinite _
  let e : LocalFiber F ζ hζ P C q ≃ₗ[ℂ] (J → ℂ) :=
    inducedCosetEquiv ((C.polarization q).L.comap (C.canonical q).heisenberg.π)
      (C.polarization q).ωL.toMonoidHom
  let b (j : J) := e.symm (Pi.single j 1)
  have hex (w : LocalFiber F ζ hζ P C q) : w = ∑ j : J, e w j • b j := by
    apply e.injective
    simp only [map_sum, map_smul, b, LinearEquiv.apply_symm_apply]
    conv_lhs => rw [← Finset.univ_sum_single (e w)]
    apply Finset.sum_congr rfl
    intro j _
    funext k
    simp [Pi.single_apply]
  let v (y : q.adicCompletion F) := f.val ((C.canonical q).borel.liftedW⁻¹ *
    (C.canonical q).borel.upperRoot (Multiplicative.ofAdd y) * g)
  let out := (KPRankOneShellContinuation.transportToSections (q.adicCompletion F)
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
    (actualCanonicalContinued F q ζ hζ (C.canonical q) (C.polarization q) μ hμ .plus s) f).val g
  have hcoord (j : J) : Integrable (fun y => e (v y) j) μ ∧ (∫ y, e (v y) j ∂μ) = e out j := by
    let h := Function.surjInv (QuotientGroup.mk'_surjective
      ((C.polarization q).L.comap (C.canonical q).heisenberg.π)) j
    refine ⟨actualCanonicalContinued_integrable F q ζ hζ (C.canonical q)
      (C.polarization q) μ hμ .plus s hs f g h, ?_⟩
    have hi := actualContinued_section_eq_integral F ζ hζ q (C.canonical q)
      (C.polarization q) μ hμ (actualFamilyUniformizer F q)
      (actualFamilyUniformizer_spec F q) .plus s hs f g h
    exact hi.symm
  have he : (fun y => L (v y)) = (fun y => ∑ j : J, e (v y) j * L (b j)) := by
    funext y
    conv_lhs => rw [hex (v y)]
    simp only [map_sum, map_smul, smul_eq_mul]
  change Integrable (fun y => L (v y)) μ ∧ (∫ y, L (v y) ∂μ) = L out
  rw [he]
  refine ⟨integrable_finsetSum _ (fun j _ => (hcoord j).1.mul_const _), ?_⟩
  rw [integral_finsetSum _ (fun j _ => (hcoord j).1.mul_const _)]
  simp_rw [integral_mul_const, (hcoord _).2]
  conv_rhs => rw [hex out]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem coreFlatInsertion_scattering_stage_integral
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (g : Raw R.A)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (hg : ∀ v, v ∉ t.val → localValue R.A P C v (g v) (plusReference R.A P C v) = reference R.A P C v)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (q.adicCompletion F)).integer : Set _) = 1)
    (s : ℂ) (hs : KPRankOneShellContinuation.convergenceHalfPlane .plus s) :
    let arg := fun y => scalarQuotient F ζ hζ
      (localInjection F ζ hζ (Sum.inr q) (finiteScatteringRaw R.A q y)) *
        scalarQuotient F ζ hζ (amalgamation F ζ hζ g)
    let f := integralSpectralSection R P C q (x ⟨Sum.inr q,hq⟩) s
    let out := KPRankOneShellContinuation.transportToSections (q.adicCompletion F)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
      (actualCanonicalContinued F q ζ hζ (C.canonical q) (C.polarization q) μ hμ .plus s) f
    Integrable (fun y => (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ t
      (PiTensorProduct.tprod ℂ x))).val s (arg y)) μ ∧
    (∫ y, (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion _ _ _ t
      (PiTensorProduct.tprod ℂ x))).val s (arg y) ∂μ) =
      Complex.exp (s * (awayHeight R P C q g : ℂ)) *
        rationalSlotContraction R.A P C t q hq
          (fun j => localValue R.A P C j.val (g j.val) (x j))
          (out.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q)))) := by
  dsimp only
  have he := funext (fun y => coreFlatInsertion_scattering_stage R P C t x g q hq hg s y)
  rw [he]
  have hi := spectral_forward_contraction R P C q μ hμ s hs
    (integralSpectralSection R P C q (x ⟨Sum.inr q,hq⟩) s)
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q)))
    (rationalSlotContraction R.A P C t q hq
      (fun j => localValue R.A P C j.val (g j.val) (x j)))
  exact ⟨hi.1.const_mul _, (integral_const_mul _ _).trans (congrArg (fun z =>
    Complex.exp (s * (awayHeight R P C q g : ℂ)) * z) hi.2)⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
