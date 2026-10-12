module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing
public import DedekindZetaZeroFree.Theta.Periods.WildPartialPeriodFactorization
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightChartJetsAndFlowWords
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.WildCompactProjectorsAndTrivialization

@[expose] public section

section

noncomputable section

set_option maxHeartbeats 1600000

set_option maxRecDepth 4096

namespace DedekindZetaZeroFree.KPWildNormalizedCoefficientInsertion

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts KPKirillovFiniteTensor

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

noncomputable instance scalarSectionAddCommGroup
    (w : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (ψ : Multiplicative (K F w) →* ℂˣ) :
    AddCommGroup (Sections F ζ hζ w m ψ ℂ) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  letI : AddCommGroup (EqSections (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ ℂ) 1) := Submodule.addCommGroup _
  letI : AddCommGroup (SmoothInd (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ ℂ) 1) := Submodule.addCommGroup _
  exact Submodule.addCommGroup (CompactSmoothInd (H F ζ hζ w)
    (coefficientRepresentation F ζ hζ w ψ ℂ) 1)

end DedekindZetaZeroFree.KPWildNormalizedCoefficientInsertion

end

end

section

noncomputable section

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPWildActualScalarPeriodSource

open KPLocalExceptionalConstruction KPWildPartialPeriodFactorization KPGlobalResidualConstruction

set_option maxHeartbeats 16000000

set_option maxRecDepth 4096

set_option synthInstance.maxHeartbeats 8000000

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev scalarSection (v : WildPlace F) :=
  KPKirillovGenuineSectionCharts.Sections F ζ hζ v.val
    (KPAdelicCoverCertificatesRaw.depth F ζ hζ v.val)
    (KPWildCompactProjectorKirillov.standardCharacter F v.val) ℂ

noncomputable instance scalarSectionAdd (v : WildPlace F) :
    AddCommGroup (scalarSection F ζ hζ v) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v.val
    (KPAdelicCoverCertificatesRaw.depth F ζ hζ v.val)
  letI : AddCommGroup (EqSections (KPKirillovGenuineSectionCharts.H F ζ hζ v.val)
      (KPKirillovGenuineSectionCharts.coefficientRepresentation F ζ hζ v.val
        (KPWildCompactProjectorKirillov.standardCharacter F v.val) ℂ) 1) :=
    Submodule.addCommGroup _
  letI : AddCommGroup (SmoothInd (KPKirillovGenuineSectionCharts.H F ζ hζ v.val)
      (KPKirillovGenuineSectionCharts.coefficientRepresentation F ζ hζ v.val
        (KPWildCompactProjectorKirillov.standardCharacter F v.val) ℂ) 1) :=
    Submodule.addCommGroup _
  exact Submodule.addCommGroup _

abbrev scalarTensor := PiTensorProduct ℂ (fun v : WildPlace F => ↥(scalarSection F ζ hζ v))

end DedekindZetaZeroFree.KPWildActualScalarPeriodSource

end

end

section

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace DedekindZetaZeroFree.KPWildNormalizedCoefficientInsertion
open scoped NumberField TensorProduct Classical
open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts KPKirillovFiniteTensor

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem exists_normalized_scalar_section
    (v : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F v m)
    (ψ : Multiplicative (K F v) →* ℂˣ) (hψ : IsLocallyConstant ψ) :
    letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m
    ∃ f : Sections F ζ hζ v m ψ ℂ,
      sectionValue F ζ hζ v m ψ f 1 = 1 := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ v m
  obtain ⟨c, hc, _⟩ := exists_localChart F ζ hζ v m hm
    (1 : (K F v)ˣ) Set.univ isOpen_univ (Set.mem_univ _)
  let t : c.ball.domain := ⟨1, hc⟩
  let a : CompactFunctions c.ball.domain ℂ := ⟨fun _ => 1,
    IsLocallyConstant.const 1, by
      letI : CompactSpace c.ball.domain :=
        isCompact_iff_compactSpace.mp c.ball.compact_domain
      exact HasCompactSupport.of_compactSpace _⟩
  let s := (patchEquiv F ζ hζ v m hm ψ hψ c ℂ).symm a
  have hs : sectionValue F ζ hζ v m ψ s.val (c.lift t) = 1 := by
    have he := congrArg (fun a => a.val t)
      ((patchEquiv F ζ hζ v m hm ψ hψ c ℂ).apply_symm_apply a)
    rw [patchEquiv_value] at he
    exact he
  refine ⟨rightAction F ζ hζ v m hm ψ ℂ (c.lift t) s.val, ?_⟩
  rw [rightAction_apply, one_mul]
  exact hs

variable (W : Finset (HeightOneSpectrum (𝓞 F)))
  (m : W → ℕ) (hm : ∀ v, KPLocalChartTopology.MatrixChartDepth F v.val (m v))
  (ψ : ∀ v : W, Multiplicative (K F v.val) →* ℂˣ)
  (V : W → Type*) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  (ρ : ∀ v : W, Representation ℂ (G F ζ hζ v.val) (V v))
  (D : LocalEmbeddingData F ζ hζ W m hm ψ V ρ)

theorem tensorEvaluation_normalized
    (f : ∀ v, ScalarSections F ζ hζ W m ψ v)
    (hf : ∀ v, sectionValue F ζ hζ v.val (m v) (ψ v) (f v) 1 = 1)
    (e : JacquetTensor F ζ hζ W ψ V ρ) :
    tensorEvaluation F ζ hζ W m ψ V ρ
      (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e) = e := by
  induction e using PiTensorProduct.induction_on with
  | add e d he hd =>
    simp only [TensorProduct.tmul_add, map_add, he, hd]
  | smul_tprod c e =>
    simp only [TensorProduct.tmul_smul, map_smul]
    congr 1
    change PiTensorProduct.map (localEvaluation F ζ hζ W m ψ V ρ)
      (tensorShuffle F ζ hζ W m ψ V ρ
        (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ e)) = _
    calc
      _ = PiTensorProduct.map (localEvaluation F ζ hζ W m ψ V ρ)
          (PiTensorProduct.tprod ℂ (fun v => f v ⊗ₜ[ℂ] e v)) :=
        congrArg (PiTensorProduct.map (localEvaluation F ζ hζ W m ψ V ρ))
          (tensorShuffle_tmul F ζ hζ W m ψ V ρ f e)
      _ = _ := by
        rw [PiTensorProduct.map_tprod]
        simp only [localEvaluation_tmul, hf, one_smul]

def fixedCoefficientMap (f : ∀ v, ScalarSections F ζ hζ W m ψ v) :
    JacquetTensor F ζ hζ W ψ V ρ →ₗ[ℂ] AmbientTensor F W V :=
  (tensorEmbedding F ζ hζ W m hm ψ V ρ D).comp
    (TensorProduct.mk ℂ (SectionTensor F ζ hζ W m ψ)
      (JacquetTensor F ζ hζ W ψ V ρ) (PiTensorProduct.tprod ℂ f))

theorem quotient_fixedCoefficientMap
    (f : ∀ v, ScalarSections F ζ hζ W m ψ v)
    (hf : ∀ v, sectionValue F ζ hζ v.val (m v) (ψ v) (f v) 1 = 1) :
    (tensorQuotient F ζ hζ W ψ V ρ).comp
      (fixedCoefficientMap F ζ hζ W m hm ψ V ρ D f) = LinearMap.id := by
  apply LinearMap.ext
  intro e
  change tensorQuotient F ζ hζ W ψ V ρ
    (tensorEmbedding F ζ hζ W m hm ψ V ρ D
      (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e)) = e
  calc
    _ = tensorEvaluation F ζ hζ W m ψ V ρ
        (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e) :=
      LinearMap.congr_fun (tensor_evaluation_square F ζ hζ W m hm ψ V ρ D) _
    _ = e := tensorEvaluation_normalized F ζ hζ W m ψ V ρ f hf e

theorem fixedCoefficientMap_injective
    (f : ∀ v, ScalarSections F ζ hζ W m ψ v)
    (hf : ∀ v, sectionValue F ζ hζ v.val (m v) (ψ v) (f v) 1 = 1) :
    Function.Injective (fixedCoefficientMap F ζ hζ W m hm ψ V ρ D f) := by
  apply Function.LeftInverse.injective (g := tensorQuotient F ζ hζ W ψ V ρ)
  intro e
  exact LinearMap.congr_fun
    (quotient_fixedCoefficientMap F ζ hζ W m hm ψ V ρ D f hf) e

end DedekindZetaZeroFree.KPWildNormalizedCoefficientInsertion

end
end
