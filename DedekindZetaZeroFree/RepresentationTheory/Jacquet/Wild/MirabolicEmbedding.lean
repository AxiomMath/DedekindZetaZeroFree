module

public import DedekindZetaZeroFree.Theta.Whittaker.Jacquet.SmoothGenuineAction
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.IntrinsicKernelCoinvariants

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.WildActualMirabolic
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPRankOneShellRepair
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
abbrev rho := actualCanonicalImageRepresentation F ζ hζ q S P μ hμ

theorem image_smooth (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    KPKirillovFiniteBallProjectors.IsSmooth F ζ hζ q m (rho F ζ hζ q S P μ hμ) := by
  unfold KPKirillovFiniteBallProjectors.IsSmooth
  change @SmoothRepresentation _ _ _ (KPPGLLocalCover.finiteTopology F ζ hζ q m) _ _ _
  rw [KPPGLLocalCover.finiteTopology_independent F ζ hζ q m
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q) hm
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)]
  exact actualCanonicalImage_smooth F ζ hζ q S P μ hμ

theorem image_genuine :
    KPLocalSmoothRepresentation.genuine F ζ hζ q (rho F ζ hζ q S P μ hμ) := by
  intro e v
  exact actualCanonicalImage_ordinary_genuine F ζ hζ q S P μ hμ e v

abbrev Jacquet := KPKirillovOrbitMapFaithful.J F ζ hζ q (rho F ζ hζ q S P μ hμ)

def embedding (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    (KPKirillovGenuineSectionCharts.Sections F ζ hζ q m
      (KPKirillovOrbitMapFaithful.ψ F q) ℂ ⊗[ℂ] Jacquet F ζ hζ q S P μ hμ) →ₗ[ℂ]
      actualCanonicalImageModule F ζ hζ q S P μ hμ :=
  KPWildCompactProjectorKirillov.Intrinsic.embedding F ζ hζ q
    (rho F ζ hζ q S P μ hμ) m hm (image_smooth F ζ hζ q S P μ hμ m hm)
    (image_genuine F ζ hζ q S P μ hμ)
    (KPWildCompactProjectorKirillov.ActualInput.standardCharacter_properties F q).1

theorem embedding_injective (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    Function.Injective (embedding F ζ hζ q S P μ hμ m hm) :=
  KPWildCompactProjectorKirillov.Intrinsic.embedding_injective F ζ hζ q
    (rho F ζ hζ q S P μ hμ) m hm (image_smooth F ζ hζ q S P μ hμ m hm)
    (image_genuine F ζ hζ q S P μ hμ)
    (KPWildCompactProjectorKirillov.ActualInput.standardCharacter_properties F q).1
theorem embedding_equivariant (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (p : KPKirillovGenuineSectionCharts.P F ζ hζ q)
    (x : KPKirillovGenuineSectionCharts.Sections F ζ hζ q m
      (KPKirillovOrbitMapFaithful.ψ F q) ℂ ⊗[ℂ] Jacquet F ζ hζ q S P μ hμ) :
    embedding F ζ hζ q S P μ hμ m hm
      (TensorProduct.map (KPKirillovGenuineSectionCharts.rightAction F ζ hζ q m hm
        (KPKirillovOrbitMapFaithful.ψ F q) ℂ p) LinearMap.id x) =
      rho F ζ hζ q S P μ hμ p.val (embedding F ζ hζ q S P μ hμ m hm x) :=
  KPWildCompactProjectorKirillov.Intrinsic.embedding_equivariant F ζ hζ q
    (rho F ζ hζ q S P μ hμ) m hm (image_smooth F ζ hζ q S P μ hμ m hm)
    (image_genuine F ζ hζ q S P μ hμ)
    (KPWildCompactProjectorKirillov.ActualInput.standardCharacter_properties F q).1 p x

theorem embedding_evaluation (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (s : KPKirillovGenuineSectionCharts.Sections F ζ hζ q m
      (KPKirillovOrbitMapFaithful.ψ F q) ℂ) (e : Jacquet F ζ hζ q S P μ hμ) :
    rootCoinvariantsMk (rho F ζ hζ q S P μ hμ)
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ q) (KPKirillovOrbitMapFaithful.ψ F q)
      (embedding F ζ hζ q S P μ hμ m hm (s ⊗ₜ[ℂ] e)) =
      KPKirillovGenuineSectionCharts.sectionValue F ζ hζ q m
        (KPKirillovOrbitMapFaithful.ψ F q) s 1 • e :=
  KPWildCompactProjectorKirillov.Intrinsic.embedding_evaluation F ζ hζ q
    (rho F ζ hζ q S P μ hμ) m hm (image_smooth F ζ hζ q S P μ hμ m hm)
    (image_genuine F ζ hζ q S P μ hμ)
    (KPWildCompactProjectorKirillov.ActualInput.standardCharacter_properties F q).1 s e

end DedekindZetaZeroFree.FourierContinuation.WildActualMirabolic

end
