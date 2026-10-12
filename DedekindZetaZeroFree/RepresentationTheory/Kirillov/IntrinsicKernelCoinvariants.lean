module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrdinarySectionCoinvariants
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.TensorSlotCoinvariants
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrbitSectionIsomorphism

@[expose] public section

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.Intrinsic
open scoped NumberField TensorProduct Classical
open NumberField IsDedekindDomain
open KPKirillovGenuineSectionCharts KPKirillovProjectorGerms
open KPKirillovFiniteBallProjectors KPKirillovOrbitMapFaithful
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (v : HeightOneSpectrum (𝓞 F))
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ v) V)
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F v m)
  (hρ : IsSmooth F ζ hζ v m ρ)
  (hgen : KPLocalSmoothRepresentation.genuine F ζ hζ v ρ)
  (hψ : IsLocallyConstant (ψ F v))

def kernelEquiv : (Sections F ζ hζ v m (ψ F v) ℂ ⊗[ℂ] J F ζ hζ v ρ) ≃ₗ[ℂ]
    ordinaryKernel F ζ hζ v ρ :=
  (sectionsTensorEquiv F ζ hζ v m hm (ψ F v) hψ (J F ζ hζ v ρ)).trans
    (KPKirillovOrbitMapSurjective.orbitEquiv F ζ hζ v ρ m hm hρ hgen).symm

def embedding : (Sections F ζ hζ v m (ψ F v) ℂ ⊗[ℂ] J F ζ hζ v ρ) →ₗ[ℂ] V :=
  (ordinaryKernel F ζ hζ v ρ).subtype.comp
    (kernelEquiv F ζ hζ v ρ m hm hρ hgen hψ).toLinearMap

theorem embedding_injective : Function.Injective (embedding F ζ hζ v ρ m hm hρ hgen hψ) :=
  Subtype.val_injective.comp (kernelEquiv F ζ hζ v ρ m hm hρ hgen hψ).injective

theorem embedding_equivariant (p : P F ζ hζ v)
    (x : Sections F ζ hζ v m (ψ F v) ℂ ⊗[ℂ] J F ζ hζ v ρ) :
    embedding F ζ hζ v ρ m hm hρ hgen hψ
      (TensorProduct.map (rightAction F ζ hζ v m hm (ψ F v) ℂ p) LinearMap.id x) =
    ρ p.val (embedding F ζ hζ v ρ m hm hρ hgen hψ x) := by
  unfold embedding kernelEquiv
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
    LinearEquiv.trans_apply]
  let T := sectionsTensorEquiv F ζ hζ v m hm (ψ F v) hψ (J F ζ hζ v ρ)
  let O := KPKirillovOrbitMapSurjective.orbitEquiv F ζ hζ v ρ m hm hρ hgen
  have ht := sectionsTensorEquiv_equivariant F ζ hζ v m hm (ψ F v) hψ p x
  have ho := KPKirillovOrbitMapSurjective.orbitEquiv_symm_intertwines
    F ζ hζ v ρ m hm hρ hgen p (T x)
  exact (congrArg (fun f => (O.symm f).val) ht).trans (congrArg Subtype.val ho)

theorem embedding_evaluation
    (s : Sections F ζ hζ v m (ψ F v) ℂ) (e : J F ζ hζ v ρ) :
    rootCoinvariantsMk ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ v) (ψ F v)
      (embedding F ζ hζ v ρ m hm hρ hgen hψ (s ⊗ₜ[ℂ] e)) =
    sectionValue F ζ hζ v m (ψ F v) s 1 • e := by
  unfold embedding kernelEquiv
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
    LinearEquiv.trans_apply]
  change quotientMap F ζ hζ v ρ 1 _ = _
  rw [KPKirillovOrbitMapSurjective.orbitEquiv_symm_quotient]
  exact sectionsTensorEquiv_tmul F ζ hζ v m hm (ψ F v) hψ s e 1

def rootHom : Multiplicative (K F v) →* P F ζ hζ v where
  toFun b := n F ζ hζ v b.toAdd
  map_one' := by
    apply Subtype.ext
    exact (KPLocalSmoothRepresentation.upperRoot F ζ hζ v).map_one
  map_mul' a b := by
    apply Subtype.ext
    exact (KPLocalSmoothRepresentation.upperRoot F ζ hζ v).map_mul a b

end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.Intrinsic

end
