module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.StabilizersAndCosets

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.NativeScalarFiniteProductFixedLevel
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming productCovariance → productCovariance
open _root_.DedekindZetaZeroFree.NativeScalarFiniteCompactRestriction renaming CompactCover → CompactCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteCompactRestriction renaming productCompactRestriction_injective → productCompactRestriction_injective
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer renaming CompactCosets → CompactCosets
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer renaming compactCosets_finite → compactCosets_finite
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer renaming compactRestriction_representatives → compactRestriction_representatives
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer renaming productSection_rectangular_level → productSection_rectangular_level
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

 def productFixedLevel (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    Submodule ℂ (ProductFunctions F ζ hζ M S) where
  carrier := { f | f ∈ productCovariance F ζ hζ M S ∧
    ∀ (j : ProductCover F ζ hζ S), (∀ q, j q ∈ U q) → ∀ g, f (g * j) = f g }
  zero_mem' := ⟨(productCovariance F ζ hζ M S).zero_mem, by intros; rfl⟩
  add_mem' := by
    intro f h hf hh
    refine ⟨(productCovariance F ζ hζ M S).add_mem hf.1 hh.1, ?_⟩
    intro j hj g
    exact congrArg₂ (· + ·) (hf.2 j hj g) (hh.2 j hj g)
  smul_mem' := by
    intro c f hf
    refine ⟨(productCovariance F ζ hζ M S).smul_mem c hf.1, ?_⟩
    intro j hj g
    exact congrArg (c • ·) (hf.2 j hj g)

 def compactCosetSampling (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    productFixedLevel F ζ hζ M S U →ₗ[ℂ]
      (CompactCosets F ζ hζ M S U → ProductFiber F ζ hζ M S) where
  toFun f c := f.val (fun q => ((c q).out : Cover F ζ hζ S q))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem compactCosetSampling_injective
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    Function.Injective (compactCosetSampling F ζ hζ M S U) := by
  intro f h heq
  apply Subtype.ext
  apply productCompactRestriction_injective F ζ hζ M S f.val h.val f.property.1 h.property.1
  intro k
  have he := congrFun heq (fun q => QuotientGroup.mk (k q))
  change f.val (fun q => ((QuotientGroup.mk (k q) :
    (M q.val).iwasawa.compact.toOpenSubgroup ⧸ _).out : Cover F ζ hζ S q)) =
    h.val (fun q => ((QuotientGroup.mk (k q) :
    (M q.val).iwasawa.compact.toOpenSubgroup ⧸ _).out : Cover F ζ hζ S q)) at he
  rw [compactRestriction_representatives F ζ hζ M S f.val U f.property.2 k,
    compactRestriction_representatives F ζ hζ M S h.val U h.property.2 k] at he
  exact he

private theorem productFixedLevel_finite
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    Module.Finite ℂ (productFixedLevel F ζ hζ M S U) := by
  let (q : S) : Module.Finite ℂ (Fiber F ζ hζ M S q) :=
    KPLocalStoneVonNeumann.tau_moduleFinite (M q.val).heisenberg
      (M q.val).polarization
  let : Finite (CompactCosets F ζ hζ M S U) := compactCosets_finite F ζ hζ M S U
  let : Module.Finite ℂ (ProductFiber F ζ hζ M S) := by
    unfold ProductFiber
    infer_instance
  let : Module.Finite ℂ (CompactCosets F ζ hζ M S U → ProductFiber F ζ hζ M S) :=
    inferInstance
  let : IsNoetherian ℂ (CompactCosets F ζ hζ M S U → ProductFiber F ζ hζ M S) := by
    exact isNoetherian_of_isNoetherianRing_of_finite ℂ
      (CompactCosets F ζ hζ M S U → ProductFiber F ζ hζ M S)
  exact Module.Finite.of_injective (compactCosetSampling F ζ hζ M S U)
    (compactCosetSampling_injective F ζ hζ M S U)

 theorem productSection_mem_finite_level
    (f : ProductFunctions F ζ hζ M S)
    (hcov : f ∈ productCovariance F ζ hζ M S)
    (hf : SmoothVector KPLocalPrincipalSeries.vectorRightTranslation f) :
    ∃ U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q),
      f ∈ productFixedLevel F ζ hζ M S U ∧
      Module.Finite ℂ (productFixedLevel F ζ hζ M S U) := by
  obtain ⟨U, hU⟩ := productSection_rectangular_level F ζ hζ M S f hf
  exact ⟨U, ⟨hcov, hU⟩, productFixedLevel_finite F ζ hζ M S U⟩

end DedekindZetaZeroFree.NativeScalarFiniteProductFixedLevel

end
