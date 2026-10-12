module

public import DedekindZetaZeroFree.Theta.Periods.KernelPeriodRealizationAndCoinvariants

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildOrdinaryImageFunctional
open KPKirillovFiniteTensor KPKirillovGenuineSectionCharts
open _root_.DedekindZetaZeroFree.KPKirillovFiniteTensor renaming scalarSectionAddCommGroup → scalarSectionAddCommGroup
open _root_.DedekindZetaZeroFree.KPKirillovFiniteTensor renaming tensorSectionAddCommGroup → tensorSectionAddCommGroup
attribute [local instance] scalarSectionAddCommGroup tensorSectionAddCommGroup
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (W : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (m : W → ℕ)
  (hm : ∀ v, KPLocalChartTopology.MatrixChartDepth F v.val (m v))
  (ψ : ∀ v : W, Multiplicative (K F v.val) →* ℂˣ)
  (V : W → Type) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  (ρ : ∀ v : W, Representation ℂ (G F ζ hζ v.val) (V v))
  (D : LocalEmbeddingData F ζ hζ W m hm ψ V ρ)
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem vanishes (q : W) (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ))
    (L : AmbientTensor F W V →ₗ[ℂ] ℂ)
    (hL : ∀ (t : K F q.val) z,
      L (ambientAction F ζ hζ W V ρ
        (Function.update (1 : ProductAffine F ζ hζ W) q (n F ζ hζ q.val t)) z) = L z)
    (z : InducedTensor F ζ hζ W m ψ V ρ E) :
    L (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E z) = 0 := by
  let J := LinearMap.range (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E)
  let A := imageSlotRootAction F ζ hζ W m hm ψ V ρ D q E
  let l : J →ₗ[ℂ] ℂ := L.comp J.subtype
  have hi (t : Multiplicative (K F q.val)) : l.comp (A t) = l := by
    ext u
    change L ((A t u).val) = L u.val
    exact (congrArg L (imageSlotRootAction_apply F ζ hζ W m hm ψ V ρ D q E t.toAdd u)).trans
      (hL t.toAdd u.val)
  have hz : l = 0 := KPWildKernelSource.invariant_linearMap_zero_of_coinvariants_subsingleton
    A (image_slot_coinvariants_vanish F ζ hζ W m hm ψ V ρ D q E) l hi
  exact LinearMap.congr_fun hz ((subspaceEmbedding F ζ hζ W m hm ψ V ρ D E).rangeRestrict z)
end DedekindZetaZeroFree.FourierContinuation.WildOrdinaryImageFunctional

end
