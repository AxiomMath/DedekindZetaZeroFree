module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.TensorEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.NativeScalarFiniteCompactRestriction
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming productCovariance → productCovariance
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
 abbrev CompactCover := ∀ q : S, (M q.val).iwasawa.compact.toOpenSubgroup

private theorem productSection_from_compact
    (f : ProductFunctions F ζ hζ M S)
    (hf : f ∈ productCovariance F ζ hζ M S) (g : ProductCover F ζ hζ S) :
    f g = PiTensorProduct.map (fun q : S =>
      KPLocalPrincipalSeries.inducingAction (M q.val).borel
        (M q.val).polarization .plus 0
        ((M q.val).iwasawa.borelPart (g q)))
      (f (fun q => ((M q.val).iwasawa.compactPart (g q) : Cover F ζ hζ S q))) := by
  have h := hf (fun q => (M q.val).iwasawa.borelPart (g q))
    (fun q => ((M q.val).iwasawa.compactPart (g q) : Cover F ζ hζ S q))
  convert h using 1
  congr 1
  funext q
  exact (M q.val).iwasawa.decomposition (g q)

 theorem productCompactRestriction_injective
    (f h : ProductFunctions F ζ hζ M S)
    (hf : f ∈ productCovariance F ζ hζ M S)
    (hh : h ∈ productCovariance F ζ hζ M S)
    (heq : ∀ k : CompactCover F ζ hζ M S,
      f (fun q => (k q : Cover F ζ hζ S q)) =
        h (fun q => (k q : Cover F ζ hζ S q))) : f = h := by
  funext g
  rw [productSection_from_compact F ζ hζ M S f hf g,
    productSection_from_compact F ζ hζ M S h hh g,
    heq (fun q => (M q.val).iwasawa.compactPart (g q))]

end DedekindZetaZeroFree.NativeScalarFiniteCompactRestriction

end
