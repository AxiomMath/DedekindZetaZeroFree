module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.CompactRestriction

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming productCovariance → productCovariance
open _root_.DedekindZetaZeroFree.NativeScalarFiniteCompactRestriction renaming CompactCover → CompactCover
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

 def slotStabilizer (J : OpenSubgroup (ProductCover F ζ hζ S)) (q : S) :
    OpenSubgroup (Cover F ζ hζ S q) where
  toSubgroup := J.toSubgroup.comap (MonoidHom.mulSingle (Cover F ζ hζ S) q)
  isOpen' := J.isOpen.preimage (continuous_mulSingle q)

private theorem product_slotStabilizer_le
    (J : OpenSubgroup (ProductCover F ζ hζ S)) :
    Subgroup.pi Set.univ (fun q => (slotStabilizer F ζ hζ S J q).toSubgroup) ≤
      J.toSubgroup := by
  intro j hj
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro q
  exact hj q (Set.mem_univ q)

 theorem productSection_rectangular_level
    (f : ProductFunctions F ζ hζ M S)
    (hf : SmoothVector KPLocalPrincipalSeries.vectorRightTranslation f) :
    ∃ U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q),
      ∀ (j : ProductCover F ζ hζ S), (∀ q, j q ∈ U q) → ∀ g, f (g * j) = f g := by
  obtain ⟨J, hJ⟩ := hf
  refine ⟨fun q => slotStabilizer F ζ hζ S J q, ?_⟩
  intro j hj g
  have hm : j ∈ J := product_slotStabilizer_le F ζ hζ S J (fun q _ => hj q)
  exact congrFun (hJ j hm) g

 def compactSlotStabilizer
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    OpenSubgroup (M q.val).iwasawa.compact.toOpenSubgroup :=
  (U q).comap
    (Subgroup.subtype (M q.val).iwasawa.compact.toOpenSubgroup.toSubgroup)
    continuous_subtype_val

 abbrev CompactCosets
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :=
  ∀ q : S, (M q.val).iwasawa.compact.toOpenSubgroup ⧸
    (compactSlotStabilizer F ζ hζ M S U q).toSubgroup

 theorem compactCosets_finite
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    Finite (CompactCosets F ζ hζ M S U) := by
  let (q : S) : CompactSpace (M q.val).iwasawa.compact.toOpenSubgroup :=
    isCompact_iff_compactSpace.mp (M q.val).iwasawa.compact.isCompact
  unfold CompactCosets
  let (q : S) : IsTopologicalGroup (M q.val).iwasawa.compact.toOpenSubgroup :=
    Topology.IsInducing.isTopologicalGroup
      (Subgroup.subtype (M q.val).iwasawa.compact.toOpenSubgroup.toSubgroup)
      Topology.IsInducing.subtypeVal
  let (q : S) : Finite ((M q.val).iwasawa.compact.toOpenSubgroup ⧸
      (compactSlotStabilizer F ζ hζ M S U q).toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ (compactSlotStabilizer F ζ hζ M S U q).isOpen
  infer_instance

 theorem compactRestriction_representatives
    (f : ProductFunctions F ζ hζ M S)
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (hU : ∀ (j : ProductCover F ζ hζ S), (∀ q, j q ∈ U q) → ∀ g, f (g * j) = f g)
    (k : CompactCover F ζ hζ M S) :
    f (fun q => ((QuotientGroup.mk (k q) :
      (M q.val).iwasawa.compact.toOpenSubgroup ⧸
        (compactSlotStabilizer F ζ hζ M S U q).toSubgroup).out : Cover F ζ hζ S q)) =
      f (fun q => (k q : Cover F ζ hζ S q)) := by
  choose j hj using fun q : S => QuotientGroup.mk_out_eq_mul
    (s := (compactSlotStabilizer F ζ hζ M S U q).toSubgroup) (k q)
  have hm : ∀ q : S, (((j q).val :
      (M q.val).iwasawa.compact.toOpenSubgroup) : Cover F ζ hζ S q) ∈ U q :=
    fun q => (j q).property
  convert hU (fun q => (((j q).val :
    (M q.val).iwasawa.compact.toOpenSubgroup) : Cover F ζ hζ S q)) hm
    (fun q => (k q : Cover F ζ hζ S q)) using 1
  congr 1
  funext q
  exact congrArg (fun a : (M q.val).iwasawa.compact.toOpenSubgroup =>
    (a : Cover F ζ hζ S q)) (hj q)

end DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer

end
