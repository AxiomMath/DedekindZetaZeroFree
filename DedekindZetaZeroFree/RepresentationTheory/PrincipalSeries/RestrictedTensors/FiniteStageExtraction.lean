module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.CoreInsertionEvaluation
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalFiberRecovery
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.StandardCompactTailEvaluation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
open scoped NumberField Classical
namespace DedekindZetaZeroFree.FourierContinuation.CurrentGlobalSource
open NumberField KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCExtraction
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCFiniteDecomposition KPLiteralScalarHCFiniteProduct
open KPLiteralScalarHCFiniteOutside KPLiteralChamber
open CurrentFiniteFamily CurrentNativeStage NativeScalarMixedTensorGeneration
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
theorem groupDecomposition (g : KPLiteralRaw.G F A.zeta12 A.primitive_zeta12) :
    ∃ (r : RestrictedCover F A.zeta12 A.primitive_zeta12)
      (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2),
      (∀ w : InfinitePlace F, r (Sum.inl w) = 1) ∧
      g = scalarQuotient F A.zeta12 A.primitive_zeta12
        (amalgamation F A.zeta12 A.primitive_zeta12 r) * archMatrixInsertion F A.zeta12 A.primitive_zeta12 m := by
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F A.zeta12 A.primitive_zeta12
  let p := e.symm g
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp p.2.property
  choose m hm using fun w => Matrix.ProjGenLinGroup.mk_surjective (p.1 w)
  refine ⟨r, m, ?_, ?_⟩
  · exact hr
  · have harch : archMatrixInsertion F A.zeta12 A.primitive_zeta12 m =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F A.zeta12 A.primitive_zeta12 p.1 := by
      change scalarQuotient F A.zeta12 A.primitive_zeta12
        (amalgamation F A.zeta12 A.primitive_zeta12 (sectionTuple F A.zeta12 A.primitive_zeta12 m)) = _
      rw [sectionTuple_insertion]
      congr 1
      exact funext hm
    have hfin : p.2.val ∈ KPGlobalTorusFunctionData.finitePart F A.zeta12 A.primitive_zeta12 := by
      apply Subgroup.mem_map.mpr
      refine ⟨r, ?_, hrg⟩
      exact Subgroup.mem_iInf.mpr hr
    have hc := KPLiteralScalarHCSliceCharts.archMatrixInsertion_commutes_finite
      F A.zeta12 A.primitive_zeta12 m (⟨p.2.val, hfin⟩ : KPGlobalTorusFunctionData.finitePart F A.zeta12 A.primitive_zeta12)
    exact (e.apply_symm_apply g).symm.trans ((he p.1 p.2).trans (by
      rw [← harch, hc.eq, ← hrg]
      rfl))

theorem rawStage (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (r : RestrictedCover F A.zeta12 A.primitive_zeta12) :
    ∃ U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)), T ⊆ U ∧
      ∀ q, q ∉ U → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
        (Sum.inr q) (r (Sum.inr q)) ∈ pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q) := by
  let B := (Filter.eventually_cofinite.mp r.property).toFinset.toRight
  refine ⟨T ∪ B, Finset.subset_union_left, ?_⟩
  intro q hq
  have hb : q ∉ B := fun h => hq (Finset.mem_union_right T h)
  have hc : r (Sum.inr q) ∈ compact F A.zeta12 A.primitive_zeta12 (Sum.inr q) := by
    by_contra h
    apply hb
    simp only [B, Finset.mem_toRight, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact h
  exact Subgroup.mem_map.mpr ⟨_, hc, rfl⟩

theorem standard_compact_mem_canonical
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (he : q ∉ C.exceptional)
    (hb : ¬ Bad F q) (g : KPPGLLocalCover.CubicPGL2 F A.zeta12 A.primitive_zeta12 (Sum.inr q))
    (hg : g ∈ pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q)) :
    g ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup := by
  obtain ⟨ht, hc⟩ := C.actual_compact q he
  change g ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup _)
  rw [hc]
  change g ∈ (finiteCompact F A.zeta12 A.primitive_zeta12 q).map (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q)) at hg
  simp only [finiteCompact, dite_eq_right hb] at hg
  rw [KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.range_comp]
  exact hg

variable (K : Subgroup (KPLiteralRaw.G F A.zeta12 A.primitive_zeta12))
  (hK : IwasawaCompact F A.zeta12 A.primitive_zeta12 K)
variable (f : Flat F A.zeta12 A.primitive_zeta12 K)
theorem remove_tail_at_stage
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hT : ∀ (r : LiteralSource.Raw A)
      (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
      (hin : ∀ q ∈ T, KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) = 1)
      (hout : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) ∈
        pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q)) (g : KPLiteralRaw.G F A.zeta12 A.primitive_zeta12),
      productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
        (g * scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r)) = productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f g)
    (r : LiteralSource.Raw A) (hi : ∀ w : InfinitePlace F, r (Sum.inl w) = 1)
    (hout : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (r (Sum.inr q)) ∈
      pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q)) (m : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
      (scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r) * archMatrixInsertion F A.zeta12 A.primitive_zeta12 m) =
    productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
      ((finiteProductInsertion F A.zeta12 A.primitive_zeta12 T (stageLocalQuotients F A.zeta12 A.primitive_zeta12 T (fun q => r (Sum.inr q.val)))).val *
        archMatrixInsertion F A.zeta12 A.primitive_zeta12 m) := by
  let a := stageLocalQuotients F A.zeta12 A.primitive_zeta12 T (fun q => r (Sum.inr q.val))
  let o := rawOutside F A.zeta12 A.primitive_zeta12 T r
  have ho := rawOutside_mem F A.zeta12 A.primitive_zeta12 T r hi
  have hoa : ∀ w : InfinitePlace F, o (Sum.inl w) = 1 := fun w => Subgroup.mem_iInf.mp ho.1 w
  have hot : ∀ q ∈ T, KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (o (Sum.inr q)) = 1 := by
    intro q hq
    have he : o (Sum.inr q) = 1 := Subgroup.mem_iInf.mp ho.2 ⟨q, hq⟩
    rw [he, map_one]
  have hoc : ∀ q, q ∉ T → KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q) (o (Sum.inr q)) ∈
      pglCompact F A.zeta12 A.primitive_zeta12 (Sum.inr q) := by
    intro q hq
    change KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inr q)
      (r (Sum.inr q) * (stageRawInsertion F A.zeta12 A.primitive_zeta12 T _ (Sum.inr q))⁻¹) ∈ _
    rw [stageRawInsertion_outside F A.zeta12 A.primitive_zeta12 T _ q hq, inv_one, mul_one]
    exact hout q hq
  let d : KPGlobalTorusFunctionData.finitePart F A.zeta12 A.primitive_zeta12 :=
    ⟨scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 o), o, ho.1, rfl⟩
  have hd : d ∈ outsideStage F A.zeta12 A.primitive_zeta12 T := ⟨o, ho, rfl⟩
  have hcomm := (outsideStage_commute_product F A.zeta12 A.primitive_zeta12 T ⟨d, hd⟩ a).eq
  have hr : scalarQuotient F A.zeta12 A.primitive_zeta12 (amalgamation F A.zeta12 A.primitive_zeta12 r) =
      (finiteProductInsertion F A.zeta12 A.primitive_zeta12 T a).val * d.val := by
    have hraw : r = o * stageRawInsertion F A.zeta12 A.primitive_zeta12 T (fun q => r (Sum.inr q.val)) := by
      dsimp [o, rawOutside]; group
    conv_lhs => rw [hraw]
    rw [map_mul, map_mul, stageRawInsertion_quotient]
    exact congrArg Subtype.val hcomm
  rw [hr, mul_assoc, ← (KPLiteralScalarHCSliceCharts.archMatrixInsertion_commutes_finite F A.zeta12 A.primitive_zeta12 m d).eq,
    ← mul_assoc]
  exact hT o hoa hot hoc _

local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (j : InfinitePlace F ⊕ T) :
    AddCommGroup (mixedSource F A.zeta12 A.primitive_zeta12 (nativeInducingData A P C) T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance
local instance (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (j : InfinitePlace F ⊕ T) :
    Module ℂ (mixedSource F A.zeta12 A.primitive_zeta12 (nativeInducingData A P C) T j) := by
  cases j <;> dsimp [mixedSource] <;> infer_instance

theorem extractTensor (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    ∃ x : PiTensorProduct ℂ (mixedSource (ι := InfinitePlace F) F A.zeta12 A.primitive_zeta12 (nativeInducingData A P C) T),
      ∀ m a, allSlotEvaluation F A.zeta12 A.primitive_zeta12 (nativeInducingData A P C) T x m a =
      productHCScalar F A.zeta12 A.primitive_zeta12 K hK P f
        ((finiteProductInsertion F A.zeta12 A.primitive_zeta12 T a).val * archMatrixInsertion F A.zeta12 A.primitive_zeta12 m) := by
  obtain ⟨x,hx⟩ := CurrentFiniteFamily.productHCFamily_all_slot_tensor A P C K hK f T 1
  refine ⟨x, ?_⟩
  intro m a
  simpa only [OneMemClass.coe_one,one_mul] using hx m a
end DedekindZetaZeroFree.FourierContinuation.CurrentGlobalSource

end
