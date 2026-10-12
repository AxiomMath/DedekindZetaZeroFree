module

public import DedekindZetaZeroFree.Adeles.Quotients.RationalComponents.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 instance instBorelSpaceHyperbolicVolumeGInfinity : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩

end DedekindZetaZeroFree.KPActualComponentHaarSources

end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def placeEquiv : NumberField.InfinitePlace F ≃ Fin (KPCuspLogShape.dimension F) where
  toFun w := Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}
    ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  invFun := KPCusp.complexPlace F
  left_inv w := congrArg Subtype.val
    ((Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}).symm_apply_apply
      ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩)
  right_inv i := by
    change Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}
      ⟨KPCusp.complexPlace F i, _⟩ = i
    unfold KPCusp.complexPlace
    convert (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex}).apply_symm_apply i

 def archEquiv : KPSmoothActualFlowData.GInfinity F ≃ₜ*
    KPCompactStabilizerHaarSources.G (KPCuspLogShape.dimension F) where
  toMulEquiv :=
    { toFun g := fun i => g (KPCusp.complexPlace F i)
      invFun g := fun w => g (placeEquiv F ζ hζ w)
      left_inv g := by funext w; exact congrArg g ((placeEquiv F ζ hζ).left_inv w)
      right_inv g := by funext i; exact congrArg g ((placeEquiv F ζ hζ).right_inv i)
      map_mul' _ _ := rfl }
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun w => continuous_apply _

 lemma basepoint_eq (g : KPSmoothActualFlowData.GInfinity F) :
    archBasepoint F g = archEquiv F ζ hζ g •
      KPCompactStabilizerHaarSources.o (KPCuspLogShape.dimension F) := by
  funext i
  show KPArch.action (g (KPCusp.complexPlace F i)).out (0, 0) =
    (g (KPCusp.complexPlace F i)) • ((0, 0) : KPArch.H3)
  conv_rhs => rw [← Quotient.out_eq (g (KPCusp.complexPlace F i))]
  change KPArch.action (Quotient.out (g (KPCusp.complexPlace F i))) (0, 0) =
    Matrix.ProjGenLinGroup.mk (Quotient.out (g (KPCusp.complexPlace F i))) •
      ((0, 0) : KPArch.H3)
  rw [Matrix.ProjGenLinGroup.mk_smul KPArch.scalar_action]
  rfl

include ζ hζ in
 lemma basepoint_continuous : Continuous (archBasepoint F) := by
  have he : archBasepoint F = fun g => archEquiv F ζ hζ g •
      KPCompactStabilizerHaarSources.o (KPCuspLogShape.dimension F) := funext (basepoint_eq F ζ hζ)
  rw [he]
  exact (archEquiv F ζ hζ).continuous.smul continuous_const

private lemma arch_pushforward (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) :
    ∃ c : ℝ≥0, 0 < c ∧ Measure.map (archBasepoint F) R.archHaar =
      (c : ℝ≥0∞) • KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := by
  letI := R.arch_isHaar
  let e := archEquiv F ζ hζ
  letI : (Measure.map e R.archHaar).IsHaarMeasure := e.isHaarMeasure_map R.archHaar
  obtain ⟨c, hc, hmap⟩ := KPCompactStabilizerHaarSources.arch_haar_pushforward_hyperbolic
    (KPCuspLogShape.dimension F) (Measure.map e R.archHaar)
  refine ⟨c, hc, ?_⟩
  have hm : Measurable (fun g : KPCompactStabilizerHaarSources.G (KPCuspLogShape.dimension F) =>
      g • KPCompactStabilizerHaarSources.o (KPCuspLogShape.dimension F)) :=
    (continuous_id.smul continuous_const).measurable
  rw [Measure.map_map hm (show Measurable (fun g => e g) from e.continuous.measurable)] at hmap
  convert hmap using 1
  exact congrArg (fun f => Measure.map f R.archHaar) (funext (basepoint_eq F ζ hζ))

 def rationalArch : KPCuspArithmetic.PGL2 F →* KPSmoothActualFlowData.GInfinity F :=
  (KPSmoothLocalQuotientCharts.archProjection F ζ hζ).comp
    ((KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp (rationalEquiv F).toMonoidHom)

private lemma rationalArch_mk (m : Matrix.GeneralLinearGroup (Fin 2) F)
    (w : NumberField.InfinitePlace F) :
    rationalArch F ζ hζ (Matrix.ProjGenLinGroup.mk m) w =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding m) := by
  have he : rationalEquiv F (Matrix.ProjGenLinGroup.mk m) =
      KPRationalAdelicSplitting.rationalPGLQuotient F m :=
    QuotientGroup.quotientMulEquivOfEq_mk _ m
  unfold rationalArch
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, he,
    KPRationalAdelicSplitting.rationalPGLHom_mk]
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (KPAdelicCoverRestrictedProduct.projection F ζ hζ
      (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ m))) = _
  rw [KPAdelicCoverRestrictedProduct.projection_rationalSection]
  have hmap : (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
      ((KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)).comp
        (algebraMap F (KPAdelicCoverRestrictedProduct.Adeles F))) = w.embedding := by
    ext x
    change NumberField.InfinitePlace.Completion.extensionEmbedding w
      ((WithAbs.equiv w.1).symm x : w.Completion) = _
    simp
  change Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ m)) = _
  simp only [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
  rw [RingHom.comp_assoc, hmap]

lemma rationalArch_injective : Function.Injective (rationalArch F ζ hζ) := by
  let lift : KPCuspArithmetic.PGL2 F →* KPSmoothLocalQuotientCharts.ActualCover F ζ hζ :=
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp (rationalEquiv F).toMonoidHom
  have hi : Function.Injective lift :=
    (KPRationalAdelicSplitting.rationalPGL_splitting F ζ hζ).1.comp (rationalEquiv F).injective
  intro x y hxy
  apply hi
  have hx : lift x ∈ ActualQuotient.rationalSubgroup F ζ hζ := ⟨rationalEquiv F x, rfl⟩
  have hy : lift y ∈ ActualQuotient.rationalSubgroup F ζ hζ := ⟨rationalEquiv F y, rfl⟩
  exact congrArg Subtype.val (ActualQuotient.actual_rational_arch_injective F ζ hζ
    (a₁ := ⟨lift x, hx⟩) (a₂ := ⟨lift y, hy⟩) hxy)

 lemma rationalArch_equivariant (γ : KPCuspArithmetic.PGL2 F)
    (g : KPSmoothActualFlowData.GInfinity F) :
    archBasepoint F (rationalArch F ζ hζ γ * g) = γ • archBasepoint F g := by
  obtain ⟨m, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  rw [basepoint_eq F ζ hζ, map_mul, mul_smul, ← basepoint_eq F ζ hζ]
  change _ = KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk m) (archBasepoint F g)
  rw [KPCuspSiegel.action_mk]
  funext i
  change rationalArch F ζ hζ (Matrix.ProjGenLinGroup.mk m) (KPCusp.complexPlace F i) •
    (archBasepoint F g i) = _
  rw [rationalArch_mk, Matrix.ProjGenLinGroup.mk_smul KPArch.scalar_action]
  rfl

 def subgroupEquiv (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount) : Gi F ζ hζ hF U A i ≃* Ga F ζ hζ hF U A i :=
  (Gi F ζ hζ hF U A i).equivMapOfInjective (rationalArch F ζ hζ)
    (rationalArch_injective F ζ hζ)

theorem arch_group_domain_quotient_volume
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (i : Fin A.componentCount)
    (D : Set (KPSmoothActualFlowData.GInfinity F))
    (hDm : MeasurableSet D)
    (hD : IsFundamentalDomain (Ga F ζ hζ hF U A i) D R.archHaar) :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (archBasepoint F) R.archHaar =
        (c : ℝ≥0∞) • KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) ∧
      Measure.map (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) ∘ archBasepoint F)
        (R.archHaar.restrict D) =
        (c : ℝ≥0∞) • KPFiniteCuspAtlas.quotientVolume F (Gi F ζ hζ hF U A i)
          (A.cuspAtlas i).fundamentalDomain := by
  obtain ⟨c, hc, hpush⟩ := arch_pushforward F ζ hζ R
  refine ⟨c, hc, hpush, ?_⟩
  let E := (A.cuspAtlas i).fundamentalDomain
  let D₀ := archBasepoint F ⁻¹' E
  have hb := (basepoint_continuous F ζ hζ).measurable
  have hE : MeasurableSet E := (A.cuspAtlas i).measurable_fundamentalDomain
  have hD₀m : MeasurableSet D₀ := hb hE
  have hqmp : Measure.QuasiMeasurePreserving (archBasepoint F) R.archHaar
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) :=
    ⟨hb, by rw [hpush]; exact Measure.smul_absolutelyContinuous⟩
  have hD₀ : IsFundamentalDomain (Ga F ζ hζ hF U A i) D₀ R.archHaar := by
    exact (A.cuspAtlas i).isFundamentalDomain.preimage_of_equiv hqmp
      (subgroupEquiv F ζ hζ hF U A i).bijective
      (fun γ g => rationalArch_equivariant F ζ hζ γ g)
  have hp : Measurable (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i)) :=
    measurable_quotient_mk''
  have hcompare : Measure.map
      (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) ∘ archBasepoint F)
      (R.archHaar.restrict D) = Measure.map
      (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) ∘ archBasepoint F)
      (R.archHaar.restrict D₀) := by
    letI := R.arch_isHaar
    letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
    letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
    letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
    letI : Countable (Ga F ζ hζ hF U A i) := (subgroupEquiv F ζ hζ hF U A i).surjective.countable
    apply Measure.ext
    intro T hT
    rw [Measure.map_apply (hp.comp hb) hT, Measure.map_apply (hp.comp hb) hT,
      Measure.restrict_apply ((hp.comp hb) hT), Measure.restrict_apply ((hp.comp hb) hT)]
    apply hD.measure_set_eq hD₀ ((hp.comp hb) hT)
    intro γ
    ext g
    have he : (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) ∘ archBasepoint F)
        (γ • g) = (KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) ∘ archBasepoint F) g := by
      let δ := (subgroupEquiv F ζ hζ hF U A i).symm γ
      change KPCuspSiegel.projection F (Gi F ζ hζ hF U A i) (archBasepoint F (γ * g)) = _
      have hγ : (γ : KPSmoothActualFlowData.GInfinity F) = rationalArch F ζ hζ δ :=
        congrArg Subtype.val ((subgroupEquiv F ζ hζ hF U A i).apply_symm_apply γ).symm
      rw [hγ, rationalArch_equivariant]
      exact Quotient.sound ⟨δ, rfl⟩
    simpa only [Set.mem_preimage, he]
  rw [hcompare]
  rw [← Measure.map_map hp hb]
  change Measure.map _ (Measure.map (archBasepoint F) (R.archHaar.restrict (archBasepoint F ⁻¹' E))) = _
  rw [← Measure.restrict_map hb hE, hpush,
    Measure.restrict_smul, Measure.map_smul _ hp.aemeasurable]
  rfl

end DedekindZetaZeroFree.KPActualComponentHaarSources

end
end
