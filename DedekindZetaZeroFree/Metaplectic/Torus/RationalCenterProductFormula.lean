module

public import DedekindZetaZeroFree.Metaplectic.Torus.RestrictedProductCubicCenterCharacter

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem localValue_diagUnit (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F)
    (y : (KPHilbert.Completion F v)ˣ) :
    localValue F ζ hζ v
      (⟨KubotaRankTwo.d (KPHilbert.Completion F v) y 1, ε⟩ :
        KPLocalCover.CubicGL2Raw F ζ hζ v) =
      KPGlobalTorusFunctionData.iota F ζ hζ ε *
        positiveComplex (sixthPower (Units.mk0 (localAbs F v y)
          (ne_of_gt (localAbs_pos F v y)))) := by
  have h1 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) y 1 :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) := by
    rw [KubotaRankTwo.coe_d]; exact Units.isUnit y
  have h2 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) y 1 :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) := by
    rw [KubotaRankTwo.coe_d]; exact isUnit_one
  rw [localValue, dif_pos ⟨h1, h2⟩]
  have hunit : h1.unit * h2.unit⁻¹ = y := by
    ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, IsUnit.unit_spec, IsUnit.unit_spec,
      KubotaRankTwo.coe_d]
    simp
  congr 1
  congr 1
  congr 1
  apply Units.ext
  show localAbs F v (h1.unit * h2.unit⁻¹) = localAbs F v y
  rw [hunit]

private theorem localAbs_one (v : KPHilbert.Place F) :
    localAbs F v (1 : (KPHilbert.Completion F v)ˣ) = 1 := by
  cases v with
  | inl w => simp [localAbs]
  | inr q => simp [localAbs]

private theorem localValue_central (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F) :
    localValue F ζ hζ v (KPLocalCover.centralInjection F ζ hζ v ε) =
      KPGlobalTorusFunctionData.iota F ζ hζ ε := by
  have h := localValue_diagUnit F ζ hζ v ε 1
  have hd : KubotaRankTwo.d (KPHilbert.Completion F v) (1 : (KPHilbert.Completion F v)ˣ) 1 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  change localValue F ζ hζ v ⟨1, ε⟩ = _
  simpa [hd, localAbs_one F v] using h

private theorem rawProduct_productOne (x : rawCenter F ζ hζ)
    (hx : x.val ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ) :
    rawProduct F ζ hζ x = 1 := by
  obtain ⟨ε, hε, hx⟩ := hx
  unfold rawProduct
  have hf : (fun v => localValue F ζ hζ v (x.val v)) =
      fun v => KPGlobalTorusFunctionData.iota F ζ hζ (ε v) := by
    funext v
    rw [← hx]
    exact localValue_central F ζ hζ v (ε v)
  rw [hf, ← MonoidHom.map_finprod _ (KPAdelicCoverRestrictedProduct.centralTuples_finiteSupport F ε)]
  change KPGlobalTorusFunctionData.iota F ζ hζ (KPAdelicCoverRestrictedProduct.centralProduct F ε) = 1
  rw [MonoidHom.mem_ker.mp hε, map_one]

private theorem localValue_scalar (v : KPHilbert.Place F)
    (u : (KPHilbert.Completion F v)ˣ) :
    localValue F ζ hζ v (KPScalarSplitCentral.scalarHom F ζ hζ v u) = 1 := by
  have hu : (KPScalarSplitCentral.scalarHom F ζ hζ v u).g 0 0 = u := by
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap, Matrix.scalar]
  have hu' : (KPScalarSplitCentral.scalarHom F ζ hζ v u).g 1 1 = u := by
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap, Matrix.scalar]
  have h1 : IsUnit ((KPScalarSplitCentral.scalarHom F ζ hζ v u).g 0 0) := hu ▸ u.isUnit
  have h2 : IsUnit ((KPScalarSplitCentral.scalarHom F ζ hζ v u).g 1 1) := hu' ▸ u.isUnit
  have he1 : h1.unit = u := Units.ext (h1.unit_spec.trans hu)
  have he2 : h2.unit = u := Units.ext (h2.unit_spec.trans hu')
  rw [localValue, dif_pos ⟨h1, h2⟩]
  simp [he1, he2, localAbs_one F v, KPScalarSplitCentral.scalarHom,
    KPScalarSplitCentral.scalarLift, KPLocalCover.sectionMap]

private theorem rawProduct_splitScalar (u : Ideles F) (x : rawCenter F ζ hζ)
    (hx : x.val = KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ u) :
    rawProduct F ζ hζ x = 1 := by
  unfold rawProduct
  have hf : (fun v => localValue F ζ hζ v (x.val v)) = fun _ => 1 := by
    funext v
    rw [hx]
    exact localValue_scalar F ζ hζ v _
  rw [hf]
  exact finprod_one

private theorem rawProduct_independent (x y : rawCenter F ζ hζ)
    (hxy : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ y.val)) :
    rawProduct F ζ hζ x = rawProduct F ζ hζ y := by
  let q := KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
  let t := KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ
  have hd : q (x.val * y.val⁻¹) ∈ KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ := by
    apply (QuotientGroup.eq_one_iff _).mp
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (q (x.val * y.val⁻¹)) = 1
    simpa only [q, map_mul, map_inv, hxy, mul_inv_cancel]
  obtain ⟨u, hu⟩ := hd
  have ht : (t u) ∈ rawCenter F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (q (t u)) ∈
      (Z F ζ hζ).map (E F ζ hζ).subtype
    have he : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (q (t u)) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨u, rfl⟩
    rw [he]
    exact Subgroup.one_mem _
  let s : rawCenter F ζ hζ := ⟨t u, ht⟩
  have hm : ((x * y⁻¹) * s⁻¹).val ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((x.val * y.val⁻¹) * (t u)⁻¹) = 1
    rw [map_mul, map_inv]
    have hu' : q (t u) = q (x.val * y.val⁻¹) := hu
    rw [hu', mul_inv_cancel]
  have hmul := (raw_character_laws F ζ hζ).2.1
  have hunit : rawProduct F ζ hζ (x * y⁻¹) = 1 := by
    have he : x * y⁻¹ = ((x * y⁻¹) * s⁻¹) * s := by group
    rw [he, hmul, rawProduct_productOne F ζ hζ _ hm,
      rawProduct_splitScalar F ζ hζ u s rfl, mul_one]
  have he : x = (x * y⁻¹) * y := by group
  rw [he, hmul, hunit, one_mul]

private theorem localAbs_inl_coe (w : InfinitePlace F) (a : Fˣ) :
    ((localAbs F (Sum.inl w) (Units.map (algebraMap F w.Completion) a) : ℝ≥0) : ℝ) =
      (w (a:F)) ^ 2 := by
  have h : ((localAbs F (Sum.inl w) (Units.map (algebraMap F w.Completion) a) : ℝ≥0) : ℝ)
      = ‖(algebraMap F w.Completion (a:F))‖ ^ 2 := rfl
  rw [h]
  have h2 : ‖(algebraMap F w.Completion (a:F))‖ = w (a:F) := by
    rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.norm_coe]
    rfl
  rw [h2]

private theorem localAbs_inr_coe (q : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    ((localAbs F (Sum.inr q) (Units.map (algebraMap F (q.adicCompletion F)) a) : ℝ≥0) : ℝ) =
      (NumberField.FinitePlace.equivHeightOneSpectrum.symm q) (a:F) := by
  have h : ((localAbs F (Sum.inr q) (Units.map (algebraMap F (q.adicCompletion F)) a) : ℝ≥0) : ℝ)
      = ‖(algebraMap F (q.adicCompletion F) (a:F))‖ := rfl
  rw [h]
  have h2 : ‖(algebraMap F (q.adicCompletion F) (a:F))‖ =
      (NumberField.FinitePlace.equivHeightOneSpectrum.symm q) (a:F) := by
    rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply]
    rfl
  rw [h2]

theorem rational_raw_product (a : Fˣ) (x : rawCenter F ζ hζ)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) =
        (KPGlobalTorusFunctionData.s F ζ hζ a).val) :
    rawProduct F ζ hζ x = 1 := by
  let x₀ : rawCenter F ζ hζ :=
    ⟨KPAdelicCoverRestrictedProduct.rationalTuple F ζ hζ (KubotaRankTwo.d F a 1), by
      show KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
            (KPAdelicCoverRestrictedProduct.rationalTuple F ζ hζ (KubotaRankTwo.d F a 1)))
          ∈ (Z F ζ hζ).map (E F ζ hζ).subtype
      rw [show KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
            (KPAdelicCoverRestrictedProduct.rationalTuple F ζ hζ (KubotaRankTwo.d F a 1)))
          = (KPGlobalTorusFunctionData.s F ζ hζ a).val from rfl]
      exact hx ▸ x.property⟩
  have hx0 : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x₀.val) =
      (KPGlobalTorusFunctionData.s F ζ hζ a).val := rfl
  rw [rawProduct_independent F ζ hζ x x₀ (hx.trans hx0.symm)]
  let A : KPHilbert.Place F → ℝ≥0 :=
    fun v => localAbs F v (Units.map (algebraMap F (KPHilbert.Completion F v)) a)
  have hApos : ∀ v, 0 < A v := fun v =>
    localAbs_pos F v (Units.map (algebraMap F (KPHilbert.Completion F v)) a)
  let L : KPHilbert.Place F → (ℝ≥0)ˣ := fun v => Units.mk0 (A v) (ne_of_gt (hApos v))
  have hx0v : ∀ v, x₀.val v =
      (⟨KubotaRankTwo.d (KPHilbert.Completion F v)
        (Units.map (algebraMap F (KPHilbert.Completion F v)) a) 1, 1⟩ :
        KPLocalCover.CubicGL2Raw F ζ hζ v) := by
    intro v
    show (KPAdelicCoverRestrictedProduct.rationalTuple F ζ hζ (KubotaRankTwo.d F a 1)) v = _
    rw [KPAdelicCoverRestrictedProduct.rationalTuple_eval]
    unfold KPAdelicCoverRestrictedProduct.rationalCoordinates KPLocalCover.sectionMap
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.coe_d, Matrix.GeneralLinearGroup.map_apply]
  have hval : ∀ v, localValue F ζ hζ v (x₀.val v) =
      (positiveComplex.comp sixthPower) (L v) := by
    intro v
    rw [hx0v v, localValue_diagUnit F ζ hζ v 1]
    simp [L, A]

  have hqfin : (Function.mulSupport
      (fun q : HeightOneSpectrum (𝓞 F) => A (Sum.inr q))).Finite := by
    have hpre : ((NumberField.FinitePlace.equivHeightOneSpectrum (K := F)).symm ⁻¹'
        Function.mulSupport (fun w : NumberField.FinitePlace F => w (a:F))).Finite :=
      Set.Finite.preimage ((NumberField.FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn)
        (NumberField.FinitePlace.hasFiniteMulSupport (Units.ne_zero a))
    refine hpre.subset ?_
    rintro q hq
    simp only [Set.mem_preimage, Function.mem_mulSupport] at hq ⊢
    intro h1
    apply hq
    have hAq : A (Sum.inr q) =
        localAbs F (Sum.inr q) (Units.map (algebraMap F (q.adicCompletion F)) a) := rfl
    rw [hAq]
    apply NNReal.coe_injective
    rw [localAbs_inr_coe F q a]
    simpa using h1
  have hAfin : Function.HasFiniteMulSupport A := by
    have hset : Function.mulSupport A =
        (Set.range (Sum.inl : InfinitePlace F → KPHilbert.Place F) ∩ Function.mulSupport A) ∪
        (Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F) ∩
          Function.mulSupport A) := by
      ext v
      constructor
      · intro hv
        cases v with
        | inl w => exact Or.inl ⟨⟨w, rfl⟩, hv⟩
        | inr q => exact Or.inr ⟨⟨q, rfl⟩, hv⟩
      · rintro (⟨⟨w, rfl⟩, hv⟩ | ⟨⟨q, rfl⟩, hv⟩) <;> exact hv
    rw [Function.HasFiniteMulSupport, hset]
    apply Set.Finite.union
    · exact (Set.finite_range _).subset Set.inter_subset_left
    · refine (hqfin.image Sum.inr).subset ?_
      rintro v ⟨⟨q, rfl⟩, hv⟩
      exact ⟨q, hv, rfl⟩
  have hLfin : Function.HasFiniteMulSupport L := by
    rw [Function.HasFiniteMulSupport]
    rw [show Function.mulSupport L = Function.mulSupport A from by
      ext v
      simp only [Function.mem_mulSupport]
      constructor
      · intro h hA
        apply h
        apply Units.ext
        show ((Units.mk0 (A v) (ne_of_gt (hApos v)) : (ℝ≥0)ˣ) : ℝ≥0) = (1 : ℝ≥0)
        rw [Units.val_mk0, hA]
      · intro h hL
        apply h
        have := congrArg (fun u : (ℝ≥0)ˣ => (u : ℝ≥0)) hL
        simpa [L, Units.val_mk0] using this]
    exact hAfin

  have hL1 : ∏ᶠ v : KPHilbert.Place F, L v = 1 := by
    have hcoe : (Units.coeHom ℝ≥0) (∏ᶠ v, L v) = ∏ᶠ v, A v := by
      rw [MonoidHom.map_finprod (Units.coeHom ℝ≥0) hLfin]
      apply finprod_congr
      intro v
      exact Units.val_mk0 (ne_of_gt (hApos v))
    apply Units.ext
    change (Units.coeHom ℝ≥0) (∏ᶠ v, L v) = (Units.coeHom ℝ≥0) 1
    rw [hcoe, map_one]
    apply NNReal.coe_injective
    have hcoe2 : ((∏ᶠ v, A v : ℝ≥0) : ℝ) =
        ∏ᶠ v : KPHilbert.Place F, ((A v : ℝ≥0) : ℝ) :=
      MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom hAfin
    rw [hcoe2]
    have hdisj : Disjoint (Set.range (Sum.inl : InfinitePlace F → KPHilbert.Place F))
        (Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)) := by
      rw [Set.disjoint_left]
      rintro _ ⟨w, rfl⟩ ⟨q, hq⟩
      exact Sum.inl_ne_inr hq.symm
    have hf1 : (Set.range (Sum.inl : InfinitePlace F → KPHilbert.Place F) ∩
        Function.mulSupport (fun v : KPHilbert.Place F => ((A v : ℝ≥0) : ℝ))).Finite :=
      (Set.finite_range _).subset Set.inter_subset_left
    have hf2 : (Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F) ∩
        Function.mulSupport (fun v : KPHilbert.Place F => ((A v : ℝ≥0) : ℝ))).Finite := by
      refine (hqfin.image Sum.inr).subset ?_
      rintro v ⟨⟨q, rfl⟩, hv2⟩
      refine ⟨q, ?_, rfl⟩
      simp only [Function.mem_mulSupport] at hv2 ⊢
      intro h
      exact hv2 (by simp [h])
    have hsplit : ∏ᶠ v : KPHilbert.Place F, ((A v : ℝ≥0) : ℝ) =
        (∏ᶠ w : InfinitePlace F, ((A (Sum.inl w) : ℝ≥0) : ℝ)) *
        (∏ᶠ q : HeightOneSpectrum (𝓞 F), ((A (Sum.inr q) : ℝ≥0) : ℝ)) := by
      rw [← finprod_mem_univ (fun v : KPHilbert.Place F => ((A v : ℝ≥0) : ℝ))]
      rw [← Set.range_inl_union_range_inr (α := InfinitePlace F) (β := HeightOneSpectrum (𝓞 F))]
      rw [finprod_mem_union' hdisj hf1 hf2, finprod_mem_range Sum.inl_injective,
        finprod_mem_range Sum.inr_injective]
    rw [hsplit]
    have hInf : (∏ᶠ w : InfinitePlace F, ((A (Sum.inl w) : ℝ≥0) : ℝ)) =
        ∏ w : InfinitePlace F, (w (a:F)) ^ w.mult := by
      rw [finprod_eq_prod_of_fintype]
      apply Finset.prod_congr rfl
      intro w _
      have hAw : A (Sum.inl w) =
          localAbs F (Sum.inl w) (Units.map (algebraMap F w.Completion) a) := rfl
      rw [hAw, localAbs_inl_coe F w a, (KPHilbert.infinite_isComplex F ζ hζ w).mult_eq_two]
    have hFin : (∏ᶠ q : HeightOneSpectrum (𝓞 F), ((A (Sum.inr q) : ℝ≥0) : ℝ)) =
        ∏ᶠ w : NumberField.FinitePlace F, w (a:F) := by
      rw [← finprod_comp_equiv (NumberField.FinitePlace.equivHeightOneSpectrum (K:=F)).symm
        (f := fun w : NumberField.FinitePlace F => w (a:F))]
      apply finprod_congr
      intro q
      have hAq : A (Sum.inr q) =
          localAbs F (Sum.inr q) (Units.map (algebraMap F (q.adicCompletion F)) a) := rfl
      rw [hAq, localAbs_inr_coe F q a]
    rw [hInf, hFin]
    simpa using NumberField.prod_abs_eq_one (Units.ne_zero a)
  unfold rawProduct
  rw [show (fun v => localValue F ζ hζ v (x₀.val v)) =
      fun v => (positiveComplex.comp sixthPower) (L v) from funext hval]
  rw [← MonoidHom.map_finprod (positiveComplex.comp sixthPower) hLfin, hL1]
  simp

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
