module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.CompactRowDistortion
public import DedekindZetaZeroFree.Eisenstein.Induction.Height.IwasawaNormBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open NumberField Matrix IsDedekindDomain KPChamberHeight

private theorem row_map (A : KPChamberHeight.RatGL F) (B : KPChamberHeight.AdelGL F)
    {K : Type*} [Field K] (f : KPChamberHeight.Adele F →+* K) (j : Fin 2) :
    KPChamberHeight.rowAction (fun i => (f.comp (algebraMap F (KPChamberHeight.Adele F))) (![0,1] i))
      (GeneralLinearGroup.map f (GeneralLinearGroup.map (algebraMap F (KPChamberHeight.Adele F)) A * B)) j =
    KPChamberHeight.rowAction (fun i => (f.comp (algebraMap F (KPChamberHeight.Adele F))) (A 1 i))
      (GeneralLinearGroup.map f B) j := by
  simp [KPChamberHeight.rowAction, Fin.sum_univ_two, Matrix.mul_apply, map_add, map_mul]

private theorem finite_rational_mul (A : RatGL F) (B : AdelGL F)
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    finiteFactor F ![0,1] (GeneralLinearGroup.map (algebraMap F (Adele F)) A * B) v =
      finiteFactor F (fun i => A 1 i) B v /
        Real.sqrt ‖algebraMap F (v.adicCompletion F) (GeneralLinearGroup.det A : F)‖ := by
  unfold finiteFactor
  dsimp only
  erw [row_map F A B (finiteEval F v) 0, row_map F A B (finiteEval F v) 1]
  rw [map_mul, map_mul, Units.val_mul, norm_mul,
    Real.sqrt_mul (norm_nonneg _)]
  have hd : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (finiteEval F v)
        (GeneralLinearGroup.map (algebraMap F (Adele F)) A)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (GeneralLinearGroup.det A : F) := by
    change ((finiteEval F v).mapMatrix
      ((algebraMap F (Adele F)).mapMatrix A.val)).det = _
    rw [← RingHom.map_det, ← RingHom.map_det]
    rfl
  have hc : (finiteEval F v).comp (algebraMap F (Adele F)) =
      algebraMap F (v.adicCompletion F) := by ext a; rfl
  rw [hd, hc]
  ring
private theorem infinite_rational_mul (A : RatGL F) (B : AdelGL F)
    (v : InfinitePlace F) :
    infiniteFactor F ![0,1] (GeneralLinearGroup.map (algebraMap F (Adele F)) A * B) v =
      infiniteFactor F (fun i => A 1 i) B v /
        (Real.sqrt (v (GeneralLinearGroup.det A : F))) ^ v.mult := by
  unfold infiniteFactor
  dsimp only
  erw [row_map F A B (infiniteEval F v) 0, row_map F A B (infiniteEval F v) 1]
  rw [map_mul, map_mul, Units.val_mul, norm_mul,
    Real.sqrt_mul (norm_nonneg _)]
  have hd : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (infiniteEval F v)
        (GeneralLinearGroup.map (algebraMap F (Adele F)) A)) : v.Completion) =
      algebraMap F v.Completion (GeneralLinearGroup.det A : F) := by
    change ((infiniteEval F v).mapMatrix
      ((algebraMap F (Adele F)).mapMatrix A.val)).det = _
    rw [← RingHom.map_det, ← RingHom.map_det]
    rfl
  have hc : (infiniteEval F v).comp (algebraMap F (Adele F)) =
      algebraMap F v.Completion := by ext a; rfl
  have hn : ‖algebraMap F v.Completion (GeneralLinearGroup.det A : F)‖ =
      v (GeneralLinearGroup.det A : F) :=
    InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm _)
  rw [hd, hc, hn]
  change (_ / (Real.sqrt (v (GeneralLinearGroup.det A : F)) * _)) ^ v.mult = _
  rw [mul_comm (Real.sqrt (v (GeneralLinearGroup.det A : F))), div_mul_eq_div_div, div_pow]
  rfl

private theorem rational_det_sqrt_product (a : F) (ha : a ≠ 0) :
    (∏ v : InfinitePlace F, (Real.sqrt (v a)) ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (RingOfIntegers F),
        Real.sqrt ‖algebraMap F (v.adicCompletion F) a‖) = 1 := by
  have hf : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (RingOfIntegers F) =>
        ‖algebraMap F (v.adicCompletion F) a‖) :=
    Function.HasFiniteMulSupport.fun_comp_of_injective
      FinitePlace.equivHeightOneSpectrum.symm.injective
      (FinitePlace.hasFiniteMulSupport ha)
  have hfs : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (RingOfIntegers F) =>
        Real.sqrt ‖algebraMap F (v.adicCompletion F) a‖) :=
    hf.comp Real.sqrt_one
  have hp : (∏ v : InfinitePlace F, v a ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (RingOfIntegers F),
        ‖algebraMap F (v.adicCompletion F) a‖) = 1 := by
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F))]
    have he : ∀ v : FinitePlace F,
        ‖algebraMap F ((FinitePlace.equivHeightOneSpectrum v).adicCompletion F) a‖ = v a := by
      intro v
      change FinitePlace.equivHeightOneSpectrum.symm (FinitePlace.equivHeightOneSpectrum v) a = v a
      rw [Equiv.symm_apply_apply]
    simp_rw [he]
    exact NumberField.prod_abs_eq_one ha
  have hs : ((∏ v : InfinitePlace F, (Real.sqrt (v a)) ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (RingOfIntegers F),
        Real.sqrt ‖algebraMap F (v.adicCompletion F) a‖)) ^ 2 = 1 := by
    rw [mul_pow, ← Finset.prod_pow, finprod_pow hfs]
    have he (v : InfinitePlace F) : ((Real.sqrt (v a)) ^ v.mult) ^ 2 = v a ^ v.mult := by
      rw [← pow_mul, mul_comm v.mult 2, pow_mul, Real.sq_sqrt (apply_nonneg v a)]
    simp_rw [he, Real.sq_sqrt (norm_nonneg _)]
    exact hp
  have hn : 0 ≤ (∏ v : InfinitePlace F, (Real.sqrt (v a)) ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (RingOfIntegers F),
        Real.sqrt ‖algebraMap F (v.adicCompletion F) a‖) :=
    mul_nonneg (Finset.prod_nonneg (fun _ _ => pow_nonneg (Real.sqrt_nonneg _) _))
      (finprod_nonneg (fun _ => Real.sqrt_nonneg _))
  nlinarith

private theorem rowHeight_rational_mul (A : RatGL F) (B : AdelGL F) :
    rowHeight F ![0,1] (GeneralLinearGroup.map (algebraMap F (Adele F)) A * B) =
      rowHeight F (fun i => A 1 i) B := by
  have hr : (fun i => A 1 i) ≠ 0 := by
    intro h
    have hz : ∀ i, A 1 i = 0 := fun i => congrFun h i
    have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) A.mul_inv
    simpa [Matrix.mul_apply, hz] using hi
  have hf : Function.HasFiniteMulSupport (finiteFactor F (fun i => A 1 i) B) :=
    Filter.eventually_cofinite.mp (finiteFactor_eventually_one F _ hr B)
  have hd : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (RingOfIntegers F) =>
        Real.sqrt ‖algebraMap F (v.adicCompletion F) (GeneralLinearGroup.det A : F)‖) :=
    (Function.HasFiniteMulSupport.fun_comp_of_injective
      FinitePlace.equivHeightOneSpectrum.symm.injective
      (FinitePlace.hasFiniteMulSupport (GeneralLinearGroup.det A).ne_zero)).comp Real.sqrt_one
  unfold rowHeight
  simp_rw [finite_rational_mul, infinite_rational_mul]
  rw [Finset.prod_div_distrib, finprod_div_distrib hf hd, div_mul_div_comm,
    rational_det_sqrt_product F _ (GeneralLinearGroup.det A).ne_zero, div_one]

theorem actualBaseRowHeight_rational_mul
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) (g : KPLiteralRaw.G F ζ hζ) :
    KPChamberHeight.height F (actualBaseRowLine F)
        (coveredHeightProjection F ζ hζ (KPLiteralRaw.rationalLift F ζ hζ γ * g)) =
      KPChamberHeight.height F (KPChamberHeight.bottomRow F γ)
        (coveredHeightProjection F ζ hζ g) := by
  rw [map_mul, coveredHeightProjection_rationalLift]
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective γ
  obtain ⟨B, hB⟩ := ProjGenLinGroup.mk_surjective (coveredHeightProjection F ζ hζ g)
  rw [← hB, bottomRow_mk]
  change height F (actualBaseRowLine F)
    (ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap F (Adele F)) A) * ProjGenLinGroup.mk B) = _
  rw [← map_mul]
  simp only [actualBaseRowLine, height_mk]
  exact rowHeight_rational_mul F A B

private theorem ideleAbs_product (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (y : KPGlobalTorusFunctionData.Ideles F) :
    (((KPGlobalTorusFunctionData.ideleAbs F y : NNReal) : ℝ)) =
      (∏ w : InfinitePlace F, ‖KPChamberHeight.infiniteEval F w (y : KPAdeles F)‖ ^ 2) *
      ∏ᶠ q : HeightOneSpectrum (𝓞 F), ‖KPChamberHeight.finiteEval F q (y : KPAdeles F)‖ := by
  letI := primitive12_totallyComplex F ζ hζ
  have h := KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.idele_localAbs_finprod F y
  let c : NNRealˣ →* ℝ := { toFun := fun a => ((a : NNReal) : ℝ), map_one' := rfl, map_mul' := fun a b => rfl }
  have hc : Function.Injective c := by
    intro a b hab
    apply Units.ext
    exact NNReal.coe_injective hab
  have he := congrArg c h
  rw [c.map_finprod_of_injective hc] at he
  let f : KPHilbert.Place F → ℝ := fun v =>
    c (Units.mk0 (KPGlobalCenterRationalCharacterExtension.localAbs F v
      (KPGlobalCubicIdelePairing.ideleEval F v y))
      (ne_of_gt (KPGlobalCenterRationalCharacterExtension.localAbs_pos F v
        (KPGlobalCubicIdelePairing.ideleEval F v y))))
  have hf : Function.HasFiniteMulSupport f :=
    (KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.idele_localAbs_hasFiniteMulSupport F y).comp c.map_one
  have hA : (Set.range (Sum.inl : InfinitePlace F → KPHilbert.Place F) ∩
      Function.mulSupport f).Finite := hf.subset (Set.inter_subset_right)
  have hB : (Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F) ∩
      Function.mulSupport f).Finite := hf.subset (Set.inter_subset_right)
  have hsplit : (∏ᶠ v, f v) =
      (∏ w : InfinitePlace F, f (Sum.inl w)) * (∏ᶠ q, f (Sum.inr q)) := by
    rw [← finprod_mem_univ f]
    rw [show (Set.univ : Set (KPHilbert.Place F)) =
        Set.range (Sum.inl : InfinitePlace F → KPHilbert.Place F) ∪
        Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F) from by
      ext v; cases v <;> simp]
    rw [finprod_mem_union' (Set.disjoint_left.mpr (fun v hv hw => by
      obtain ⟨w, rfl⟩ := hv; obtain ⟨q, h⟩ := hw; exact Sum.inr_ne_inl h)) hA hB]
    congr 1
    · rw [finprod_mem_range Sum.inl_injective, finprod_eq_prod_of_fintype]
    · rw [finprod_mem_range Sum.inr_injective]
  change (∏ᶠ v, f v) = _ at he
  change c (KPGlobalTorusFunctionData.ideleAbs F y) = _
  rw [← he, hsplit]
  rfl

private theorem eval_upper_ratio {K : Type*} [NormedField K]
    (e : KPAdeles F →+* K) (B : KPChamberHeight.AdelGL F) (hB : B 1 0 = 0) :
    ‖e (KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio F B hB : KPAdeles F)‖ =
      ‖e (B 0 0)‖ / ‖e (B 1 1)‖ := by
  unfold KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio
  rw [Units.val_mul, map_mul, norm_mul]
  have hi : e (↑(KPGlobalTorusBorelNormTwistTransport.iwasawaUpperUnits F B hB).2.unit⁻¹ : KPAdeles F) =
      (e (↑(KPGlobalTorusBorelNormTwistTransport.iwasawaUpperUnits F B hB).2.unit : KPAdeles F))⁻¹ := by
    exact Units.val_inv_eq_inv_val (Units.map e.toMonoidHom _)
  rw [hi, norm_inv, IsUnit.unit_spec, IsUnit.unit_spec, div_eq_mul_inv]

private theorem root_projection (x : KPAdeles F) :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.N F ζ hζ x) =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
        (Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x) := by
  change QuotientGroup.mk' _
    (KPAdelicCoverRestrictedProduct.projection F ζ hζ (KPRationalAdelicSplitting.N F ζ hζ x)) = _
  congr 1
  have ht (v : KPHilbert.Place F) :
      KPAdelicCoverRestrictedProduct.matrixEval F v
        (Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x) =
      KubotaRankTwo.n (KPHilbert.Completion F v) (KPAdelicCoverRestrictedProduct.adeleEval F v x) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPAdelicCoverRestrictedProduct.matrixEval, Matrix.GeneralLinearGroup.transvection,
        Matrix.transvection, Matrix.single, KubotaRankTwo.n]
  apply Units.ext
  ext i j
  apply Prod.ext
  · funext w
    exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inl w) => M i j)
      ((KPRationalAdelicSplitting.projection_N F ζ hζ x (Sum.inl w)).trans (ht (Sum.inl w)).symm)
  · apply Subtype.ext
    funext q
    exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M i j)
      ((KPRationalAdelicSplitting.projection_N F ζ hζ x (Sum.inr q)).trans (ht (Sum.inr q)).symm)

theorem actualBaseRowHeight_torus_root_modulus
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) :
    (KPChamberHeight.height F (actualBaseRowLine F)
        (coveredHeightProjection F ζ hζ
          (t.val * KPGlobalTorusFunctionData.N F ζ hζ x))) ^ (-2 : ℤ) =
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  let B := A * Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
  have hB : B 1 0 = 0 := by
    simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, h10]
  have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) := by
    simp only [B, map_mul, root_projection F ζ hζ x, hA]
  have hp : coveredHeightProjection F ζ hζ
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) = Matrix.ProjGenLinGroup.mk B := by
    change adelicHeightProjection F (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ _) = _
    rw [← he]
    rfl
  rw [hp]
  simp only [actualBaseRowLine, KPChamberHeight.height_mk]
  rw [KPGlobalResidualKernel.ChamberNorm.upper_rowHeight_modulus F B hB]
  have hr := KPGlobalTorusBorelNormTwistTransport.iwasawaUpperRatio_torus_root F ζ hζ t x B hB he
  change _ = (((KPGlobalTorusFunctionData.ideleAbs F (KPGlobalTorusFunctionData.p F ζ hζ t) : NNReal) : ℝ))
  rw [← hr, ideleAbs_product F ζ hζ]
  simp_rw [eval_upper_ratio F]
  have hd (w : InfinitePlace F) : KPChamberHeight.infiniteDegree F w = 2 := by
    exact if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (KPHilbert.infinite_isComplex F ζ hζ w))
  simp_rw [hd]

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
