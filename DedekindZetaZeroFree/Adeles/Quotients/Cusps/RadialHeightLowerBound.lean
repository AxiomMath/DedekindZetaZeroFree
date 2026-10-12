module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.CompactRowDistortion
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Iwasawa.ArchimedeanInsertion
public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.CoveredSphericalSpaces

@[expose] public section

noncomputable section
open scoped Classical NumberField Matrix
open NumberField Matrix

namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
 def radialGL (t : ℝ) : KPChamberHeight.AdelGL F :=
  KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun _ => (Real.exp t : ℂ)))
private lemma radial_infinite (t : ℝ) (w : InfinitePlace F) :
    GeneralLinearGroup.map (KPChamberHeight.infiniteEval F w) (radialGL F ζ hζ t) =
      KubotaRankTwo.d w.Completion
        (Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp t : ℂ))
          (by simpa using Real.exp_ne_zero t)) 1 := by
  have H := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ
    (KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun _ => (Real.exp t : ℂ))) (Sum.inl w)
  change GeneralLinearGroup.map (KPChamberHeight.infiniteEval F w) (radialGL F ζ hζ t) =
    (KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
      (if hh : (Real.exp t : ℂ) = 0 then 1 else Units.mk0 _ _)).g at H
  simp only [show (Real.exp t : ℂ) ≠ 0 by exact_mod_cast Real.exp_ne_zero t, ↓reduceDIte] at H
  exact H

private lemma radial_finite (t : ℝ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    GeneralLinearGroup.map (KPChamberHeight.finiteEval F v) (radialGL F ζ hζ t) = 1 := by
  have H := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ
    (KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun _ => (Real.exp t : ℂ))) (Sum.inr v)
  simpa [KPGlobalTorusFunctionData.archDiagonalTuple, KPAdelicCoverRestrictedProduct.matrixEval,
    KPAdelicCoverRestrictedProduct.adeleEval, KPChamberHeight.finiteEval, radialGL] using H

private lemma radial_local_lower {K : Type*} [NormedField K]
    (r : Fin 2 → K) (A : GL (Fin 2) K) (y : Kˣ)
    (t : ℝ) (hy : ‖(y : K)‖ = Real.exp t) (ht : 0 ≤ t) :
    Real.exp (-t) *
      (Real.sqrt (‖KPChamberHeight.rowAction r A 0‖ ^ 2 + ‖KPChamberHeight.rowAction r A 1‖ ^ 2) /
        Real.sqrt ‖(GeneralLinearGroup.det A : K)‖) ^ 2 ≤
      (Real.sqrt (‖KPChamberHeight.rowAction r (A * KubotaRankTwo.d K y 1) 0‖ ^ 2 +
        ‖KPChamberHeight.rowAction r (A * KubotaRankTwo.d K y 1) 1‖ ^ 2) /
        Real.sqrt ‖(GeneralLinearGroup.det (A * KubotaRankTwo.d K y 1) : K)‖) ^ 2 := by
  have hrow (j : Fin 2) : KPChamberHeight.rowAction r (A * KubotaRankTwo.d K y 1) j =
      if j = 0 then KPChamberHeight.rowAction r A 0 * (y : K) else KPChamberHeight.rowAction r A 1 := by
    fin_cases j <;>
      simp [KPChamberHeight.rowAction, GeneralLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, KubotaRankTwo.d, mul_add, add_mul, mul_assoc]
  have hdet : ‖(GeneralLinearGroup.det (A * KubotaRankTwo.d K y 1) : K)‖ =
      ‖(GeneralLinearGroup.det A : K)‖ * Real.exp t := by
    rw [map_mul, Units.val_mul, norm_mul]
    simp [KubotaRankTwo.d, GeneralLinearGroup.det, Matrix.det_fin_two, hy]
  rw [hrow 0, hrow 1, if_pos rfl, if_neg (by decide), norm_mul, hy, hdet,
    div_pow, div_pow, Real.sq_sqrt (norm_nonneg _),
    Real.sq_sqrt (mul_nonneg (norm_nonneg _) (Real.exp_pos t).le),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hd : 0 < ‖(GeneralLinearGroup.det A : K)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have he : 1 ≤ Real.exp t := Real.one_le_exp ht
  rw [Real.exp_neg]
  field_simp
  have he2 : 1 ≤ Real.exp t ^ 2 := one_le_pow₀ he
  have H := mul_le_mul_of_nonneg_right he2 (sq_nonneg ‖KPChamberHeight.rowAction r A 0‖)
  nlinarith

private lemma infinite_lower (r : Fin 2 → F) (A : KPChamberHeight.AdelGL F)
    (t : ℝ) (ht : 0 ≤ t) (w : InfinitePlace F) :
    Real.exp (-t) * KPChamberHeight.infiniteFactor F r A w ≤
      KPChamberHeight.infiniteFactor F r (A * radialGL F ζ hζ t) w := by
  have hy : ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp t : ℂ)‖ = Real.exp t := by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (KPHilbert.infinite_isComplex F ζ hζ w)
    have H := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (e.symm (Real.exp t : ℂ))
    change ‖e (e.symm (Real.exp t : ℂ))‖ = _ at H
    rw [e.apply_symm_apply] at H
    simpa using H.symm
  simp only [KPChamberHeight.infiniteFactor, KPChamberHeight.infiniteDegree,
    InfinitePlace.not_isReal_iff_isComplex.mpr (KPHilbert.infinite_isComplex F ζ hζ w), ↓reduceIte, map_mul,
    radial_infinite F ζ hζ t w]
  simpa only [map_mul] using radial_local_lower (fun i => algebraMap F w.Completion (r i))
    (GeneralLinearGroup.map (KPChamberHeight.infiniteEval F w) A)
    (Units.mk0 _ (by simpa using Real.exp_ne_zero t)) t hy ht

private lemma row_radial_lower (r : Fin 2 → F) (hr : r ≠ 0) (A : KPChamberHeight.AdelGL F)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(KPCuspLogShape.dimension F : ℝ) * t) * KPChamberHeight.rowHeight F r A ≤
      KPChamberHeight.rowHeight F r (A * radialGL F ζ hζ t) := by
  have hf : ∀ v, KPChamberHeight.finiteFactor F r (A * radialGL F ζ hζ t) v =
      KPChamberHeight.finiteFactor F r A v := by
    intro v
    simp only [KPChamberHeight.finiteFactor, map_mul, radial_finite F ζ hζ t v, mul_one]
  simp only [KPChamberHeight.rowHeight, hf]
  have H := Finset.prod_le_prod₀ (s := Finset.univ)
    (f := fun w => Real.exp (-t) * KPChamberHeight.infiniteFactor F r A w)
    (g := fun w => KPChamberHeight.infiniteFactor F r (A * radialGL F ζ hζ t) w)
    (fun w _ => mul_nonneg (Real.exp_pos _).le (by unfold KPChamberHeight.infiniteFactor; positivity))
    (fun w _ => infinite_lower F ζ hζ r A t ht w)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at H
  have hn : Fintype.card (InfinitePlace F) = KPCuspLogShape.dimension F := by
    have he := KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ
    simpa only [Fintype.card_fin, KPCuspLogShape.dimension] using Fintype.card_congr he
  rw [← Real.exp_nat_mul, hn] at H
  have hE : (KPCuspLogShape.dimension F : ℝ) * -t = -(KPCuspLogShape.dimension F : ℝ) * t := by ring
  rw [hE] at H
  have hp : 0 ≤ ∏ᶠ v, KPChamberHeight.finiteFactor F r A v := by
    apply finprod_nonneg
    intro v
    unfold KPChamberHeight.finiteFactor
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right H hp

private lemma radial_projection (t : ℝ) :
    KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ
      (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun _ => (Real.exp t : ℂ))) =
      ProjGenLinGroup.mk (radialGL F ζ hζ t) := by
  rfl

 def radialSection (t : ℝ) : KPSmoothActualFlowData.GInfinity F := fun w =>
  ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (Units.mk0 (Real.exp t : ℂ)
    (by exact_mod_cast Real.exp_ne_zero t)) 1)
private lemma section_radial (xb : KPCuspCharts.Cross F) (t : ℝ) :
    KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,t)) =
      KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,0)) *
        radialSection F t := by
  funext w
  change ProjGenLinGroup.mk _ = ProjGenLinGroup.mk _ * ProjGenLinGroup.mk _
  rw [← map_mul]
  congr 1
  apply Units.ext
  change KPContSectorArchSphericalFibers.sectionMatrix F ζ hζ (KPCuspCharts.toArch F (xb,t)) w =
    (KPContSectorArchSphericalFibers.sectionMatrix F ζ hζ (KPCuspCharts.toArch F (xb,0)) w) * _
  rw [KPContSectorArchSphericalFibers.sectionMatrix_formula,
    KPContSectorArchSphericalFibers.sectionMatrix_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KPCuspCharts.toArch, radialSection, KubotaRankTwo.d, Matrix.mul_apply,
      Fin.sum_univ_two, Real.exp_add, mul_comm]

private lemma height_radial_lower (ℓ : KPChamberHeight.Line F) (g : KPChamberHeight.AdelPGL F)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(KPCuspLogShape.dimension F : ℝ) * t) * KPChamberHeight.height F ℓ g ≤
      KPChamberHeight.height F ℓ (g * ProjGenLinGroup.mk (radialGL F ζ hζ t)) := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [← map_mul, ← ℓ.mk_rep, KPChamberHeight.height_mk, KPChamberHeight.height_mk]
  exact row_radial_lower F ζ hζ ℓ.rep ℓ.rep_nonzero A t ht

 def zeroHeight (xb : KPCuspCharts.Cross F) : KPSmoothActualFlowData.G F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,0)))
private lemma zeroHeight_continuous : Continuous (zeroHeight F ζ hζ) := by
  apply (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
  apply (KPContSectorArchSphericalFibers.section_continuous F ζ hζ).comp
  exact (KPCuspCharts.toArch_contDiff F).continuous.comp (continuous_id.prodMk continuous_const)

theorem movingRowHeight_lower
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (B : Set (KPCuspCharts.Cross F)) (hB : IsCompact B)
    (D : Set (KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ))
    (hD : IsCompact D) :
    ∃ m : ℝ, 0 < m ∧
      ∀ (ℓ : KPChamberHeight.Line F) (xb : KPCuspCharts.Cross F), xb ∈ B →
        ∀ c ∈ D, ∀ (t : ℝ), 0 ≤ t →
          m * Real.exp (-(KPCuspLogShape.dimension F : ℝ) * t) *
              Projectivization.mulHeight ℓ ≤
            KPChamberHeight.height F ℓ
              (KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ
                (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
                  (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
                    (KPCuspCharts.toArch F (xb, t))) * c.val)) := by
  let E : Set (KPChamberHeight.AdelPGL F) :=
    (fun p : KPCuspCharts.Cross F × KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ =>
      KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ (zeroHeight F ζ hζ p.1 * p.2.val)) '' (B ×ˢ D)
  have hE : IsCompact E := by
    apply (hB.prod hD).image
    apply (KPLiteralExceptionalResidue.coveredHeightProjection_continuous F ζ hζ).comp
    exact ((zeroHeight_continuous F ζ hζ).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  obtain ⟨m, M, hm, hmM, hbound⟩ := KPChamberHeight.compact_uniform_height F E hE
  refine ⟨m, hm, ?_⟩
  intro ℓ xb hxb c hc t ht
  have hmem : KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ (zeroHeight F ζ hζ xb * c.val) ∈ E :=
    ⟨(xb,c), ⟨hxb,hc⟩, rfl⟩
  have hb := (hbound ℓ _ hmem).1
  obtain ⟨CF, hCF, hcompare⟩ := KPChamberHeight.height_one_compare F
  have hh := (hcompare ℓ).2.1
  have H := height_radial_lower F ζ hζ ℓ
    (KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ (zeroHeight F ζ hζ xb * c.val)) t ht
  have hf : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,t))) * c.val =
      (zeroHeight F ζ hζ xb * c.val) *
        KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun _ => (Real.exp t : ℂ)) := by
    rw [section_radial F ζ hζ xb t,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    have hd : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (radialSection F t) =
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun _ => (Real.exp t : ℂ)) := by
      exact ChamberFlatCasimir.arch_diagonal_insertion F ζ hζ _ (fun _ => by exact_mod_cast Real.exp_ne_zero t)
    have hc' := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
      F ζ hζ (radialSection F t) c
    change zeroHeight F ζ hζ xb * _ * c.val = _
    rw [mul_assoc, hc'.eq, ← mul_assoc, hd]
  rw [hf, map_mul, radial_projection F ζ hζ t]
  apply le_trans _ H
  have hb' := (mul_le_mul_of_nonneg_left hh hm.le).trans hb
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hb' (Real.exp_pos _).le

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
