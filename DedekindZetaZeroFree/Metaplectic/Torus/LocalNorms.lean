module

public import DedekindZetaZeroFree.Metaplectic.Torus.LocalSectionValues
public import DedekindZetaZeroFree.Eisenstein.Induction.TorusTensorFormula

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.TorusNorms
open KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

 def localNorm (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) : KPHilbert.Place F → ℝ
  | Sum.inl w => KPCplxPrincipalSeriesCharts.complexAbs ((a w : ℂ) / (d w : ℂ))
  | Sum.inr q => KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate (t q))

 theorem finite_coordinate (q : HeightOneSpectrum (𝓞 F))
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : t.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
    (h10 : g.g 1 0 = 0) :
    ((C.canonical q).borel.coordinate t : q.adicCompletion F) = g.g 0 0 / g.g 1 1 := by
  let S := C.canonical q
  have hp : Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (q.adicCompletion F) (S.borel.coordinate t) 1) =
      Matrix.ProjGenLinGroup.mk g.g := by
    rw [← S.borel.torus_projection, S.torus_full, ht]
    exact (S.openCell (C.polarization q)).projection_eq g
  let b : KPRankOneInduction.upperBorel F q := ⟨Matrix.ProjGenLinGroup.mk g.g, g.g, rfl, h10⟩
  have h1 := KPRankOneInduction.borelRatio_eq F q b
    (KubotaRankTwo.d (q.adicCompletion F) (S.borel.coordinate t) 1) hp (by simp [KubotaRankTwo.d])
  have h2 := KPRankOneInduction.borelRatio_eq F q b g.g rfl h10
  simpa [KubotaRankTwo.coe_d] using h1.symm.trans h2

 theorem arch_matrix (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w))
    (h : IsUnit (g.g 0 0) ∧ IsUnit (g.g 1 1))
    (h10 : g.g 1 0 = 0) (h01 : g.g 0 1 = 0) :
    LocalCovariance.complexMatrix F ζ hζ w g = KPCplxPrincipalSeriesCharts.upperTriangular
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom h.1.unit)
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom h.2.unit) 0 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [LocalCovariance.complexMatrix, KPCplxPrincipalSeriesCharts.upperTriangular,
      Matrix.GeneralLinearGroup.map_apply, Units.coe_map, IsUnit.unit_spec, h10, h01]

 theorem arch_norm (w : InfinitePlace F) (x y : w.Completionˣ) :
    KPCplxPrincipalSeriesCharts.complexAbs
      (((Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom x : ℂˣ) : ℂ) /
      ((Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom y : ℂˣ) : ℂ)) =
    (KPGlobalCenterRationalCharacterExtension.localAbs F (Sum.inl w) (x * y⁻¹) : ℝ) := by
  let E := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  have hn (z : w.Completion) : ‖E z‖ = ‖z‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).isometry.norm_map_of_map_zero (map_zero E) z
  simp only [KPCplxPrincipalSeriesCharts.complexAbs, Units.coe_map, RingHom.coe_coe,
    ← map_div₀, KPGlobalCenterRationalCharacterExtension.localAbs, Units.val_mul,
    Units.val_inv_eq_inv_val, NNReal.coe_pow, coe_nnnorm]
  change ‖E (x : w.Completion) / E (y : w.Completion)‖ ^ 2 = _
  rw [← map_div₀, hn, div_eq_mul_inv]

 theorem given_raw_norm (u : RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, LocalCovariance.complexMatrix F ζ hζ w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val) :
    Function.HasFiniteMulSupport (localNorm F ζ hζ P C t a d) ∧
      (((KPGlobalCenterRationalCharacter.nu F ζ hζ e : ℝ≥0) : ℝ)) =
        ∏ᶠ v, Real.rpow (localNorm F ζ hζ P C t a d v) (1/6 : ℝ) := by
  have hd := FullTorusFormula.raw_diagonal F ζ hζ e u he
  let h v := (KPGlobalCenterRationalCharacterModulus.raw_torus_local_ratio F ζ hζ u e he v).choose
  have hr v := (KPGlobalCenterRationalCharacterModulus.raw_torus_local_ratio F ζ hζ u e he v).choose_spec
  let abs v := KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
    (KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e))
  have hn v : localNorm F ζ hζ P C t a d v = ((abs v : ℝ≥0) : ℝ) := by
    cases v with
    | inl w =>
      change KPCplxPrincipalSeriesCharts.complexAbs ((a w : ℂ) / (d w : ℂ)) = _
      have hm := arch_matrix F ζ hζ w (u (Sum.inl w)) (h (Sum.inl w)) (hd _).1 (hd _).2
      have hm' := hm.symm.trans (hp w)
      have h00 := congrArg (fun M : KPCplxCharacterHaar.ComplexGL2 => M 0 0) hm'
      have h11 := congrArg (fun M : KPCplxCharacterHaar.ComplexGL2 => M 1 1) hm'
      simp only [KPCplxPrincipalSeriesCharts.upperTriangular, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
      rw [← h00, ← h11, arch_norm F ζ hζ w (h (Sum.inl w)).1.unit (h (Sum.inl w)).2.unit, hr]
      rfl
    | inr q =>
      have hc : (C.canonical q).borel.coordinate (t q) =
          KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) (KPGlobalTorusFunctionData.p F ζ hζ e) := by
        apply Units.ext
        rw [finite_coordinate F ζ hζ P C q (u (Sum.inr q)) (t q) (ht q) (hd _).1]
        rw [← hr (Sum.inr q), Units.val_mul, Units.val_inv_eq_inv_val, IsUnit.unit_spec,
          IsUnit.unit_spec, div_eq_mul_inv]
      change (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate (t q)) : ℝ) = _
      rw [hc]
      rfl
  obtain ⟨ha, hprod⟩ := KPGlobalCenterRationalCharacterModulus.idele_abs_finite_product F
    (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by norm_num) hζ)
    (KPGlobalTorusFunctionData.p F ζ hζ e)
  have ha' : Function.HasFiniteMulSupport abs := ha
  have hreal : Function.HasFiniteMulSupport (fun v => ((abs v : ℝ≥0) : ℝ)) :=
    ha'.comp (map_one (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom ℝ≥0)))
  constructor
  · convert hreal using 1
    funext v
    exact hn v
  · rw [KPGlobalCenterRationalCharacter.nu_formula]
    have hroot := MonoidHom.map_finprod KPGlobalCenterRationalCharacter.sixthPower ha'
    have hcoe := MonoidHom.map_finprod
      (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom ℝ≥0))
      (ha'.comp (map_one KPGlobalCenterRationalCharacter.sixthPower))
    rw [hprod] at hroot
    have hrootcoe := congrArg (fun x : (ℝ≥0)ˣ => ((x : ℝ≥0) : ℝ)) hroot
    change _ = ((NNReal.toRealHom.toMonoidHom.comp (Units.coeHom ℝ≥0))
      (∏ᶠ v, (KPGlobalCenterRationalCharacter.sixthPower ∘ abs) v)) at hrootcoe
    rw [hcoe] at hrootcoe
    convert hrootcoe using 1
    · simp [KPGlobalCenterRationalCharacter.sixthPower, NNReal.coe_rpow]
    · apply finprod_congr
      intro v
      rw [hn]
      simp [KPGlobalCenterRationalCharacter.sixthPower, NNReal.coe_rpow]

 theorem raw_lifts (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    ∃ (u : RestrictedCover F ζ hζ)
      (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
      (a d : InfinitePlace F → ℂˣ),
      (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q))) ∧
      (∀ w, LocalCovariance.complexMatrix F ζ hζ w (u (Sum.inl w)) =
        KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) 0) ∧
      scalarQuotient F ζ hζ (amalgamation F ζ hζ u) = e.val := by
  have hsur : Function.Surjective (fun u : RestrictedCover F ζ hζ =>
      scalarQuotient F ζ hζ (amalgamation F ζ hζ u)) :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, he⟩ := hsur e.val
  have hd := FullTorusFormula.raw_diagonal F ζ hζ e u he
  let h v := (KPGlobalCenterRationalCharacterModulus.raw_torus_local_ratio F ζ hζ u e he v).choose
  let t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q := fun q =>
    ⟨KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)),
      (u (Sum.inr q)).g, rfl, (hd _).1, (hd _).2⟩
  let E w := (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
  refine ⟨u, t, (fun w => Units.map (E w) (h (Sum.inl w)).1.unit),
    (fun w => Units.map (E w) (h (Sum.inl w)).2.unit), fun _ => rfl, ?_, he⟩
  intro w
  exact arch_matrix F ζ hζ w _ (h _) (hd _).1 (hd _).2

end DedekindZetaZeroFree.EisensteinReferenceSections.TorusNorms

end
