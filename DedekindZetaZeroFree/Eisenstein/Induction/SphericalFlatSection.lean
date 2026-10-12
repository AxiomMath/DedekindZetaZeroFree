module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeCore.DirectedFiniteTypeStages
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalFlatFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

private theorem actual_right_chart_smooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hleft := KPContFlatStageJetHolomorphy.L_contDiffOn F ζ hζ
    (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι)
    (KPContActualSphericalFlatStage.stage_smooth F ζ hζ U ι) (fun _ => v) s
    (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀)
  have hc := hleft.comp hq hqO
  apply (hc.congr (fun x hx => congrArg
    (KPContActualSphericalFlatStage.L F ζ hζ U ι s v) (heq x hx))).mono
  exact Set.inter_subset_right

private theorem actual_scalar_kfinite
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (v : S) :
    KPLiteralRaw.KFinite F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K
      (KPContActualSphericalFlatStage.L F ζ hζ U ι 0 v) := by
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : Nonempty (KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) := ⟨U⟩
  let f := KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v
  obtain ⟨J, T, hT⟩ := KPGlobalResidualKernel.CommonSourceStage.hcHeckeCore_mem_stage
    _ _ _ f.property
  let A := (KPMsRationalCompactCrossPairing.Source F ζ hζ 0).subtype
  let W := T.space.map A
  have hW : FiniteDimensional ℂ W :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (((Submodule.fg_iff_finiteDimensional _).mpr T.finiteDimensional).map A)
  refine ⟨W, hW, ?_, ?_⟩
  · refine ⟨f.val, hT.2, ?_⟩
    funext g
    simp [A, f, KPContFlatCommonLevelKernel.L_formula]
  · intro k w hw
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨(KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)) k.val w',
      T.invariant k w' hw', ?_⟩
    rfl

private theorem actual_level_all
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
    KPContActualSphericalFlatStage.L F ζ hζ U ι s v (g * u.val) =
      KPContActualSphericalFlatStage.L F ζ hζ U ι s v g := by
  have hc := (ι v).property.1 g u
  rw [KPContFlatCommonLevelKernel.L_formula, KPContFlatCommonLevelKernel.L_formula, hc.1]
  rcases mul_eq_zero.mp hc.2 with ha | hz
  · have he : KPContFlatSourceRecipe.alpha F ζ hζ (g * u.val) =
        KPContFlatSourceRecipe.alpha F ζ hζ g := sub_eq_zero.mp
      (Complex.ofReal_eq_zero.mp ha)
    rw [he]
  · rw [hz, mul_zero, mul_zero]

private theorem half_modulus_multiplier
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (s : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalTorusFunctionData.deltaHalf F ζ hζ t *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s t =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) (1 / 2 + s) := by
  have hr : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
  unfold KPGlobalTorusFunctionData.deltaHalf
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Complex.ofReal_exp]
  unfold KPGlobalExceptionalParameter.realLogPower KPGlobalTorusBorelTwistCompatibility.normPower
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem actual_fixedVector_flat
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (v : S) :
    ∃ φ : KPLiteralRaw.Flat F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K,
      ∀ (s : ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ),
        φ.val s g = KPContActualSphericalFlatStage.L F ζ hζ U ι s v g := by
  refine ⟨⟨fun s => KPContActualSphericalFlatStage.L F ζ hζ U ι s v, ?_, ?_,
    actual_scalar_kfinite F ζ hζ U ι v⟩, fun _ _ => rfl⟩
  · intro s
    dsimp only
    refine ⟨⟨?_, actual_right_chart_smooth F ζ hζ U ι s v, ?_⟩, ?_⟩
    · have he : KPContActualSphericalFlatStage.L F ζ hζ U ι s v =
        fun g => Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ g : ℂ)) *
          (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v).val.val g :=
        funext (fun g => KPContFlatCommonLevelKernel.L_formula F ζ hζ U ι s v g)
      rw [he]
      exact (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (KPContFlatLogNormSmooth.alpha_continuous F ζ hζ)))).mul
        (KPMsRationalCompactCrossPairingProof.sourceCore_continuous
          (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v))
    · refine ⟨U, ?_⟩
      intro g u hu
      exact actual_level_all F ζ hζ U ι s v g ⟨u, hu⟩
    · intro r x g
      have hcov := (KPContFlatSourceRecipe.flatR F ζ hζ s
        (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v)).property r x g
      change KPContActualSphericalFlatStage.L F ζ hζ U ι s v
          ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
          ((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
            KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s r.val) *
          KPContActualSphericalFlatStage.L F ζ hζ U ι s v g at hcov
      rw [hcov]
      rw [← half_modulus_multiplier]
      ring
  · intro s t k
    dsimp only
    rw [KPContFlatCommonLevelKernel.L_formula, KPContFlatCommonLevelKernel.L_formula]
    have ha : KPContFlatSourceRecipe.alpha F ζ hζ (t.val * k.val) =
        Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) := by
      have h := KPContFlatFullProductIwasawa.alpha_borel_mul F ζ hζ t 0 k.val
      have hk : KPContFlatFullProductIwasawa.alpha F ζ hζ k.val = 0 := by
        have he := KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ 1 k
        simpa using he
      have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
        (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
      simpa only [hN, mul_one, hk, add_zero] using h
    rw [ha]
    simp only [zero_mul, Complex.exp_zero, one_mul]
    rfl

end DedekindZetaZeroFree.KPContinuation.ChamberFlatSource

end
