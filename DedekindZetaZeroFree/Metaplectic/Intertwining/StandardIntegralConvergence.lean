module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuity
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelQuotientMajorants
public import DedekindZetaZeroFree.Adeles.Lattices.AdditiveFundamentalDomain

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal DedekindZetaZeroFree.KPAdditiveFundamentalDomain
open MeasureTheory NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable {T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)
local notation "V" => KPMsRationalCompactCrossPairing.Vplus F ζ hζ D
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
local notation "Adeles" => KPGlobalTorusFunctionData.Adeles F
local notation "W" => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPCubicCoverConstruction.adelicW F ζ hζ)
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming rational → rational
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming scalar_rational_borel_invariant → scalar_rational_borel_invariant
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming compatible_unipotent → compatible_unipotent
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming section_signed_weyl → section_signed_weyl
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming literal_compact_majorants → literal_compact_majorants
open _root_.DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual renaming actual_sourceFlat_continuous → actual_sourceFlat_continuous
private theorem actual_upper_root_continuous : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
  letI : ∀ v : KPHilbert.Place F, TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : TopologicalSpace (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.restrictedTopology F ζ hζ
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hcoord (v : KPHilbert.Place F) :
      Continuous (fun x : KPGlobalTorusFunctionData.Adeles F =>
        KPStandardLocalRootLifts.N F ζ hζ v
          (KPAdelicCoverRestrictedProduct.adeleEval F v x)) := by
    cases v with
    | inl w =>
      exact (KPStandardLocalRootLifts.complex_N_continuous F ζ hζ w).comp
        ((continuous_apply w).comp continuous_fst)
    | inr q =>
      exact (KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).comp
        ((RestrictedProduct.continuous_eval q).comp continuous_snd)
  let U : Set (KPGlobalTorusFunctionData.Adeles F) :=
    {x | ∀ q, ¬ KPAdelicCoverRestrictedProduct.Bad F q →
      x.2 q ∈ q.adicCompletionIntegers F}
  have hU : IsOpen U :=
    (RestrictedProduct.isOpen_forall_imp_mem
      (fun q : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring
        (q.adicCompletion F))).preimage continuous_snd
  have h0 : (0 : KPGlobalTorusFunctionData.Adeles F) ∈ U := by
    intro q hq
    exact zero_mem _
  let S : Set (KPHilbert.Place F) :=
    {v | match v with | .inl _ => True | .inr q => ¬ KPAdelicCoverRestrictedProduct.Bad F q}
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ S
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨Set.toFinite _, by simpa [S] using KPAdelicCoverRestrictedProduct.bad_finite F⟩
  have hmem (x : U) (v : KPHilbert.Place F) (hv : v ∈ S) :
      KPStandardLocalRootLifts.N F ζ hζ v
        (KPAdelicCoverRestrictedProduct.adeleEval F v x) ∈
          KPAdelicCoverRestrictedProduct.compact F ζ hζ v := by
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q =>
      have hi (t : q.adicCompletion F) :
          t ∈ KPTameCompact.O F q ↔ t ∈ q.adicCompletionIntegers F := by
        letI : ValuativeRel (q.adicCompletion F) :=
          ClassFieldTheory.finitePlaceCompletionValuativeRel F q
        change (ValuativeRel.valuation (q.adicCompletion F)) t ≤ 1 ↔ Valued.v t ≤ 1
        rw [← Valuation.vle_one_iff]
        letI : Valued.v.Compatible := Valuation.Compatible.ofValuation
          (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))
        exact Valuation.vle_one_iff Valued.v
      have hx : x.val.2 q ∈ KPTameCompact.O F q := (hi _).mpr (x.property q hv)
      simp only [KPAdelicCoverRestrictedProduct.compact,
        KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hv]
      refine ⟨KPStandardLocalRootLifts.integralN F q ⟨_, hx⟩, ?_⟩
      exact (KPStandardLocalRootLifts.N_eq_compact F ζ hζ q
        (fun h3 => hv (Or.inr h3)) ⟨_, hx⟩).symm
  let f : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _))
      (Filter.principal S) :=
    fun x => ⟨fun v => KPStandardLocalRootLifts.N F ζ hζ v
      (KPAdelicCoverRestrictedProduct.adeleEval F v x), hmem x⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun v => (hcoord v).comp continuous_subtype_val))
  have hrt : ContinuousAt (KPGlobalTorusFunctionData.rootTuple F ζ hζ) 0 := by
    have hr : Continuous (U.domRestrict (KPGlobalTorusFunctionData.rootTuple F ζ hζ)) :=
      (RestrictedProduct.continuous_inclusion hS).comp hf
    exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hU.mem_nhds h0)
  have hN : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
    have hh : Continuous (KPGlobalTorusFunctionData.Nhom F ζ hζ) := by
      apply continuous_of_continuousAt_one
      exact QuotientGroup.continuous_mk.continuousAt.comp
        (QuotientGroup.continuous_mk.continuousAt.comp hrt)
    exact hh
  exact hN

private theorem rationalLift_eq (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    KPLiteralRaw.rationalLift F ζ hζ γ = rational F ζ hζ γ := by
  have hm : Matrix.ProjGenLinGroup.mk (Quotient.out γ) = γ := Quotient.out_eq' γ
  calc
    KPLiteralRaw.rationalLift F ζ hζ γ = rational F ζ hζ
        (Matrix.ProjGenLinGroup.mk (Quotient.out γ)) := rfl
    _ = rational F ζ hζ γ := congrArg (rational F ζ hζ) hm

private theorem open_cell_term (s : ℂ) (v : V) (g : G) (t : F) (x : Adeles) :
    (A.sourceFlat s v).val
      (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out (KPChamberBruhatTwoCells.cellIndex F (some t))) *
        (KPGlobalTorusFunctionData.N F ζ hζ x * g)) =
    (A.sourceFlat s v).val
      (W * KPGlobalTorusFunctionData.N F ζ hζ
        (algebraMap F Adeles t + x) * g) := by
  let v' := A.sourceFlat s v
  change v'.val _ = v'.val _
  rw [rationalLift_eq]
  change KPChamberBruhatTwoCells.rationalTerm F (rational F ζ hζ)
    v'.val (KPGlobalTorusFunctionData.N F ζ hζ x * g)
    (KPChamberBruhatTwoCells.cellIndex F (some t)) = _
  simp only [KPChamberBruhatTwoCells.cellIndex]
  rw [KPChamberBruhatTwoCells.rationalTerm_eq F _ _
    (scalar_rational_borel_invariant F ζ hζ s v')]
  have h := KPChamberBruhatTwoCells.open_cell_translate F (rational F ζ hζ)
    (KPGlobalTorusFunctionData.Nhom F ζ hζ) (compatible_unipotent F ζ hζ)
    v'.val t x g
  change v'.val (_ * (KPGlobalTorusFunctionData.N F ζ hζ x * g)) = _
  dsimp only [KPGlobalTorusFunctionData.Nhom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  simp only [toAdd_ofAdd] at h
  rw [← mul_assoc, h]
  simpa only [mul_assoc] using section_signed_weyl F ζ hζ s v'
    (KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F Adeles t + x) * g)

 theorem actual_standard_integrable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) (μ : Measure Adeles) [μ.IsAddHaarMeasure]
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (v : V) (g : G) :
    KPGlobalEisensteinData.IntertwinerIntegrable μ
      (W)
      (KPGlobalTorusFunctionData.N F ζ hζ) (A.sourceFlat s v).val g := by
  have :=  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let D := KPAdditiveFundamentalDomain.domain F
  let K : Set Adeles := closure (KPAdditiveFundamentalDomain.archParallelepiped F) ×ˢ
    (KPAdelicTopology.integralAdeles F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  have hK : IsCompact K := KPAdditiveFundamentalDomain.compact_closed_cover F
  have hDK : D ⊆ K := by
    intro x hx
    exact ⟨subset_closure hx.1, hx.2⟩
  let C := (fun x : Adeles => KPGlobalTorusFunctionData.N F ζ hζ x * g) '' K
  have hN := actual_upper_root_continuous F ζ hζ
  have hA : IsCompact C := hK.image (hN.mul continuous_const)
  obtain ⟨b, hb, hbound⟩ := literal_compact_majorants F ζ hζ A U s hs v C hA
  let h : Adeles → ℂ := fun x => (A.sourceFlat s v).val
    (W * KPGlobalTorusFunctionData.N F ζ hζ x * g)
  have hh : Measurable h := by
    have hc := actual_sourceFlat_continuous A U s v
    exact (hc.comp ((continuous_const.mul hN).mul continuous_const)).measurable
  have hsum_bound : ∀ x ∈ D,
      (∑' t : F, ENNReal.ofReal ‖h (algebraMap F Adeles t + x)‖) ≤
        ∑' q, ENNReal.ofReal (b q) := by
    intro x hx
    let e : F → KPChamberBruhatTwoCells.RationalQuotient F :=
      fun t => KPChamberBruhatTwoCells.cellIndex F (some t)
    have he : Function.Injective e :=
      (KPChamberBruhatTwoCells.cellIndex_bijective F).1.comp (Option.some_injective F)
    have ht : ∀ t, ‖h (algebraMap F Adeles t + x)‖ ≤ b (e t) := by
      intro t
      have hq := hbound (e t) (KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ⟨x, hDK hx, rfl⟩
      simpa only [e, open_cell_term, h] using hq
    exact (ENNReal.tsum_le_tsum (fun t => ENNReal.ofReal_le_ofReal (ht t))).trans
      (ENNReal.tsum_comp_le_tsum_of_injective he (fun q => ENNReal.ofReal (b q)))
  have : MeasurableConstVAdd F Adeles := ⟨fun t =>
    (measurable_const.add measurable_id : Measurable (fun x : Adeles => algebraMap F Adeles t + x))⟩
  have : VAddInvariantMeasure F Adeles μ := ⟨fun t S hS => by
    have hp := measurePreserving_add_left μ (algebraMap F Adeles t)
    exact hp.measure_preimage hS.nullMeasurableSet⟩
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hfd := KPAdditiveFundamentalDomain.isAddFundamentalDomain F μ
  have hfinite : (∫⁻ x : Adeles, ENNReal.ofReal ‖h x‖ ∂μ) < ⊤ := by
    rw [hfd.lintegral_eq_tsum'']
    rw [← lintegral_tsum]
    · have hle : (∫⁻ x in D, ∑' t : F, ENNReal.ofReal ‖h (algebraMap F Adeles t + x)‖
          ∂μ) ≤ ∫⁻ _ in D, ∑' q, ENNReal.ofReal (b q) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (KPAdditiveFundamentalDomain.domain_measurableSet F)] with x hx
        exact hsum_bound x hx
      apply lt_of_le_of_lt hle
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      apply ENNReal.mul_lt_top _ (KPAdditiveFundamentalDomain.domain_mass F μ).2
      have he : ∑' q, ENNReal.ofReal (b q) = ∑' q, ENNReal.ofReal (max (b q) 0) := by
        congr 1; funext q; simp
      have hpos : Summable (fun q => max (b q) 0) :=
        Summable.of_nonneg_of_le (fun q => le_max_right (b q) 0)
          (fun q => by
            change max (b q) 0 ≤ |b q|
            exact max_le (le_abs_self (b q)) (abs_nonneg (b q))) hb.norm
      rw [he, ← ENNReal.ofReal_tsum_of_nonneg (fun q => le_max_right _ _) hpos]
      exact ENNReal.ofReal_ne_top.lt_top
    · intro t
      exact (hh.comp (measurable_const.add measurable_id)).norm.ennreal_ofReal.aemeasurable
  exact ⟨hh.aestronglyMeasurable, by simpa only [HasFiniteIntegral, ofReal_norm] using hfinite⟩

end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual

end
