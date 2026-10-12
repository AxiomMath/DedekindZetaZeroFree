module

public import DedekindZetaZeroFree.Moments.Probes.TripleMellinIdentity
public import DedekindZetaZeroFree.MeasureTheory.BorelCocompactTransversals

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PrincipalProbeConstruction
variable {F : Type} [Field F] [NumberField F]
local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

theorem exists_domain_with_disintegration (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (C : A.GeneralArithmeticContext σ η hS) :
    ∃ (Q : NormalizedProbe.DomainData A)
      (ν : @Measure (SLocalProduct F A.Sf)ˣ
        (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _))),
      @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
        (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν ∧
      @ProbeSheet.HaarDisintegration F _ _ A ν Q.measure := by
  letI : CompactSpace (A.G1 ⧸ A.Gamma1) := C.normOne_compact
  letI : DiscreteTopology A.Gamma1 := A.discreteTopology_Gamma1
  obtain ⟨n, V, hV, hc⟩ := exists_finite_relativelyCompact_quotient_slices A.Gamma1
  obtain ⟨D, hD, hDc, hDf⟩ :=
    exists_measurable_relativelyCompact_exact_transversal_of_finite_slices A.G1
      A.Gamma1 n V (fun i => (hV i).1) (fun i => (hV i).2.1)
      (fun i => (hV i).2.2) hc
  letI : BorelSpace (SLocalProduct F A.Sf)ˣ := by
    constructor
    unfold Units.instMeasurableSpace
    have he : Topology.IsEmbedding (Units.val : (SLocalProduct F A.Sf)ˣ → SLocalProduct F A.Sf) := by
      let e := Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := (v : A.Sf) → v.val.adicCompletion F)
      have h1 := (Topology.IsEmbedding.piMap (fun w : InfinitePlace F =>
        Units.isEmbedding_val₀ (G₀ := w.Completion))).comp
        (ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).isEmbedding
      have h2 := (Topology.IsEmbedding.piMap (fun v : A.Sf =>
        Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F))).comp
        (ContinuousMulEquiv.piUnits (M := fun v : A.Sf => v.val.adicCompletion F)).isEmbedding
      exact (h1.prodMap h2).comp e.isEmbedding
    change MeasurableSpace.comap (Units.val : (SLocalProduct F A.Sf)ˣ → SLocalProduct F A.Sf)
      (borel (SLocalProduct F A.Sf)) = borel (SLocalProduct F A.Sf)ˣ
    rw [← borel_comap, ← he.isInducing.eq_induced]
  let ν : Measure (SLocalProduct F A.Sf)ˣ := Measure.haar
  have hν : ν.IsHaarMeasure := inferInstance
  obtain ⟨dt, hdt, hdis⟩ := probe_sheet_norm_one_haar_exists F A ν hν
  exact ⟨⟨D, hD, hDc, hDf, dt, hdt⟩, ν, hν, hdis⟩

 def freeReps (A : SArithmeticData F) : Detector.FrequencyRepresentatives F A.Sf := by
  let H := Detector.frequencyGamma F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
  let P (q : Fˣ ⧸ H) := ∃ x : Fˣ, Detector.sixthPowerFreeFrequency F A.Sf x ∧ QuotientGroup.mk x = q
  have h1 : Detector.sixthPowerFreeFrequency F A.Sf 1 := by
    refine ⟨one_mem _, fun v hv => ⟨0, ?_⟩⟩
    simp
  let pick (q : Fˣ ⧸ H) : Fˣ := if q = 1 then 1 else if h : P q then h.choose else 1
  have hpick (q : Fˣ ⧸ H) (hq : P q) :
      Detector.sixthPowerFreeFrequency F A.Sf (pick q) ∧ QuotientGroup.mk (pick q) = q := by
    by_cases he : q = 1
    · subst q; simpa [pick] using h1
    · simpa [pick, he, hq] using hq.choose_spec
  refine ⟨{u | ∃ q, P q ∧ pick q = u}, ?_, ?_, ?_⟩
  · exact ⟨1, ⟨1, h1, by simp⟩, by simp [pick]⟩
  · rintro u ⟨q, hq, rfl⟩
    exact (hpick q hq).1
  · intro x hx
    let q : Fˣ ⧸ H := QuotientGroup.mk x
    have hq : P q := ⟨x, hx, rfl⟩
    refine ⟨⟨pick q, ⟨q, hq, rfl⟩⟩, ?_, ?_⟩
    · change x / pick q ∈ H
      apply (QuotientGroup.eq_one_iff _).mp
      simp only [QuotientGroup.mk_div, (hpick q hq).2]
      exact div_self' q
    · rintro ⟨u, q', hq', rfl⟩ hu
      apply Subtype.ext
      have he : q = q' := by
        have ht := (QuotientGroup.eq_one_iff _).mpr hu
        change QuotientGroup.mk (x / pick q') = 1 at ht
        rw [QuotientGroup.mk_div, (hpick q' hq').2] at ht
        exact (div_eq_one.mp ht)
      exact congrArg pick he.symm

 def rowOf (A : SArithmeticData F) (u : Fˣ)
    (hu : (u : F) ∈ A.R) : ThetaReflectionData.Row A :=
  ⟨⟨(u : F), hu⟩, by intro h; exact u.ne_zero (congrArg Subtype.val h)⟩
 theorem rowOf_unit (A : SArithmeticData F) (u : Fˣ) (hu : (u : F) ∈ A.R) :
    ThetaReflectionData.rowUnit A (rowOf A u hu) = u := by
  apply Units.ext; rfl

 def unitReps (A : SArithmeticData F) : ThetaBranch.UnitRepresentatives A :=
  ⟨fun q => Quotient.out q, fun q => Quotient.out_eq q⟩

private theorem presentation (A : SArithmeticData F) (G : ThetaBranch.AllowedRecipe A)
    (U : Detector.FrequencyRepresentatives F A.Sf) (h : ThetaReflectionData.Row A)
    [IsPrincipalIdealRing A.R] :
    ∃! x : U.carrier × A.Exterior,
      ∃ γ : A.U, ThetaReflectionData.rowUnit A h = x.1.val * G.generator x.2 ^ 6 * γ.val ^ 6 := by
  let hu := ThetaReflectionData.rowUnit A h
  have hint : (hu : F) ∈ A.R := h.val.property
  obtain ⟨p, hp, huniq⟩ := Detector.frequency_unique_presentation F A.Sf A.Sf.finite_toSet U hu hint
  let I := A.exteriorIdealEquiv.symm p.2
  have hI : A.extendIdeal I = p.2.val := by
    rw [← A.exteriorIdealEquiv_apply, Equiv.apply_symm_apply]
  have convert (q : U.carrier × {J : Ideal A.R // J ≠ ⊥})
      (hq : ∃ r : A.R, r ≠ 0 ∧ Ideal.span {r} = q.2.val ∧
        ∃ rF : Fˣ, (rF : F) = (r : F) ∧
        Detector.frequencyEquivalent F A.Sf hu (q.1.val * rF ^ 6)) :
      ∃ γ : A.U, hu = q.1.val * G.generator (A.exteriorIdealEquiv.symm q.2) ^ 6 * γ.val ^ 6 := by
    obtain ⟨r, hr0, hrJ, rF, hrF, a, haS, ha⟩ := hq
    obtain ⟨s, hs, hsF⟩ := G.generates (A.exteriorIdealEquiv.symm q.2)
    have hsJ : Ideal.span {s} = q.2.val := by
      rw [hs.2, ← A.exteriorIdealEquiv_apply, Equiv.apply_symm_apply]
    obtain ⟨b, hb⟩ := Ideal.span_singleton_eq_span_singleton.mp (hsJ.trans hrJ.symm)
    let bU := A.unitEquiv.symm b
    have hrU : rF = G.generator (A.exteriorIdealEquiv.symm q.2) * bU.val := by
      apply Units.ext
      have hh := congrArg (fun z : A.R => (z : F)) hb
      change (s : F) * (bU.val : F) = (r : F) at hh
      rw [Units.val_mul, hsF, hrF]
      exact hh.symm
    refine ⟨⟨a, haS⟩ * bU, ?_⟩
    have he : hu = q.1.val * rF ^ 6 * a ^ 6 := by
      change a ^ 6 = hu / (q.1.val * rF ^ 6) at ha
      rw [ha]
      simp only [div_eq_mul_inv]
      calc
        hu = hu * ((q.1.val * rF ^ 6) * (q.1.val * rF ^ 6)⁻¹) := by simp
        _ = _ := by ac_rfl
    change hu = q.1.val * G.generator (A.exteriorIdealEquiv.symm q.2) ^ 6 * (a * bU.val) ^ 6
    rw [he, hrU, mul_pow, mul_pow]
    simp only [← mul_assoc]
    exact mul_right_comm _ _ _
  refine ⟨(p.1, I), convert p hp, ?_⟩
  intro x hx
  have hx' : ∃ r : A.R, r ≠ 0 ∧ Ideal.span {r} = (A.exteriorIdealEquiv x.2).val ∧
      ∃ rF : Fˣ, (rF : F) = (r : F) ∧
      Detector.frequencyEquivalent F A.Sf hu (x.1.val * rF ^ 6) := by
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨r, hr, hrF⟩ := G.generates x.2
    refine ⟨r, hr.1, ?_, G.generator x.2, hrF, γ.val, γ.property, ?_⟩
    · rw [hr.2, A.exteriorIdealEquiv_apply]
    · change γ.val ^ 6 = hu / (x.1.val * G.generator x.2 ^ 6)
      dsimp [hu]
      rw [hγ]
      exact (mul_div_cancel_left _ _).symm
  have he := huniq (x.1, A.exteriorIdealEquiv x.2) hx'
  have hfst := congrArg Prod.fst he
  have hsnd := congrArg Prod.snd he
  refine Prod.ext (by exact hfst) ?_
  apply A.exteriorIdealEquiv.injective
  simpa [I] using hsnd
 def rowRepsEquiv (A : SArithmeticData F) (U : Detector.FrequencyRepresentatives F A.Sf) :
    {h : ThetaReflectionData.Row A // ThetaReflectionData.rowUnit A h ∈ U.carrier} ≃ U.carrier where
  toFun h := ⟨ThetaReflectionData.rowUnit A h.val, h.property⟩
  invFun u := ⟨rowOf A u.val (U.power_free u.val u.property).1, by
    rw [rowOf_unit]; exact u.property⟩
  left_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := by apply Subtype.ext; exact rowOf_unit _ _ _

set_option maxHeartbeats 800000 in

theorem exists_frequency_representatives (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (C : A.GeneralArithmeticContext σ η hS)
    (G : ThetaBranch.AllowedRecipe A) (hG : G.B = C.correction.B) :
    ∃ U : ThetaBranch.UnitRepresentatives A,
      Nonempty (NormalizedProbe.FrequencyRepresentatives A G U) := by
  letI := C.principal
  let U := freeReps A
  let V := unitReps A
  refine ⟨V, ⟨{
    reps := {h | ThetaReflectionData.rowUnit A h ∈ U.carrier}
    containsOne := ?_
    sixthFree := ?_
    unitClasses := ?_
    factorization := ?_ }⟩⟩
  · change ThetaReflectionData.rowUnit A ⟨1, one_ne_zero⟩ ∈ U.carrier
    have he : ThetaReflectionData.rowUnit A ⟨1, one_ne_zero⟩ = 1 := by
      apply Units.ext; rfl
    rw [he]; exact U.one_mem
  · intro u hu p
    obtain ⟨e, he⟩ := (U.power_free _ hu).2 p.val p.property
    have ho : ThetaBranch.order p.val (ThetaReflectionData.rowUnit A u) = e.val := by
      rw [ThetaBranch.order, he, WithZero.log_exp, neg_neg]
    rw [ho]
    exact ⟨by omega, by exact_mod_cast e.isLt⟩
  · intro ε
    let u := V.representative ε
    have hf : Detector.sixthPowerFreeFrequency F A.Sf u.val := by
      refine ⟨(A.unitEquiv u).val.property, fun p hp => ⟨0, ?_⟩⟩
      change p.valuation F (u.val : F) = 1
      exact u.property p hp
    obtain ⟨v, hv, hvuniq⟩ := U.represents u.val hf
    obtain ⟨γ, hγ, he⟩ := hv
    refine ⟨rowOf A v.val (U.power_free v.val v.property).1, ?_, ⟨γ, hγ⟩⁻¹, ?_⟩
    · change ThetaReflectionData.rowUnit A (rowOf A v.val _) ∈ U.carrier
      rw [rowOf_unit]; exact v.property
    · rw [rowOf_unit]
      change v.val = u.val * (γ⁻¹) ^ 6
      change γ ^ 6 = u.val / v.val at he
      rw [inv_pow, he]
      simp
  · intro h
    let e := (rowRepsEquiv A U).prodCongr (Equiv.refl A.Exterior)
    obtain ⟨x, hx, huniq⟩ := presentation A G U h
    refine ⟨e.symm x, ?_, ?_⟩
    · change ∃ γ : A.U, ThetaReflectionData.rowUnit A h = (e (e.symm x)).1.val *
        G.generator (e (e.symm x)).2 ^ 6 * γ.val ^ 6
      rw [e.apply_symm_apply]
      exact hx
    · intro y hy
      have hy' : ∃ γ : A.U, ThetaReflectionData.rowUnit A h = (e y).1.val *
          G.generator (e y).2 ^ 6 * γ.val ^ 6 := hy
      have he : e y = x := huniq (e y) hy'
      exact e.injective (he.trans (e.apply_symm_apply x).symm)

set_option backward.isDefEq.respectTransparency false in

theorem canonical_trace_compatible (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) :
    ProbeAdditive.TraceCompatible F A.Sf
      (fun v => ResidueTrace.localTraceCharacter v.val) := by
  have harch (x : InfiniteAdeleRing F) :
      ProbeAdditive.archPhase F x = ∏ w, (archTraceCharacter w (x w) : ℂ) := by
    simp only [archTraceCharacter_of_isComplex _ (A.complex_place _), Circle.coe_exp,
      InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    rw [ProbeAdditive.archPhase, ← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  intro r
  have hr := congrArg (fun z : Circle => (z : ℂ)) (A.eS_integer hS r)
  change Circle.coeHom ((∏ w, archTraceCharacter w
    ((sLocalDiagonal F A.Sf (r : F)).1 w)) *
    ∏ v : ↥A.Sf, ResidueTrace.localTraceCharacter v.val
      ((sLocalDiagonal F A.Sf (r : F)).2 v)) = 1 at hr
  rw [map_mul, map_prod, map_prod] at hr
  simpa only [ProbeAdditive.phase, harch, sIntegerDiagonal_apply, Circle.coeHom_apply] using hr

theorem canonical_trace_contract (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) :
    (∀ v : ↥A.Sf, Continuous (ResidueTrace.localTraceCharacter v.val)) ∧
    ProbeAdditive.TraceCompatible F A.Sf (fun v => ResidueTrace.localTraceCharacter v.val) ∧
    PoissonS.TraceConductor F A.Sf (fun v => ResidueTrace.localTraceCharacter v.val) := by
  refine ⟨fun v => ResidueTrace.continuous_localTraceCharacter v.val,
    canonical_trace_compatible A hS, ?_⟩
  exact canonical_trace_conductor A

theorem exists_trace_normalized_haar (A : SArithmeticData F) :
    ∃ μ : (v : ↥A.Sf) → @Measure (v.val.adicCompletion F) (borel _),
      (∀ v, @Measure.IsAddHaarMeasure (v.val.adicCompletion F) _ _ (borel _) (μ v)) ∧
      PoissonS.LocalNormalization F A.Sf μ ∧
      @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _)
        (NormalizedProbe.poissonAdditiveMeasure A μ) := by
  letI (v : ↥A.Sf) : MeasurableSpace (v.val.adicCompletion F) := borel _
  letI (v : ↥A.Sf) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  letI (v : ↥A.Sf) : LocallyCompactSpace (v.val.adicCompletion F) :=
    (PoissonS.finite_components_locallyCompact F A.Sf).1 v
  let μ₀ (v : ↥A.Sf) : Measure (v.val.adicCompletion F) := Measure.addHaar
  have hp (v : ↥A.Sf) : 0 < μ₀ v {x | ‖x‖ ≤ (1 : ℝ)} := by
    apply IsOpen.measure_pos
    · simpa [Metric.closedBall, dist_zero_right] using
        IsUltrametricDist.isOpen_closedBall (0 : v.val.adicCompletion F) one_ne_zero
    · exact ⟨0, by simp⟩
  have hf (v : ↥A.Sf) : μ₀ v {x | ‖x‖ ≤ (1 : ℝ)} ≠ ⊤ := by
    have hc : IsCompact {x : v.val.adicCompletion F | ‖x‖ ≤ (1 : ℝ)} := by
      simpa [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : v.val.adicCompletion F) (1 : ℝ)
    exact hc.measure_lt_top.ne
  let μ (v : ↥A.Sf) : Measure (v.val.adicCompletion F) :=
    (ENNReal.ofReal (PoissonS.integerVolume F v.val) / μ₀ v {x | ‖x‖ ≤ (1 : ℝ)}) • μ₀ v
  have hμ (v : ↥A.Sf) : (μ v).IsAddHaarMeasure := by
    apply Measure.IsAddHaarMeasure.smul (μ₀ v)
    · exact ENNReal.div_ne_zero.mpr
        ⟨(ENNReal.ofReal_pos.mpr (PoissonS.integerVolume_pos F v.val)).ne', hf v⟩
    · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (hp v).ne'
  letI := hμ
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro v
    change (ENNReal.ofReal (PoissonS.integerVolume F v.val) /
      μ₀ v {x | ‖x‖ ≤ (1 : ℝ)}) * μ₀ v {x | ‖x‖ ≤ (1 : ℝ)} = _
    exact ENNReal.div_mul_cancel (hp v).ne' (hf v)
  · haveI : (PoissonArch.traceMeasure F).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.smul volume
        (ENNReal.ofReal_pos.mpr (PoissonArch.haarScalar_pos F)).ne' ENNReal.ofReal_ne_top
    haveI : (PoissonS.productMeasure F A.Sf μ).IsAddHaarMeasure := by
      unfold PoissonS.productMeasure
      exact Measure.prod.instIsAddHaarMeasure _ _
    letI : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩
    apply AddEquiv.isAddHaarMeasure_map
    · exact (PoissonArch.infiniteAdeleToSpace F).symm.continuous.prodMap continuous_id
    · exact (PoissonArch.infiniteAdeleToSpace F).continuous.prodMap continuous_id

theorem poisson_measure_coordinate_coherence (A : SArithmeticData F)
    (μ : (v : ↥A.Sf) → @Measure (v.val.adicCompletion F) (borel _)) :
    NormalizedProbe.poissonAdditiveMeasure A μ =
      Measure.map (PoissonS.localProductToSpace F A.Sf).symm
        (PoissonS.productMeasure F A.Sf μ) := by
  rfl

end DedekindZetaZeroFree.PrincipalProbeConstruction

end
