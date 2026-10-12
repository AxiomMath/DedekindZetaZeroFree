module

public import DedekindZetaZeroFree.Metaplectic.Weil.Finite.CutoffStationaryCosetReduction
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CompletionDifferentExponent
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.FiniteTraceNormalization

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace DedekindZetaZeroFree.SArithmeticData

variable {F : Type} [Field F] [NumberField F]

def finiteTraceAnnihilator (v : HeightOneSpectrum (𝓞 F))
    (H : AddSubgroup (v.adicCompletion F)) : AddSubgroup (v.adicCompletion F) where
  carrier := {y | ∀ x ∈ H, ResidueTrace.localTraceCharacter v (x * y) = 1}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz x hx
    rw [mul_add, AddChar.map_add_eq_mul, hy x hx, hz x hx, one_mul]
  neg_mem' := by
    intro y hy x hx
    rw [mul_neg, AddChar.map_neg_eq_inv, hy x hx, inv_one]

def finiteStationarySubgroup (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (H : AddSubgroup (v.adicCompletion F)) :
    AddSubgroup (v.adicCompletion F) :=
  (finiteTraceAnnihilator v H).comap
    (AddMonoidHom.mulLeft ((2 : v.adicCompletion F) * (a : v.adicCompletion F)))

def FiniteQuadraticAdmissible (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (H : AddSubgroup (v.adicCompletion F)) : Prop :=
  (∃ c : (v.adicCompletion F)ˣ,
    H = (v.adicCompletionIntegers F).toSubring.toAddSubgroup.map
      (AddMonoidHom.mulLeft (c : v.adicCompletion F))) ∧
  (∀ h ∈ H, ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * h ^ 2) = 1) ∧
  H ≤ finiteStationarySubgroup v a H

abbrev finiteStationaryQuotient (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (H : AddSubgroup (v.adicCompletion F)) :=
  finiteStationarySubgroup v a H ⧸
    H.comap (finiteStationarySubgroup v a H).subtype

def finiteStationaryPhase (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (H : AddSubgroup (v.adicCompletion F))
    (x : finiteStationaryQuotient v a H) : Circle :=
  ResidueTrace.localTraceCharacter v
    ((a : v.adicCompletion F) * ((Quotient.out x : finiteStationarySubgroup v a H) : v.adicCompletion F) ^ 2)

def finiteStationaryGauss (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (H : AddSubgroup (v.adicCompletion F)) : ℂ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  exact (((A.finiteTraceHaar v) (H : Set (v.adicCompletion F))).toReal : ℂ) *
    ∑ᶠ x : finiteStationaryQuotient v a H, (finiteStationaryPhase v a H x : ℂ)

def finiteOscillatoryIntegral (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) (n : ℕ) : ℂ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  exact ∫ x in exteriorQuadraticCutoff v n,
    (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * x ^ 2) : ℂ)
      ∂A.finiteTraceHaar v

def finiteOscillatoryValue (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) : ℂ :=
  A.finiteGamma v a /
    (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ)

private theorem prime_eq (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.rationalPrimeBelow v = PlaceTraceAdapter.prime F v := by
  apply Subtype.ext
  change ringChar (𝓞 F ⧸ v.asIdeal) = Rat.HeightOneSpectrum.natGenerator _
  rw [Ideal.ringChar_quot]
  have h := Rat.HeightOneSpectrum.span_natGenerator (PlaceTraceAdapter.rationalPlace F v)
  have he : (v.asIdeal.under ℤ) =
      (PlaceTraceAdapter.rationalPlace F v).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    ext x
    rw [← Ideal.comap_symm]
    rw [Ideal.mem_comap]
    change algebraMap ℤ (𝓞 F) x ∈ v.asIdeal ↔
      algebraMap (𝓞 ℚ) (𝓞 F) ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm x) ∈ v.asIdeal
    rw [DFunLike.congr_fun (RingHom.ext_int (algebraMap ℤ (𝓞 F))
      ((algebraMap (𝓞 ℚ) (𝓞 F)).comp (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom)) x]
    rfl
  rw [he, ← h, Ideal.absNorm_span_singleton]
  simp
private theorem continuous_cast_map {p q : Nat.Primes} {K : Type} [Field K]
    [TopologicalSpace K] (h : p = q) (j : ℚ_[q] →+* K) (hc : Continuous j) :
    Continuous ((cast (congrArg (fun p : Nat.Primes => ℚ_[p] →+* K) h.symm) j) :
      ℚ_[p] →+* K) := by
  subst q
  exact hc

private theorem traceChar_cast {p q : Nat.Primes} {K : Type} [Field K]
    (h : p = q) (j : ℚ_[q] →+* K) :
    (letI := (cast (congrArg (fun p : Nat.Primes => ℚ_[p] →+* K) h.symm) j).toAlgebra
     letI : Fact p.1.Prime := ⟨p.2⟩
     (rationalPadicCharacter p).compAddMonoidHom (Algebra.trace ℚ_[p] K).toAddMonoidHom) =
    (letI := j.toAlgebra
     letI : Fact q.1.Prime := ⟨q.2⟩
     (rationalPadicCharacter q).compAddMonoidHom (Algebra.trace ℚ_[q] K).toAddMonoidHom) := by
  subst q
  rfl

private theorem char_eq (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.localTraceCharacter v = localFiniteCharacter F v := by
  have hp := prime_eq v
  have hmap : Continuous (PlaceTraceAdapter.padicMap F v) := by
    letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
      HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ (PlaceTraceAdapter.rationalPlace F v)
    exact (finitePlaceAdicCompletionMap_continuous ℚ F
      (PlaceTraceAdapter.rationalPlace F v) ⟨v, rfl⟩).comp
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
        (PlaceTraceAdapter.rationalPlace F v)).symm.continuous
  let j : ℚ_[ResidueTrace.rationalPrimeBelow v] →+* v.adicCompletion F :=
    cast (congrArg (fun p : Nat.Primes => ℚ_[p] →+* v.adicCompletion F) hp.symm)
      (PlaceTraceAdapter.padicMap F v)
  have hj (q : ℚ) : j (q : ℚ_[ResidueTrace.rationalPrimeBelow v]) =
      algebraMap F (v.adicCompletion F) (algebraMap ℚ F q) := by
    exact DFunLike.congr_fun (RingHom.ext_rat (j.comp (algebraMap ℚ _))
      ((algebraMap F _).comp (algebraMap ℚ F))) q
  have hc : Continuous j := continuous_cast_map hp _ hmap
  have hb : j = ResidueTrace.baseEmbedding v :=
    (Classical.choose_spec (ResidueTrace.existsUnique_baseEmbedding v)).2 j ⟨hc, hj⟩
  unfold ResidueTrace.localTraceCharacter localFiniteCharacter PlaceTraceAdapter.trace
  rw [← hb]
  exact traceChar_cast hp (PlaceTraceAdapter.padicMap F v)

 def twoA (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    (v.adicCompletion F)ˣ :=
  Units.mk0 ((2 : v.adicCompletion F) * (a : v.adicCompletion F))
    (mul_ne_zero (by exact_mod_cast (show (2 : F) ≠ 0 from two_ne_zero)) a.ne_zero)

private theorem stationary_ball (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (m : ℤ) :
    finiteStationarySubgroup v a (finiteCompletionBall F v m) =
      localScaledBallDual F v (twoA v a) m := by
  ext x
  change (∀ h ∈ finiteCompletionBall F v m,
    ResidueTrace.localTraceCharacter v (h * (2 * (a : v.adicCompletion F) * x)) = 1) ↔ _
  simp only [char_eq]
  rfl

private theorem admissible_ball (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (H : AddSubgroup (v.adicCompletion F))
    (hH : FiniteQuadraticAdmissible v a H) :
    ∃ m : ℤ, H = finiteCompletionBall F v m := by
  obtain ⟨c, rfl⟩ := hH.1
  refine ⟨finiteCompletionUnitOrder F v c, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change Valued.v ((c : v.adicCompletion F) * y) ≤ _
    rw [map_mul, finiteCompletionUnitOrder_valuation]
    change Valued.v y ≤ 1 at hy
    simpa using mul_le_mul_left hy (WithZero.exp (-finiteCompletionUnitOrder F v c))
  · intro hx
    refine ⟨(↑c⁻¹ : v.adicCompletion F) * x, ?_, by simp [mul_assoc]⟩
    change Valued.v ((↑c⁻¹ : v.adicCompletion F) * x) ≤ 1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, finiteCompletionUnitOrder_valuation]
    exact (inv_mul_le_one₀ WithZero.exp_pos).mpr hx

private theorem phase_ball (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v (twoA v a) m) :
    (fun x : localScaledBallDualQuotient F v (twoA v a) m =>
      ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) *
        ((Quotient.out x : localScaledBallDual F v (twoA v a) m) : v.adicCompletion F) ^ 2)) =
      localFinitePerfectQuadraticPhase F v a (twoA v a) rfl m hq hHL := by
  funext x
  rw [char_eq]
  change localFinitePerfectQuadraticPhase F v a (twoA v a) rfl m hq hHL
    (QuotientAddGroup.mk (Quotient.out x)) = _
  exact congrArg _ (Quotient.out_eq x)

 local instance stabilizationMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
 local instance stabilizationBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem haar_scalar (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ c : ℝ≥0∞, A.finiteTraceHaar v = c • localNormalizedHaar F v := by
  let μ : Measure (v.adicCompletion F) := Measure.addHaar
  let K := finiteCompletionIntegersPositiveCompacts F v
  have hμ : μ = μ K • Measure.addHaarMeasure K := Measure.addHaarMeasure_unique μ K
  have hO : (K : Set (v.adicCompletion F)) = {x | ‖x‖ ≤ (1 : ℝ)} := by
    rw [coe_finiteCompletionIntegersPositiveCompacts]
    ext x
    exact ⟨norm_le_one_of_mem_adicCompletionIntegers v,
      mem_adicCompletionIntegers_of_norm_le_one v⟩
  have hp : μ K ≠ 0 := (MeasureTheory.Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hf : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  refine ⟨ENNReal.ofReal (PoissonS.integerVolume F v) /
    ENNReal.ofReal (localHalfDifferentFactor F v), ?_⟩
  change (ENNReal.ofReal (PoissonS.integerVolume F v) / μ {x | ‖x‖ ≤ (1 : ℝ)}) • μ = _
  rw [← hO]
  conv_lhs => arg 2; rw [hμ]
  rw [smul_smul]
  rw [localNormalizedHaar, smul_smul]
  congr 1
  rw [ENNReal.div_mul_cancel hp hf,
    ENNReal.div_mul_cancel (by simpa using localHalfDifferentFactor_pos F v)
      ENNReal.ofReal_ne_top]

private theorem cutoff_ball (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    exteriorQuadraticCutoff v n =
      (finiteCompletionBall F v (-(n : ℤ)) : Set (v.adicCompletion F)) := by
  let u := Units.mk0 (finiteCompletionUniformizer F v)
    (finiteCompletionUniformizer_ne_zero F v)
  have hu : finiteCompletionUnitOrder F v u = 1 := by
    simp [finiteCompletionUnitOrder, u, finiteCompletionUniformizer_valuation]
  have hv : Valued.v ((u : v.adicCompletion F) ^ (-(n : ℤ))) = WithZero.exp (n : ℤ) := by
    rw [map_zpow₀, finiteCompletionUnitOrder_valuation, hu, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hn : ‖((u : v.adicCompletion F) ^ (-(n : ℤ)))‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
    rw [norm_zpow, finiteCompletionUnitOrder_norm, hu]
    simp
  ext x
  change ‖x‖ ≤ _ ↔ Valued.v x ≤ _
  rw [← hn]
  simpa only [hv, neg_neg] using (Valued.toNormedField.norm_le_iff (x := x)
    (x' := ((u : v.adicCompletion F) ^ (-(n : ℤ)))))

private theorem gauss_ball (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v (twoA v a) m)
    (c : ℝ≥0∞) (hc : A.finiteTraceHaar v = c • localNormalizedHaar F v) :
    A.finiteStationaryGauss v a (finiteCompletionBall F v m) =
      (c.toReal : ℂ) * localFiniteStationaryGaussSum F v a (twoA v a) rfl m hq hHL := by
  letI := finite_localScaledBallDualQuotient F v (twoA v a) m hHL
  letI := Fintype.ofFinite (localScaledBallDualQuotient F v (twoA v a) m)
  unfold finiteStationaryGauss finiteStationaryPhase finiteStationaryQuotient
  rw [stationary_ball]
  have hp (x : localScaledBallDualQuotient F v (twoA v a) m) :=
    congrFun (phase_ball v a m hq hHL) x
  simp_rw [hp]
  rw [finsum_eq_sum_of_fintype]
  rw [hc, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  simp only [Complex.ofReal_mul, localFiniteStationaryGaussSum]
  ring

theorem exists_finiteQuadraticAdmissible (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) :
    ∃ H : AddSubgroup (v.adicCompletion F), FiniteQuadraticAdmissible v a H := by
  letI : Fact (ResidueTrace.rationalPrimeBelow v).1.Prime :=
    ⟨(ResidueTrace.rationalPrimeBelow v).2⟩
  letI := (ResidueTrace.baseEmbedding v).toAlgebra
  letI := ResidueTrace.localTrace_finite v
  letI : ContinuousSMul ℚ_[ResidueTrace.rationalPrimeBelow v] (v.adicCompletion F) := by
    constructor
    change Continuous (fun x : ℚ_[ResidueTrace.rationalPrimeBelow v] × v.adicCompletion F =>
      ResidueTrace.baseEmbedding v x.1 * x.2)
    exact ((ResidueTrace.baseEmbedding_spec v).1.comp continuous_fst).mul continuous_snd
  let t := Algebra.trace ℚ_[ResidueTrace.rationalPrimeBelow v] (v.adicCompletion F)
  have ht : Continuous (fun h : v.adicCompletion F => t ((a : v.adicCompletion F) * h ^ 2)) :=
    t.continuous_of_finiteDimensional.comp (by fun_prop)
  have hopen := PadicInt.isOpenEmbedding_coe (p := (ResidueTrace.rationalPrimeBelow v).1)
  have hn : {h : v.adicCompletion F | t ((a : v.adicCompletion F) * h ^ 2) ∈
      Set.range (fun z : ℤ_[ResidueTrace.rationalPrimeBelow v] =>
        (z : ℚ_[ResidueTrace.rationalPrimeBelow v]))} ∈ 𝓝 (0 : v.adicCompletion F) :=
    (hopen.isOpen_range.preimage ht).mem_nhds (by simp [t])
  obtain ⟨m, _, hm⟩ := (finiteCompletionBall_hasBasis_nhds F v 0).mem_iff.mp hn
  let H := finiteCompletionBall F v m
  have hq : ∀ h ∈ H, ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * h ^ 2) = 1 := by
    intro h hh
    exact (rationalPadicCharacter_eq_one_iff _ _).mpr (hm (by simpa [H] using hh))
  refine ⟨H, ?_, hq, ?_⟩
  · refine ⟨Units.mk0 (finiteCompletionUniformizer F v ^ m)
      (zpow_ne_zero m (finiteCompletionUniformizer_ne_zero F v)), ?_⟩
    ext x
    change x ∈ H ↔ ∃ y, y ∈ (v.adicCompletionIntegers F).toSubring.toAddSubgroup ∧
      finiteCompletionUniformizer F v ^ m * y = x
    simpa [H] using (Set.ext_iff.mp (finiteCompletionBall_eq_uniformizer_image F v _
      (finiteCompletionUniformizer_valuation F v) m) x)
  · intro h hh k hk
    have he : (a : v.adicCompletion F) * (k + h) ^ 2 =
        (a : v.adicCompletion F) * k ^ 2 + (a : v.adicCompletion F) * h ^ 2 +
        k * ((2 : v.adicCompletion F) * a * h) := by ring
    have hz := hq (k + h) (H.add_mem hk hh)
    rw [he, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hq k hk, hq h hh,
      one_mul, one_mul] at hz
    exact hz

theorem finiteStationaryQuotient_finite (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (H : AddSubgroup (v.adicCompletion F))
    (hH : FiniteQuadraticAdmissible v a H) : Finite (finiteStationaryQuotient v a H) := by
  obtain ⟨m, rfl⟩ := admissible_ball v a H hH
  unfold finiteStationaryQuotient
  rw [stationary_ball]
  apply finite_localScaledBallDualQuotient F v (twoA v a) m
  simpa only [stationary_ball] using hH.2.2

theorem finiteStationaryPhase_mk (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) (H : AddSubgroup (v.adicCompletion F))
    (hH : FiniteQuadraticAdmissible v a H) (x : finiteStationarySubgroup v a H) :
    finiteStationaryPhase v a H
        (QuotientAddGroup.mk' (H.comap (finiteStationarySubgroup v a H).subtype) x) =
      ResidueTrace.localTraceCharacter v
        ((a : v.adicCompletion F) * (x : v.adicCompletion F) ^ 2) := by
  let q : finiteStationaryQuotient v a H → Circle := Quotient.lift
    (fun y : finiteStationarySubgroup v a H =>
      ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * (y : v.adicCompletion F) ^ 2))
    (by
      intro y z hyz
      have hh : -(y : v.adicCompletion F) + z ∈ H :=
        show -y + z ∈ H.comap (finiteStationarySubgroup v a H).subtype from
          QuotientAddGroup.leftRel_apply.mp hyz
      have hc : ResidueTrace.localTraceCharacter v
          ((-(y : v.adicCompletion F) + z) * ((2 : v.adicCompletion F) * a * y)) = 1 :=
        y.property _ hh
      have he : (a : v.adicCompletion F) * (z : v.adicCompletion F) ^ 2 =
          (a : v.adicCompletion F) * (y : v.adicCompletion F) ^ 2 +
          (a : v.adicCompletion F) * (-(y : v.adicCompletion F) + z) ^ 2 +
          (-(y : v.adicCompletion F) + z) * ((2 : v.adicCompletion F) * a * y) := by ring
      rw [he, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hH.2.1 _ hh,
        hc, mul_one, mul_one])
  have hq (t : finiteStationaryQuotient v a H) : finiteStationaryPhase v a H t = q t := by
    change q (QuotientAddGroup.mk (Quotient.out t)) = q t
    exact congrArg q (Quotient.out_eq t)
  rw [hq]
  rfl

theorem finiteOscillatoryIntegral_eventually_eq_gauss (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (H : AddSubgroup (v.adicCompletion F)) (hH : FiniteQuadraticAdmissible v a H) :
    ∀ᶠ n : ℕ in atTop, A.finiteOscillatoryIntegral v a n = A.finiteStationaryGauss v a H := by
  obtain ⟨m, rfl⟩ := admissible_ball v a H hH
  have hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1 := by
    simpa only [char_eq] using hH.2.1
  have hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v (twoA v a) m := by
    simpa only [stationary_ball] using hH.2.2
  obtain ⟨c, hc⟩ := haar_scalar A v
  obtain ⟨N, hN⟩ := localFiniteQuadraticCutoff_eventually_eq_stationaryGaussSum F v a
    (twoA v a) rfl m hq hHL
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [gauss_ball A v a m hq hHL c hc]
  unfold finiteOscillatoryIntegral
  rw [cutoff_ball, hc, Measure.restrict_smul, integral_smul_measure]
  simp only [smul_eq_mul, char_eq]
  rw [hN n hn]
  simp only [Complex.real_smul]

theorem finiteQuadratic_stabilizes (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    A.FiniteQuadraticStabilizes v a := by
  obtain ⟨H, hH⟩ := exists_finiteQuadraticAdmissible v a
  refine ⟨(Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) *
    A.finiteStationaryGauss v a H, ?_⟩
  filter_upwards [finiteOscillatoryIntegral_eventually_eq_gauss A v a H hH] with n hn
  change (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) *
    A.finiteOscillatoryIntegral v a n = _
  rw [hn]

theorem finiteOscillatoryIntegral_eventually_eq_value (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    ∀ᶠ n : ℕ in atTop, A.finiteOscillatoryIntegral v a n = A.finiteOscillatoryValue v a := by
  have hb : (2 : v.adicCompletion F) * (a : v.adicCompletion F) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show (2 : F) ≠ 0 from two_ne_zero)) a.ne_zero
  have hs : (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_iff.mpr hb)).ne'
  filter_upwards [A.finiteQuadraticCutoff_eventually_eq_gamma v a
    (A.finiteQuadratic_stabilizes v a)] with n hn
  change (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) *
    A.finiteOscillatoryIntegral v a n = A.finiteGamma v a at hn
  exact (eq_div_iff hs).mpr (by simpa [mul_comm] using hn)

theorem finiteOscillatoryValue_eq_gauss (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (H : AddSubgroup (v.adicCompletion F)) (hH : FiniteQuadraticAdmissible v a H) :
    A.finiteOscillatoryValue v a = A.finiteStationaryGauss v a H := by
  obtain ⟨n, hv, hg⟩ := ((A.finiteOscillatoryIntegral_eventually_eq_value v a).and
    (A.finiteOscillatoryIntegral_eventually_eq_gauss v a H hH)).exists
  exact hv.symm.trans hg

private theorem localStationaryGauss_norm (v : HeightOneSpectrum (𝓞 F))
    (a b : (v.adicCompletion F)ˣ)
    (hb : (b : v.adicCompletion F) = (2 : v.adicCompletion F) * a) (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m) :
    ‖localFiniteStationaryGaussSum F v a b hb m hq hHL‖ =
      (Real.sqrt ‖(b : v.adicCompletion F)‖)⁻¹ := by
  letI := finite_localScaledBallDualQuotient F v b m hHL
  letI := Fintype.ofFinite (localScaledBallDualQuotient F v b m)
  obtain ⟨hz, hl, hr, hn, _⟩ := weil_finite_perfect_quadratic_quotient F v a b hb m hq hHL
  have hnd : ∀ x : localScaledBallDualQuotient F v b m, x ≠ 0 → ∃ y,
      finiteQuadraticPolarization (localFinitePerfectQuadraticPhase F v a b hb m hq hHL) x y ≠ 1 := by
    intro x hx
    by_contra he
    apply hx
    apply hn
    simpa only [localFinitePerfectQuadraticPolar, not_exists, not_not] using he
  have hg := weil_finite_quadratic_gauss_modulus
    (localFinitePerfectQuadraticPhase F v a b hb m hq hHL) hz hl hr hnd
  have hc := natCard_localScaledBallDualQuotient F v b m hHL
  rw [Nat.card_eq_fintype_card] at hc
  have hp := localScaledBallDual_mass_product F v b m
  have hpos := (localScaledBallDual_masses_pos_finite F v b m).1
  have hs : ‖localFiniteStationaryGaussSum F v a b hb m hq hHL‖ ^ 2 =
      ‖(b : v.adicCompletion F)‖⁻¹ := by
    unfold localFiniteStationaryGaussSum
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hg, hc]
    calc
      _ = (localNormalizedHaar F v (finiteCompletionBall F v m : Set _)).toReal *
          (localNormalizedHaar F v (localScaledBallDual F v b m : Set _)).toReal := by
            field_simp
      _ = _ := hp
  have hbpos : 0 < ‖(b : v.adicCompletion F)‖ := norm_pos_iff.mpr b.ne_zero
  have hsq : ((Real.sqrt ‖(b : v.adicCompletion F)‖)⁻¹) ^ 2 = ‖(b : v.adicCompletion F)‖⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hbpos.le]
  nlinarith [norm_nonneg (localFiniteStationaryGaussSum F v a b hb m hq hHL),
    inv_pos.mpr (Real.sqrt_pos.mpr hbpos)]

private theorem value_norm_of_haar (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (hhaar : A.finiteTraceHaar v = localNormalizedHaar F v) :
    ‖A.finiteOscillatoryValue v a‖ =
      (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖)⁻¹ := by
  obtain ⟨H, hH⟩ := exists_finiteQuadraticAdmissible v a
  rw [A.finiteOscillatoryValue_eq_gauss v a H hH]
  obtain ⟨m, rfl⟩ := admissible_ball v a H hH
  have hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1 := by
    simpa only [char_eq] using hH.2.1
  have hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v (twoA v a) m := by
    simpa only [stationary_ball] using hH.2.2
  rw [gauss_ball A v a m hq hHL 1 (by simpa using hhaar)]
  simpa only [ENNReal.toReal_one, Complex.ofReal_one, one_mul, twoA, Units.val_mk0] using
    (localStationaryGauss_norm v a (twoA v a) rfl m hq hHL)

theorem norm_finiteOscillatoryValue (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    ‖A.finiteOscillatoryValue v a‖ =
      (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖)⁻¹ := by
  have hvolume : PoissonS.integerVolume F v = localHalfDifferentFactor F v := by
    rw [PoissonS.integerVolume,
      FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent F v,
      zpow_natCast, localHalfDifferentFactor_eq_inv_sqrt F v,
      localDifferentNorm, Nat.cast_pow, one_div]
  exact value_norm_of_haar A v a
    (FiniteOscillatoryStabilization.finiteTraceHaar_eq_localNormalizedHaar_of_integerVolume
      A v hvolume)

theorem norm_finiteGamma (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    ‖A.finiteGamma v a‖ = 1 := by
  have hb : (2 : v.adicCompletion F) * (a : v.adicCompletion F) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show (2 : F) ≠ 0 from two_ne_zero)) a.ne_zero
  have hs := Real.sqrt_pos.mpr (norm_pos_iff.mpr hb)
  have hv := A.norm_finiteOscillatoryValue v a
  rw [finiteOscillatoryValue, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs] at hv
  exact (div_eq_iff hs.ne').mp hv |>.trans (inv_mul_cancel₀ hs.ne')

end DedekindZetaZeroFree.SArithmeticData

end
