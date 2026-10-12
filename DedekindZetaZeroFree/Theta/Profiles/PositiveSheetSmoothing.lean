module

public import DedekindZetaZeroFree.Theta.Profiles.ReflectedOrbitSmoothing
public import DedekindZetaZeroFree.Theta.Whittaker.RationalFrequencyDilation
public import DedekindZetaZeroFree.Theta.Whittaker.UpperTranslation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def positiveProfile {Q : AdmissibleFlatSources R} (P : Packet R Q) (y : R.A.G) : ℝ :=
  (if ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p then 1 else 0) *
    ∏ w : InfinitePlace F, ‖(y.1 w : w.Completion)‖ ^ 2 *
      KThird (P.scale w * Real.sqrt (‖(y.1 w : w.Completion)‖ ^ 2))

lemma forwardProfile_branch {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) :
    P.forwardProfile v y = P.branch v y * (positiveProfile R P y : ℂ) := by
  by_cases hc : ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p
  · rw [Packet.forwardProfile, positiveProfile, if_pos hc, if_pos hc,
      P.branch_exact v y hc]
    push_cast
    simp only [one_mul, Finset.prod_mul_distrib]
    ring
  · rw [Packet.forwardProfile, positiveProfile, if_neg hc, if_neg hc]
    simp only [zero_mul, Complex.ofReal_zero, mul_zero]

lemma cutoff_class_one {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (y : R.A.G) (hc : ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p) :
    QuotientGroup.mk' R.A.sixthPowers y = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  choose tf htf using fun p => P.cutoff_sixth p (y.2 p) (hc p)
  have hi (w : InfinitePlace F) : ∃ t : w.Completionˣ, t ^ 6 = y.1 w := by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y.1 w : w.Completion)) (by decide : 0 < 6)
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide)] at hz
      exact (y.1 w).ne_zero (e.injective (hz.symm.trans (map_zero e).symm))
    refine ⟨Units.mk0 (e.symm z) (by simpa using hz0), ?_⟩
    apply Units.ext
    apply e.injective
    simpa using hz
  choose ti hti using hi
  refine ⟨(ti, tf), ?_⟩
  apply Prod.ext
  · funext w; exact hti w
  · funext p; exact htf p

lemma positive_uniform_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (x : PositiveAxis) :
    letI : MeasurableSpace R.A.G1 := borel _;
    Integrable (fun z : R.A.G1 => (positiveProfile R C.packet
      (z.val * R.A.radialSection x.val x.property) : ℂ)) R.probe.domain.measure := by
  letI : MeasurableSpace R.A.G1 := borel _
  exact Complex.ofRealCLM.integrable_comp (C.mellin.positive_sheet_integrable x)

lemma positive_sheet_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (x : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    Integrable (fun y : Sheet R.A x => (positiveProfile R C.packet y.val : ℂ))
      (sheetHaar R.A C.packet.v₀ C.transport.groupHaar x) := by
  letI := C.transport.groupHaar_isHaar
  have hu := (GaussianSmoothing.probeHaar_integrable _).mpr (positive_uniform_integrable R C x)
  have ht := (complex_integrable_uniform_iff R C.transport C.packet.v₀ x
    (fun y => (positiveProfile R C.packet y : ℂ))).mpr hu
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe]
  exact (sheetTranslation R.A C.packet.v₀ x).toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr ht

lemma positive_sheet_integral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (x : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    (∫ y : Sheet R.A x, (positiveProfile R C.packet y.val : ℂ)
      ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar x) =
      (C.packet.positiveSheet x : ℂ) := by
  letI := C.transport.groupHaar_isHaar
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe,
    integral_map (sheetTranslation R.A C.packet.v₀ x).measurable.aemeasurable]
  · change (∫ z : R.A.G1, (positiveProfile R C.packet
        (normSection R.A C.packet.v₀ x * z.val) : ℂ) ∂GaussianSmoothing.probeHaar R) = _
    rw [complex_integral_uniform_eq R C.transport C.packet.v₀ x
      (fun y => (positiveProfile R C.packet y : ℂ))
      ((GaussianSmoothing.probeHaar_integrable _).mpr (positive_uniform_integrable R C x)),
      GaussianSmoothing.probeHaar_integral]
    letI : MeasurableSpace R.A.G1 := borel _
    change (∫ z : R.A.G1, (positiveProfile R C.packet
      (z.val * R.A.radialSection x.val x.property) : ℂ) ∂(R.probe.domain.measure)) = _
    rw [integral_complex_ofReal]
    rfl
  · have hm := (positive_sheet_integrable R C x).aestronglyMeasurable
    simpa only [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe] using hm

def forwardSheetWord {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (x : Fˣ)
    (γ : ThetaReflectionData.rationalGamma R.A) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹ *
    (R.σ ((R.probe.correction.H
      (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal (γ.val * x)))
      (QuotientGroup.mk' R.A.sixthPowers y) : Fˣ) : F) ^ 2)⁻¹ *
    P.forwardProfile v (R.A.diagonal (γ.val * x) * y)

lemma forwardSheetWord_eq {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (x : Fˣ)
    (hx : ThetaReflectionData.rationalClass R.A x ∈ R.probe.correction.B)
    (γ : ThetaReflectionData.rationalGamma R.A) (y : R.A.G) :
    forwardSheetWord R P v x γ y = Characters.L R v x *
      (positiveProfile R P (R.A.diagonal (γ.val * x) * y) : ℂ) := by
  let z := R.A.diagonal (γ.val * x) * y
  let k : R.A.G →* R.A.V := QuotientGroup.mk' R.A.sixthPowers
  have hkγ : k (R.A.diagonal γ.val) = 1 := rational_gamma_class R γ
  have hkx : k (R.A.diagonal (γ.val * x)) = k (R.A.diagonal x) := by
    rw [map_mul R.A.diagonal, map_mul k, hkγ]
    exact one_mul (k (R.A.diagonal x))
  have hb : P.branch v z = Characters.L R v x * P.branch v y := by
    dsimp [z]
    rw [map_mul, map_mul R.A.diagonal, map_mul, packet_branch_gamma,
      one_mul, packet_branch_rational]
  by_cases hc : ∀ p : R.A.Sf, z.2 p ∈ P.cutoff p
  · have hkz : k z = 1 := cutoff_class_one R P z hc
    have hprod : k (R.A.diagonal x) * k y = 1 := by
      simpa only [z, map_mul k, hkx] using hkz
    have hy : k y ∈ R.probe.correction.B := by
      have heq : k y = (k (R.A.diagonal x))⁻¹ := by
        exact @eq_inv_of_mul_eq_one_right R.A.V _ _ _ hprod
      rw [heq]
      exact R.probe.correction.B.inv_mem hx
    have hh : R.probe.correction.H (k (R.A.diagonal (γ.val * x))) (k y) = 1 := by
      rw [hkx]
      exact R.probe.correction.B_complement.2.1 _ hx _ hy
    unfold forwardSheetWord
    rw [if_pos hy, one_mul, hh]
    simp only [Units.val_one, map_one, one_pow, inv_one, mul_one]
    rw [forwardProfile_branch, hb]
    change (P.branch v y)⁻¹ * ((Characters.L R v x * P.branch v y) * _) = _
    calc
      _ = Characters.L R v x * (((P.branch v y)⁻¹ * P.branch v y) *
        (positiveProfile R P (R.A.diagonal (γ.val * x) * y) : ℂ)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (packet_branch_ne_zero R P v y), one_mul]
  · have hf : P.forwardProfile v z = 0 := by
      simp only [Packet.forwardProfile, if_neg hc, zero_mul]
    have hp : positiveProfile R P z = 0 := by
      simp only [positiveProfile, if_neg hc, zero_mul]
    unfold forwardSheetWord
    change _ * P.forwardProfile v z = _
    rw [hf, hp, Complex.ofReal_zero, mul_zero, mul_zero]

theorem forward_sheet_orbit {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x : Fˣ)
    (hx : ThetaReflectionData.rationalClass R.A x ∈ R.probe.correction.B)
    (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩ : letI := C.transport.groupHaar_isHaar;
      IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A C.packet.v₀ C.transport.groupHaar l)) :
    letI := C.transport.groupHaar_isHaar;
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A => ∫ y in Ω,
      ‖forwardSheetWord R C.packet v x γ y.val‖
        ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar l) ∧
    (∑' γ : ThetaReflectionData.rationalGamma R.A, ∫ y in Ω,
      forwardSheetWord R C.packet v x γ y.val
        ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar l) =
      Characters.L R v x * (C.packet.positiveSheet (q R.A x * l) : ℂ) := by
  letI := C.transport.groupHaar_isHaar
  let f : R.A.G → ℂ := fun z => Characters.L R v x * (positiveProfile R C.packet z : ℂ)
  have hf : Integrable (fun y : Sheet R.A (q R.A x * l) => f y.val)
      (sheetHaar R.A C.packet.v₀ C.transport.groupHaar (q R.A x * l)) :=
    (positive_sheet_integrable R C _).const_mul _
  have he (γ : ThetaReflectionData.rationalGamma R.A) (y : Sheet R.A l) :
      forwardSheetWord R C.packet v x γ y.val =
        f ((gammaEquiv R γ).val.val * R.A.diagonal x * y.val) := by
    rw [forwardSheetWord_eq R C.packet v x hx, gammaEquiv_val, ← map_mul]
  have hi := integral_mul_unfold R.A C.packet.v₀ C.transport.groupHaar x l Ω hΩ f hf
  have ha := integral_mul_unfold R.A C.packet.v₀ C.transport.groupHaar x l Ω hΩ
    (fun y => (‖f y‖ : ℂ)) (Complex.ofRealCLM.integrable_comp hf.norm)
  have hn := ha.1.map Complex.reCLM Complex.reCLM.continuous
  simp only [integral_complex_ofReal, Function.comp_def, Complex.reCLM_apply,
    Complex.ofReal_re] at hn
  refine ⟨?_, ?_⟩
  · have h := hn.comp_injective (gammaEquiv R).injective
    simpa only [Function.comp_def, he] using h
  · simp_rw [he]
    have hsum := (gammaEquiv R).toEquiv.tsum_eq (fun γ : R.A.Gamma1 =>
      ∫ y in Ω, f (γ.val.val * R.A.diagonal x * y.val)
        ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar l)
    refine hsum.trans (hi.2.trans ?_)
    dsimp [f]
    rw [integral_const_mul, positive_sheet_integral]

theorem forward_sheet_smoothing {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (x : Fˣ) (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      (C.packet.positiveSheet (q R.A x * ⟨t.val / Z, div_pos t.property hZ⟩) : ℂ)) positiveHaar ∧
    (∫ t : PositiveAxis, C.packet.kernel t.val *
      (C.packet.positiveSheet (q R.A x * ⟨t.val / Z, div_pos t.property hZ⟩) : ℂ) ∂positiveHaar) =
      (thetaReflectionGaussian ((q R.A x).val / Z) : ℂ) := by
  let a : PositiveAxis := ⟨(q R.A x).val / Z, div_pos (q R.A x).property hZ⟩
  have he (t : PositiveAxis) :
      q R.A x * ⟨t.val / Z, div_pos t.property hZ⟩ =
        (⟨a.val * t.val, mul_pos a.property t.property⟩ : PositiveAxis) := by
    apply Subtype.ext
    change (q R.A x).val * (t.val / Z) = ((q R.A x).val / Z) * t.val
    ring
  simp_rw [he]
  exact ⟨C.mellin.smoothing_integrable a, C.mellin.smoothing a⟩

end DedekindZetaZeroFree.OrbitExpansion

end
