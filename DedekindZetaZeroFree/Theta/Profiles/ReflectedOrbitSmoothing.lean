module

public import DedekindZetaZeroFree.Theta.Profiles.ReflectedSheetClasses
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ProbeAndUniformSection

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def gammaEquiv : ThetaReflectionData.rationalGamma R.A ≃* R.A.Gamma1 :=
  MulEquiv.ofBijective
    ({ toFun := fun γ => ⟨⟨R.A.diagonal γ.val, R.A.Gamma_le_G1
          (Subgroup.mem_map.mpr ⟨γ.val, γ.property, rfl⟩)⟩,
          Subgroup.mem_map.mpr ⟨γ.val, γ.property, rfl⟩⟩
       map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
       map_mul' := by intro x y; apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _ } :
      ThetaReflectionData.rationalGamma R.A →* R.A.Gamma1)
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        apply Units.ext
        let w : InfinitePlace F := Classical.choice inferInstance
        have hw := congrArg (fun γ : R.A.Gamma1 => (γ.val.val.1 w : w.Completion)) h
        exact (algebraMap F w.Completion).injective hw
      · intro γ
        obtain ⟨a, ha, he⟩ := Subgroup.mem_map.mp γ.property
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he)

@[simp] lemma gammaEquiv_val (γ : ThetaReflectionData.rationalGamma R.A) :
    (gammaEquiv R γ).val.val = R.A.diagonal γ.val := rfl

lemma uniform_sheet_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (κ : R.A.V) (x : PositiveAxis) :
    letI : MeasurableSpace R.A.G1 := borel _;
    Integrable (fun y : R.A.G1 => C.realization.sheetIntegrand C.packet v κ
      (y.val * R.A.radialSection x.val x.property)) R.probe.domain.measure := by
  letI : MeasurableSpace R.A.G1 := borel _
  have h := C.profiles.absolute_sheet_jets v κ 0 (by omega) x.val x.property
  simpa only [iteratedDeriv_zero, Real.exp_log x.property] using h

lemma complex_integrable_uniform_iff (N : TraceHaarTransport R) (w : InfinitePlace F)
    (x : PositiveAxis) (f : R.A.G → ℂ) :
    Integrable (fun z : R.A.G1 => f (normSection R.A w x * z.val)) (GaussianSmoothing.probeHaar R) ↔
      Integrable (fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property))
        (GaussianSmoothing.probeHaar R) := by
  letI := GaussianSmoothing.probeHaar_isHaar R
  let q := GaussianSmoothing.sectionRatio R.A w x
  have h (z : R.A.G1) : normSection R.A w x * z.val =
      (q * z).val * R.A.radialSection x.val x.property := by
    change _ = (normSection R.A w x / R.A.radialSection x.val x.property * z.val) * _
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  simp_rw [h]
  exact (measurePreserving_mul_left (GaussianSmoothing.probeHaar R) q).integrable_comp_emb
    (Homeomorph.mulLeft q).measurableEmbedding
    (g := fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property))

lemma complex_integral_uniform_eq (N : TraceHaarTransport R) (w : InfinitePlace F)
    (x : PositiveAxis) (f : R.A.G → ℂ)
    (hf : Integrable (fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property))
      (GaussianSmoothing.probeHaar R)) :
    (∫ z : R.A.G1, f (normSection R.A w x * z.val) ∂GaussianSmoothing.probeHaar R) =
      ∫ z : R.A.G1, f (z.val * R.A.radialSection x.val x.property) ∂GaussianSmoothing.probeHaar R := by
  have he (z : R.A.G1) : normSection R.A w x * z.val =
      z.val * (GaussianSmoothing.sectionRatio R.A w x).val * R.A.radialSection x.val x.property := by
    change _ = z.val * (normSection R.A w x / R.A.radialSection x.val x.property) * _
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  simp_rw [he]
  rw [GaussianSmoothing.probeHaar_integral, GaussianSmoothing.probeHaar_integral]
  exact N.section_independent x (GaussianSmoothing.sectionRatio R.A w x) f
    ((GaussianSmoothing.probeHaar_integrable _).mp hf)

lemma selected_sheet_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (κ : R.A.V) (x : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    Integrable (fun y : Sheet R.A x => C.realization.sheetIntegrand C.packet v κ y.val)
      (sheetHaar R.A C.packet.v₀ C.transport.groupHaar x) := by
  letI := C.transport.groupHaar_isHaar
  have hu := (GaussianSmoothing.probeHaar_integrable _).mpr (uniform_sheet_integrable R C v κ x)
  have ht := (complex_integrable_uniform_iff R C.transport C.packet.v₀ x _).mpr hu
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe]
  exact (sheetTranslation R.A C.packet.v₀ x).toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr ht

lemma selected_sheet_integral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (κ : R.A.V) (x : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    (∫ y : Sheet R.A x, C.realization.sheetIntegrand C.packet v κ y.val
      ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar x) =
      C.realization.sheet C.packet v κ x := by
  letI := C.transport.groupHaar_isHaar
  rw [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe,
    integral_map (sheetTranslation R.A C.packet.v₀ x).measurable.aemeasurable]
  · change (∫ z : R.A.G1, C.realization.sheetIntegrand C.packet v κ
      (normSection R.A C.packet.v₀ x * z.val) ∂GaussianSmoothing.probeHaar R) = _
    rw [complex_integral_uniform_eq R C.transport C.packet.v₀ x _
      ((GaussianSmoothing.probeHaar_integrable _).mpr (uniform_sheet_integrable R C v κ x)),
      GaussianSmoothing.probeHaar_integral]
    rfl
  · have h := (selected_sheet_integrable R C v κ x).aestronglyMeasurable
    simpa only [sheetHaar, GaussianSmoothing.kernelHaar_eq_probe] using h

theorem reverse_sheet_orbit {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x : Fˣ) (l : PositiveAxis)
    (Ω : Set (Sheet R.A l))
    (hΩ : letI := C.transport.groupHaar_isHaar;
      IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A C.packet.v₀ C.transport.groupHaar l)) :
    letI := C.transport.groupHaar_isHaar;
    Summable (fun γ : ThetaReflectionData.rationalGamma R.A => ∫ y in Ω,
      ‖reverseSheetWord R C.realization C.packet v x γ y.val‖
        ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar l) ∧
    (∑' γ : ThetaReflectionData.rationalGamma R.A, ∫ y in Ω,
      reverseSheetWord R C.realization C.packet v x γ y.val
        ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar l) =
      (Characters.L R v x)⁻¹ * C.realization.sheet C.packet v
        (ThetaReflectionData.rationalClass R.A x) (q R.A x / l) := by
  letI := C.transport.groupHaar_isHaar
  let f : R.A.G → ℂ := fun z => (Characters.L R v x)⁻¹ *
    C.realization.sheetIntegrand C.packet v (ThetaReflectionData.rationalClass R.A x) z
  have hf : Integrable (fun y : Sheet R.A (q R.A x / l) => f y.val)
      (sheetHaar R.A C.packet.v₀ C.transport.groupHaar (q R.A x / l)) :=
    (selected_sheet_integrable R C v _ _).const_mul _
  have he (γ : ThetaReflectionData.rationalGamma R.A) (y : Sheet R.A l) :
      reverseSheetWord R C.realization C.packet v x γ y.val =
        f ((gammaEquiv R γ).val.val * R.A.diagonal x / y.val) := by
    rw [reverseSheetWord_eq, gammaEquiv_val, ← map_mul]
  have hi := integral_div_unfold R.A C.packet.v₀ C.transport.groupHaar x l Ω hΩ f hf
  have ha := integral_div_unfold R.A C.packet.v₀ C.transport.groupHaar x l Ω hΩ
    (fun y => (‖f y‖ : ℂ)) (Complex.ofRealCLM.integrable_comp hf.norm)
  have hn := ha.1.map Complex.reCLM Complex.reCLM.continuous
  simp only [integral_complex_ofReal, Function.comp_def, Complex.reCLM_apply,
    Complex.ofReal_re] at hn
  refine ⟨?_, ?_⟩
  · have h := hn.comp_injective (gammaEquiv R).injective
    simpa only [Function.comp_def, he] using h
  · simp_rw [he]
    have hsum := (gammaEquiv R).toEquiv.tsum_eq (fun γ : R.A.Gamma1 =>
      ∫ y in Ω, f (γ.val.val * R.A.diagonal x / y.val)
        ∂sheetHaar R.A C.packet.v₀ C.transport.groupHaar l)
    refine hsum.trans (hi.2.trans ?_)
    dsimp [f]
    rw [integral_const_mul, selected_sheet_integral]

theorem reverse_sheet_smoothing {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (ξ : ThetaReflectionData.Frequency R.A)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun t : PositiveAxis => C.packet.kernel t.val *
      C.realization.sheet C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
        ⟨Z * ThetaReflectionData.frequencyNorm R.A ξ / t.val,
          div_pos (mul_pos hZ (ThetaReflectionData.frequencyNorm_pos R.A ξ)) t.property⟩) positiveHaar ∧
    (∫ t : PositiveAxis, C.packet.kernel t.val *
      C.realization.sheet C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
        ⟨Z * ThetaReflectionData.frequencyNorm R.A ξ / t.val,
          div_pos (mul_pos hZ (ThetaReflectionData.frequencyNorm_pos R.A ξ)) t.property⟩ ∂positiveHaar) =
      C.realization.H C.packet v (ThetaReflectionData.frequencyClass R.A ξ)
        (Z * ThetaReflectionData.frequencyNorm R.A ξ) := by
  have hx := mul_pos hZ (ThetaReflectionData.frequencyNorm_pos R.A ξ)
  have hi := C.profiles.absolute_smoothing_jets v (ThetaReflectionData.frequencyClass R.A ξ)
    0 (by omega) _ hx
  refine ⟨?_, ?_⟩
  · simpa only [iteratedDeriv_zero, Real.exp_log hx] using hi
  · rw [Realization.H, dif_pos hx]

theorem reverse_sheet_word_integrable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A)
    (l : PositiveAxis) :
    letI := C.transport.groupHaar_isHaar;
    Integrable (fun y : Sheet R.A l => reverseSheetWord R C.realization C.packet v x γ y.val)
      (sheetHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
  letI := C.transport.groupHaar_isHaar
  let a := γ.val * x
  let f : R.A.G → ℂ := fun z => (Characters.L R v x)⁻¹ *
    C.realization.sheetIntegrand C.packet v (ThetaReflectionData.rationalClass R.A x) z
  have hf : Integrable (fun y : Sheet R.A (q R.A a / l) => f y.val)
      (sheetHaar R.A C.packet.v₀ C.transport.groupHaar (q R.A a / l)) :=
    (selected_sheet_integrable R C v _ _).const_mul _
  have hp := sheetDiv_measurePreserving R.A C.packet.v₀ C.transport.groupHaar a l
  have hi := (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  simpa only [Function.comp_def, sheetDiv_val, f, a, reverseSheetWord_eq] using hi

lemma reflected_scale (ξ : ThetaReflectionData.Frequency R.A) (Z : ℝ) (hZ : 0 < Z)
    (t : PositiveAxis) :
    q R.A (Quotient.out ξ) / ⟨t.val / Z, div_pos t.property hZ⟩ =
      (⟨Z * ThetaReflectionData.frequencyNorm R.A ξ / t.val,
        div_pos (mul_pos hZ (ThetaReflectionData.frequencyNorm_pos R.A ξ)) t.property⟩ : PositiveAxis) := by
  apply Subtype.ext
  change R.A.norm (R.A.diagonal (Quotient.out ξ)) / (t.val / Z) = _
  rw [frequencyNorm_out]
  field_simp

end DedekindZetaZeroFree.OrbitExpansion

end
