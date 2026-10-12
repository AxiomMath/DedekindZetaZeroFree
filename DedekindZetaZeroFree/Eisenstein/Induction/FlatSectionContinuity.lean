module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactModels.SmoothAngularProfiles

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal Topology
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {T : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ T D R P H)
private theorem normalized_mem
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (g : KPMsRationalCompactCrossPairing.G F ζ hζ) :
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      ((KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (A.atlasLevel U)).radial.slot
        ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ),
          NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩)⁻¹ * g) = 1 := by
  let B := (H.disintegration (A.atlasLevel U)).radial
  let r : KPMsFixedHaarDisintegration.Radius :=
    ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ),
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩
  let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
    (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ t =
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g := by
    apply Units.ext
    apply NNReal.eq
    exact KPMsRationalCompactCrossPairing.compact_radialSection_delta B r
  change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
    ((t⁻¹).val * g) = 1
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul
    F ζ hζ D (t⁻¹) 0 g
  rw [hN, mul_one] at h
  rw [h, map_inv, hd, inv_mul_cancel]

private theorem sourceFlat_formula
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) (s : ℂ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D)
    (g : KPMsRationalCompactCrossPairing.G F ζ hζ) :
    (A.sourceFlat s f).val g =
      Complex.exp (s * (Real.log
        (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) : ℂ)) *
        f.val.val g := by
  let r : KPMsFixedHaarDisintegration.Radius :=
    ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ),
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩
  let a := KPMsFixedHaarDisintegration.radialSection F ζ hζ
    (H.disintegration (A.atlasLevel U)).radial.slot r
  let k : KPMsRationalCompactCrossPairing.NormOne F ζ hζ D :=
    ⟨a⁻¹ * g, normalized_mem A U g⟩
  have hg : a * k.val = g := by dsimp [k]; group
  have hs := (KPMsRationalCompactCrossPairing.full_radial_angular_decomposition
    (A := A) U s r f 0 k).1
  have hz := (KPMsRationalCompactCrossPairing.full_radial_angular_decomposition
    (A := A) U 0 r f 0 k).1
  rw [hg] at hs hz
  rw [A.sourceFlat_zero] at hz
  rw [hs, hz]
  simp only [KPGlobalExceptionalParameter.realLogPower, add_zero, add_mul, Complex.exp_add]
  ring

 theorem actual_sourceFlat_continuous
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) (s : ℂ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ D) :
    Continuous (A.sourceFlat s f).val := by
  have he : (A.sourceFlat s f).val = fun g =>
      Complex.exp (s * (Real.log
        (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) : ℂ)) * f.val.val g :=
    funext (sourceFlat_formula A U s f)
  rw [he]
  have hn := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous F ζ hζ D
  have hne : ∀ g, (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) ≠ 0 :=
    fun g => by exact_mod_cast Units.ne_zero (KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g)
  exact (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (hn.log hne)))).mul
    (KPMsRationalCompactCrossPairingProof.sourceCore_continuous f)

end DedekindZetaZeroFree.KPGlobalResidualKernel.ChamberNorm.Actual

end
