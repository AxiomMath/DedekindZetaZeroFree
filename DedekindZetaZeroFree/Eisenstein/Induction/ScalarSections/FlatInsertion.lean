module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ContinuityAndSmoothness
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.RationalInduction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.KFiniteEvaluators
public import DedekindZetaZeroFree.Eisenstein.Induction.TensorProducts.FlatSectionsAndResidues

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages ThetaExpansion MomentSources
open KPGlobalTorusFunctionData KPGlobalExceptionalParameter TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

 theorem height_borel (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : Group R) :
    iwasawaLogHeight R ((t.val * N F ζ hζ x) * g) =
      Real.log ((delta F ζ hζ t : NNReal) : ℝ) + iwasawaLogHeight R g := by
  unfold iwasawaLogHeight
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul]
  simp only [Units.val_mul, NNReal.coe_mul]
  exact Real.log_mul (by exact_mod_cast Units.ne_zero _) (by exact_mod_cast Units.ne_zero _)

 theorem height_compact (g : Group R) (k : fullProductCompact R) :
    iwasawaLogHeight R (g * k.val) = iwasawaLogHeight R g := by
  unfold iwasawaLogHeight
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact]

 theorem height_one : iwasawaLogHeight R 1 = 0 := by
  unfold iwasawaLogHeight
  have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_compact F ζ hζ
    (fullProductIwasawaData R) (1 : fullProductCompact R)
  change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (fullProductIwasawaData R) 1 = 1 at h
  rw [h]; simp

 def refinedLevel (J : FiniteLevel F ζ hζ) : FiniteLevel F ζ hζ :=
  let L := EisensteinReferenceSections.SourceLevels.level F ζ hζ P C
  ⟨J.toOpenSubgroup ⊓ L.toOpenSubgroup, J.isCompact.inter_right L.toOpenSubgroup.isClosed⟩

 theorem refinedLevel_le (J : FiniteLevel F ζ hζ) :
    globalLevel F ζ hζ (refinedLevel R P C J) ≤ fullProductCompact R := by
  apply le_trans (Subgroup.map_mono (show (refinedLevel R P C J).toOpenSubgroup.toSubgroup ≤
    (EisensteinReferenceSections.SourceLevels.level F ζ hζ P C).toOpenSubgroup.toSubgroup from inf_le_right))
  change globalLevel F ζ hζ (EisensteinReferenceSections.SourceLevels.level F ζ hζ P C) ≤ fullProductCompact R
  rw [EisensteinReferenceSections.SourceLevels.globalLevel_eq]
  exact EisensteinReferenceSections.SourceLevels.refined_compact_le R P C

def scalarTwist (f : Functions R) (z : ℂ) : Functions R :=
  fun g => Complex.exp (z * (iwasawaLogHeight R g : ℂ)) * f g

@[simp] theorem scalarTwist_zero (f : Functions R) : scalarTwist R f 0 = f := by
  funext g
  simp [scalarTwist]

include P C

 theorem scalarTwist_induced (f : Functions R)
    (hf : KPLiteralRaw.Induced F ζ hζ 0 f) (z : ℂ) :
    KPLiteralRaw.Induced F ζ hζ z (scalarTwist R f z) := by
  obtain ⟨J, hJ⟩ := hf.1.2.2
  refine ⟨⟨?_, ?_, refinedLevel R P C J, ?_⟩, ?_⟩
  · exact ((continuous_const.mul (Complex.continuous_ofReal.comp
      (HeightGeometry.height_continuous R))).cexp).mul hf.1.1
  · intro g
    exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (HeightGeometry.height_right_chart_smooth R g))).cexp).mul (hf.1.2.1 g)
  · intro g u hu
    unfold scalarTwist
    rw [height_compact R g ⟨u, refinedLevel_le R P C J hu⟩,
      hJ g u (Subgroup.map_mono inf_le_left hu)]
  · intro r x g
    unfold scalarTwist
    rw [height_borel, hf.2 r x g]
    unfold realLogPower
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    simp only [add_zero]
    rw [show (1 / 2 + z) * (Real.log ((delta F ζ hζ r.val : NNReal) : ℝ) : ℂ) =
      z * (Real.log ((delta F ζ hζ r.val : NNReal) : ℝ) : ℂ) +
      (1 / 2) * (Real.log ((delta F ζ hζ r.val : NNReal) : ℝ) : ℂ) by ring,
      Complex.exp_add]
    ring

 theorem scalarTwist_flat (f : Functions R)
    (hf : KPLiteralRaw.Induced F ζ hζ 0 f)
    (hk : KPLiteralRaw.KFinite F ζ hζ (fullProductCompact R) f) :
    scalarTwist R f ∈ literalFlatModule (fullProductCompact R) := by
  refine ⟨scalarTwist_induced R P C f hf, ?_, ?_⟩
  · intro z t k
    have hN : N F ζ hζ 0 = 1 := (Nhom F ζ hζ).map_one
    have hk : iwasawaLogHeight R k.val = 0 := by
      simpa [height_one R] using height_compact R 1 k
    have ht := height_borel R t 0 k.val
    simp only [hN, mul_one, hk, add_zero] at ht
    rw [scalarTwist_zero]
    simp only [scalarTwist, ht, realLogPower]
  · rwa [scalarTwist_zero]

def coreFlatInsertion :
    RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) →ₗ[ℂ]
      literalFlatModule (fullProductCompact R) where
  toFun x := ⟨scalarTwist R (quotientCoreEvaluator R.A P C x), scalarTwist_flat R P C _
    (quotientCoreEvaluator_induced R.A P C x) (quotientCoreEvaluator_kFinite R P C x)⟩
  map_add' x y := by
    apply Subtype.ext
    funext z g
    change Complex.exp _ * (quotientCoreEvaluator R.A P C (x + y) g) =
      Complex.exp _ * quotientCoreEvaluator R.A P C x g +
        Complex.exp _ * quotientCoreEvaluator R.A P C y g
    rw [map_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    apply Subtype.ext
    funext z g
    change Complex.exp _ * (quotientCoreEvaluator R.A P C (c • x) g) =
      c * (Complex.exp _ * quotientCoreEvaluator R.A P C x g)
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    ring

@[simp] theorem coreFlatInsertion_zero
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)) :
    (coreFlatInsertion R P C x).val 0 = quotientCoreEvaluator R.A P C x :=
  scalarTwist_zero R _

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
