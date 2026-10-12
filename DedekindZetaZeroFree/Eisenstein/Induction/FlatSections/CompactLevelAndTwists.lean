module

public import DedekindZetaZeroFree.Eisenstein.Induction.OrdinaryAndGenuineFlatSections
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.KFiniteness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct ThetaExpansion
open _root_.DedekindZetaZeroFree.ThetaExpansion renaming height_borel → height_borel
open _root_.DedekindZetaZeroFree.ThetaExpansion renaming height_compact → height_compact
open _root_.DedekindZetaZeroFree.ThetaExpansion renaming height_one → height_one
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem scalarSource_has_compact_level (x : PlusCore R N P C) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12,
      KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U ≤ fullProductCompact R ∧
      ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U →
        scalarSourceEvaluator R N P C x (g*u) = scalarSourceEvaluator R N P C x g := by
  obtain ⟨U, hu⟩ := scalarSource_has_level R N P C x
  let V := EisensteinReferenceSections.SourceLevels.level F R.A.zeta12 R.A.primitive_zeta12 P C
  let W : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12 :=
    ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
  have hV : KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 V ≤ fullProductCompact R := by
    rw [EisensteinReferenceSections.SourceLevels.globalLevel_eq]
    exact EisensteinReferenceSections.SourceLevels.refined_compact_le R P C
  have hWU : KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 W ≤
      KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 U :=
    Subgroup.map_mono inf_le_left
  have hWV : KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 W ≤
      KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 V :=
    Subgroup.map_mono inf_le_right
  exact ⟨W, hWV.trans hV, fun g u h => hu g u (hWU h)⟩

def sourceTwist (x : PlusCore R N P C) (s : ℂ) : Functions R :=
  fun g => Complex.exp (s * (iwasawaLogHeight R g : ℂ)) * scalarSourceEvaluator R N P C x g

@[simp] theorem sourceTwist_zero (x : PlusCore R N P C) :
    sourceTwist R N P C x 0 = scalarSourceEvaluator R N P C x := by
  ext g
  simp [sourceTwist]

theorem sourceTwist_induced (x : PlusCore R N P C) (s : ℂ) :
    KPLiteralRaw.Induced F R.A.zeta12 R.A.primitive_zeta12 s (sourceTwist R N P C x s) := by
  obtain ⟨U, hU, hf⟩ := scalarSource_has_compact_level R N P C x
  have h0 := scalarSource_induced R N P C x
  refine ⟨⟨?_, ?_, U, ?_⟩, ?_⟩
  · exact ((continuous_const.mul (Complex.continuous_ofReal.comp (iwasawa_log_height_regular R).1)).cexp).mul h0.1.1
  · intro g
    exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((iwasawa_log_height_regular R).2 g))).cexp).mul (h0.1.2.1 g)
  · intro g u hu
    unfold sourceTwist
    rw [height_compact R g ⟨u, hU hu⟩, hf g u hu]
  · intro r y g
    unfold sourceTwist
    rw [height_borel, h0.2 r y g]
    unfold KPGlobalExceptionalParameter.realLogPower
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    simp only [add_zero]
    rw [show (1/2+s) * (Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12
      R.A.primitive_zeta12 r.val : NNReal) : ℝ) : ℂ) =
        s * (Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12
          R.A.primitive_zeta12 r.val : NNReal) : ℝ) : ℂ) +
        (1/2) * (Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12
          R.A.primitive_zeta12 r.val : NNReal) : ℝ) : ℂ) by ring, Complex.exp_add]
    ring

def sourceFlat (x : PlusCore R N P C) :
    KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) := by
  refine ⟨sourceTwist R N P C x, sourceTwist_induced R N P C x, ?_, ?_⟩
  · intro s t k
    have hN : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
    have hk : iwasawaLogHeight R k.val = 0 := by
      simpa [height_one] using height_compact R 1 k
    have ht := height_borel R t 0 k.val
    simp only [hN, mul_one, hk, add_zero] at ht
    rw [sourceTwist_zero]
    simp only [sourceTwist, ht, KPGlobalExceptionalParameter.realLogPower]
  · rw [sourceTwist_zero]
    exact scalarSource_kfinite R N P C x

@[simp] theorem sourceFlat_zero (x : PlusCore R N P C) :
    (sourceFlat R N P C x).val 0 = scalarSourceEvaluator R N P C x := sourceTwist_zero R N P C x

theorem sourceFlat_value (x : PlusCore R N P C) (s : ℂ) (g : Group R) :
    (sourceFlat R N P C x).val s g =
      Complex.exp (s * (iwasawaLogHeight R g : ℂ)) * scalarSourceEvaluator R N P C x g := rfl

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
