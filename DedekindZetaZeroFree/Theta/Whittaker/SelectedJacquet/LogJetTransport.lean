module

public import DedekindZetaZeroFree.Adeles.Quotients.ComplexRadialCoordinates
public import DedekindZetaZeroFree.Theta.Profiles.RadialJetsAndLocalNorms

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory KPCplxRotatedRapidDecay
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def selectedComplexWeyl (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient)
    (w : InfinitePlace F) (z : ℂˣ) : ℂ :=
  ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place w)).symm.toMonoidHom z)

theorem archJet_complex_transport (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient)
    (w : InfinitePlace F) (j : ℕ) (z : w.Completionˣ) :
    ThetaExpansion.localWeylArchJet R C v w j z =
      ((InfinitePlace.nrComplexPlaces F : ℝ)⁻¹ : ℂ) ^ j *
        ((logarithmicDerivative^[j]) (selectedComplexWeyl R C v w))
          (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z) := by
  have hmap (z : w.Completionˣ) :
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (R.A.complex_place w)).symm.toMonoidHom
        (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z) = z := by
    apply Units.ext
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place w)).symm
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w))
        (z : w.Completion)) = (z : w.Completion)
    exact RingEquiv.symm_apply_apply _ _
  have heq (t : ℝ) :
      ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
        (z * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w) =
      selectedComplexWeyl R C v w
        (logarithmicRadialFlow (t / (InfinitePlace.nrComplexPlaces F : ℝ))
          (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z)) := by
    rw [← SArithmeticData.radialSection_complex_flow R.A w t z]
    unfold selectedComplexWeyl
    rw [hmap]
  unfold ThetaExpansion.localWeylArchJet
  simp_rw [heq]
  exact iteratedDeriv_logarithmicRadialFlow_div _ _ j _

lemma archJet_norm_le_complex_jet (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) (v : R.A.UnitQuotient)
    (w : InfinitePlace F) (j : ℕ) (z : w.Completionˣ) :
    ‖ThetaExpansion.localWeylArchJet R C v w j z‖ ≤
      ‖((logarithmicDerivative^[j]) (selectedComplexWeyl R C v w))
        (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z)‖ := by
  have hr : (1 : ℝ) ≤ InfinitePlace.nrComplexPlaces F := by
    exact_mod_cast R.A.nrComplexPlaces_pos
  rw [archJet_complex_transport, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith :
      0 ≤ (InfinitePlace.nrComplexPlaces F : ℝ))]
  have hi : (InfinitePlace.nrComplexPlaces F : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith : 0 < (InfinitePlace.nrComplexPlaces F : ℝ))).mpr hr
  have hp : (InfinitePlace.nrComplexPlaces F : ℝ)⁻¹ ^ j ≤ 1 :=
    pow_le_one₀ (inv_nonneg.mpr (by linarith)) hi
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _)

end DedekindZetaZeroFree.SheetRescaling

end
