module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScatteringChamberAnalyticity
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.LocalMeromorphicContinuation
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.Chamber
open MomentSources
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming literal_two_cells → literal_two_cells
open _root_.DedekindZetaZeroFree.KPLiteralChamberWeight renaming standard_integrable → standard_integrable
open _root_.DedekindZetaZeroFree.KPLiteralScatteringGlobalContinuation renaming exponential_integral_differentiable → exponential_integral_differentiable
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}

theorem upper_analyticOnNhd (Q : AdmissibleFlatSources R) (v : R.A.UnitQuotient)
    (g : Group R) :
    AnalyticOnNhd ℂ (fun s => upper R Q.dq
      (KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s) g)
      {s : ℂ | (1 / 3 : ℝ) < s.re} := by
  let A : ℂ → ℂ := fun s => ∫ x : KPAdeles F, (Q.flat v).val s
    (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12
      (KPChamberBruhatTwoCells.rationalWeyl F) *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)
    ∂KPAdditiveHaar.adelicMeasure F
  have he (s : ℂ) : A s = ∫ x : KPAdeles F, (Q.flat v).val s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)
      ∂KPAdditiveHaar.adelicMeasure F := by
    unfold A
    congr 1
    funext x
    rw [KPLiteralExceptionalResidue.rationalLift_eq_constructed, mul_assoc]
    have hw := KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.section_signed_weyl
      F R.A.zeta12 R.A.primitive_zeta12 s
      (KPLiteralChamber.literalSource F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g)
    simpa only [KPLiteralChamber.literalSource, KPRationalAdelicSplitting.pglW, mul_assoc] using hw
  let arg : KPAdeles F → Group R := fun x =>
    KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g
  let p := fun x => KPLiteralChamber.iwasawaTriple F R.A.zeta12
    R.A.primitive_zeta12 Q.K Q.iwasawa (arg x)
  let l : KPAdeles F → ℝ := fun x => Real.log
    (((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 (p x).1 : NNReal) : ℝ))
  let c : KPAdeles F → ℂ := fun x => (Q.flat v).val 0 ((p x).1.val * (p x).2.2.val)
  have hf (s : ℂ) (x : KPAdeles F) :
      (Q.flat v).val s (arg x) = Complex.exp (s * (l x : ℂ)) * c x := by
    rw [← KPLiteralChamber.compactExtension_eq_flat F R.A.zeta12 R.A.primitive_zeta12
      Q.K Q.iwasawa (Q.flat v) s (arg x)]
    rfl
  have hint (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) :
      Integrable (fun x => Complex.exp (s * (l x : ℂ)) * c x)
        (KPAdditiveHaar.adelicMeasure F) := by
    simpa only [← hf] using standard_integrable F R.A.zeta12 R.A.primitive_zeta12
      Q.K Q.iwasawa (Q.flat v) s hs g
  have hA : AnalyticOnNhd ℂ A {s : ℂ | (1 / 3 : ℝ) < s.re} := by
    have hd := exponential_integral_differentiable (KPAdditiveHaar.adelicMeasure F) l c
      ((1 : ℝ) / 3) hint
    have heq : A = (fun s => ∫ x, Complex.exp (s * (l x : ℂ)) * c x
        ∂KPAdditiveHaar.adelicMeasure F) := by
      funext s
      rw [he]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => hf s x)
    rw [heq]
    exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hflat : AnalyticOnNhd ℂ (fun s => (Q.flat v).val s g) Set.univ :=
    (EisensteinFourierContinuation.flat_entire R Q v g).differentiableOn.analyticOnNhd isOpen_univ
  apply (hflat.mono (Set.subset_univ _)).add hA |>.congr
    (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have hi := upper_integrable F R.A.zeta12 R.A.primitive_zeta12
    Q.K Q.iwasawa (Q.flat v) Q.dq Q.quotientHaar s hs g
  have ht := literal_two_cells F R.A.zeta12 R.A.primitive_zeta12
    Q.K Q.iwasawa Q.dq Q.quotientHaar (Q.flat v) s hs g
  have hmass : Q.dq.real Set.univ = 1 := by simp [Measure.real, Q.probability]
  rw [hmass, Complex.ofReal_one, one_mul] at ht
  change (Q.flat v).val s g + A s = _
  rw [he]
  exact ht.symm

end DedekindZetaZeroFree.CompactPeriodAnalyticity.Chamber

end
