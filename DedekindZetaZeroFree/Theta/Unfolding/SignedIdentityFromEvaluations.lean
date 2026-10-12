module

public import DedekindZetaZeroFree.Theta.Unfolding.ReflectedFrequencyExpansion

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion.SignedUnfoldingSub7
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem dyadic_row_factorization (u : R.A.Rˣ) (h d : R.A.Exterior)
    (hh : Powerful h.val) (hd : Squarefree d.val) (hcop : h.val ⊔ d.val = ⊤) :
    ∃ D : ThetaBranch.RowFactorization R.A R.probe.allowed
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d), D.h = h ∧ D.d = d := by
  let m := ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d
  let I := ExteriorIdealEuler.mul h d
  have hm : R.A.Generates I m.val := by
    constructor
    · exact m.property
    · change Ideal.span {((u : R.A.R) * R.probe.coefficients.generator h *
        R.probe.coefficients.generator d)} = _
      rw [← Ideal.span_singleton_mul_span_singleton]
      have hu : Ideal.span {((u : R.A.R) * R.probe.coefficients.generator h)} =
          Ideal.span {R.probe.coefficients.generator h} :=
        Ideal.span_singleton_eq_span_singleton.mpr
          (associated_unit_mul_left _ _ (Units.isUnit u))
      rw [hu, (R.probe.coefficients.generates h).2, (R.probe.coefficients.generates d).2]
      exact (Ideal.map_mul _ _ _).symm
  have hI : ActualRowTransfer.rowIdeal R.A m = I := by
    apply R.A.exteriorIdealEquiv.injective
    apply Subtype.ext
    rw [R.A.exteriorIdealEquiv_apply, R.A.exteriorIdealEquiv_apply]
    exact (ActualRowTransfer.span_rowIdeal R.A m).symm.trans hm.2
  obtain ⟨eps, heps⟩ := ActualRowTransfer.exists_unit_mul_generator R.A R.probe.coefficients m
  rw [hI] at heps
  let epsilon : R.A.U := R.A.unitEquiv.symm eps
  have hrow : ThetaReflectionData.rowUnit R.A m = epsilon.val * R.probe.allowed.generator I := by
    apply Units.ext
    change (m.val : F) = (epsilon.val : F) * (R.probe.allowed.generator I : F)
    rw [R.probe.sameGenerator]
    have hv : (epsilon.val : F) = ((eps : R.A.R) : F) := by
      simp [epsilon, SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
    rw [hv, heps]
    exact map_mul (algebraMap R.A.R F) _ _
  exact ⟨⟨I, h, d, hh, hd, hcop, rfl, hm, epsilon, hrow⟩, rfl, rfl⟩

theorem forward_of_evaluation {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (u : R.A.Rˣ) (h d : R.A.Exterior)
    (Z : ℝ) (hZ : 0 < Z)
    (he : HasSum (orbitTerm R C (rowClass R u)
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z hZ)
      (ThetaReflectionData.forwardB R.A R.probe.coefficients
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z)) :
    ThetaReflectionData.forwardB R.A R.probe.coefficients
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z =
      smoothedTheta R C.transport C.sources C.realization C.packet (rowClass R u)
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z -
      mainTerm R C.transport C.sources C.realization C.packet (rowClass R u)
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z := by
  exact he.unique (hx (rowClass R u) _ true Z hZ).2.2.2.1

theorem reflected_term_eq_of_coefficient {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (Z : ℝ)
    (hc : ∀ x : Fˣ, exteriorDigitCoefficient R C m x =
      ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D x)
    (ξ : ThetaReflectionData.Frequency R.A) :
    actualReflectedTerm R C v m Z ξ = numericalReflectedTerm R C v m D Z ξ := by
  have hmk : (QuotientGroup.mk (Quotient.out ξ) : ThetaReflectionData.Frequency R.A) = ξ :=
    Quotient.out_eq ξ
  have hchar : ThetaExpansion.BranchCoordinateSeries.sourceFrequencyCharacter R (Characters.psi R)
      (Characters.L R) (Characters.compatible R) v ξ = Characters.L R v (Quotient.out ξ) := by
    exact (congrArg (ThetaExpansion.BranchCoordinateSeries.sourceFrequencyCharacter R (Characters.psi R)
      (Characters.L R) (Characters.compatible R) v) hmk).symm
  have hext : ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R)
      m D (Quotient.out ξ) =
      ThetaBranch.exteriorFrequencyCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D ξ := by
    conv_rhs => rw [← hmk]
    rfl
  simp only [actualReflectedTerm, numericalReflectedTerm, hc, hext, hchar]

theorem reverse_of_evaluation {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (Z : ℝ) (hZ : 0 < Z)
    (hc : ∀ x : Fˣ, exteriorDigitCoefficient R C m x =
      ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D x)
    (he : HasSum (actualReflectedTerm R C v m Z)
      (∑' i : OrbitIndex R, orbitTerm R C v m false Z hZ i)) :
    RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps R.σ
      (Characters.psi R) (Characters.L R v) (C.realization.H C.packet v) D.h D.d Z =
      smoothedTheta R C.transport C.sources C.realization C.packet v m false Z -
        mainTerm R C.transport C.sources C.realization C.packet v m false Z := by
  calc
    _ = ∑' ξ, numericalReflectedTerm R C v m D Z ξ :=
      (numerical_frequency_dictionary R C v m D Z hZ).2.symm
    _ = ∑' ξ, actualReflectedTerm R C v m Z ξ :=
      tsum_congr (fun ξ => (reflected_term_eq_of_coefficient R C v m D Z hc ξ).symm)
    _ = ∑' i : OrbitIndex R, orbitTerm R C v m false Z hZ i := he.tsum_eq
    _ = _ := (hx v m false Z hZ).2.2.2.1.tsum_eq

def signedUnfolding_of_analytic_evaluations {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C)
    (hf : ∀ (u : R.A.Rˣ) (h d : R.A.Exterior),
      Powerful h.val → Squarefree d.val → h.val ⊔ d.val = ⊤ →
      ∀ (Z : ℝ) (hZ : 0 < Z),
      HasSum (orbitTerm R C (rowClass R u)
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z hZ)
        (ThetaReflectionData.forwardB R.A R.probe.coefficients
          (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z))
    (hc : ∀ (m : ThetaReflectionData.Row R.A)
      (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (x : Fˣ),
      exteriorDigitCoefficient R C m x =
        ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D x)
    (hr : ∀ (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
      (Z : ℝ) (hZ : 0 < Z), HasSum (actualReflectedTerm R C v m Z)
        (∑' i : OrbitIndex R, orbitTerm R C v m false Z hZ i)) :
    SignedUnfolding R C.transport C.sources C.realization C.packet := by
  let Ur := (PrincipalMellinGrowth.exists_sixth_unit_representatives R.A).choose
  have hUr := (PrincipalMellinGrowth.exists_sixth_unit_representatives R.A).choose_spec
  refine {
    Ur := Ur
    units := hUr
    row_class := rowClass R
    forward_smoothing_integrable := ?_
    reverse_smoothing_integrable := ?_
    forward_unfolding := ?_
    reverse_unfolding := ?_
  }
  · intro u hu h d hh hd hcop Z hZ
    exact (hx (rowClass R u) _ true Z hZ).2.2.2.2
  · intro u hu h d hh hd hcop Z hZ
    exact (hx (rowClass R u) _ false Z hZ).2.2.2.2
  · intro u hu h d hh hd hcop Z hZ
    exact forward_of_evaluation R C hx u h d Z hZ (hf u h d hh hd hcop Z hZ)
  · intro u hu h d hh hd hcop Z hZ
    obtain ⟨D, hDh, hDd⟩ := dyadic_row_factorization R u h d hh hd hcop
    have he := reverse_of_evaluation R C hx (rowClass R u)
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) D Z hZ
      (hc _ D) (hr _ _ Z hZ)
    simpa only [hDh, hDd] using he

end DedekindZetaZeroFree.OrbitExpansion.SignedUnfoldingSub7

end
