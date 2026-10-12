module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem uniform_section_add (A : SArithmeticData F) (s t : ℝ) :
    A.radialSection (Real.exp (s + t)) (Real.exp_pos _) =
      A.radialSection (Real.exp s) (Real.exp_pos _) *
        A.radialSection (Real.exp t) (Real.exp_pos _) := by
  simpa only [Real.exp_add] using A.radialSection_mul
    (Real.exp s) (Real.exp t) (Real.exp_pos s) (Real.exp_pos t)

theorem uniform_section_sixth (A : SArithmeticData F) (t : ℝ) :
    A.radialSection (Real.exp (t / 6)) (Real.exp_pos _) ^ 6 =
      A.radialSection (Real.exp t) (Real.exp_pos _) := by
  have h (n : ℕ) : A.radialSection (Real.exp (t / 6)) (Real.exp_pos _) ^ n =
      A.radialSection (Real.exp ((n : ℝ) * (t / 6))) (Real.exp_pos _) := by
    induction n with
    | zero => simpa using A.radialSection_one.symm
    | succ n ih =>
      rw [pow_succ, ih, ← uniform_section_add]
      congr 1
      push_cast
      ring
  convert h 6 using 1 <;> congr 1 <;> norm_num <;> ring

theorem uniform_section_class (A : SArithmeticData F) (t : ℝ) (y : A.G) :
    QuotientGroup.mk' A.sixthPowers
        (y * A.radialSection (Real.exp t) (Real.exp_pos t)) =
      QuotientGroup.mk' A.sixthPowers y := by
  have hmem : A.radialSection (Real.exp t) (Real.exp_pos t) ∈ A.sixthPowers :=
    ⟨A.radialSection (Real.exp (t / 6)) (Real.exp_pos _), uniform_section_sixth A t⟩
  have hk : QuotientGroup.mk' A.sixthPowers (A.radialSection (Real.exp t) (Real.exp_pos t)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_mul, hk]
  exact mul_one (QuotientGroup.mk' A.sixthPowers y)

theorem uniform_section_branch (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient) (t : ℝ) :
    P.branch v (R.A.radialSection (Real.exp t) (Real.exp_pos t)) = 1 := by
  rw [P.branch_exact v _ (by intro p; exact (P.cutoff p).one_mem)]
  apply Finset.prod_eq_one
  intro w _
  have hpos := Real.rpow_pos_of_pos (Real.exp_pos t)
    (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)))
  have he : InfinitePlace.Completion.extensionEmbedding w
      ((R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w : w.Completion) =
      ((Real.exp t ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℝ) : ℂ) := by
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm _) = _
    exact RingEquiv.apply_symm_apply _ _
  rw [he]
  have hang : DHCubic.angular
      (((Real.exp t ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)))) : ℝ) : ℂ) = 1 := by
    unfold DHCubic.angular
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    exact div_self (Complex.ofReal_ne_zero.mpr hpos.ne')
  rw [hang, one_zpow]

theorem branch_uniform_radial (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient)
    (t : ℝ) (y : R.A.G) :
    P.branch v (y * R.A.radialSection (Real.exp t) (Real.exp_pos t)) = P.branch v y := by
  rw [map_mul, uniform_section_branch, mul_one]

def sheetPhase (R : PrincipalMellin.ActualRecipe S η) (κ : R.A.V) (y : R.A.G) : ℂ :=
  (if κ * (QuotientGroup.mk' R.A.sixthPowers y)⁻¹ ∈ R.probe.correction.B then 1 else 0) *
    (R.σ ((R.probe.correction.H κ (QuotientGroup.mk' R.A.sixthPowers y) : Fˣ) : F) ^ 2)⁻¹

theorem sheetPhase_uniform_radial (R : PrincipalMellin.ActualRecipe S η)
    (κ : R.A.V) (t : ℝ) (y : R.A.G) :
    sheetPhase R κ (y * R.A.radialSection (Real.exp t) (Real.exp_pos t)) = sheetPhase R κ y := by
  simp only [sheetPhase, uniform_section_class]

theorem finiteClass_measurable (R : PrincipalMellin.ActualRecipe S η) (f : R.A.V → ℂ) :
    Measurable (fun y : R.A.G => f (QuotientGroup.mk' R.A.sixthPowers y)) := by
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (R.A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F)ˣ :=
    fun p => Units.isEmbedding_val₀.secondCountableTopology
  have hpow : MeasurableSet (R.A.sixthPowers : Set R.A.G) := by
    have hc : Continuous (fun y : R.A.G => y ^ 6) := continuous_id.pow 6
    obtain ⟨K, hK, hU⟩ := isSigmaCompact_range hc
    change MeasurableSet (Set.range (fun y : R.A.G => y ^ 6))
    rw [← hU]
    exact MeasurableSet.iUnion (fun i => (hK i).measurableSet)
  letI : MeasurableSingletonClass R.A.V := by
    constructor
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R.A.sixthPowers q
    apply measurableSet_quotient.mpr
    have he : (Quotient.mk'' ⁻¹' {QuotientGroup.mk' R.A.sixthPowers y} : Set R.A.G) =
        (fun z => z / y) ⁻¹' (R.A.sixthPowers : Set R.A.G) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact QuotientGroup.eq_iff_div_mem
    rw [he]
    exact hpow.preimage (continuous_id.div' continuous_const).measurable
  letI := R.A.V_finite
  have h : Measurable f := measurable_of_finite _
  exact h.comp measurable_quotient_mk''

theorem sheetPhase_measurable (R : PrincipalMellin.ActualRecipe S η) (κ : R.A.V) :
    Measurable (sheetPhase R κ) := by
  unfold sheetPhase
  exact finiteClass_measurable R (fun q =>
    (if κ * q⁻¹ ∈ R.probe.correction.B then (1 : ℂ) else 0) *
      (R.σ ((R.probe.correction.H κ q : Fˣ) : F) ^ 2)⁻¹)

end DedekindZetaZeroFree.SheetRescaling

end
