module

public import DedekindZetaZeroFree.Moments.Reflected.ProbeExponentBound
public import DedekindZetaZeroFree.Moments.Probes.MixedPhaseQuadraticHeckeFamily
public import DedekindZetaZeroFree.Arithmetic.Units.SixthPowerRepresentatives
public import DedekindZetaZeroFree.CharacterSums.Gauss.CompatibleCharactersAndSquarefreeReciprocity

@[expose] public section

namespace DedekindZetaZeroFree.MomentSources
open PrincipalMellin
open Filter Asymptotics
variable {F : Type} [Field F] [NumberField F]

structure SelectedMomentSource
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) where
  Ur : Finset R.A.Rˣ
  units : ActualRowTransfer.UnitRepresentatives R.A Ur
  psi : ∀ p : ThetaBranch.ExteriorPrime R.A, AddChar (DHCubic.Residue F p.val) ℂ
  primitive : ∀ p, (psi p).IsPrimitive
  L : R.A.UnitQuotient → Fˣ →* ℂ
  norm_one : ∀ v x, ‖L v x‖ = 1
  characters_compatible : PrincipalMellinSource.SourceCharacterCompatibility R psi L
  H : R.A.UnitQuotient → R.A.V → ℝ → ℂ
  profiles : RMSeparatedExpansion.FiniteProfileFamily R.A H
  reflected_domination : ∀ u ∈ Ur, ∀ h d : R.A.Exterior,
    Powerful h.val → Squarefree d.val → h.val ⊔ d.val = ⊤ →
    ∀ Z : ℝ, 0 < Z → ∃ v : R.A.UnitQuotient,
      ‖ThetaReflectionData.forwardB R.A R.probe.coefficients
        (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z‖ ^ 2 ≤
      ‖RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps
        R.σ psi (L v) (H v) h d Z‖ ^ 2

private theorem actual_allowed_section
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (R : ActualRecipe S η) :
    ActualRowTransfer.AllowedSection R.A R.probe.coefficients R.probe.correction.B := by
  intro I
  have he : R.probe.allowed.generator I = ThetaReflectionData.rowUnit R.A
      ⟨R.probe.coefficients.generator I, (R.probe.coefficients.generates I).1⟩ := by
    apply Units.ext
    exact R.probe.sameGenerator I
  have h := R.probe.allowed.allowed I
  rw [R.probe.sameComplement, he] at h
  exact h

theorem reflectedMoment_of_dyadic
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (U : Finset R.A.Rˣ)
    (hU : ActualRowTransfer.UnitRepresentatives R.A U)
    (hdyadic : ∀ Cstar : ℝ, 0 < Cstar →
      ActualRowTransfer.DyadicBound R.A R.probe.coefficients U
        (1033 / 1000 : ℝ) Cstar) :
    PoissonProbe.BalancedReflectedMomentConclusion R.A R.probe.coefficients := by
  intro Kshape hKshape Cstar hCstar δ hδ
  obtain ⟨K, hK, hbound⟩ := ActualRowTransfer.balancedRowMass_bound_of_dyadic
    R.A R.probe.coefficients R.classKilled R.probe.correction.H
    R.probe.correction.B R.probe.correction.B_complement
    (actual_allowed_section S η R) R.probe.sixthUnitCharacters U hU
    Kshape hKshape (1033 / 1000 : ℝ) Cstar δ (by norm_num) hCstar hδ
    (hdyadic Cstar hCstar)
  refine ⟨K, hK.le, ?_⟩
  intro Z hZ rows hrows
  exact hbound Z (by linarith) rows hrows

noncomputable section
open scoped Classical NumberField

private theorem mask_reindex (A : SArithmeticData F) (P Q : ℝ)
    (f : A.Exterior → A.Exterior → ℝ) :
    (∑' h : A.Exterior, ∑' d : A.Exterior,
      if Powerful h.val ∧ Squarefree d.val ∧ h.val ⊔ d.val = ⊤ ∧
        P ≤ A.exteriorNorm h ∧ A.exteriorNorm h < 2 * P ∧
        Q ≤ A.exteriorNorm d ∧ A.exteriorNorm d < 2 * Q then f h d else 0) =
    ∑' h : exteriorPowerfulDyad A.cS P,
      ∑' d : RMRetainedAggregation.rowDyad A h.val Q, f h.val d.val.val := by
  change _ = ∑' h : exteriorPowerfulDyad A.cS P,
    (fun h : A.Exterior => ∑' d : RMRetainedAggregation.rowDyad A h Q, f h d.val.val) h.val
  rw [tsum_subtype (exteriorPowerfulDyad A.cS P)
    (fun h : A.Exterior => ∑' d : RMRetainedAggregation.rowDyad A h Q, f h d.val.val)]
  apply tsum_congr
  intro h
  by_cases hh : h ∈ exteriorPowerfulDyad A.cS P
  · rw [Set.indicator_of_mem hh]
    rw [tsum_subtype (RMRetainedAggregation.rowDyad A h Q)
      (fun d : ExteriorSquarefreeIdeal A.cS => f h d.val)]
    simp only [RMRetainedAggregation.rowDyad, Set.indicator_apply, Set.mem_setOf_eq]
    change _ = ∑' d : {d : A.Exterior | Squarefree d.val},
      (fun d : A.Exterior =>
        if Q ≤ A.exteriorNorm d ∧ A.exteriorNorm d < 2 * Q ∧ d.val ⊔ h.val = ⊤
        then f h d else 0) d.val
    rw [tsum_subtype {d : A.Exterior | Squarefree d.val}
      (fun d : A.Exterior =>
        if Q ≤ A.exteriorNorm d ∧ A.exteriorNorm d < 2 * Q ∧ d.val ⊔ h.val = ⊤
        then f h d else 0)]
    apply tsum_congr
    intro d
    by_cases hd : Squarefree d.val
    · rw [Set.indicator_of_mem hd]
      have hhh : Powerful h.val ∧ P ≤ A.exteriorNorm h ∧
          A.exteriorNorm h < 2 * P := hh
      simp only [hhh.1, hhh.2.1, hhh.2.2, hd, true_and, and_true]
      congr 1
      simp [sup_comm, and_comm, and_left_comm, and_assoc]
    · rw [Set.indicator_of_notMem hd]
      simp [hd]
  · rw [Set.indicator_of_notMem hh]
    have hz : ∀ d : A.Exterior,
        (if Powerful h.val ∧ Squarefree d.val ∧ h.val ⊔ d.val = ⊤ ∧
          P ≤ A.exteriorNorm h ∧ A.exteriorNorm h < 2 * P ∧
          Q ≤ A.exteriorNorm d ∧ A.exteriorNorm d < 2 * Q then f h d else 0) = 0 := by
      intro d
      have hhh : ¬ (Powerful h.val ∧ P ≤ A.exteriorNorm h ∧
          A.exteriorNorm h < 2 * P) := hh
      split_ifs with hm
      · exact False.elim (hhh ⟨hm.1, hm.2.2.2.1, hm.2.2.2.2.1⟩)
      · rfl
    simp only [hz, tsum_zero]

theorem dyadicBound_of_source
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (M : SelectedMomentSource R)
    (Cstar : ℝ) (hCstar : 0 < Cstar) :
    ActualRowTransfer.DyadicBound R.A R.probe.coefficients M.Ur
      (1033 / 1000 : ℝ) Cstar := by
  obtain ⟨𝓕, h𝓕⟩ := PrincipalMellinGrowth.actual_quadratic_family_exists R
  letI := RMTailCutoff.Reindex.unit_finite R.A
  letI := Fintype.ofFinite R.A.UnitQuotient
  intro δ hδ
  obtain ⟨K, hK, hb⟩ := ReflectedMoment.separated_mean_square_bound
    R.A R.probe.allowed R.probe.unitReps R.σ M.psi M.primitive M.L M.norm_one M.H M.profiles 𝓕 h𝓕
    (1033 / 1000 : ℝ) Cstar δ (by norm_num) hCstar hδ
  refine ⟨(Fintype.card R.A.UnitQuotient + 1) * K, by positivity, ?_⟩
  intro Z P Q hZ hP hQ hPQ u hu
  rw [mask_reindex]
  letI := (exteriorPowerfulDyad_finite R.A.cS P).fintype
  letI (h : exteriorPowerfulDyad R.A.cS P) :=
    (RMRetainedAggregation.rowDyad_finite R.A h.val Q).fintype
  simp only [tsum_fintype]
  calc
    _ ≤ ∑ h : exteriorPowerfulDyad R.A.cS P,
        ∑ d : RMRetainedAggregation.rowDyad R.A h.val Q,
          ∑ v : R.A.UnitQuotient,
            ‖RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps
              R.σ M.psi (M.L v) (M.H v) h.val d.val.val Z‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro d _
      obtain ⟨v, hv⟩ := M.reflected_domination u hu h.val d.val.val h.property.1
        d.val.property (by simpa only [sup_comm] using d.property.2.2) Z (by linarith)
      exact hv.trans (Finset.single_le_sum (fun (w : R.A.UnitQuotient) _ =>
        sq_nonneg ‖RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps
          R.σ M.psi (M.L w) (M.H w) h.val d.val.val Z‖) (Finset.mem_univ v))
    _ = ∑ v : R.A.UnitQuotient,
        ReflectedMoment.separatedSquareMass R.A R.probe.allowed R.probe.unitReps
          R.σ M.psi (M.L v) (M.H v) Z P Q := by
      simp only [ReflectedMoment.separatedSquareMass, tsum_fintype]
      calc
        _ = ∑ h : exteriorPowerfulDyad R.A.cS P, ∑ v : R.A.UnitQuotient,
            ∑ d : RMRetainedAggregation.rowDyad R.A h.val Q,
              ‖RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps
                R.σ M.psi (M.L v) (M.H v) h.val d.val.val Z‖ ^ 2 :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ ≤ ∑ _v : R.A.UnitQuotient,
        K * Z ^ δ * Real.sqrt P * (Q + Q ^ 2 * P / Z) := by
      exact Finset.sum_le_sum (fun v _ => hb v Z P Q hZ hP hQ hPQ)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hscale : 0 ≤ K * Z ^ δ * Real.sqrt P * (Q + Q ^ 2 * P / Z) := by
        positivity
      nlinarith

theorem moment_of_source
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : ActualRecipe S η) (M : SelectedMomentSource R) :
    PoissonProbe.BalancedReflectedMomentConclusion R.A R.probe.coefficients :=
  reflectedMoment_of_dyadic R M.Ur M.units (dyadicBound_of_source R M)

end
end DedekindZetaZeroFree.MomentSources
