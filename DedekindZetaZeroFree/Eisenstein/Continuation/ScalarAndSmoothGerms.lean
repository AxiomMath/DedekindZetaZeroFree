module

public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.EisensteinSmoothGerms
open MomentSources
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure ScalarContinuation (R : PrincipalMellin.ActualRecipe S η)
    (Q : AdmissibleFlatSources R) where
  E : R.A.UnitQuotient → ℂ → C(Group R, ℂ)
  meromorphic : ∀ v g, MeromorphicOn (fun s => E v s g) KPContinuation.spectralDomain
  chamber : ∀ v s, (1 / 3 : ℝ) < s.re → ∀ g,
    E v s g = KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s g

structure ScalarGerm {R : PrincipalMellin.ActualRecipe S η}
    {Q : AdmissibleFlatSources R} (C : ScalarContinuation R Q) (v : R.A.UnitQuotient) where
  radius : ℝ
  radius_pos : 0 < radius
  cleared : ℂ → C(Group R, ℂ)
  clears : ∀ s, s ∈ Metric.ball (0 : ℂ) radius → s ≠ 0 →
    (cleared s : Functions R) = s • (C.E v s : Functions R)
  analytic : ∀ g, AnalyticOnNhd ℂ (fun s => cleared s g) (Metric.ball (0 : ℂ) radius)

structure IndividualSmoothGerm {R : PrincipalMellin.ActualRecipe S η}
    {Q : AdmissibleFlatSources R} (C : ScalarContinuation R Q) (v : R.A.UnitQuotient) where
  radius : ℝ
  radius_pos : 0 < radius
  cleared : ℂ → Functions R
  clears : ∀ s, s ∈ Metric.ball (0 : ℂ) radius → s ≠ 0 →
    cleared s = s • (C.E v s : Functions R)
  smooth : ∀ s, s ∈ Metric.ball (0 : ℂ) radius →
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (cleared s)
  analytic : ∀ g, AnalyticOnNhd ℂ (fun s => cleared s g) (Metric.ball (0 : ℂ) radius)
  coefficients : ℕ → Functions R
  coefficients_smooth : ∀ n,
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (coefficients n)
  compact_smooth_taylor : ∀ g (m : ℕ) (K : Set (KPGlobalResidualConstruction.ArchCoordinates F)),
    IsCompact K → K ⊆ KPGlobalResidualConstruction.archDomain F →
    ∀ r : ℝ, 0 < r → r < radius → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ M : ℕ, N ≤ M → ∀ s : ℂ, ‖s‖ ≤ r → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun x =>
        cleared s (g * KPGlobalResidualConstruction.archChart F R.A.zeta12 R.A.primitive_zeta12 x) -
        ∑ n ∈ Finset.range M, s ^ n * coefficients n
          (g * KPGlobalResidualConstruction.archChart F R.A.zeta12 R.A.primitive_zeta12 x)) x‖ < ε

theorem finite_positive_lower_bound {ι : Type*} [Finite ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ r i := by
  classical
  letI := Fintype.ofFinite ι
  have h : ∀ I : Finset ι, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ I, ε ≤ r i := by
    intro I
    induction I using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a I ha ih =>
      obtain ⟨ε, hε, hb⟩ := ih
      refine ⟨min ε (r a), lt_min hε (hr a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb i hi)
  obtain ⟨ε, hε, hb⟩ := h Finset.univ
  exact ⟨ε, hε, fun i => hb i (Finset.mem_univ i)⟩

theorem common_radius {R : PrincipalMellin.ActualRecipe S η}
    {Q : AdmissibleFlatSources R} {C : ScalarContinuation R Q}
    (G : ∀ v, IndividualSmoothGerm C v) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ KPContinuation.spectralDomain ∧
      ∀ v, ρ ≤ (G v).radius := by
  letI := Q.finite_companions
  obtain ⟨ε, hε, hb⟩ := finite_positive_lower_bound (fun v => (G v).radius)
    (fun v => (G v).radius_pos)
  refine ⟨min ε (1 / 6), lt_min hε (by norm_num), ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans
      KPContinuation.exceptionalBall_subset_spectralDomain
  · intro v
    exact (min_le_left _ _).trans (hb v)
end DedekindZetaZeroFree.EisensteinSmoothGerms

end
