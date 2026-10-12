module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAbsoluteConvergence
public import DedekindZetaZeroFree.Eisenstein.Residues.NormalizedGermIdentification
public import DedekindZetaZeroFree.Eisenstein.Induction.FiniteSpanDescent

@[expose] public section

noncomputable section
open scoped Classical Topology BigOperators
open Filter
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem flat_companion_relation (c : R.A.UnitQuotient →₀ ℂ)
    (hc : ∀ g, ∑ v ∈ c.support, c v * (Q.flat v).val 0 g = 0)
    (s : ℂ) (g : Group R) :
    ∑ v ∈ c.support, c v * (Q.flat v).val s g = 0 := by
  have hmul (v : R.A.UnitQuotient) :=
    KPLiteralChamber.JointProfile.literal_flat_multiplier_formula
      F R.A.zeta12 R.A.primitive_zeta12 Q.K Q.iwasawa (Q.flat v) s g
  calc
    _ = Complex.exp (s * (Real.log
        (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F R.A.zeta12
          R.A.primitive_zeta12
          (KPLiteralChamber.literalIwasawa F R.A.zeta12 R.A.primitive_zeta12
            Q.K Q.iwasawa) g : NNReal) : ℝ)) : ℂ)) *
        (∑ v ∈ c.support, c v * (Q.flat v).val 0 g) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hmul v]
      ring
    _ = 0 := by rw [hc g, mul_zero]

theorem chamber_companion_relation (c : R.A.UnitQuotient →₀ ℂ)
    (hc : ∀ g, ∑ v ∈ c.support, c v * (Q.flat v).val 0 g = 0)
    (s : ℂ) (hs : (1 / 3 : ℝ) < s.re) (g : Group R) :
    ∑ v ∈ c.support, c v *
      KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s g = 0 := by
  unfold KPLiteralRaw.eisenstein
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum]
  · simp_rw [flat_companion_relation c hc s]
    simp
  · intro v hv
    exact (KPLiteralExceptionalResidue.chamberConvergence F R.A.zeta12 R.A.primitive_zeta12
      Q.K Q.iwasawa (Q.flat v) s hs g).mul_left (c v)

theorem scalar_continuation_companion_relation {C : ScalarContinuation R Q}
    (c : R.A.UnitQuotient →₀ ℂ)
    (hc : ∀ g, ∑ v ∈ c.support, c v * (Q.flat v).val 0 g = 0)
    (g : Group R) (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain) :
    (fun s => ∑ v ∈ c.support, c v * C.E v s g) =ᶠ[𝓝[≠] z] (fun _ => 0) := by
  let A : ℂ → ℂ := fun s => ∑ v ∈ c.support, c v * C.E v s g
  have hA : MeromorphicOn A KPContinuation.spectralDomain := by
    have h := MeromorphicOn.sum (s := c.support) (f := fun v s => c v * C.E v s g)
      (fun v _ s hs => (MeromorphicAt.const _ _).mul (C.meromorphic v g s hs))
    convert h using 1
    ext s
    simp only [A, Finset.sum_apply]
  apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
    hA (MeromorphicOn.const 0)
    KPContinuation.spectralDomain_isConnected.isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re)
    KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1, by norm_num⟩ ?_ hz
  intro s hs
  change (∑ v ∈ c.support, c v * C.E v s g) = 0
  simp_rw [C.chamber _ s hs]
  exact chamber_companion_relation c hc s hs g

theorem scalar_residue_companion_relation {C : ScalarContinuation R Q}
    (H : ∀ v, ScalarGerm C v) (c : R.A.UnitQuotient →₀ ℂ)
    (hc : ∀ g, ∑ v ∈ c.support, c v * (Q.flat v).val 0 g = 0)
    (g : Group R) : ∑ v ∈ c.support, c v * (H v).cleared 0 g = 0 := by
  let A : ℂ → ℂ := fun s => ∑ v ∈ c.support, c v * C.E v s g
  have he : A =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => 0) :=
    scalar_continuation_companion_relation c hc g 0
      (by norm_num [KPContinuation.spectralDomain])
  letI := Q.finite_companions
  obtain ⟨r, hr, hb⟩ := finite_positive_lower_bound (fun v => (H v).radius)
    (fun v => (H v).radius_pos)
  have hN : (fun s => ∑ v ∈ c.support, c v * (H v).cleared s g) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun _ => 0) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with s hs hsr hs0
    have hclear (v : R.A.UnitQuotient) : (H v).cleared s g = s * C.E v s g :=
      congrFun ((H v).clears s (Metric.ball_subset_ball (hb v) hsr) hs0) g
    simp_rw [hclear]
    calc
      _ = s * A s := by
        dsimp [A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = 0 := by rw [hs, mul_zero]
  have hcont : ContinuousAt (fun s => ∑ v ∈ c.support, c v * (H v).cleared s g) 0 := by
    have hh : ∀ I : Finset R.A.UnitQuotient,
        ContinuousAt (fun s => ∑ v ∈ I, c v * (H v).cleared s g) 0 := by
      intro I
      induction I using Finset.induction_on with
      | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) 0)
      | @insert v I hv ih =>
        simp only [Finset.sum_insert hv]
        exact (continuousAt_const.mul ((H v).analytic g 0
          (Metric.mem_ball_self (H v).radius_pos)).continuousAt).add ih
    exact hh c.support
  exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hN.symm)

theorem finite_source_residue_map {C : ScalarContinuation R Q}
    (H : ∀ v, ScalarGerm C v) :
    ∃ L : flatScalarStage Q →ₗ[ℂ] Functions R,
      ∀ v, L ⟨(Q.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩ =
        ((H v).cleared 0 : Functions R) := by
  apply flatSource_span_descent Q (fun v => ((H v).cleared 0 : Functions R))
  intro c hc
  funext g
  simpa using scalar_residue_companion_relation H c hc g

def finiteSourceResidue {C : ScalarContinuation R Q} (H : ∀ v, ScalarGerm C v) :
    flatScalarStage Q →ₗ[ℂ] Functions R := Classical.choose (finite_source_residue_map H)

theorem finiteSourceResidue_companion {C : ScalarContinuation R Q}
    (H : ∀ v, ScalarGerm C v) (v : R.A.UnitQuotient) :
    finiteSourceResidue H ⟨(Q.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩ =
      ((H v).cleared 0 : Functions R) :=
  Classical.choose_spec (finite_source_residue_map H) v

theorem finiteSourceResidue_combination {C : ScalarContinuation R Q}
    (H : ∀ v, ScalarGerm C v) (c : R.A.UnitQuotient →₀ ℂ) :
    finiteSourceResidue H
      (∑ v ∈ c.support, c v •
        (⟨(Q.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩ : flatScalarStage Q)) =
      ∑ v ∈ c.support, c v • ((H v).cleared 0 : Functions R) := by
  simp only [map_sum, map_smul, finiteSourceResidue_companion]

theorem finiteSourceResidue_range {C : ScalarContinuation R Q}
    (H : ∀ v, ScalarGerm C v) :
    (finiteSourceResidue H).range =
      Submodule.span ℂ (Set.range (fun v => ((H v).cleared 0 : Functions R))) := by
  let A := Finsupp.linearCombination ℂ (fun v => (Q.flat v).val 0)
  let B := Finsupp.linearCombination ℂ (fun v => ((H v).cleared 0 : Functions R))
  have hrange : A.range = flatScalarStage Q := by rw [Finsupp.range_linearCombination]; rfl
  have hcomb (c : R.A.UnitQuotient →₀ ℂ) :
      finiteSourceResidue H ⟨A c, hrange ▸ LinearMap.mem_range_self A c⟩ = B c := by
    have he : (⟨A c, hrange ▸ LinearMap.mem_range_self A c⟩ : flatScalarStage Q) =
        ∑ v ∈ c.support, c v •
          (⟨(Q.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩ : flatScalarStage Q) := by
      apply Subtype.ext
      simp [A, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [he, finiteSourceResidue_combination]
    simp [B, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [← Finsupp.range_linearCombination (R := ℂ) (v := fun v => ((H v).cleared 0 : Functions R))]
  change (finiteSourceResidue H).range = B.range
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x.val ∈ A.range := hrange.symm ▸ x.property
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    have he : (⟨A c, hrange ▸ LinearMap.mem_range_self A c⟩ : flatScalarStage Q) = x :=
      Subtype.ext hc
    rw [← he, hcomb]
  · rintro ⟨c, rfl⟩
    exact ⟨⟨A c, hrange ▸ LinearMap.mem_range_self A c⟩, hcomb c⟩

end DedekindZetaZeroFree.SharedSource

end
