module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteLocalProjectors
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.DiagonalProjector
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.LocalDiagonalGeometry
public import DedekindZetaZeroFree.Theta.Profiles.FirstRootSphericalRadialModel

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def finiteRoot (q : KPFinitePlace F) (t : q.adicCompletion F) : Group R :=
  KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)

theorem selected_root_fixed_near_zero {Q : AdmissibleFlatSources R}
    {T : Realization R Q} (D : SourceFactorization R Q T) (q : R.A.Sf)
    (v : R.A.UnitQuotient) :
    ∀ᶠ t in nhds (0 : q.val.adicCompletion F), ∀ g : Group R,
      T.theta v (g * finiteRoot R q.val t) = T.theta v g := by
  obtain ⟨s, x, hs, hx⟩ := D.selected_frozen_stage v
  have hq : Sum.inr q.val ∈ s.val := by
    rw [hs]
    exact (D.bad_exact _).mpr (Or.inr ⟨q.val, rfl, q.property⟩)
  have hn : Continuous (fun t : q.val.adicCompletion F =>
      KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t) :=
    (KPPGLLocalCover.finite_lifts_continuous F R.A.zeta12 R.A.primitive_zeta12 q.val _
      (KPAdelicCoverRestrictedProduct.depth_admissible F R.A.zeta12 R.A.primitive_zeta12 q.val)).1
  have he : ∀ᶠ t in nhds (0 : q.val.adicCompletion F),
      actualFiniteAction R D q.val
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t)
          (x ⟨Sum.inr q.val, hq⟩) = x ⟨Sum.inr q.val, hq⟩ := by
    apply ((stabilizer_open R D q.val _).preimage hn).mem_nhds
    simp [KPPGLLocalCover.N, KPStandardLocalRootLifts.N_zero]
  filter_upwards [he] with t ht g
  rw [← D.selected_eq v, hx]
  have hi := D.finite_intertwining q.val
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t)
      s hq x g
  change D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
    (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q.val, hq⟩
      (actualFiniteAction R D q.val
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) t)
          (x ⟨Sum.inr q.val, hq⟩))))) g = _ at hi
  rw [ht, Function.update_eq_self, ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R] at hi
  exact hi.symm

theorem common_root_sublevel {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (q : R.A.Sf)
    (L : AddSubgroup (q.val.adicCompletion F)) (hLo : IsOpen (L : Set (q.val.adicCompletion F))) :
    ∃ J : AddSubgroup (q.val.adicCompletion F), J ≤ L ∧ IsOpen (J : Set (q.val.adicCompletion F)) ∧
      (∀ j ∈ J, (actualFiniteCharacter q.val).toAddChar j = 1) ∧
      ∀ j ∈ J, ∀ v g, T.theta v (g * finiteRoot R q.val j) = T.theta v g := by
  letI := Q.finite_companions
  have hfix : ∀ᶠ t in nhds (0 : q.val.adicCompletion F), ∀ v g,
      T.theta v (g * finiteRoot R q.val t) = T.theta v g :=
    Filter.eventually_all.mpr (selected_root_fixed_near_zero R D q)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hfix
  let B : AddSubgroup (q.val.adicCompletion F) := {
    carrier := {t | ‖t‖ < r}
    zero_mem' := by simpa using hr
    add_mem' := by intro x y hx hy; exact (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
    neg_mem' := by intro x hx; simpa using hx }
  have hBo : IsOpen (B : Set (q.val.adicCompletion F)) := by
    change IsOpen {t : q.val.adicCompletion F | ‖t‖ < r}
    simpa only [Metric.ball, dist_zero_right] using (Metric.isOpen_ball (x := (0 : q.val.adicCompletion F)) (ε := r))
  obtain ⟨J, hJL, hJo, hphase⟩ := ThetaFiniteCutoff.PhaseSublevels.exists_uniform_phase_sublevel
    F q.val (actualFiniteCharacter q.val) (L ⊓ B) (hLo.inter hBo) 1
  refine ⟨J, hJL.trans inf_le_left, hJo, ?_, ?_⟩
  · intro j hj
    simpa using hphase 1 (by simp) j hj
  · intro j hj v g
    have hb : ‖j‖ < r := (hJL hj).2
    exact hball (show dist j 0 < r by simpa using hb) v g

theorem trace_finite_diagonal (y : R.A.G) (q : R.A.Sf) (t : q.val.adicCompletion F) :
    (adelicTraceQuotientCharacter F (QuotientAddGroup.mk
      ((localIdele R y : KPAdeles F) * KPRationalAdelicSplitting.localAdele F (Sum.inr q.val) t)) : ℂ) =
      (actualFiniteCharacter q.val).toAddChar ((y.2 q : q.val.adicCompletion F) * t) := by
  have he : (localIdele R y : KPAdeles F) *
      KPRationalAdelicSplitting.localAdele F (Sum.inr q.val) t =
      KPRationalAdelicSplitting.localAdele F (Sum.inr q.val) ((y.2 q : q.val.adicCompletion F) * t) := by
    apply Prod.ext
    · funext w
      change (localIdele R y : KPAdeles F).1 w * 0 = 0
      exact mul_zero _
    · apply RestrictedProduct.ext
      intro p
      change (localIdele R y : KPAdeles F).2 p *
        RestrictedProduct.single (fun p => p.adicCompletionIntegers F) q.val t p =
        RestrictedProduct.single (fun p => p.adicCompletionIntegers F) q.val
          ((y.2 q : q.val.adicCompletion F) * t) p
      by_cases hp : p = q.val
      · subst p
        have hy := congrArg Units.val (selected_localIdele_finite R y q)
        change (localIdele R y : KPAdeles F).2 q.val = _ at hy
        simp only [RestrictedProduct.single_eq_same, hy]
      · simp [RestrictedProduct.single, Pi.single_eq_of_ne hp]
  rw [he]
  change (adelicTraceCharacter F (KPRationalAdelicSplitting.localAdele F
    (Sum.inr q.val) ((y.2 q : q.val.adicCompletion F) * t)) : ℂ) = _
  have ht := adelicTraceCharacter_finite_single F q.val ((y.2 q : q.val.adicCompletion F) * t)
  have hh := CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter (F := F) q.val
  change (adelicTraceCharacter F _ : ℂ) = (ResidueTrace.localTraceCharacter q.val _ : ℂ)
  rw [hh]
  exact congrArg (fun z : Circle => (z : ℂ)) ht

theorem selected_phase_on_support {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (q : R.A.Sf) (J : AddSubgroup (q.val.adicCompletion F))
    (hχ : ∀ j ∈ J, (actualFiniteCharacter q.val).toAddChar j = 1)
    (hfix : ∀ j ∈ J, ∀ v g,
      A.realization.theta v (g * finiteRoot R q.val j) = A.realization.theta v g)
    (v : R.A.UnitQuotient) (y : R.A.G)
    (hy : fourier R A.sources.dq (A.realization.theta v) (diagonal R y) ≠ 0) :
    ∀ j ∈ J, (actualFiniteCharacter q.val).toAddChar (((y.2 q : q.val.adicCompletion F) - 1) * j) = 1 := by
  intro j hj
  have ht := stage08_fourier_root_translate R A v y
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q.val) j)
  have he : KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
      (finiteRoot R q.val j) (A.realization.theta v) = A.realization.theta v := by
    funext g
    exact hfix j hj v g
  change fourier R A.sources.dq
    (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 (finiteRoot R q.val j)
      (A.realization.theta v)) (diagonal R y) = _ at ht
  rw [he, trace_finite_diagonal] at ht
  have hp : (actualFiniteCharacter q.val).toAddChar ((y.2 q : q.val.adicCompletion F) * j) = 1 := by
    exact (mul_right_cancel₀ hy (ht.symm.trans (one_mul _).symm))
  have hs : ((y.2 q : q.val.adicCompletion F) - 1) * j + j = (y.2 q : q.val.adicCompletion F) * j := by ring
  have h := congrArg (actualFiniteCharacter q.val).toAddChar hs
  rw [AddChar.map_add_eq_mul, hχ j hj, mul_one, hp] at h
  exact h

theorem selected_cutoff_weights {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (q : R.A.Sf) (U : Subgroup (q.val.adicCompletion F)ˣ)
    (H : AddSubgroup (q.val.adicCompletion F))
    (hHc : IsCompact (H : Set (q.val.adicCompletion F)))
    (hHo : IsOpen (H : Set (q.val.adicCompletion F)))
    (hU : ∀ y : (q.val.adicCompletion F)ˣ, y ∈ U ↔ (y : q.val.adicCompletion F) - 1 ∈ H) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℂ) (t : I → q.val.adicCompletion F),
      ∀ v y, fourier R A.sources.dq (A.realization.theta v) (diagonal R y) ≠ 0 →
        (∑ i, c i * (actualFiniteCharacter q.val).toAddChar ((y.2 q : q.val.adicCompletion F) * t i)) =
          if y.2 q ∈ U then 1 else 0 := by
  obtain ⟨L, hLc, hLo, hdual⟩ := ThetaFiniteCutoff.PhaseSublevels.exists_additive_dual_level
    F q.val (actualFiniteCharacter q.val) (character_nontrivial q.val) H hHc hHo
  obtain ⟨J, hJL, hJo, hχ, hfix⟩ := common_root_sublevel R A.factorization q L hLo
  letI := KPRootAverage.finite_levelQuotient L J hJL hLc hJo
  letI := Fintype.ofFinite (KPRootAverage.LevelQuotient L J)
  refine ⟨KPRootAverage.LevelQuotient L J, inferInstance,
    (fun i => (Fintype.card (KPRootAverage.LevelQuotient L J) : ℂ)⁻¹ *
      (actualFiniteCharacter q.val).toAddChar (-(KPRootAverage.representative L J i : q.val.adicCompletion F))),
    (fun i => (KPRootAverage.representative L J i : q.val.adicCompletion F)), ?_⟩
  intro v y hy
  have he (i : KPRootAverage.LevelQuotient L J) :
      ((Fintype.card (KPRootAverage.LevelQuotient L J) : ℂ)⁻¹ *
        (actualFiniteCharacter q.val).toAddChar (-(KPRootAverage.representative L J i : q.val.adicCompletion F))) *
        (actualFiniteCharacter q.val).toAddChar ((y.2 q : q.val.adicCompletion F) *
          (KPRootAverage.representative L J i : q.val.adicCompletion F)) =
      (Fintype.card (KPRootAverage.LevelQuotient L J) : ℂ)⁻¹ *
        (actualFiniteCharacter q.val).toAddChar (((y.2 q : q.val.adicCompletion F) - 1) *
          (KPRootAverage.representative L J i : q.val.adicCompletion F)) := by
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, ThetaFiniteCutoff.additive_quotient_character_sum
    (actualFiniteCharacter q.val).toAddChar L J hJL hLc hJo
    ((y.2 q : q.val.adicCompletion F) - 1)
    (selected_phase_on_support R A q J hχ hfix v y hy)]
  rw [hdual, ← hU]

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
