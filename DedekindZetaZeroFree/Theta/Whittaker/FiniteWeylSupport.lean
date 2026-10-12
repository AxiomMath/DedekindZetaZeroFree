module

public import DedekindZetaZeroFree.Theta.Whittaker.FourierRootEquivariance
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.RankOne.SmallNormDecay

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

theorem finite_trace_value (q : KPFinitePlace F) (t : q.adicCompletion F) :
    adelicTraceQuotientCharacter F (QuotientAddGroup.mk
      (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)) =
      localFiniteCharacter F q t := by
  exact (adelicTraceQuotientCharacter_mk F _).trans
    (adelicTraceCharacter_finite_single F q t)

def finiteTrace (q : KPFinitePlace F) : ContinuousAddChar (q.adicCompletion F) where
  toAddChar :=
    { toFun := fun t => (localFiniteCharacter F q t : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intros; simp [AddChar.map_add_eq_mul] }
  continuous_toFun := continuous_subtype_val.comp (continuous_localFiniteCharacter F q)
  unitary := fun t => Circle.norm_coe _

def finiteEll (q : KPFinitePlace F) : CanonicalSmoothModule
    (actualLocal R C.factorization.finiteData (Sum.inr q)) →L[ℂ] ℂ :=
  let f := (C.factorization.ell (Sum.inr q)).comp
    (canonicalSmoothModuleEquiv (actualLocal R C.factorization.finiteData (Sum.inr q))).toLinearMap
  ⟨f, canonicalSmoothModule_linear_continuous f⟩

theorem finiteEll_whittaker (v : R.A.UnitQuotient)
    (s : RestrictedTensorSimple.Level C.factorization.bad)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p)
    (hx : C.factorization.selected v = RestrictedTensorSimple.stageInclusion _
      C.factorization.references C.factorization.bad s (PiTensorProduct.tprod ℂ x))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) :
    finiteEll R C q ∈ localWhittakerSpace (Multiplicative (q.adicCompletion F))
      (CanonicalSmoothModule (actualLocal R C.factorization.finiteData (Sum.inr q)))
      ((canonicalSmoothRepresentation
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
          R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
          (C.factorization.finiteData q).inducing.polarization
          (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer)).comp
        (KPLocalJacquetImage.root (C.factorization.finiteData q).inducing.borel))
      (finiteTrace (F := F) q).toAddChar.toMonoidHom := by
  intro t b
  have h := selected_ell_root R C v s x hx q hq t.toAdd b
  rw [finite_trace_value] at h
  have hr := ((C.factorization.finiteData q).inducing.openCell
    (C.factorization.finiteData q).inducing.polarization).upper_eq t.toAdd
  change C.factorization.ell (Sum.inr q)
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
      (C.factorization.finiteData q).inducing.polarization
      (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
      ((C.factorization.finiteData q).inducing.borel.upperRoot t) b) = _
  change ((C.factorization.finiteData q).inducing.borel.upperRoot t :
    KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) = _ at hr
  rw [hr]
  exact h

theorem localWeyl_small_norm (v : R.A.UnitQuotient) (p : R.A.Sf) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : (p.val.adicCompletion F)ˣ,
      ‖(z : p.val.adicCompletion F)‖ ≤ 1 →
      ‖ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) z‖ ≤
        D * Real.rpow ‖(z : p.val.adicCompletion F)‖ (1 / 4 : ℝ) := by
  obtain ⟨s, x, hs, hx⟩ := C.factorization.selected_frozen_stage v
  have hp : Sum.inr p.val ∈ s.val := by
    rw [hs]
    exact (C.factorization.bad_exact _).mpr (Or.inr ⟨p.val, rfl, p.property⟩)
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
    R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
    (C.factorization.finiteData p.val).inducing.polarization
    (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer
  let φ : CanonicalSmoothModule (actualLocal R C.factorization.finiteData (Sum.inr p.val)) :=
    ρ (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) (x ⟨Sum.inr p.val, hp⟩)
  obtain ⟨B, hB, hb⟩ := KPInterface.ActualFiniteOutputSteps.actual_small_norm_decay_canonical
    R.A.zeta12 R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
    (C.factorization.finiteData p.val).inducing.polarization
    (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer
    (finiteTrace p.val) (finiteEll R C p.val) (finiteEll_whittaker R C v s x hx p.val hp)
    φ (1 / 4) (by norm_num) (by norm_num)
  have hd : 0 < ‖C.factorization.ell (Sum.inr p.val) (x ⟨Sum.inr p.val, hp⟩)‖ :=
    norm_pos_iff.mpr (selected_tensor_nonzero R C v s x hx ⟨Sum.inr p.val, hp⟩)
  refine ⟨B / ‖C.factorization.ell (Sum.inr p.val) (x ⟨Sum.inr p.val, hp⟩)‖,
    div_pos hB hd, ?_⟩
  intro z hz
  rw [localWeylValue_eq R C v s x hx p.val hp, norm_div]
  have h := hb z (norm_pos_iff.mpr z.ne_zero) hz
  have he : (finiteEll R C p.val)
      (canonicalSmoothRepresentation ρ (KPPGLLocalCover.A F R.A.zeta12
        R.A.primitive_zeta12 (Sum.inr p.val) z) φ) =
      C.factorization.ell (Sum.inr p.val)
        (ρ (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z *
          KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
          (x ⟨Sum.inr p.val, hp⟩)) := by
    simp only [finiteEll, ContinuousLinearMap.coe_mk', LinearMap.comp_apply,
      canonicalSmoothModuleEquiv, LinearEquiv.refl_apply,
      canonicalSmoothRepresentation, φ, map_mul, Module.End.mul_apply]
    rfl
  change ‖(finiteEll R C p.val) (canonicalSmoothRepresentation ρ
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z) φ)‖ ≤ _ at h
  rw [he] at h
  exact (div_le_div_of_nonneg_right h hd.le).trans_eq (by ring)

abbrev finiteAction (q : KPFinitePlace F) :=
  KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
    R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
    (C.factorization.finiteData q).inducing.polarization
    (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer

def finiteRoot (q : KPFinitePlace F) : AddChar (q.adicCompletion F)
    (KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) where
  toFun := KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
  map_zero_eq_one' := by simp [KPPGLLocalCover.N, KPStandardLocalRootLifts.N_zero]
  map_add_eq_mul' := KPPGLLocalCover.N_add F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)

theorem finite_trace_nontrivial (q : KPFinitePlace F) : localFiniteCharacter F q ≠ 1 := by
  intro h
  apply one_ne_zero (α := q.adicCompletion F)
  apply (localFiniteCharacter_nondegenerate F q 1).mp
  intro z
  simp [h]

theorem finite_conjugacy (q : KPFinitePlace F) (z : (q.adicCompletion F)ˣ)
    (t : q.adicCompletion F) :
    KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) z * finiteRoot R q t =
      finiteRoot R q ((z : q.adicCompletion F) * t) *
        KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) z := by
  have h := (KPCorrectedBruhatLifts.quotient_upper_diagonal F R.A.zeta12
    R.A.primitive_zeta12 (Sum.inr q) ((z : q.adicCompletion F) * t) z).symm
  rw [mul_div_cancel_left₀ t z.ne_zero] at h
  exact h

theorem localWeyl_locallyConstant (v : R.A.UnitQuotient) (p : R.A.Sf) :
    IsLocallyConstant (fun z => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) z) := by
  obtain ⟨s, x, hs, hx⟩ := C.factorization.selected_frozen_stage v
  have hp : Sum.inr p.val ∈ s.val := by
    rw [hs]
    exact (C.factorization.bad_exact _).mpr (Or.inr ⟨p.val, rfl, p.property⟩)
  have hsmooth := smoothRepresentation_orbit_isLocallyConstant (finiteAction R C p.val)
    (KPRankOneShellRepair.actualCanonicalImage_smooth F R.A.zeta12
      R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
      (C.factorization.finiteData p.val).inducing.polarization
      (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer)
  have ha := (KPPGLLocalCover.finite_lifts_continuous F R.A.zeta12 R.A.primitive_zeta12 p.val
    (KPAdelicCoverRestrictedProduct.depth F R.A.zeta12 R.A.primitive_zeta12 p.val)
    (KPAdelicCoverRestrictedProduct.depth_admissible F R.A.zeta12 R.A.primitive_zeta12 p.val)).2.2
  have hl := KPFiniteLocal.whittakerValue_locallyConstant (finiteAction R C p.val) hsmooth
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) ha
    (C.factorization.ell (Sum.inr p.val))
    (finiteAction R C p.val (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
      (x ⟨Sum.inr p.val, hp⟩))
  have he : (fun z => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) z) =
      (fun z => KPFiniteLocal.whittakerValue (finiteAction R C p.val)
        (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
        (C.factorization.ell (Sum.inr p.val))
        (finiteAction R C p.val (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
          (x ⟨Sum.inr p.val, hp⟩)) z /
        C.factorization.ell (Sum.inr p.val) (x ⟨Sum.inr p.val, hp⟩)) := by
    funext z
    rw [localWeylValue_eq R C v s x hx p.val hp]
    simp only [KPFiniteLocal.whittakerValue, map_mul, Module.End.mul_apply]
  rw [he]
  exact hl.comp (fun b => b / C.factorization.ell (Sum.inr p.val) (x ⟨Sum.inr p.val, hp⟩))

theorem localWeyl_support (v : R.A.UnitQuotient) (p : R.A.Sf) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : (p.val.adicCompletion F)ˣ,
      M < ‖(z : p.val.adicCompletion F)‖ →
        ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) z = 0 := by
  obtain ⟨s, x, hs, hx⟩ := C.factorization.selected_frozen_stage v
  have hp : Sum.inr p.val ∈ s.val := by
    rw [hs]
    exact (C.factorization.bad_exact _).mpr (Or.inr ⟨p.val, rfl, p.property⟩)
  have hsmooth := smoothRepresentation_orbit_isLocallyConstant (finiteAction R C p.val)
    (KPRankOneShellRepair.actualCanonicalImage_smooth F R.A.zeta12
      R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
      (C.factorization.finiteData p.val).inducing.polarization
      (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer)
  have hn := (KPPGLLocalCover.finite_lifts_continuous F R.A.zeta12 R.A.primitive_zeta12 p.val
    (KPAdelicCoverRestrictedProduct.depth F R.A.zeta12 R.A.primitive_zeta12 p.val)
    (KPAdelicCoverRestrictedProduct.depth_admissible F R.A.zeta12 R.A.primitive_zeta12 p.val)).1
  have hWh : ∀ t b, C.factorization.ell (Sum.inr p.val)
      (finiteAction R C p.val (finiteRoot R p.val t) b) =
      (localFiniteCharacter F p.val t : ℂ) * C.factorization.ell (Sum.inr p.val) b := by
    intro t b
    have h := selected_ell_root R C v s x hx p.val hp t b
    rw [finite_trace_value] at h
    exact h
  obtain ⟨M, hM, hm⟩ := KPFiniteLocal.generic_fixed_vector_support p.val
    (finiteAction R C p.val) hsmooth (finiteRoot R p.val) hn
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (finite_conjugacy R p.val) (localFiniteCharacter F p.val) (finite_trace_nontrivial p.val)
    (C.factorization.ell (Sum.inr p.val)) hWh
    (finiteAction R C p.val (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
      (x ⟨Sum.inr p.val, hp⟩))
  refine ⟨M, hM, fun z hz => ?_⟩
  rw [localWeylValue_eq R C v s x hx p.val hp]
  have h := hm z hz
  simp only [KPFiniteLocal.whittakerValue, ← Module.End.mul_apply, ← map_mul] at h
  rw [h, zero_div]

end DedekindZetaZeroFree.SheetRescaling

end
