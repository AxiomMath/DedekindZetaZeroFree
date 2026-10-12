module

public import DedekindZetaZeroFree.Theta.Unfolding.ReflectedEvaluationFromExtraction
public import DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits
public import DedekindZetaZeroFree.Theta.Whittaker.ImageRepresentationUniqueness

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

local notation "V" => actualLocal R D.finiteData
local notation "Core" => RestrictedTensorSimple.Core V D.references D.bad

theorem tensor_period_integrable (x : Core) (g : Group R) :
    Integrable (fun q => D.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  exact FourierContinuation.sameResidue_period_integrable T (D.core_same_residue x) g

def tensorPeriod (g : Group R) : Core →ₗ[ℂ] ℂ where
  toFun x := fourier R Q.dq (D.coreMap x) g
  map_add' x y := by
    simp only [map_add, MomentSources.fourier, Pi.add_apply, add_mul]
    exact integral_add (tensor_period_integrable R D x g) (tensor_period_integrable R D y g)
  map_smul' c x := by
    simp only [map_smul, MomentSources.fourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _

def finitePeriodLift (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) : Group R :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)

def finiteSlotPeriod (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, V p) (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (g : Group R) : V (Sum.inr q) →ₗ[ℂ] ℂ :=
  (tensorPeriod R D g).comp
    ((RestrictedTensorSimple.stageInclusion V D.references D.bad s).comp
      ((PiTensorProduct.tprod ℂ).toLinearMap x ⟨Sum.inr q, hq⟩))

theorem tensor_finite_translate (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, V p) (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (g : Group R) :
    fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion V D.references D.bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
          (D.finiteData q).haar (D.finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩)))))) g =
    fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion V D.references D.bad s
      (PiTensorProduct.tprod ℂ x))) (g * finitePeriodLift R q a) := by
  have hi := tensor_period_integrable R D
    (RestrictedTensorSimple.stageInclusion V D.references D.bad s (PiTensorProduct.tprod ℂ x))
    (g * finitePeriodLift R q a)
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with t
  rw [D.finite_intertwining, mul_assoc]
  rfl

def exteriorTrace (q : KPFinitePlace F) : Multiplicative (q.adicCompletion F) →ₜ* ℂˣ where
  toFun t := Circle.toUnits (localFiniteCharacter F q t.toAdd)
  map_one' := by simp
  map_mul' := by intro x y; simp [AddChar.map_add_eq_mul]
  continuous_toFun := by
    have hc : Continuous (Circle.toUnits : Circle → ℂˣ) := by
      rw [Units.continuous_iff]
      constructor
      · exact continuous_subtype_val
      · change Continuous (fun z : Circle => (z : ℂ)⁻¹)
        exact continuous_subtype_val.inv₀ (fun z : Circle => Circle.coe_ne_zero z)
    exact hc.comp ((continuous_localFiniteCharacter F q).comp continuous_toAdd)

@[simp] theorem exteriorTrace_coe (q : KPFinitePlace F) (t : Multiplicative (q.adicCompletion F)) :
    (exteriorTrace (F := F) q t : ℂ) = (localFiniteCharacter F q t.toAdd : ℂ) := rfl

theorem exteriorTrace_ne_one (q : KPFinitePlace F) :
    (exteriorTrace (F := F) q).toMonoidHom ≠ 1 := by
  intro h
  apply one_ne_zero (α := q.adicCompletion F)
  apply (localFiniteCharacter_nondegenerate F q 1).mp
  intro z
  have he := congrArg (fun χ : Multiplicative (q.adicCompletion F) →* ℂˣ =>
    (χ (Multiplicative.ofAdd z) : ℂ)) h
  apply Subtype.ext
  change (localFiniteCharacter F q z : ℂ) = 1 at he
  simpa only [one_mul, Circle.coe_one] using he

theorem finiteSlotPeriod_root (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, V p) (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (g : Group R)
    (hg : ∀ t : q.adicCompletion F, Commute g (finitePeriodLift R q
      (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t)))
    (t : q.adicCompletion F) (b : V (Sum.inr q)) :
    finiteSlotPeriod R D s x q hq g
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) =
      (localFiniteCharacter F q t : ℂ) * finiteSlotPeriod R D s x q hq g b := by
  let i : s.val := ⟨Sum.inr q, hq⟩
  let y := Function.update x i b
  let c := RestrictedTensorSimple.stageInclusion V D.references D.bad s (PiTensorProduct.tprod ℂ y)
  have he := tensor_finite_translate R D s y q hq
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) g
  have hu : Function.update y i
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) (y i)) =
      Function.update x i
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
          (D.finiteData q).haar (D.finiteData q).haar_integer
          (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) := by
    simp [y]
  simp only [finiteSlotPeriod, LinearMap.comp_apply, tensorPeriod, LinearMap.coe_mk,
    AddHom.coe_mk, MultilinearMap.toLinearMap_apply]
  change MomentSources.fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion V
    D.references D.bad s (PiTensorProduct.tprod ℂ (Function.update x i
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b))))) g = _
  rw [← hu]
  unfold KPPGLLocalCover.N at he ⊢
  dsimp only [i] at hu ⊢
  rw [he, (hg t).eq]
  unfold finitePeriodLift
  rw [ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R]
  letI := Q.quotientHaar
  have h := ExteriorWhittakerValues.StoredWhittaker.fourier_left_root R Q.dq (D.coreMap c)
    (ExteriorWhittakerValues.StoredWhittaker.core_rational_root R D c)
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) g
    (tensor_period_integrable R D c g)
  have ht : adelicTraceQuotientCharacter F (QuotientAddGroup.mk
      (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)) = localFiniteCharacter F q t :=
    (adelicTraceQuotientCharacter_mk F _).trans (adelicTraceCharacter_finite_single F q t)
  rw [ht] at h
  exact h

theorem finiteSlotPeriod_exterior (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, V p) (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (htame : (3 : (ValuativeRel.valuation (q.adicCompletion F)).integer) ∉
      IsLocalRing.maximalIdeal (ValuativeRel.valuation (q.adicCompletion F)).integer)
    (href : D.ell (Sum.inr q) (D.references (Sum.inr q)) = 1)
    (g : Group R)
    (hg : ∀ t : q.adicCompletion F, Commute g (finitePeriodLift R q
      (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t)))
    (b : V (Sum.inr q)) :
    finiteSlotPeriod R D s x q hq g b = D.ell (Sum.inr q) b *
      finiteSlotPeriod R D s x q hq g (D.references (Sum.inr q)) := by
  let M := D.finiteData q
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    q M.inducing M.inducing.polarization M.haar M.haar_integer
  let W := RootEquivariantMaps ρ (KPLocalJacquetImage.root M.inducing.borel)
    (exteriorTrace (F := F) q).toMonoidHom ℂ
  have hroot (t : Multiplicative (q.adicCompletion F)) :
      KPLocalJacquetImage.root M.inducing.borel t =
        KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t.toAdd := by
    exact (M.inducing.openCell M.inducing.polarization).upper_eq t.toAdd
  have he : D.ell (Sum.inr q) ∈ W := by
    intro t v
    rw [hroot]
    change D.ell (Sum.inr q) (ρ
      (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t.toAdd) v) =
      (localFiniteCharacter F q t.toAdd : ℂ) * D.ell (Sum.inr q) v
    simpa only [CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter] using
      ExteriorWhittakerValues.StoredWhittaker.ell_finite_root R D q t.toAdd v
  have hl : finiteSlotPeriod R D s x q hq g ∈ W := by
    intro t v
    rw [hroot]
    exact finiteSlotPeriod_root R D s x q hq g hg t.toAdd v
  have hr : Module.rank ℂ W ≤ 1 := ExteriorWhittakerValues.ActualWhittaker.rank_le_one F R.A.zeta12
    R.A.primitive_zeta12 q M.inducing M.inducing.polarization M.haar M.haar_integer htame
    (exteriorTrace (F := F) q) (exteriorTrace_ne_one q)
  letI : Module.Finite ℂ W := Module.rank_lt_aleph0_iff.mp (hr.trans_lt Cardinal.one_lt_aleph0)
  let e : W := ⟨D.ell (Sum.inr q), he⟩
  have hene : e ≠ 0 := by
    intro hz
    have h := congrArg (fun l : W => l.val (D.references (Sum.inr q))) hz
    change D.ell (Sum.inr q) (D.references (Sum.inr q)) = 0 at h
    rw [href] at h
    exact one_ne_zero h
  letI : Nontrivial W := ⟨⟨e, 0, hene⟩⟩
  have hdim : Module.finrank ℂ W = 1 := le_antisymm
    (Module.finrank_le_of_rank_le (by simpa using hr : Module.rank ℂ W ≤ (1 : ℕ)))
    (Module.finrank_pos (R := ℂ) (M := W))
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hene
    (⟨finiteSlotPeriod R D s x q hq g, hl⟩ : W)
  have hh : c • D.ell (Sum.inr q) = finiteSlotPeriod R D s x q hq g := congrArg Subtype.val hc
  have hscalar : c = finiteSlotPeriod R D s x q hq g (D.references (Sum.inr q)) := by
    have h := LinearMap.congr_fun hh (D.references (Sum.inr q))
    simpa only [LinearMap.smul_apply, smul_eq_mul, href, mul_one] using h
  rw [← hh]
  simp only [LinearMap.smul_apply, smul_eq_mul, href, mul_one]
  exact mul_comm _ _

end DedekindZetaZeroFree.OrbitExpansion

end
