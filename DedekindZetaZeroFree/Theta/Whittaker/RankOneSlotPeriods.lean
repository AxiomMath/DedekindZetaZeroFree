module

public import DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits

public import DedekindZetaZeroFree.Theta.Profiles.PositiveSheetSmoothing
public import DedekindZetaZeroFree.Theta.Whittaker.ImageRepresentationUniqueness

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

lemma core_period_integrable
    (x : RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad)
    (g : Group R) :
    Integrable (fun q => D.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
      star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  exact FourierContinuation.sameResidue_period_integrable T (D.core_same_residue x) g

def corePeriod (g : Group R) :
    RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad →ₗ[ℂ] ℂ where
  toFun x := fourier R Q.dq (D.coreMap x) g
  map_add' x y := by
    simp only [map_add, MomentSources.fourier, Pi.add_apply, add_mul]
    exact integral_add (core_period_integrable R D x g) (core_period_integrable R D y g)
  map_smul' a x := by
    simp only [map_smul, MomentSources.fourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _

def finiteLift (p : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) : Group R :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a)

def slotPeriod (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (p : KPFinitePlace F) (hp : Sum.inr p ∈ s.val) (g : Group R) :
    actualLocal R D.finiteData (Sum.inr p) →ₗ[ℂ] ℂ :=
  (corePeriod R D g).comp
    ((RestrictedTensorSimple.stageInclusion _ D.references D.bad s).comp
      ((PiTensorProduct.tprod ℂ).toLinearMap x ⟨Sum.inr p, hp⟩))

lemma slotPeriod_finite_action (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j)
    (p : KPFinitePlace F) (hp : Sum.inr p ∈ s.val) (g : Group R)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (b : actualLocal R D.finiteData (Sum.inr p)) :
    slotPeriod R D s x p hp g
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
        (D.finiteData p).haar (D.finiteData p).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a) b) =
      slotPeriod R D s x p hp (g * finiteLift R p a) b := by
  let i : s.val := ⟨Sum.inr p, hp⟩
  let y := Function.update x i b
  have hu : Function.update x i
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
        (D.finiteData p).haar (D.finiteData p).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a) b) =
    Function.update y i
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
        (D.finiteData p).haar (D.finiteData p).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) a) (y i)) := by
    simp only [y, Function.update_self, Function.update_idem]
  change fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
    (PiTensorProduct.tprod ℂ (Function.update x i _)))) g = _
  rw [hu]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  rw [D.finite_intertwining, mul_assoc]
  rfl

lemma slotPeriod_root (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j)
    (p : KPFinitePlace F) (hp : Sum.inr p ∈ s.val) (g : Group R)
    (hg : ∀ t : p.adicCompletion F, Commute g
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr p) t)))
    (t : p.adicCompletion F) (b : actualLocal R D.finiteData (Sum.inr p)) :
    slotPeriod R D s x p hp g
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
        (D.finiteData p).haar (D.finiteData p).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t) b) =
      (ResidueTrace.localTraceCharacter p t : ℂ) * slotPeriod R D s x p hp g b := by
  let y := Function.update x ⟨Sum.inr p, hp⟩ b
  let core := RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ y)
  have ha := slotPeriod_finite_action R D s x p hp g
    (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t) b
  change slotPeriod R D s x p hp g
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      p (D.finiteData p).inducing (D.finiteData p).inducing.polarization
      (D.finiteData p).haar (D.finiteData p).haar_integer
      (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t) b) = _ at ha
  rw [ha]
  change fourier R Q.dq (D.coreMap core)
    (g * finiteLift R p (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t)) = _
  rw [show finiteLift R p (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) t) =
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr p) t) from
      ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R p t, (hg t).eq]
  letI := Q.quotientHaar
  rw [ExteriorWhittakerValues.StoredWhittaker.fourier_left_root R Q.dq (D.coreMap core)
    (ExteriorWhittakerValues.StoredWhittaker.core_rational_root R D core) _ g (core_period_integrable R D core g)]
  have htrace : adelicTraceQuotientCharacter F (QuotientAddGroup.mk
      (KPRationalAdelicSplitting.localAdele F (Sum.inr p) t)) = ResidueTrace.localTraceCharacter p t := by
    rw [CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter]
    exact (adelicTraceQuotientCharacter_mk F _).trans (adelicTraceCharacter_finite_single F p t)
  rw [htrace]
  rfl

lemma normalized_form_of_rank_le_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ (V →ₗ[ℂ] ℂ)) (hrank : Module.rank ℂ W ≤ 1)
    (L M : V →ₗ[ℂ] ℂ) (hL : L ∈ W) (hM : M ∈ W) (b : V) (hb : L b = 1) :
    M = (M b) • L := by
  letI : Module.Free ℂ W := Module.Free.of_divisionRing ℂ W
  letI : Module.Finite ℂ W := Module.rank_lt_aleph0_iff.mp (hrank.trans_lt Cardinal.one_lt_aleph0)
  let l₀ : W := ⟨L, hL⟩
  have hl₀ : l₀ ≠ 0 := by
    intro he
    have hh := congrArg (fun l : W => l.val b) he
    change L b = 0 at hh
    rw [hb] at hh
    exact one_ne_zero hh
  letI : Nontrivial W := ⟨⟨l₀, 0, hl₀⟩⟩
  have hdim : Module.finrank ℂ W = 1 := le_antisymm
    (Module.finrank_le_of_rank_le (by simpa using hrank : Module.rank ℂ W ≤ (1 : ℕ)))
    (Module.finrank_pos (R := ℂ) (M := W))
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hl₀ (⟨M, hM⟩ : W)
  have hc' : c • L = M := congrArg Subtype.val hc
  have hcv := LinearMap.congr_fun hc' b
  simp only [LinearMap.smul_apply, smul_eq_mul, hb, mul_one] at hcv
  rw [← hcv]
  exact hc'.symm

lemma slotPeriod_exterior (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j)
    (p : ThetaBranch.ExteriorPrime R.A) (hp : Sum.inr p.val ∈ s.val) (g : Group R)
    (hg : ∀ t : p.val.adicCompletion F, Commute g
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr p.val) t))) :
    slotPeriod R D s x p.val hp g =
      (slotPeriod R D s x p.val hp g (D.references (Sum.inr p.val))) •
        D.ell (Sum.inr p.val) := by
  let ψ : AddChar (p.val.adicCompletion F) ℂ :=
    { toFun := fun t => (ResidueTrace.localTraceCharacter p.val t : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intros; simp [AddChar.map_add_eq_mul] }
  let χ : Multiplicative (p.val.adicCompletion F) →ₜ* ℂˣ :=
    { toFun := fun t => (ψ.val_isUnit t.toAdd).unit
      map_one' := by apply Units.ext; simp
      map_mul' := by intros; apply Units.ext; simp [ψ.map_add_eq_mul]
      continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
        (by
          change Continuous (fun t : Multiplicative (p.val.adicCompletion F) => ψ t.toAdd)
          exact (continuous_subtype_val.comp
            (ResidueTrace.continuous_localTraceCharacter p.val)).comp continuous_toAdd) }
  have hχ (t : Multiplicative (p.val.adicCompletion F)) :
      (χ t : ℂ) = (ResidueTrace.localTraceCharacter p.val t.toAdd : ℂ) :=
    (ψ.val_isUnit _).unit_spec
  have hχne : χ.toMonoidHom ≠ 1 := by
    intro he
    have hh : ∀ t : p.val.adicCompletion F, localFiniteCharacter F p.val (1 * t) = 1 := by
      intro t
      have ht := congrArg (fun c : Multiplicative (p.val.adicCompletion F) →* ℂˣ =>
        (c (Multiplicative.ofAdd t) : ℂ)) he
      change (χ (Multiplicative.ofAdd t) : ℂ) = 1 at ht
      rw [hχ] at ht
      apply Subtype.ext
      rw [CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter] at ht
      simpa using ht
    exact one_ne_zero ((localFiniteCharacter_nondegenerate F p.val 1).mp hh)
  have h6 : IsUnit (6 : (ValuativeRel.valuation (p.val.adicCompletion F)).integer) :=
    (Valuation.integer.integers (ValuativeRel.valuation (p.val.adicCompletion F))).isUnit_iff_valuation_eq_one.mpr
      (by simpa only [map_ofNat] using ExteriorWhittakerValues.exterior_good_six p)
  have h3 : IsUnit (3 : (ValuativeRel.valuation (p.val.adicCompletion F)).integer) := by
    apply isUnit_of_mul_isUnit_right (x := (2 : (ValuativeRel.valuation (p.val.adicCompletion F)).integer))
    convert h6 using 1 <;> norm_num
  have ht3 : (3 : (ValuativeRel.valuation (p.val.adicCompletion F)).integer) ∉
      IsLocalRing.maximalIdeal (ValuativeRel.valuation (p.val.adicCompletion F)).integer := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h3
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p.val (D.finiteData p.val).inducing (D.finiteData p.val).inducing.polarization
    (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
  let W := RootEquivariantMaps ρ (KPLocalJacquetImage.root (D.finiteData p.val).inducing.borel)
    χ.toMonoidHom ℂ
  have hn (t : Multiplicative (p.val.adicCompletion F)) :
      KPLocalJacquetImage.root (D.finiteData p.val).inducing.borel t =
        KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) t.toAdd :=
    ((D.finiteData p.val).inducing.openCell (D.finiteData p.val).inducing.polarization).upper_eq t.toAdd
  have hl : D.ell (Sum.inr p.val) ∈ W := by
    intro t b
    change D.ell (Sum.inr p.val) (ρ (KPLocalJacquetImage.root (D.finiteData p.val).inducing.borel t) b) =
      (χ t : ℂ) * D.ell (Sum.inr p.val) b
    rw [hn, hχ]
    exact ExteriorWhittakerValues.StoredWhittaker.ell_finite_root R D p.val t.toAdd b
  have hs : slotPeriod R D s x p.val hp g ∈ W := by
    intro t b
    change slotPeriod R D s x p.val hp g
      (ρ (KPLocalJacquetImage.root (D.finiteData p.val).inducing.borel t) b) =
        (χ t : ℂ) * slotPeriod R D s x p.val hp g b
    rw [hn, hχ]
    exact slotPeriod_root R D s x p.val hp g hg t.toAdd b
  have hrank : Module.rank ℂ W ≤ 1 := ExteriorWhittakerValues.ActualWhittaker.rank_le_one F
    R.A.zeta12 R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
    (D.finiteData p.val).inducing.polarization (D.finiteData p.val).haar
    (D.finiteData p.val).haar_integer ht3 χ hχne
  have hval : D.ell (Sum.inr p.val) (D.references (Sum.inr p.val)) = 1 := by
    apply D.reference_value
    intro hbad
    rcases (D.bad_exact _).mp hbad with ⟨w, hw⟩ | ⟨q, hq, hqS⟩
    · cases hw
    · exact p.property (Sum.inr.inj hq ▸ hqS)
  exact normalized_form_of_rank_le_one W hrank _ _ hl hs _ hval

end DedekindZetaZeroFree.OrbitExpansion

end
