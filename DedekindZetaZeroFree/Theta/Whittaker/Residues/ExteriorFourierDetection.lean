module

public import DedekindZetaZeroFree.Eisenstein.Residues.FourierPeriods
public import DedekindZetaZeroFree.Theta.Whittaker.Exterior.SphericalNormalization
public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorLineDetection
public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorTensorPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
variable (N : MomentSources.TraceHaarTransport R)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "W" => MomentSources.actualLocal R (actualImageData R P C μ hμ)
local notation "V" => RestrictedTensorSimple.Core W (actualReference R P C μ hμ) (bad R.A P C)
local notation "dq" => KPWildKernelUpperBound.quotientHaar F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000

open ExteriorWhittakerValues.ActualShellNormalization
open scoped ValuativeRel
open ValuativeRel

theorem exterior_whittaker_comparison (p : ThetaBranch.ExteriorPrime R.A)
    (ell L : W (Sum.inr p.val) →ₗ[ℂ] ℂ)
    (hell : IsWhittaker F ζ hζ p.val (actualImageData R P C μ hμ p.val).inducing
      (C.polarization p.val) (μ p.val) (hμ p.val) (ExteriorWhittakerValues.ShellArithmetic.tracePsi p.val) ell)
    (hL : IsWhittaker F ζ hζ p.val (actualImageData R P C μ hμ p.val).inducing
      (C.polarization p.val) (μ p.val) (hμ p.val) (ExteriorWhittakerValues.ShellArithmetic.tracePsi p.val) L)
    (href : ell (actualReference R P C μ hμ (Sum.inr p.val)) = 1) :
    L = (L (actualReference R P C μ hμ (Sum.inr p.val))) • ell := by
  classical
  let M := actualImageData R P C μ hμ p.val
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F ζ hζ p.val
    M.inducing M.inducing.polarization M.haar M.haar_integer
  let S₀ := RootEquivariantMaps ρ (KPLocalJacquetImage.root M.inducing.borel)
    (OrbitExpansion.exteriorTrace (F := F) p.val).toMonoidHom ℂ
  have hmem (l : W (Sum.inr p.val) →ₗ[ℂ] ℂ)
      (hl : IsWhittaker F ζ hζ p.val M.inducing M.inducing.polarization
        M.haar M.haar_integer (ExteriorWhittakerValues.ShellArithmetic.tracePsi p.val) l) : l ∈ S₀ := by
    intro t v
    change l (ImageAction F ζ hζ p.val M.inducing M.inducing.polarization M.haar M.haar_integer
      (M.inducing.borel.upperRoot t) v) = (localFiniteCharacter F p.val t.toAdd : ℂ) * l v
    convert hl t.toAdd v using 1
    · rfl
    · simp only [ExteriorWhittakerValues.ShellArithmetic.tracePsi, AddChar.coe_mk,
        CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter]
      rfl
  have h6 : IsUnit (6 : (valuation (p.val.adicCompletion F)).integer) :=
    (Valuation.integer.integers (valuation (p.val.adicCompletion F))).isUnit_iff_valuation_eq_one.mpr
      (by simpa only [map_ofNat] using ExteriorWhittakerValues.exterior_good_six p)
  have h3 : IsUnit (3 : (valuation (p.val.adicCompletion F)).integer) := by
    apply isUnit_of_mul_isUnit_right (x := (2 : (valuation (p.val.adicCompletion F)).integer))
    convert h6 using 1 <;> norm_num
  have ht3 : (3 : (valuation (p.val.adicCompletion F)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (p.val.adicCompletion F)).integer := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h3
  have hr : Module.rank ℂ S₀ ≤ 1 := ExteriorWhittakerValues.ActualWhittaker.rank_le_one F ζ hζ p.val
    M.inducing M.inducing.polarization M.haar M.haar_integer ht3
    (OrbitExpansion.exteriorTrace (F := F) p.val) (OrbitExpansion.exteriorTrace_ne_one p.val)
  letI : Module.Finite ℂ S₀ := Module.rank_lt_aleph0_iff.mp (hr.trans_lt Cardinal.one_lt_aleph0)
  let e : S₀ := ⟨ell,hmem ell hell⟩
  have he : e ≠ 0 := by
    intro hz
    have hz' := congrArg (fun f : S₀ => f.val (actualReference R P C μ hμ (Sum.inr p.val))) hz
    change ell (actualReference R P C μ hμ (Sum.inr p.val)) = 0 at hz'
    rw [href] at hz'
    exact one_ne_zero hz'
  letI : Nontrivial S₀ := ⟨⟨e,0,he⟩⟩
  have hd : Module.finrank ℂ S₀ = 1 := le_antisymm
    (Module.finrank_le_of_rank_le (by simpa using hr : Module.rank ℂ S₀ ≤ (1:ℕ)))
    (Module.finrank_pos (R := ℂ) (M := S₀))
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hd he (⟨L,hmem L hL⟩ : S₀)
  have hh : c • ell = L := congrArg Subtype.val hc
  have hv := LinearMap.congr_fun hh (actualReference R P C μ hμ (Sum.inr p.val))
  simp only [LinearMap.smul_apply,smul_eq_mul,href,mul_one] at hv
  rw [← hv]
  exact hh.symm

def actualSlotPeriod (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j:t.val, W j.val) (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val) :
    W (Sum.inr q) →ₗ[ℂ] ℂ :=
  (KPFrozenDetection.stagePeriod W (actualReference R P C μ hμ) (bad R.A P C)
    (actualCoreFourier R P C μ hμ N 1) t).toLinearMap x ⟨Sum.inr q,hq⟩

theorem actualSlotPeriod_whittaker (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j:t.val, W j.val) (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val) :
    IsWhittaker F ζ hζ q (actualImageData R P C μ hμ q).inducing
      (C.polarization q) (μ q) (hμ q) (ExteriorWhittakerValues.ShellArithmetic.tracePsi q)
      (actualSlotPeriod R P C μ hμ N t x q hq) := by
  intro z b
  let M := actualImageData R P C μ hμ q
  have hr := (M.inducing.openCell M.inducing.polarization).upper_eq z
  change actualSlotPeriod R P C μ hμ N t x q hq
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F ζ hζ q M.inducing
      M.inducing.polarization (μ q) (hμ q) (M.inducing.borel.upperRoot (Multiplicative.ofAdd z)) b) = _
  rw [hr]
  have he := actualCoreFourier_stage_upper R P C μ hμ N t q hq z
    (Function.update x ⟨Sum.inr q,hq⟩ b)
  simp only [Function.update_self,Function.update_idem] at he
  change actualCoreFourier R P C μ hμ N 1
    (RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ) (bad R.A P C) t
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F ζ hζ q M.inducing
          M.inducing.polarization (μ q) (hμ q) (KPPGLLocalCover.N F ζ hζ (Sum.inr q) z) b)))) = _
  rw [he]
  congr 1
  change (adelicTraceQuotientCharacter F (QuotientAddGroup.mk
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q) z)) : ℂ) = _
  exact congrArg (fun a : Circle => (a:ℂ))
    (((adelicTraceQuotientCharacter_mk F _).trans
      (adelicTraceCharacter_finite_single F q z)).trans
      (congrArg (fun c : AddChar (q.adicCompletion F) Circle => c z)
        (CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter q)).symm)

def actualExteriorEll (hC : C.exceptional = R.A.Sf) (v : KPHilbert.Place F) : W v →ₗ[ℂ] ℂ :=
  match v with
  | Sum.inl _ => 0
  | Sum.inr q => if h : q ∉ R.A.Sf then
      (actualReference_normalized_whittaker R P C μ hμ hC ⟨q,h⟩).choose else 0

theorem actualExteriorEll_normalized (hC : C.exceptional = R.A.Sf)
    (v : KPHilbert.Place F) (hv : v ∉ bad R.A P C) :
    actualExteriorEll R P C μ hμ hC v (actualReference R P C μ hμ v) = 1 := by
  cases v with
  | inl q => exact False.elim (hv (by simp [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad]))
  | inr q =>
    have hq : q ∉ R.A.Sf := by
      simpa only [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad,
        Finset.inr_mem_disjSum,hC] using hv
    simp only [actualExteriorEll,dif_pos hq]
    exact (actualReference_normalized_whittaker R P C μ hμ hC ⟨q,hq⟩).choose_spec.2

theorem actualExteriorEll_slot (hC : C.exceptional = R.A.Sf)
    (t : RestrictedTensorSimple.Level (bad R.A P C)) (j : t.val)
    (hj : j.val ∉ bad R.A P C) (x : ∀ i:t.val, W i.val) (a : W j.val) :
    KPFrozenDetection.stagePeriod W (actualReference R P C μ hμ) (bad R.A P C)
      (actualCoreFourier R P C μ hμ N 1) t (Function.update x j a) =
    KPFrozenDetection.stagePeriod W (actualReference R P C μ hμ) (bad R.A P C)
      (actualCoreFourier R P C μ hμ N 1) t
      (Function.update x j (actualReference R P C μ hμ j.val)) *
      actualExteriorEll R P C μ hμ hC j.val a := by
  rcases j with ⟨v,hv⟩
  cases v with
  | inl q => exact False.elim (hj (by simp [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad]))
  | inr q =>
    have hq : q ∉ R.A.Sf := by
      simpa only [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad,
        Finset.inr_mem_disjSum,hC] using hj
    have hell := (actualReference_normalized_whittaker R P C μ hμ hC ⟨q,hq⟩).choose_spec.1
    have hc := exterior_whittaker_comparison R P C μ hμ ⟨q,hq⟩
      (actualExteriorEll R P C μ hμ hC (Sum.inr q))
      (actualSlotPeriod R P C μ hμ N t x q hv)
      (by simpa only [actualExteriorEll,dif_pos hq] using hell)
      (actualSlotPeriod_whittaker R P C μ hμ N t x q hv)
      (actualExteriorEll_normalized R P C μ hμ hC (Sum.inr q) hj)
    exact LinearMap.congr_fun hc a

theorem actualCoreFourier_detected_initial (hC : C.exceptional = R.A.Sf)
    (z : V) (hz : actualCoreFourier R P C μ hμ N 1 z ≠ 0) :
    ∃ x : ∀ j : bad R.A P C, W j.val,
      actualCoreFourier R P C μ hμ N 1
        (RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ)
          (bad R.A P C) ⟨bad R.A P C,le_rfl⟩ (PiTensorProduct.tprod ℂ x)) ≠ 0 := by
  exact KPFrozenDetection.detected_initial_of_exterior_comparison W
    (actualReference R P C μ hμ) (bad R.A P C) (actualCoreFourier R P C μ hμ N 1)
    (actualExteriorEll R P C μ hμ hC) (actualExteriorEll_normalized R P C μ hμ hC)
    (by
      intro s j hj x a
      convert actualExteriorEll_slot R P C μ hμ N hC s j hj x a using 1 <;> congr 4 <;> exact Subsingleton.elim _ _) z hz
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
