module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.UpperResidueFactorization

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators NNReal
open NumberField Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentMinusSlot
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (s : RestrictedTensorSimple.Level (bad R P C))
variable (x : ∀ j : s.val, actualLocal R (imageData R N P C) j.val)

def finiteValues (a : Raw R) : ∀ j : s.val, Fiber R P C j.val := fun j =>
  match j with
  | ⟨.inl _,_⟩ => 1
  | ⟨.inr q,hq⟩ => (x ⟨.inr q,hq⟩).val.val
      (KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (a (.inr q)))

def observation : MultilinearMap ℂ (fun j : s.val => Fiber R P C j.val) ℂ :=
  (({ toFun := fun f : smoothRationalFiber F ζ hζ => f.val.val 1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } : smoothRationalFiber F ζ hζ →ₗ[ℂ] ℂ).comp
    ((comparisonSmooth R P C).comp
      (RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C)
        (bad R P C) s))).compMultilinearMap (PiTensorProduct.tprod ℂ)

def finiteScalar (a : Raw R) : ℂ := observation R P C s (finiteValues R N P C s x a)

def archFactor (a : Raw R) (j : s.val) : ℂ :=
  match j with
  | ⟨.inl u,hu⟩ => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ
      (a (.inl u)).epsilon : ℂ) * (x ⟨.inl u,hu⟩).val.val (complexMatrix R u (a (.inl u)))
  | ⟨.inr _,_⟩ => 1

theorem reflected_pure (a : Raw R) :
    (reflectedStage R N P C s a (PiTensorProduct.tprod ℂ x)).val.val 1 =
      (∏ j, archFactor R N P C s x a j) * finiteScalar R N P C s x a := by
  simp only [reflectedStage, LinearMap.comp_apply, PiTensorProduct.map_tprod]
  change observation R P C s (fun j => localMinusValue R N P C j.val (a j.val) (x j)) = _
  have he : (fun j : s.val => localMinusValue R N P C j.val (a j.val) (x j)) =
      fun j => archFactor R N P C s x a j • finiteValues R N P C s x a j := by
    funext j
    rcases j with ⟨j,hj⟩
    cases j <;> simp [archFactor, finiteValues, localMinusValue]
  rw [he, MultilinearMap.map_smul_univ]
  rfl

theorem finiteValues_locallyConstant : IsLocallyConstant (finiteValues R N P C s x) := by
  have hl (j : s.val) : IsLocallyConstant (fun a : Raw R => finiteValues R N P C s x a j) := by
    rcases j with ⟨j,hj⟩
    cases j with
    | inl w => exact IsLocallyConstant.const _
    | inr q =>
      have hc : IsLocallyConstant (x ⟨.inr q,hj⟩).val.val := by
        obtain ⟨J,hJ⟩ := (x ⟨.inr q,hj⟩).val.property.2
        rw [IsLocallyConstant.iff_eventually_eq]
        intro g
        have hc : Continuous (fun y : KPLocalExceptionalConstruction.ActualCover F ζ hζ q => g⁻¹*y) :=
          continuous_const.mul continuous_id
        have hm : ∀ᶠ y in nhds g, g⁻¹*y ∈ J :=
          hc.continuousAt.preimage_mem_nhds (by simpa using J.isOpen.mem_nhds J.one_mem)
        filter_upwards [hm] with y hy
        have he := congrFun (hJ (g⁻¹*y) hy) g
        simpa [KPLocalPrincipalSeries.vectorRightTranslation] using he
      exact hc.comp_continuous (QuotientGroup.continuous_mk.comp (RestrictedProduct.continuous_eval _))
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have he : ∀ j : s.val, ∀ᶠ b in nhds a, finiteValues R N P C s x b j = finiteValues R N P C s x a j := by
    intro j
    have h := hl j
    rw [IsLocallyConstant.iff_eventually_eq] at h
    exact h a
  filter_upwards [Filter.eventually_all.mpr he] with b hb
  exact funext hb

theorem finiteScalar_continuous : Continuous (finiteScalar R N P C s x) :=
  ((finiteValues_locallyConstant R N P C s x).comp (observation R P C s)).continuous

def coefficient (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (a : Raw R) : ℂ :=
  (∏ j ∈ Finset.univ.erase ⟨Sum.inl w,hw⟩, archFactor R N P C s x a j) *
    finiteScalar R N P C s x a *
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (a (.inl w)).epsilon : ℂ)

theorem archFactor_continuous (j : s.val) : Continuous (fun a : Raw R => archFactor R N P C s x a j) := by
  rcases j with ⟨j,hj⟩
  cases j with
  | inr q => exact continuous_const
  | inl w =>
    exact ((ComplexLines.CanonicalStageSlot.phase_continuous R.A w).comp
      (RestrictedProduct.continuous_eval _)).mul
        ((EisensteinReferenceSections.SourceContinuity.principal_continuous negativeParameter
          (x ⟨.inl w,hj⟩).val).comp
          ((ComplexLines.CanonicalStageSlot.matrix_continuous R.A w).comp
            (RestrictedProduct.continuous_eval _)))

theorem coefficient_continuous (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) :
    Continuous (coefficient R N P C s x w hw) :=
  ((continuous_finsetProd _ (fun j _ => archFactor_continuous R N P C s x j)).mul
    (finiteScalar_continuous R N P C s x)).mul
      ((ComplexLines.CanonicalStageSlot.phase_continuous R.A w).comp
        (RestrictedProduct.continuous_eval _))

def smoothSlot (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (a : Raw R) : PrincipalSeries negativeParameter →ₗ[ℂ] ℂ where
  toFun f := coefficient R N P C s x w hw a * f (complexMatrix R w (a (.inl w)))
  map_add' := by intros; simp [mul_add]
  map_smul' := by intros; simp [mul_left_comm]

theorem smoothSlot_compact_bound (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (K : Set (Raw R)) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (f : PrincipalSeries negativeParameter) (a : Raw R), a ∈ K →
        ‖smoothSlot R N P C s x w hw a f‖ ≤
          B * (orders.sup (chartSeminorm negativeParameter)) f := by
  let M : Raw R → ComplexGL2 := fun a => complexMatrix R w (a (.inl w))
  have hM : Continuous M := (ComplexLines.CanonicalStageSlot.matrix_continuous R.A w).comp
    (RestrictedProduct.continuous_eval _)
  let L := M '' K
  have hL : IsCompact L := hK.image hM
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let ev := KPActualReflectionData.LiteralProductPointBound.compactMatrixEvaluation
    negativeParameter L hL
  let Q : Seminorm ℂ (PrincipalSeries negativeParameter) :=
    (normSeminorm ℂ C(L,ℂ)).comp ev
  have hQ : Continuous Q := continuous_norm.comp
    (KPActualReflectionData.LiteralProductPointBound.compactMatrixEvaluation_continuous
      negativeParameter L hL)
  obtain ⟨orders,B,hB,hb⟩ := Seminorm.bound_of_continuous
    (show WithSeminorms (chartSeminorm negativeParameter) from ⟨rfl⟩) Q hQ
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (coefficient_continuous R N P C s x w hw).continuousOn
  let d : ℝ≥0 := ⟨max 0 D,le_max_left _ _⟩
  refine ⟨orders,(1+d)*B,by positivity,?_⟩
  intro f a ha
  have he : ‖f (M a)‖ ≤ B * (orders.sup (chartSeminorm negativeParameter)) f :=
    ((ev f).norm_coe_le_norm ⟨M a,Set.mem_image_of_mem M ha⟩).trans (hb f)
  have hc : ‖coefficient R N P C s x w hw a‖ ≤ d := (hD a ha).trans (le_max_right _ _)
  change ‖coefficient R N P C s x w hw a * f (M a)‖ ≤ _
  rw [norm_mul]
  have hh := mul_le_mul hc he (norm_nonneg _) d.coe_nonneg
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
  exact hh.trans (by
    have hp := mul_nonneg B.coe_nonneg (apply_nonneg (orders.sup (chartSeminorm negativeParameter)) f)
    nlinarith only [hp])

theorem finiteValues_update (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (v : complexCore) (a : Raw R) :
    finiteValues R N P C s (Function.update x ⟨.inl w,hw⟩ v) a =
      finiteValues R N P C s x a := by
  funext j
  rcases j with ⟨j,hj⟩
  cases j with
  | inl u => rfl
  | inr q =>
    simp only [finiteValues, Function.update_of_ne
      (show (⟨Sum.inr q,hj⟩ : s.val) ≠ ⟨Sum.inl w,hw⟩ from by intro h; cases congrArg Subtype.val h)]

theorem reflected_update (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (v : complexCore) (a : Raw R) :
    (reflectedStage R N P C s a
      (PiTensorProduct.tprod ℂ (Function.update x ⟨.inl w,hw⟩ v))).val.val 1 =
        smoothSlot R N P C s x w hw a v.val := by
  rw [reflected_pure]
  have hfin : finiteScalar R N P C s (Function.update x ⟨.inl w,hw⟩ v) a =
      finiteScalar R N P C s x a := by
    unfold finiteScalar
    rw [finiteValues_update]
  rw [hfin, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ⟨Sum.inl w,hw⟩)]
  have hp : (∏ j ∈ Finset.univ.erase (⟨Sum.inl w,hw⟩ : s.val),
      archFactor R N P C s (Function.update x ⟨.inl w,hw⟩ v) a j) =
      ∏ j ∈ Finset.univ.erase (⟨Sum.inl w,hw⟩ : s.val), archFactor R N P C s x a j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hne := (Finset.mem_erase.mp hj).1
    rcases j with ⟨j,hj⟩
    cases j with
    | inr q => rfl
    | inl u => simp only [archFactor, Function.update_of_ne hne]
  rw [hp]
  simp only [archFactor, Function.update_self, smoothSlot, LinearMap.coe_mk, AddHom.coe_mk,
    coefficient]
  ring

theorem reflected_update_compact_bound (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (K : Set (Raw R)) (hK : IsCompact K) :
    ∃ orders : Finset ℕ, ∃ B : ℝ≥0, B ≠ 0 ∧
      ∀ (v : complexCore) (a : Raw R), a ∈ K →
        ‖(reflectedStage R N P C s a
          (PiTensorProduct.tprod ℂ (Function.update x ⟨.inl w,hw⟩ v))).val.val 1‖ ≤
          B * (orders.sup (chartSeminorm negativeParameter)) v.val := by
  obtain ⟨orders,B,hB,hb⟩ := smoothSlot_compact_bound R N P C s x w hw K hK
  exact ⟨orders,B,hB,fun v a ha => by rw [reflected_update]; exact hb v.val a ha⟩

end DedekindZetaZeroFree.FourierContinuation.CurrentMinusSlot

end
