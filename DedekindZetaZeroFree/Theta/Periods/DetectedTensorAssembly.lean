module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorFactorizationAndDetection
public import DedekindZetaZeroFree.Theta.Periods.FiniteHaarTransport
public import DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

structure TensorSeed extends JointRealizedFlatSources R N where
  finiteData : ∀ q, LocalImageData R q
  references : ∀ p, actualLocal R finiteData p
  bad : Finset (KPHilbert.Place F)
  bad_exact : ∀ p, p ∈ bad ↔ (∃ w : InfinitePlace F, p = Sum.inl w) ∨
    (∃ q : KPFinitePlace F, p = Sum.inr q ∧ q ∈ R.A.Sf)
  scalarSlot : R.A.Sf
  coreMap : RestrictedTensorSimple.Core (actualLocal R finiteData) references bad →ₗ[ℂ] Functions R
  selected : R.A.UnitQuotient → RestrictedTensorSimple.Core (actualLocal R finiteData) references bad
  selected_eq : ∀ v, coreMap (selected v) = realization.theta v
  selected_frozen_stage : ∀ v, ∃ (s : RestrictedTensorSimple.Level bad)
    (x : ∀ p : s.val, actualLocal R finiteData p), s.val = bad ∧
      selected v = RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x)
  core_injective : Function.Injective coreMap
  regular : ∀ x, coreMap x ∈ regularResidualFunctions R

structure TensorHC extends TensorSeed R N where
  generated : ∀ x, coreMap x ∈ hcHeckeSpan realization

structure TensorActions extends TensorHC R N where
  finite_intertwining : ∀ q (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (s : RestrictedTensorSimple.Level bad) (hq : Sum.inr q ∈ s.val)
    (x : ∀ p : s.val, actualLocal R finiteData p) g,
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q (finiteData q).inducing (finiteData q).inducing.polarization
          (finiteData q).haar (finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩))))) g =
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a))
  complex_intertwining : ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (s : RestrictedTensorSimple.Level bad) (hw : Sum.inl w ∈ s.val)
    (x : ∀ p : s.val, actualLocal R finiteData p) g,
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w, hw⟩
        (KPGlobalResidualConstruction.complexCoreSU2Action k (x ⟨Sum.inl w, hw⟩))))) g =
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x))
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k)

structure TensorDetected extends TensorActions R N where
  detected : ∃ v, fourier R sources.dq (realization.theta v) 1 ≠ 0

structure TensorSpherical extends TensorDetected R N where
  spherical_reference : ∀ (q : KPFinitePlace F), q ∉ R.A.Sf →
    references (Sum.inr q) ≠ 0 ∧ ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q),
      k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) →
      KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (finiteData q).inducing (finiteData q).inducing.polarization (finiteData q).haar (finiteData q).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) k)
        (references (Sum.inr q)) = references (Sum.inr q)

namespace TensorHC
variable {R N}

theorem same_residue (D : TensorHC R N) (x) :
    D.coreMap x ∈ sameResidueModule D.realization :=
  ⟨D.generated x, D.regular x⟩

theorem integrable (D : TensorHC R N) (x) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => D.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) D.sources.dq :=
  sameResidue_period_integrable D.realization (D.same_residue x) g

def literalPeriod (D : TensorHC R N) (g : Group R) :
    RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad →ₗ[ℂ] ℂ where
  toFun x := fourier R D.sources.dq (D.coreMap x) g
  map_add' x y := by
    unfold MomentSources.fourier
    simp only [map_add, Pi.add_apply, add_mul]
    exact integral_add (D.integrable x g) (D.integrable y g)
  map_smul' c x := by
    unfold MomentSources.fourier
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _

def sliceLine (D : TensorHC R N) (p : KPHilbert.Place F) :
    Submodule ℂ (actualLocal R D.finiteData p →ₗ[ℂ] ℂ) :=
  Submodule.span ℂ {l | ∃ (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j) (hp : p ∈ s.val),
    l = (coreStageMultilinear (actualLocal R D.finiteData) D.references D.bad
      (D.literalPeriod 1) s).toLinearMap x ⟨p, hp⟩}

theorem slice_mem (D : TensorHC R N) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ j : s.val, actualLocal R D.finiteData j) (i : s.val) :
    (coreStageMultilinear (actualLocal R D.finiteData) D.references D.bad
      (D.literalPeriod 1) s).toLinearMap x i ∈ D.sliceLine i :=
  Submodule.subset_span ⟨s, x, i.property, rfl⟩
end TensorHC

namespace TensorDetected
variable {R N}

theorem exists_detected_slice (D : TensorDetected R N) (p : KPHilbert.Place F) :
    ∃ l ∈ D.toTensorHC.sliceLine p, l ≠ 0 ∧
      (p ∉ D.bad → l (D.references p) ≠ 0) := by
  obtain ⟨v, hv⟩ := D.detected
  obtain ⟨s, x, hs, hx⟩ := D.selected_frozen_stage v
  have hd : D.toTensorHC.literalPeriod 1
      (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x)) ≠ 0 := by
    change fourier R D.sources.dq (D.coreMap _) 1 ≠ 0
    rw [← hx, D.selected_eq]
    exact hv
  let t : RestrictedTensorSimple.Level D.bad :=
    ⟨insert p s.val, s.property.trans (Finset.subset_insert _ _)⟩
  let y : ∀ j : t.val, actualLocal R D.finiteData j :=
    fun j => if h : j.val ∈ s.val then x ⟨j.val, h⟩ else D.references j
  have htrans : RestrictedTensorSimple.stageInclusion _ D.references D.bad t (PiTensorProduct.tprod ℂ y) =
      RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x) := by
    rw [← RestrictedTensorSimple.insert_pure (actualLocal R D.finiteData) D.references s.val
      t.val (Finset.subset_insert p s.val) x]
    exact Module.DirectLimit.of_f
  let i : t.val := ⟨p, Finset.mem_insert_self _ _⟩
  let l := (coreStageMultilinear (actualLocal R D.finiteData) D.references D.bad
    (D.toTensorHC.literalPeriod 1) t).toLinearMap y i
  have hvalue : l (y i) ≠ 0 := by
    simpa only [l, MultilinearMap.toLinearMap_apply, Function.update_eq_self,
      coreStageMultilinear, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      htrans] using hd
  refine ⟨l, D.toTensorHC.slice_mem t y i, ?_, ?_⟩
  · intro hz
    exact hvalue (by rw [hz, LinearMap.zero_apply])
  · intro hp
    have hps : p ∉ s.val := by rwa [hs]
    have hy : y i = D.references p := by simp [y, i, hps]
    rwa [hy] at hvalue

theorem exists_nonzero_slice (D : TensorDetected R N) (p : KPHilbert.Place F) :
    ∃ l ∈ D.toTensorHC.sliceLine p, l ≠ 0 := by
  obtain ⟨l, hl, hn, _⟩ := D.exists_detected_slice p
  exact ⟨l, hl, hn⟩
end TensorDetected

structure TensorFiniteLines extends TensorSpherical R N where
  finite_rank : ∀ q, Module.rank ℂ (toTensorHC.sliceLine (Sum.inr q)) ≤ 1

structure TensorLocalLines extends TensorFiniteLines R N where
  complex_rank : ∀ w, Module.rank ℂ (toTensorHC.sliceLine (Sum.inl w)) ≤ 1

theorem line_finrank_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ (V →ₗ[ℂ] ℂ)) (hr : Module.rank ℂ W ≤ 1)
    (l : V →ₗ[ℂ] ℂ) (hl : l ∈ W) (hne : l ≠ 0) : Module.finrank ℂ W = 1 := by
  letI : Module.Finite ℂ W := Module.rank_lt_aleph0_iff.mp (hr.trans_lt Cardinal.one_lt_aleph0)
  have hle : Module.finrank ℂ W ≤ 1 := Module.finrank_le_of_rank_le
    (by simpa using hr : Module.rank ℂ W ≤ (1 : ℕ))
  letI : Nontrivial W := ⟨⟨⟨l, hl⟩, 0, by
    intro h; exact hne (congrArg Subtype.val h)⟩⟩
  exact le_antisymm hle (Module.finrank_pos (R := ℂ) (M := W))

namespace TensorLocalLines
variable {R N}

theorem exists_localEll (D : TensorLocalLines R N) (p : KPHilbert.Place F) :
    ∃ l ∈ D.toTensorHC.sliceLine p, l ≠ 0 ∧
      (p ∉ D.bad → l (D.references p) = 1) := by
  by_cases hp : p ∈ D.bad
  · obtain ⟨l, hl, hn⟩ := D.toTensorDetected.exists_nonzero_slice p
    exact ⟨l, hl, hn, fun h => False.elim (h hp)⟩
  · cases p with
    | inl w => exact False.elim (hp ((D.bad_exact _).mpr (Or.inl ⟨w, rfl⟩)))
    | inr q =>
      obtain ⟨l, hl, _, hreference⟩ := D.toTensorDetected.exists_detected_slice (Sum.inr q)
      have hn := hreference hp
      let m := (l (D.references (Sum.inr q)))⁻¹ • l
      have hm : m (D.references (Sum.inr q)) = 1 := by simp [m, hn]
      refine ⟨m, (D.toTensorHC.sliceLine _).smul_mem _ hl, ?_, fun _ => hm⟩
      intro hz
      have he := congrArg (fun f : actualLocal R D.finiteData (Sum.inr q) →ₗ[ℂ] ℂ =>
        f (D.references (Sum.inr q))) hz
      rw [hm, LinearMap.zero_apply] at he
      exact one_ne_zero he

def localEll (D : TensorLocalLines R N) (p : KPHilbert.Place F) :
    actualLocal R D.finiteData p →ₗ[ℂ] ℂ := Classical.choose (D.exists_localEll p)

theorem localEll_mem (D : TensorLocalLines R N) (p) :
    D.localEll p ∈ D.toTensorHC.sliceLine p := (Classical.choose_spec (D.exists_localEll p)).1

theorem localEll_ne (D : TensorLocalLines R N) (p) : D.localEll p ≠ 0 :=
  (Classical.choose_spec (D.exists_localEll p)).2.1

theorem line_dimension (D : TensorLocalLines R N) (p) :
    Module.finrank ℂ (D.toTensorHC.sliceLine p) = 1 := by
  apply line_finrank_one _ _ (D.localEll p) (D.localEll_mem p) (D.localEll_ne p)
  cases p with
  | inl w => exact D.complex_rank w
  | inr q => exact D.finite_rank q

theorem reference_value (D : TensorLocalLines R N) (p) (hp : p ∉ D.bad) :
    D.localEll p (D.references p) = 1 :=
  (Classical.choose_spec (D.exists_localEll p)).2.2 hp

theorem normalized_bad_tuple (D : TensorLocalLines R N) :
    ∃ x : ∀ p : D.bad, actualLocal R D.finiteData p,
      ∀ p : D.bad, D.localEll p (x p) = 1 := by
  have hex : ∀ p : D.bad, ∃ y : actualLocal R D.finiteData p, D.localEll p y ≠ 0 := by
    intro p
    by_contra hn
    apply D.localEll_ne p
    ext y
    simpa only [not_not, LinearMap.zero_apply] using (not_exists.mp hn y)
  choose y hy using hex
  refine ⟨fun p => (D.localEll p (y p))⁻¹ • y p, ?_⟩
  intro p
  simp [hy p]

theorem literalPeriod_ne (D : TensorLocalLines R N) : D.toTensorHC.literalPeriod 1 ≠ 0 := by
  obtain ⟨v, hv⟩ := D.detected
  intro hz
  have h := LinearMap.congr_fun hz (D.selected v)
  change fourier R D.sources.dq (D.coreMap (D.selected v)) 1 = 0 at h
  rw [D.selected_eq] at h
  exact hv h

def factorization (D : TensorLocalLines R N) :
    SourceFactorization R D.sources D.realization := by
  let x₀ := Classical.choose D.normalized_bad_tuple
  have hx₀ := Classical.choose_spec D.normalized_bad_tuple
  let V := actualLocal R D.finiteData
  let L := D.toTensorHC.literalPeriod 1
  let W := D.toTensorHC.sliceLine
  let b : RestrictedTensorSimple.Level D.bad := ⟨D.bad, le_rfl⟩
  let c : ℂ := L (RestrictedTensorSimple.stageInclusion V D.references D.bad b
    (PiTensorProduct.tprod ℂ x₀))
  let slot : D.bad := ⟨Sum.inr D.scalarSlot.val,
    (D.bad_exact _).mpr (Or.inr ⟨D.scalarSlot.val, rfl, D.scalarSlot.property⟩)⟩
  have hm := D.toTensorHC.slice_mem
  have hc : c ≠ 0 := core_reference_detected V D.references D.bad L W hm
    D.line_dimension D.localEll D.localEll_mem D.reference_value x₀ hx₀ D.literalPeriod_ne
  let ell := Function.update D.localEll slot.val (c • D.localEll slot.val)
  have hnorm : ∀ p ∉ D.bad, ell p (D.references p) = 1 :=
    absorb_reference_value V D.references D.bad D.localEll D.reference_value slot c
  have heq : L = productFunctional V D.references D.bad ell hnorm :=
    core_factorization_absorbed V D.references D.bad L W hm D.line_dimension
      D.localEll D.localEll_mem D.reference_value x₀ hx₀ slot
  refine {
    finiteData := D.finiteData
    references := D.references
    bad := D.bad
    bad_exact := D.bad_exact
    ell := ell
    reference_value := hnorm
    scalarSlot := D.scalarSlot
    coreMap := D.coreMap
    selected := D.selected
    selected_eq := D.selected_eq
    selected_frozen_stage := D.selected_frozen_stage
    core_injective := D.core_injective
    core_same_residue := D.toTensorHC.same_residue
    finite_intertwining := by
      intro q a s hq x g
      convert D.finite_intertwining q a s hq x g using 1 <;> congr!
    complex_intertwining := by
      intro w k s hw x g
      convert D.complex_intertwining w k s hw x g using 1 <;> congr!
    product_integrable := ?_
    product_exact := ?_
    spherical_reference := D.spherical_reference
    detected_tensor := ⟨b, x₀, rfl, hc⟩
    period_integrable := theta_period_integrable D.realization
    detected := D.detected }
  · intro s x
    convert D.toTensorHC.integrable
      (RestrictedTensorSimple.stageInclusion V D.references D.bad s (PiTensorProduct.tprod ℂ x)) 1 using 1 <;>
      simp only [mul_one] <;> congr!
  · intro s x
    change L (RestrictedTensorSimple.stageInclusion V D.references D.bad s
      (PiTensorProduct.tprod ℂ x)) = _
    rw [heq, productFunctional_stage]
end TensorLocalLines
end DedekindZetaZeroFree.FourierContinuation

end
