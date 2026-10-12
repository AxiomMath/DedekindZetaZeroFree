module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.StabilizersAndCosets

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Cover → Cover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Fiber → Fiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming Source → Source
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductCover → ProductCover
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFiber → ProductFiber
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming ProductFunctions → ProductFunctions
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming evaluation → evaluation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation renaming tensorEvaluation → tensorEvaluation
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer renaming compactSlotStabilizer → compactSlotStabilizer
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer renaming CompactCosets → CompactCosets
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductStabilizer renaming compactCosets_finite → compactCosets_finite
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

local instance (q : S) : AddCommGroup (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusAdd F ζ hζ M (Sum.inr q.val)
local instance (q : S) : Module ℂ (Source F ζ hζ M S q) :=
  FourierContinuation.SourceReconstruction.localPlusModule F ζ hζ M (Sum.inr q.val)

 def localFixedLevel (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    Submodule ℂ (Source F ζ hζ M S q) where
  carrier := { f | ∀ j ∈ U q, ∀ g, f.val (g * j) = f.val g }
  zero_mem' := by
    change ∀ j ∈ U q, ∀ g, (0 : Source F ζ hζ M S q).val (g * j) = 0
    intros
    rfl
  add_mem' := by
    intro f h hf hh j hj g
    exact congrArg₂ (· + ·) (hf j hj g) (hh j hj g)
  smul_mem' := by
    intro c f hf j hj g
    exact congrArg (c • ·) (hf j hj g)

 abbrev LocalCosets (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :=
  (M q.val).iwasawa.compact.toOpenSubgroup ⧸
    (compactSlotStabilizer F ζ hζ M S U q).toSubgroup

 theorem localCosets_finite
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    Finite (LocalCosets F ζ hζ M S U q) := by
  let : CompactSpace (M q.val).iwasawa.compact.toOpenSubgroup :=
    isCompact_iff_compactSpace.mp (M q.val).iwasawa.compact.isCompact
  let : IsTopologicalGroup (M q.val).iwasawa.compact.toOpenSubgroup :=
    Topology.IsInducing.isTopologicalGroup
      (Subgroup.subtype (M q.val).iwasawa.compact.toOpenSubgroup.toSubgroup)
      Topology.IsInducing.subtypeVal
  exact Subgroup.quotient_finite_of_isOpen _
    (compactSlotStabilizer F ζ hζ M S U q).isOpen

 def localSampling (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    localFixedLevel F ζ hζ M S U q →ₗ[ℂ]
      (LocalCosets F ζ hζ M S U q → Fiber F ζ hζ M S q) where
  toFun f c := f.val.val (c.out : Cover F ζ hζ S q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem localSampling_representative
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S)
    (f : localFixedLevel F ζ hζ M S U q)
    (k : (M q.val).iwasawa.compact.toOpenSubgroup) :
    localSampling F ζ hζ M S U q f (QuotientGroup.mk k) = f.val.val k := by
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul
    (s := (compactSlotStabilizer F ζ hζ M S U q).toSubgroup) k
  change f.val.val (((QuotientGroup.mk k : LocalCosets F ζ hζ M S U q).out) :
    Cover F ζ hζ S q) = _
  rw [hj]
  exact f.property (j.val : Cover F ζ hζ S q) j.property k

 theorem localSampling_injective
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    Function.Injective (localSampling F ζ hζ M S U q) := by
  intro f h he
  apply Subtype.ext
  apply Subtype.ext
  funext g
  let b := (M q.val).iwasawa.borelPart g
  let k := (M q.val).iwasawa.compactPart g
  have hk : f.val.val (k : Cover F ζ hζ S q) = h.val.val (k : Cover F ζ hζ S q) := by
    have hh := congrFun he (QuotientGroup.mk k)
    rw [localSampling_representative, localSampling_representative] at hh
    exact hh
  have hd := (M q.val).iwasawa.decomposition g
  rw [hd, f.val.property.1, h.val.property.1, hk]

private theorem localFixedLevel_finite
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    Module.Finite ℂ (localFixedLevel F ζ hζ M S U q) := by
  let : Module.Finite ℂ (Fiber F ζ hζ M S q) :=
    KPLocalStoneVonNeumann.tau_moduleFinite (M q.val).heisenberg
      (M q.val).polarization
  let : Finite (LocalCosets F ζ hζ M S U q) := localCosets_finite F ζ hζ M S U q
  let : Module.Finite ℂ (LocalCosets F ζ hζ M S U q → Fiber F ζ hζ M S q) :=
    inferInstance
  let : IsNoetherian ℂ (LocalCosets F ζ hζ M S U q → Fiber F ζ hζ M S q) :=
    isNoetherian_of_isNoetherianRing_of_finite ℂ _
  exact Module.Finite.of_injective (localSampling F ζ hζ M S U q)
    (localSampling_injective F ζ hζ M S U q)

local instance (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    Finite (LocalCosets F ζ hζ M S U q) := localCosets_finite F ζ hζ M S U q

 def localSamplingFinsupp
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    localFixedLevel F ζ hζ M S U q →ₗ[ℂ]
      (LocalCosets F ζ hζ M S U q →₀ Fiber F ζ hζ M S q) :=
  (Finsupp.linearEquivFunOnFinite ℂ (Fiber F ζ hζ M S q)
    (LocalCosets F ζ hζ M S U q)).symm.toLinearMap.comp
      (localSampling F ζ hζ M S U q)

private theorem localSamplingFinsupp_injective
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) (q : S) :
    Function.Injective (localSamplingFinsupp F ζ hζ M S U q) :=
  (Finsupp.linearEquivFunOnFinite ℂ (Fiber F ζ hζ M S q)
    (LocalCosets F ζ hζ M S U q)).symm.injective.comp
      (localSampling_injective F ζ hζ M S U q)

 def tensorCosetSampling
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S U q) →ₗ[ℂ]
      (CompactCosets F ζ hζ M S U → ProductFiber F ζ hζ M S) :=
  (Finsupp.linearEquivFunOnFinite ℂ (ProductFiber F ζ hζ M S)
    (CompactCosets F ζ hζ M S U)).toLinearMap.comp
      (PiTensorProduct.ofFinsuppEquiv.toLinearMap.comp
        (PiTensorProduct.map (fun q => localSamplingFinsupp F ζ hζ M S U q)))

private theorem tensorCosetSampling_injective
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    Function.Injective (tensorCosetSampling F ζ hζ M S U) := by
  have hmap : Function.Injective
      (PiTensorProduct.map (fun q => localSamplingFinsupp F ζ hζ M S U q)) := by
    let retract (q : S) := LinearMap.leftInverse (K := ℂ)
      (V := localFixedLevel F ζ hζ M S U q)
      (V' := LocalCosets F ζ hζ M S U q →₀ Fiber F ζ hζ M S q)
      (localSamplingFinsupp F ζ hζ M S U q)
    have hleft :
        (PiTensorProduct.map retract).comp
          (PiTensorProduct.map (fun q => localSamplingFinsupp F ζ hζ M S U q)) =
        LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      have hh : (fun q => (retract q).comp
        (localSamplingFinsupp F ζ hζ M S U q)) = fun q => LinearMap.id := by
        funext q
        have hk : (localSamplingFinsupp F ζ hζ M S U q).ker = ⊥ := by
          exact (LinearMap.ker_eq_bot (R := ℂ) (R₂ := ℂ)
            (M := localFixedLevel F ζ hζ M S U q)
            (M₂ := LocalCosets F ζ hζ M S U q →₀ Fiber F ζ hζ M S q)).mpr
              (localSamplingFinsupp_injective F ζ hζ M S U q)
        exact LinearMap.leftInverse_comp_of_inj (K := ℂ)
          (V := localFixedLevel F ζ hζ M S U q)
          (V' := LocalCosets F ζ hζ M S U q →₀ Fiber F ζ hζ M S q) hk
      rw [hh, PiTensorProduct.map_id]
    intro x y he
    have hh := congrArg (PiTensorProduct.map retract) he
    change ((PiTensorProduct.map _).comp (PiTensorProduct.map _)) x =
      ((PiTensorProduct.map _).comp (PiTensorProduct.map _)) y at hh
    simpa only [hleft, LinearMap.id_apply] using hh
  exact (Finsupp.linearEquivFunOnFinite ℂ (ProductFiber F ζ hζ M S)
    (CompactCosets F ζ hζ M S U)).injective.comp
      (PiTensorProduct.ofFinsuppEquiv.injective.comp hmap)

 theorem tensorCosetSampling_formula
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (x : PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S U q))
    (c : CompactCosets F ζ hζ M S U) :
    tensorCosetSampling F ζ hζ M S U x c =
      tensorEvaluation F ζ hζ M S
        (PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q) x)
        (fun q => ((c q).out : Cover F ζ hζ S q)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, PiTensorProduct.mapIncl, PiTensorProduct.map_tprod]
    change r • (tensorCosetSampling F ζ hζ M S U (PiTensorProduct.tprod ℂ x)) c =
      r • (tensorEvaluation F ζ hζ M S (PiTensorProduct.tprod ℂ (fun q => (x q).val))) _
    congr 1
    simp only [tensorCosetSampling, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      PiTensorProduct.map_tprod, PiTensorProduct.ofFinsuppEquiv_apply,
      Finsupp.linearEquivFunOnFinite_apply]
    change PiTensorProduct.tprod ℂ (fun q => localSamplingFinsupp F ζ hζ M S U q (x q) (c q)) = _
    simp only [localSamplingFinsupp, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Finsupp.linearEquivFunOnFinite_symm_apply, localSampling]
    change _ = PiTensorProduct.map _ (PiTensorProduct.tprod ℂ _)
    rw [PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

 theorem fixedTensorEvaluation_injective
    (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q)) :
    Function.Injective ((tensorEvaluation F ζ hζ M S).comp
      (PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q))) := by
  intro x y he
  apply tensorCosetSampling_injective F ζ hζ M S U
  funext c
  rw [tensorCosetSampling_formula, tensorCosetSampling_formula]
  exact congrFun he (fun q => ((c q).out : Cover F ζ hζ S q))

 theorem localFixedLevel_antitone
    (U V : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (hUV : ∀ q, U q ≤ V q) (q : S) :
    localFixedLevel F ζ hζ M S V q ≤ localFixedLevel F ζ hζ M S U q := by
  intro f hf j hj g
  exact hf j (hUV q hj) g

 def fixedTensorInclusion
    (U V : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (hUV : ∀ q, U q ≤ V q) :
    PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S V q) →ₗ[ℂ]
      PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S U q) :=
  PiTensorProduct.map (fun q => Submodule.inclusion
    (localFixedLevel_antitone F ζ hζ M S U V hUV q))

 theorem fixedTensorInclusion_comp
    (U V : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
    (hUV : ∀ q, U q ≤ V q) :
    (PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q)).comp
      (fixedTensorInclusion F ζ hζ M S U V hUV) =
        PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S V q) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    fixedTensorInclusion, PiTensorProduct.mapIncl, PiTensorProduct.map_tprod,
    Submodule.inclusion_apply, Submodule.subtype_apply]

private theorem tensor_mem_local_fixed_level
    (x : PiTensorProduct ℂ (Source F ζ hζ M S)) :
    ∃ (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))
      (y : PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S U q)),
      PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q) y = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    choose U hU using fun q => (x q).property.2
    have hx (q : S) : x q ∈ localFixedLevel F ζ hζ M S U q := by
      intro j hj g
      exact congrFun (hU q j hj) g
    refine ⟨U, c • PiTensorProduct.tprod ℂ (fun q => ⟨x q, hx q⟩), ?_⟩
    simp only [map_smul, PiTensorProduct.mapIncl, PiTensorProduct.map_tprod,
      Submodule.subtype_apply]
  | add x y hx hy =>
    obtain ⟨U, x', hx'⟩ := hx
    obtain ⟨V, y', hy'⟩ := hy
    let W : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q) := fun q => U q ⊓ V q
    have hWU : ∀ q, W q ≤ U q := fun q => inf_le_left
    have hWV : ∀ q, W q ≤ V q := fun q => inf_le_right
    refine ⟨W, fixedTensorInclusion F ζ hζ M S W U hWU x' +
      fixedTensorInclusion F ζ hζ M S W V hWV y', ?_⟩
    rw [map_add]
    change ((PiTensorProduct.mapIncl _).comp
      (fixedTensorInclusion F ζ hζ M S W U hWU)) x' +
      ((PiTensorProduct.mapIncl _).comp
        (fixedTensorInclusion F ζ hζ M S W V hWV)) y' = _
    rw [fixedTensorInclusion_comp, fixedTensorInclusion_comp, hx', hy']

 theorem tensorEvaluation_injective :
    Function.Injective (tensorEvaluation F ζ hζ M S) := by
  intro x y he
  obtain ⟨U, z, hz⟩ := tensor_mem_local_fixed_level F ζ hζ M S (x - y)
  have hzero : ((tensorEvaluation F ζ hζ M S).comp
      (PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q))) z = 0 := by
    rw [LinearMap.comp_apply, hz, map_sub, he]
    funext g
    exact sub_self ((tensorEvaluation F ζ hζ M S) y g)
  have hz0 : z = 0 := fixedTensorEvaluation_injective F ζ hζ M S U (by
    rw [hzero, map_zero])
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

end DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel

end
