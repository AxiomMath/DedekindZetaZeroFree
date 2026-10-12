module

public import DedekindZetaZeroFree.Metaplectic.Kubota.Borel.FiniteCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
open WildCurrentGlobalMap KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance archExteriorDecidablePlace : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def archPlaces : Finset (KPHilbert.Place F) := Finset.univ.image Sum.inl

def archRaw (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) :=
  WildRestrictedTruncation.truncate _ (compact F R.A.zeta12 R.A.primitive_zeta12) a (archPlaces (F := F))

def finiteRaw (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) := (archRaw (R := R) a)⁻¹ * a

theorem archRaw_finite (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (q : KPFinitePlace F) : archRaw (R := R) a (Sum.inr q) = 1 := by
  change (if Sum.inr q ∈ archPlaces (F := F) then a (Sum.inr q) else 1) = 1
  simp [archPlaces]

theorem finiteRaw_arch (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (w : InfinitePlace F) : finiteRaw (R := R) a (Sum.inl w) = 1 := by
  change (if Sum.inl w ∈ archPlaces (F := F) then a (Sum.inl w) else 1)⁻¹ * a (Sum.inl w) = 1
  simp [archPlaces]

theorem finiteRaw_finite (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (q : KPFinitePlace F) : finiteRaw (R := R) a (Sum.inr q) = a (Sum.inr q) := by
  change (archRaw (R := R) a (Sum.inr q))⁻¹ * a (Sum.inr q) = _
  rw [archRaw_finite, inv_one, one_mul]

theorem raw_arch_finite_split (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) :
    rawGlobal (R := R) (archRaw a) * rawGlobal (R := R) (finiteRaw a) = rawGlobal (R := R) a := by
  rw [← map_mul]
  apply congrArg (rawGlobal (R := R))
  exact mul_inv_cancel_left (archRaw a) a

def JointArchExterior (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) : Prop :=
  ∀ h : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12,
    (∀ q : KPFinitePlace F, h (Sum.inr q) = 1) →
    ∀ (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12),
      (∀ w : InfinitePlace F, a (Sum.inl w) = 1) → ∃ c : ℂ,
      ∀ z : AmbientTensor F W (fiber D W),
        fourier R D.sources.dq (globalMap D W s hW x z)
          (rawGlobal (R := R) h * rawGlobal (R := R) a) =
        c * fourier R D.sources.dq (globalMap D W s hW x z) (rawGlobal (R := R) a)

theorem joint_kernel_all_borel_of_arch_exterior (D : TensorDetected R N)
    (W : Finset (KPFinitePlace F)) (s : RestrictedTensorSimple.Level D.bad)
    (hW : places W ⊆ s.val) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (hx : coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s x ≠ 0)
    (ht : ∀ q : KPFinitePlace F, Sum.inr q ∉ places W →
      WildCurrentTameExterior.tameSlot (Sum.inr q))
    (H : JointArchExterior D.toTensorActions W s hW x)
    (f : ∀ v, ScalarSections F R.A.zeta12 R.A.primitive_zeta12 W
      (depth (R := R) W) (character W) v)
    (e : JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W (character W)
      (fiber D.toTensorActions W) (action D.toTensorActions W))
    (he : WildCurrentJointForm.jointForm D.toTensorActions W s hW x e = 0)
    (b : KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12) :
    fourier R D.sources.dq (globalMap D.toTensorActions W s hW x
      (tensorEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
        (depth (R := R) W) (depth_valid (R := R) W) (character W)
        (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W)
        (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e))) b.val = 0 := by
  let u := tensorEmbedding F R.A.zeta12 R.A.primitive_zeta12 W
    (depth (R := R) W) (depth_valid (R := R) W) (character W)
    (fiber D.toTensorActions W) (action D.toTensorActions W) (localData D.toTensorActions W)
    (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] e)
  let θ : Functions R := globalMap D.toTensorActions W s hW x u
  let a := Classical.choose (exists_raw_borel (R := R) b)
  have ha := (Classical.choose_spec (exists_raw_borel (R := R) b)).1
  have hb := (Classical.choose_spec (exists_raw_borel (R := R) b)).2
  let hfactor := H (archRaw (R := R) a) (archRaw_finite (R := R) a)
    (finiteRaw (R := R) a) (finiteRaw_arch (R := R) a)
  let c := Classical.choose hfactor
  have hc := Classical.choose_spec hfactor
  have hfinite := joint_kernel_finite_raw D W s hW x hx ht (finiteRaw (R := R) a)
    (finiteRaw_arch (R := R) a) (fun q ↦ by simpa only [finiteRaw_finite (R := R)] using hb q.val) f e he
  have hzero : fourier R D.sources.dq θ
      (rawGlobal (R := R) (archRaw a) * rawGlobal (R := R) (finiteRaw a)) = 0 := by
    exact (hc u).trans
      ((congrArg (fun t : ℂ ↦ c * t) hfinite).trans (mul_zero c))
  calc
    _ = fourier R D.sources.dq θ (rawGlobal (R := R) a) := congrArg (fourier R D.sources.dq θ) ha.symm
    _ = fourier R D.sources.dq θ
        (rawGlobal (R := R) (archRaw a) * rawGlobal (R := R) (finiteRaw a)) :=
      congrArg (fourier R D.sources.dq θ) (raw_arch_finite_split (R := R) a).symm
    _ = 0 := hzero
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
