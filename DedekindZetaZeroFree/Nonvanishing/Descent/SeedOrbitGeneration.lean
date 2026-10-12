module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.CyclicSeed

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem stage_image_le_of_seed_orbit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {A : ι → Type*} (op : ∀ i, A i → Module.End ℂ (V i))
    (v : ∀ i, V i) (hv : tupleOrbitSpan op v = ⊤)
    (L : PiTensorProduct ℂ V →ₗ[ℂ] Functions R) (M : Submodule ℂ (Functions R))
    (horbit : ∀ a, L (tupleOperator op a (PiTensorProduct.tprod ℂ v)) ∈ M) :
    ∀ x, L x ∈ M := by
  intro x
  have hx : x ∈ tupleOrbitSpan op v := hv ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact horbit a
  | zero => simpa only [map_zero] using M.zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using M.add_mem ihx ihy
  | smul c x hx ihx => simpa only [map_smul] using M.smul_mem c ihx

theorem generated_of_detected_seed_orbits (D : Dictionary R N)
    (s : RestrictedTensorSimple.Level D.bad)
    (v : ∀ p : s.val, actualLocal R D.finiteData p)
    (hs : s.val = D.bad) (hv : ∀ p, v p ≠ 0)
    (horbit : ∀ (t : RestrictedTensorSimple.Level D.bad)
      (a : ∀ p : t.val, LocalOperation R p),
      D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad t
        (tupleOperator (fun p : t.val => localOperation R D.finiteData p) a
          (PiTensorProduct.tprod ℂ (insertedSeed D s t v)))) ∈ hcHeckeSpan D.realization) :
    ∀ x, D.coreMap x ∈ hcHeckeSpan D.realization := by
  intro x
  letI : Nonempty (RestrictedTensorSimple.Level D.bad) := ⟨s⟩
  obtain ⟨t, y, rfl⟩ := Module.DirectLimit.exists_of x
  exact stage_image_le_of_seed_orbit
    (fun p : t.val => localOperation R D.finiteData p)
    (insertedSeed D s t v) (insertedSeed_cyclic D s t hs v hv)
    (D.coreMap.comp (RestrictedTensorSimple.stageInclusion _ D.references D.bad t))
    (hcHeckeSpan D.realization) (horbit t) y

def faithfulGeneratedOfSeedOrbits (D : Faithful R N)
    (s : RestrictedTensorSimple.Level D.bad)
    (v : ∀ p : s.val, actualLocal R D.finiteData p)
    (hs : s.val = D.bad) (hv : ∀ p, v p ≠ 0)
    (horbit : ∀ (t : RestrictedTensorSimple.Level D.bad)
      (a : ∀ p : t.val, LocalOperation R p),
      D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad t
        (tupleOperator (fun p : t.val => localOperation R D.finiteData p) a
          (PiTensorProduct.tprod ℂ (insertedSeed D.toDictionary s t v)))) ∈ hcHeckeSpan D.realization) :
    Generated R N where
  toFaithful := D
  generated := generated_of_detected_seed_orbits D.toDictionary s v hs hv horbit

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
