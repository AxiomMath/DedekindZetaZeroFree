module

public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationFiniteLevelCovers
public import DedekindZetaZeroFree.Metaplectic.Intertwining.FiniteLevelCompactTypeFactorization
public import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts
public import DedekindZetaZeroFree.Eisenstein.Residues.AdelicChamberContinuationData
public import DedekindZetaZeroFree.Metaplectic.Torus.UpperRootNormalization
public import DedekindZetaZeroFree.RepresentationTheory.Induction.FiniteDimensionalIntertwiners
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.RightConvolutionApproximation

@[expose] public section

section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.KPSpatialSamplingClosure
open CovariantSampling
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

theorem covariant_smooth_approximation_closed
    {G X W : Type*} [Group G]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (C K J : Subgroup G) (chi : C →* ℂ) (n : ℕ) (r : Fin n → G)
    (hcover : ∀ g : G, ∃ (i : Fin n) (c : C) (k : K) (j : J),
      g = c.val * r i * k.val * j.val)
    (hnormalize : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
    (tau : Representation ℂ K W) (chart : X → G) (O : Set X)
    (i : tau.IntertwiningMap (rho_J C K J chi hnormalize))
    (t : ℕ → tau.IntertwiningMap (rho_J C K J chi hnormalize))
    (ht : ∀ m w g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (t m w).val (chart z * g)) O)
    (w : W) (hlim : ∀ g, Filter.Tendsto (fun m => (t m w).val g)
      Filter.atTop (𝓝 ((i w).val g))) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (i w).val (chart z * g)) O := by
  let A := tau.IntertwiningMap (rho_J C K J chi hnormalize)
  letI : AddCommGroup A := inferInstance
  let B : Submodule ℂ A := {
    carrier := {t | ∀ w g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (t w).val (chart z * g)) O}
    zero_mem' := by intro w g; exact contDiffOn_const
    add_mem' := by
      intro t u ht hu w g
      exact (ht w g).add (hu w g)
    smul_mem' := by
      intro a t ht w g
      exact contDiffOn_const.mul (ht w g) }
  let ev : A →ₗ[ℂ] (G → ℂ) := {
    toFun := fun t => (t w).val
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let U := B.map ev
  let : FiniteDimensional ℂ A :=
    intertwiningMap_finiteDimensional C K J chi n r hcover hnormalize tau
  let : FiniteDimensional ℂ B := inferInstance
  let : FiniteDimensional ℂ U := inferInstance
  have hu : (i w).val ∈ U := by
    apply U.closed_of_finiteDimensional.mem_of_tendsto
      (tendsto_pi_nhds.mpr hlim)
    exact Filter.Eventually.of_forall (fun m => Submodule.mem_map.mpr
      ⟨t m, ht m, rfl⟩)
  obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp hu
  intro g
  have hs := ha w g
  change ev a = (i w).val at he
  rw [← he]
  exact hs

end DedekindZetaZeroFree.KPSpatialSamplingClosure

end

end

section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.KPSpatialCovariantOrbit
open CovariantSampling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {G : Type*} [Group G]
variable (C K J : Subgroup G) (chi : C →* ℂ)
variable (hn : ∀ (k : K) (j : J), k.val⁻¹ * j.val * k.val ∈ J)
variable (v : V_J C J chi)

theorem orbit_finiteDimensional
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun k : K => fun g => v.val (g * k.val))))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun k : K => rho_J C K J chi hn k v))) := by
  let W := Submodule.span ℂ (Set.range (fun k : K => rho_J C K J chi hn k v))
  let i := (V_J C J chi).subtype
  have he : W.map i = Submodule.span ℂ (Set.range
      (fun k : K => fun g => v.val (g * k.val))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  let : FiniteDimensional ℂ (W.map i) := by rw [he]; exact hfin
  exact FiniteDimensional.of_injective
    ((i.comp W.subtype).codRestrict (W.map i)
      (fun w => Submodule.mem_map.mpr ⟨w.val, w.property, rfl⟩))
    (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : W.map i => z.val) h)

theorem orbit_stable :
    ∀ k : K, (Submodule.span ℂ (Set.range
      (fun l : K => rho_J C K J chi hn l v))) ≤
      (Submodule.span ℂ (Set.range
        (fun l : K => rho_J C K J chi hn l v))).comap (rho_J C K J chi hn k) := by
  intro k w hw
  let rho := rho_J C K J chi hn
  let W := Submodule.span ℂ (Set.range (fun l : K => rho l v))
  change rho k w ∈ W
  apply Submodule.span_induction (p := fun w _ => rho k w ∈ W) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨l, rfl⟩
    have he : rho k (rho l v) = rho (k * l) v := by rw [map_mul]; rfl
    rw [he]
    exact Submodule.subset_span ⟨k * l, rfl⟩
  · simpa using W.zero_mem
  · intro x y hx hy hxm hym
    simpa only [map_add] using W.add_mem hxm hym
  · intro c x hx hxm
    simpa only [map_smul] using W.smul_mem c hxm

theorem orbit_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    (hv : Continuous v.val)
    (w : Submodule.span ℂ (Set.range (fun l : K => rho_J C K J chi hn l v))) :
    Continuous w.val.val := by
  apply Submodule.span_induction (p := fun w _ => Continuous w.val) ?_ ?_ ?_ ?_ w.property
  · rintro _ ⟨k, rfl⟩
    exact hv.comp (continuous_id.mul continuous_const)
  · exact continuous_const
  · intro x y hx hy hxc hyc
    exact hxc.add hyc
  · intro c x hx hxc
    exact continuous_const.mul hxc

end DedekindZetaZeroFree.KPSpatialCovariantOrbit

end

end
