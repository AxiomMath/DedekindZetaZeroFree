module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.CharacterTensorFibers

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.WildJointCoinvariantDescent
variable {I : Type} [Fintype I]
  {G H V : I → Type} [∀ i, Group (G i)] [∀ i, Group (H i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ (G i) (V i))
  (u : ∀ i, H i →* G i) (χ : ∀ i, H i →* ℂˣ)
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem exists_descent (L : PiTensorProduct ℂ V →ₗ[ℂ] ℂ)
    (hL : ∀ (x : ∀ i, V i) i (t : H i) (v : V i),
      L (PiTensorProduct.tprod ℂ (Function.update x i (ρ i (u i t) v))) =
        (χ i t : ℂ) * L (PiTensorProduct.tprod ℂ (Function.update x i v))) :
    ∃ l : PiTensorProduct ℂ (fun i => RootCoinvariants (ρ i) (u i) (χ i)) →ₗ[ℂ] ℂ,
      l.comp (PiTensorProduct.map (fun i => rootCoinvariantsMk (ρ i) (u i) (χ i))) = L := by
  let q := fun i => rootCoinvariantsMk (ρ i) (u i) (χ i)
  have hs : ∀ i, ∃ s : RootCoinvariants (ρ i) (u i) (χ i) →ₗ[ℂ] V i,
      (q i).comp s = LinearMap.id := by
    intro i
    exact LinearMap.exists_rightInverse_of_surjective _
      (LinearMap.range_eq_top.mpr (rootCoinvariantsMk_surjective _ _ _))
  choose s hs using hs
  have hqs (i) (v) : q i (s i v) = v := LinearMap.congr_fun (hs i) v
  have hslot (x : ∀ i, V i) (i) (v : V i) :
      L (PiTensorProduct.tprod ℂ (Function.update x i (s i (q i v)))) =
        L (PiTensorProduct.tprod ℂ (Function.update x i v)) := by
    let T : V i →ₗ[ℂ] ℂ := L.comp ((PiTensorProduct.tprod ℂ).toLinearMap x i)
    let E : RootEquivariantMaps (ρ i) (u i) (χ i) ℂ := ⟨T,by
      intro t v
      exact hL x i t v⟩
    let l := rootCoinvariantsLift (ρ i) (u i) (χ i) E
    have hl (v : V i) : l (q i v) = T v := rfl
    calc
      _ = l (q i (s i (q i v))) := (hl _).symm
      _ = l (q i v) := congrArg l (hqs i (q i v))
      _ = _ := hl v
  have hreplace (x : ∀ i, V i) (A : Finset I) :
      L (PiTensorProduct.tprod ℂ (A.piecewise (fun i => s i (q i (x i))) x)) =
        L (PiTensorProduct.tprod ℂ x) := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert i A hi ih =>
      let y := A.piecewise (fun j => s j (q j (x j))) x
      have hy : y i = x i := by simp [y,hi]
      have he : (insert i A).piecewise (fun j => s j (q j (x j))) x =
          Function.update y i (s i (q i (x i))) := by
        funext j
        by_cases hj : j = i
        · subst j; simp
        · simp [Finset.piecewise,y,hj]
      rw [he,hslot]
      have hu : Function.update y i (x i) = y := by rw [←hy,Function.update_eq_self]
      rw [hu]
      exact ih
  refine ⟨L.comp (PiTensorProduct.map s),?_⟩
  apply PiTensorProduct.ext
  ext x
  change L (PiTensorProduct.map s (PiTensorProduct.map q (PiTensorProduct.tprod ℂ x))) = _
  rw [PiTensorProduct.map_tprod,PiTensorProduct.map_tprod]
  simpa using hreplace x Finset.univ
end DedekindZetaZeroFree.FourierContinuation.WildJointCoinvariantDescent

end
