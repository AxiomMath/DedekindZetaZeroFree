module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.FrozenTensor

@[expose] public section

noncomputable section
open scoped Classical
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

theorem independent_slot_word {I : Type*} [DecidableEq I] {V : I → Type*}
    {G : Type*} [Group G] {E : Type*}
    (T : (∀ i, V i) → G → E) (L : ∀ i, V i → V i) (a : I → G)
    (h : ∀ i x g, T (Function.update x i (L i (x i))) g = T x (g * a i))
    (l : List I) (hl : l.Nodup) (x : ∀ i, V i) (g : G) :
    T (fun i => if i ∈ l then L i (x i) else x i) g =
      T x (g * (l.reverse.map a).prod) := by
  induction l generalizing x g with
  | nil => simp
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    let y := Function.update x i (L i (x i))
    have he : (fun j => if j ∈ i :: l then L j (x j) else x j) =
        (fun j => if j ∈ l then L j (y j) else y j) := by
      funext j
      by_cases hj : j = i
      · subst j; simp [y,hi]
      · simp [List.mem_cons, hj, y, Function.update_of_ne hj]
    rw [he, ih hl' y]
    change T (Function.update x i (L i (x i))) _ = _
    rw [h]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.prod_append, List.prod_singleton, mul_assoc]

theorem list_single_product {I J : Type*} [DecidableEq I] [DecidableEq J]
    {G : J → Type*} [∀ j, Group (G j)] (e : I → J) (he : Function.Injective e)
    (a : ∀ i, G (e i)) (l : List I) (hl : l.Nodup) (i : I) :
    ((l.map (fun i => Pi.mulSingle (e i) (a i))).prod) (e i) =
      if i ∈ l then a i else 1 := by
  induction l with
  | nil => simp
  | cons u l ih =>
    have hn := List.nodup_cons.mp hl
    by_cases hu : u = i
    · subst u
      have hz : (l.map (fun u => Pi.mulSingle (e u) (a u) (e i))).prod = 1 := by
        apply List.prod_eq_one
        intro b hb
        obtain ⟨u,hu,hb⟩ := List.mem_map.mp hb
        rw [← hb]
        apply Pi.mulSingle_eq_of_ne
        intro h
        have hui : u = i := he h.symm
        exact hn.1 (hui ▸ hu)
      simp only [List.map_cons,List.prod_cons,Pi.mul_apply,Pi.mulSingle_eq_same,
        List.mem_cons_self,ite_true]
      have heval : (l.map (fun u => Pi.mulSingle (e u) (a u))).prod (e i) =
          (l.map (fun u => Pi.mulSingle (e u) (a u) (e i))).prod := by
        exact (map_list_prod (Pi.evalMonoidHom G (e i)) _).trans (by simp only [List.map_map]; rfl)
      rw [heval,hz,mul_one]
    · simp only [List.map_cons,List.prod_cons,Pi.mul_apply,
        Pi.mulSingle_eq_of_ne (he.ne (Ne.symm hu)),one_mul,ih hn.2,List.mem_cons]
      simp only [Ne.symm hu, false_or]

theorem list_single_product_off {I J : Type*} [DecidableEq J] {G : J → Type*}
    [∀ j, Group (G j)] (e : I → J) (a : ∀ i, G (e i)) (l : List I)
    (j : J) (hj : ∀ i ∈ l, j ≠ e i) :
    ((l.map (fun i => Pi.mulSingle (e i) (a i))).prod) j = 1 := by
  change (Pi.evalMonoidHom G j) ((l.map (fun i => Pi.mulSingle (e i) (a i))).prod) = 1
  rw [map_list_prod]
  simp only [List.map_map]
  change (l.map (fun i => Pi.mulSingle (e i) (a i) j)).prod = 1
  apply List.prod_eq_one
  intro b hb
  obtain ⟨i,hi,hb⟩ := List.mem_map.mp hb
  rw [← hb]
  exact Pi.mulSingle_eq_of_ne (hj i hi) _

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
