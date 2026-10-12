module

public import DedekindZetaZeroFree.RepresentationTheory.Heisenberg.ContinuousMaximalPolarizations
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

section

namespace DedekindZetaZeroFree.KPLocalHeisenbergPolarization

open DedekindZetaZeroFree.FinitePolarization

theorem maximal_isotropic_index {D : Type*} [CommGroup D] [Finite D]
    (b : D →* (D →* rootsOfUnity 3 ℂ))
    (halt : ∀ d : D, b d d = 1) (hperfect : Function.Bijective b)
    (L : Subgroup D) (hL : IsMaximalIsotropic b L) :
    L.index = Nat.sqrt (Nat.card D) := by
  classical
  have hexp : ∀ x : D, x ^ 3 = 1 := by
    intro x
    apply hperfect.1
    apply MonoidHom.ext
    intro y
    change b (x ^ 3) y = b 1 y
    simp only [map_pow, map_one, MonoidHom.pow_apply, MonoidHom.one_apply]
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp (b x y).property
  let p : D →* (D →* ℂˣ) := (MonoidHom.compHom (rootsOfUnity 3 ℂ).subtype).comp b
  have hp : Function.Bijective p := by
    constructor
    · intro x y h
      apply hperfect.1
      apply MonoidHom.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f : D →* ℂˣ => f z) h
    · intro f
      let f' : D →* rootsOfUnity 3 ℂ := f.codRestrict _ (fun x => by
        rw [mem_rootsOfUnity, ← map_pow, hexp, map_one])
      obtain ⟨x, hx⟩ := hperfect.2 f'
      refine ⟨x, ?_⟩
      apply MonoidHom.ext
      intro z
      exact congrArg (fun g : D →* rootsOfUnity 3 ℂ => (g z : ℂˣ)) hx
  have horth := orthogonal_eq_of_isMaximalIsotropic b halt hL
  let k := (MonoidHom.domRestrictHom L ℂˣ).ker
  have hmem : ∀ x : D, p x ∈ k ↔ x ∈ L := by
    intro x
    change (MonoidHom.domRestrictHom L ℂˣ) (p x) = 1 ↔ x ∈ L
    have hr : x ∈ L ↔ ∀ l : L, b (l : D) x = 1 := by
      rw [← mem_orthogonal, horth]
    rw [hr]
    constructor
    · intro hx l
      have h := congrArg (fun f : L →* ℂˣ => f l) hx
      have h' : b x l = 1 := Subtype.ext h
      rw [pairing_swap_inv b halt, h', inv_one]
    · intro hx
      apply MonoidHom.ext
      intro l
      change (b x l : ℂˣ) = 1
      rw [pairing_swap_inv b halt, hx, inv_one]
      rfl
  let f : L → k := fun x => ⟨p x, (hmem x).mpr x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hp.1 (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := hp.2 y
      have hxL : x ∈ L := (hmem x).mp (hx ▸ y.property)
      exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩
  have hc : Nat.card L = L.index := by
    rw [Nat.card_congr (Equiv.ofBijective f hf)]
    exact (CommGroup.card_domRestrictHom_ker ℂ L).trans L.index_eq_card.symm
  rw [← L.card_mul_index, hc, Nat.sqrt_eq]

end DedekindZetaZeroFree.KPLocalHeisenbergPolarization

end

section

namespace DedekindZetaZeroFree.KPLocalHeisenbergPolarization

theorem finite_of_scalar_finite_index {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (hρ : ρ.IsIrreducible) (C : Subgroup H) [C.FiniteIndex]
    (ω : C →* ℂˣ) (hscalar : ∀ (c : C) (v : V),
      ρ (c : H) v = (ω c : ℂ) • v) : Module.Finite ℂ V := by
  classical
  letI : ρ.IsIrreducible := hρ
  nontriviality V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let W : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range fun g : H => ρ g v)
      apply_mem_toSubmodule := by
        intro g x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          apply Submodule.subset_span
          exact ⟨g * k, by simp [map_mul]⟩
        | zero => simpa using (Submodule.zero_mem (Submodule.span ℂ
            (Set.range fun k : H => ρ k v)))
        | add x y hx hy ihx ihy =>
          simpa using Submodule.add_mem _ ihx ihy
        | smul a x hx ih =>
          simpa using Submodule.smul_mem _ a ih }
  have hvW : v ∈ W := by
    change v ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v)
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (by
    intro h
    have : v = 0 := by
      have hmem : v ∈ (⊥ : Subrepresentation ρ) := h ▸ hvW
      exact (show v ∈ (⊥ : Submodule ℂ V) from hmem)
    exact hv this)
  let f : H ⧸ C → V := fun q => ρ q.out v
  have horbit : ∀ g : H, ρ g v ∈ Submodule.span ℂ (Set.range f) := by
    intro g
    let q : H ⧸ C := QuotientGroup.mk g
    have hc : q.out⁻¹ * g ∈ C := QuotientGroup.eq.mp (Quotient.out_eq' q)
    let c : C := ⟨q.out⁻¹ * g, hc⟩
    have hg : g = q.out * (c : H) := by simp [c]
    rw [hg, map_mul]
    change ρ q.out (ρ (c : H) v) ∈ Submodule.span ℂ (Set.range f)
    rw [hscalar, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
    apply top_unique
    have hwtop : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule hW
    rw [← hwtop]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr horbit)
  exact ⟨⟨(Set.finite_range f).toFinset, by
    simpa using hspan⟩⟩

end DedekindZetaZeroFree.KPLocalHeisenbergPolarization

end

section

namespace DedekindZetaZeroFree.KPLocalHeisenbergPolarization

open scoped commutatorElement
open DedekindZetaZeroFree.FinitePolarization

private theorem trace_off_center {H D V : Type*}
    [Group H] [CommGroup D] [Finite D] [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (C : Subgroup H) (π : H →* D) (hπ : Function.Surjective π)
    (ω : C →* ℂˣ) (b : D →* (D →* rootsOfUnity 3 ℂ))
    (halt : ∀ d : D, b d d = 1) (hperfect : Function.Bijective b)
    (hcomm : ∀ x y : H, ⁅x, y⁆ ∈ C)
    (hpair : ∀ x y : H, ω ⟨⁅x, y⁆, hcomm x y⟩ = (b (π x) (π y) : ℂˣ))
    (ρ : Representation ℂ H V)
    (hscalar : ∀ (c : C) (v : V), ρ (c : H) v = (ω c : ℂ) • v)
    (a : H) (ha : π a ≠ 1) : LinearMap.trace ℂ V (ρ a) = 0 := by
  have hex : ∃ d : D, b d (π a) ≠ 1 := by
    by_contra hh
    push Not at hh
    apply ha
    apply hperfect.1
    apply MonoidHom.ext
    intro d
    rw [map_one, MonoidHom.one_apply, pairing_swap_inv b halt, hh, inv_one]
  obtain ⟨d, hd⟩ := hex
  obtain ⟨g, hg⟩ := hπ d
  let z : ℂ := ((b d (π a) : ℂˣ) : ℂ)
  have hz : z ≠ 1 := by
    intro h
    apply hd
    apply Subtype.ext
    apply Units.ext
    exact h
  have hconj : ρ g * ρ a * ρ g⁻¹ = z • ρ a := by
    have hc : ρ ⁅g, a⁆ = z • (1 : Module.End ℂ V) := by
      ext v
      rw [hscalar ⟨⁅g, a⁆, hcomm g a⟩ v, hpair, hg]
      rfl
    calc
      ρ g * ρ a * ρ g⁻¹ = ρ (⁅g, a⁆ * a) := by
        rw [← map_mul, ← map_mul]
        congr 1
        rw [commutatorElement_def]
        group
      _ = z • ρ a := by rw [map_mul, hc, smul_mul_assoc, one_mul]
  have ht : LinearMap.trace ℂ V (ρ a) = z * LinearMap.trace ℂ V (ρ a) := by
    calc
      _ = LinearMap.trace ℂ V (ρ g * ρ a * ρ g⁻¹) := by
        symm
        simpa only [← map_inv, Representation.asGroupHom_apply] using
          LinearMap.trace_conj ℂ (ρ a) (ρ.asGroupHom g)
      _ = _ := by rw [hconj, map_smul, smul_eq_mul]
  exact (mul_eq_zero.mp (by linear_combination -ht :
    (z - 1) * LinearMap.trace ℂ V (ρ a) = 0)).resolve_left (sub_ne_zero.mpr hz)

private theorem finite_average_functional {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
    (τ : Representation ℂ G V)
    (ht : ∀ g : G, g ≠ 1 → LinearMap.trace ℂ V (τ g) = 0) :
    ∃ ℓ : V →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧ ∀ (g : G) (v : V), ℓ (τ g v) = ℓ v := by
  classical
  letI := Fintype.ofFinite G
  let P : Module.End ℂ V := ∑ g : G, τ g
  have htr : LinearMap.trace ℂ V P = (Module.finrank ℂ V : ℂ) := by
    dsimp [P]
    rw [map_sum]
    rw [Finset.sum_eq_single 1]
    · rw [map_one, LinearMap.trace_one]
    · intro g _ hg
      exact ht g hg
    · simp
  have hP : P ≠ 0 := by
    intro hh
    rw [hh, map_zero] at htr
    exact (Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℂ) (M := V)))) htr.symm
  have hinv (g : G) : P * τ g = P := by
    dsimp [P]
    rw [Finset.sum_mul]
    simp_rw [← map_mul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)
  obtain ⟨v, hv⟩ : ∃ v : V, P v ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hP (LinearMap.ext hh)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  refine ⟨f.comp P, ?_, ?_⟩
  · intro hh
    exact hf (LinearMap.congr_fun hh v)
  · intro g v
    change f ((P * τ g) v) = f (P v)
    rw [hinv]

theorem exists_polarization_eigenfunctional {H D V : Type*}
    [Group H] [CommGroup D] [Finite D] [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (C : Subgroup H) (hC : C ≤ Subgroup.center H)
    (π : H →* D) (hπ : Function.Surjective π) (hker : π.ker = C)
    (ω : C →* ℂˣ) (b : D →* (D →* rootsOfUnity 3 ℂ))
    (halt : ∀ d : D, b d d = 1) (hperfect : Function.Bijective b)
    (hcomm : ∀ x y : H, ⁅x, y⁆ ∈ C)
    (hpair : ∀ x y : H, ω ⟨⁅x, y⁆, hcomm x y⟩ = (b (π x) (π y) : ℂˣ))
    (L : Subgroup D) (hL : IsMaximalIsotropic b L)
    (χ : L.comap π →* ℂˣ)
    (hext : ∀ a : L.comap π, ∀ ha : (a : H) ∈ C,
      χ a = ω ⟨(a : H), ha⟩)
    (ρ : Representation ℂ H V) (hρ : ρ.IsIrreducible)
    (hscalar : ∀ (c : C) (v : V), ρ (c : H) v = (ω c : ℂ) • v) :
    ∃ ℓ : V →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
      ∀ (a : L.comap π) (v : V), ℓ (ρ (a : H) v) = (χ a : ℂ) * ℓ v := by
  classical
  haveI : ρ.IsIrreducible := hρ
  haveI : Nontrivial V := by
    by_contra hn
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have hh : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.ext
      ext v
      simp [Subsingleton.elim v 0]
    exact bot_ne_top hh
  let A := L.comap π
  let f : A →* L := π.subgroupComap L
  have hf : Function.Surjective f := π.subgroupComap_surjective_of_surjective L hπ
  let σ : Representation ℂ A V :=
    { toFun := fun a => ((χ a : ℂ)⁻¹) • ρ (a : H)
      map_one' := by simp
      map_mul' := by
        intro a a'
        simp only [map_mul, Subgroup.coe_mul, Units.val_mul, mul_inv_rev]
        rw [smul_mul_smul_comm, mul_comm] }
  have hk : f.ker ≤ σ.asGroupHom.ker := by
    intro a ha
    have haC : (a : H) ∈ C := by
      rw [← hker]
      apply MonoidHom.mem_ker.mpr
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change ((χ a : ℂ)⁻¹) • ρ (a : H) = 1
    ext v
    change ((χ a : ℂ)⁻¹) • ρ (a : H) v = v
    rw [hscalar ⟨a, haC⟩ v, ← hext a haC, smul_smul, inv_mul_cancel₀ (Units.ne_zero _)]
    simp
  let t : L →* (Module.End ℂ V)ˣ := f.liftOfSurjective hf ⟨σ.asGroupHom, hk⟩
  let τ : Representation ℂ L V := (Units.coeHom _).comp t
  have he (a : A) : τ (f a) = σ a := by
    have h := f.liftOfRightInverse_comp_apply (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨σ.asGroupHom, hk⟩ a
    exact congrArg Units.val h
  have ht (l : L) (hl : l ≠ 1) : LinearMap.trace ℂ V (τ l) = 0 := by
    obtain ⟨a, rfl⟩ := hf l
    rw [he]
    change LinearMap.trace ℂ V (((χ a : ℂ)⁻¹) • ρ (a : H)) = 0
    rw [map_smul, trace_off_center C π hπ ω b halt hperfect hcomm hpair ρ hscalar]
    · simp
    · intro ha
      apply hl
      exact Subtype.ext ha
  obtain ⟨ℓ, hℓ, hinv⟩ := finite_average_functional τ ht
  refine ⟨ℓ, hℓ, ?_⟩
  intro a v
  have hh := hinv (f a) v
  rw [he] at hh
  change ℓ (((χ a : ℂ)⁻¹) • ρ (a : H) v) = ℓ v at hh
  rw [map_smul, smul_eq_mul] at hh
  calc
    ℓ (ρ (a : H) v) = (χ a : ℂ) * ((χ a : ℂ)⁻¹ * ℓ (ρ (a : H) v)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    _ = _ := by rw [hh]

end DedekindZetaZeroFree.KPLocalHeisenbergPolarization

end

section

namespace DedekindZetaZeroFree.KPLocalHeisenbergPolarization

open DedekindZetaZeroFree.FinitePolarization

theorem coefficient_intertwiner {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℂ V]
    (A : Subgroup H) (χ : A →* ℂˣ)
    (ρ : Representation ℂ H V)
    (σ : Representation ℂ H (inducedSpace A χ))
    (htranslate : ∀ (g : H) (f : inducedSpace A χ) (x : H),
      (σ g f).val x = f.val (x * g))
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (hcov : ∀ (a : A) (v : V), ℓ (ρ (a : H) v) = (χ a : ℂ) * ℓ v) :
    ∃ F : Representation.IntertwiningMap ρ σ, F ≠ 0 ∧
      ∀ (v : V) (g : H), (F v).val g = ℓ (ρ g v) := by
  classical

  have hmem : ∀ v : V, (fun g : H => ℓ (ρ g v)) ∈ inducedSpace A χ := by
    intro v a g
    show ℓ (ρ ((a : H) * g) v) = (χ a : ℂ) * ℓ (ρ g v)
    rw [map_mul, Module.End.mul_apply, hcov a (ρ g v)]

  let φ : V →ₗ[ℂ] inducedSpace A χ :=
    { toFun := fun v => ⟨fun g => ℓ (ρ g v), hmem v⟩
      map_add' := fun v w => by
        apply Subtype.ext
        funext g
        simp
      map_smul' := fun c v => by
        apply Subtype.ext
        funext g
        simp [smul_eq_mul] }
  have hφval : ∀ (v : V) (g : H), (φ v).val g = ℓ (ρ g v) := fun v g => rfl

  have hφ : ∀ (g : H) (v : V), φ (ρ g v) = σ g (φ v) := by
    intro g v
    apply Subtype.ext
    funext x
    rw [htranslate g (φ v) x, hφval, hφval]
    show ℓ (ρ x (ρ g v)) = ℓ (ρ (x * g) v)
    rw [show ρ (x * g) v = ρ x (ρ g v) from by rw [map_mul, Module.End.mul_apply]]
  let F : Representation.IntertwiningMap ρ σ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ φ hφ
  have hFval : ∀ (v : V) (g : H), (F v).val g = ℓ (ρ g v) := by
    intro v g
    exact hφval v g
  refine ⟨F, ?_, hFval⟩

  intro hzero
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ v ≠ 0 :=
    not_forall.mp (fun hall => hℓ (LinearMap.ext hall))
  have h1 : (F v).val 1 = ℓ v := by
    rw [hFval v 1, map_one, Module.End.one_apply]
  have h2 : (F v).val 1 = 0 := by
    rw [hzero]
    rfl
  exact hv (by rw [← h1, h2])

end DedekindZetaZeroFree.KPLocalHeisenbergPolarization

end

section

namespace DedekindZetaZeroFree.KPLocalStoneVonNeumann

open scoped commutatorElement Valued
open ValuativeRel
open DedekindZetaZeroFree.FinitePolarization

structure LocalHeisenbergData (H D : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D] where
  C : Subgroup H
  central : C ≤ Subgroup.center H
  center_open : IsOpen (C : Set H)
  π : H →* D
  quotient_surjective : Function.Surjective π
  quotient_kernel : π.ker = C
  ω : C →ₜ* ℂˣ
  character_kernel_open : IsOpen {c : C | ω c = 1}
  pairing : D →* (D →* rootsOfUnity 3 ℂ)
  alternating : ∀ d : D, pairing d d = 1
  perfect : Function.Bijective pairing
  commutator_mem : ∀ x y : H, ⁅x, y⁆ ∈ C
  commutator_pairing : ∀ x y : H,
    ω ⟨⁅x, y⁆, commutator_mem x y⟩ = (pairing (π x) (π y) : ℂˣ)
  detects_commutation : ∀ x y : H, Commute x y ↔ pairing (π x) (π y) = 1

structure Polarization {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D] (T : LocalHeisenbergData H D) where
  L : Subgroup D
  maximal : IsMaximalIsotropic T.pairing L
  ωL : L.comap T.π →ₜ* ℂˣ
  extends_center : ∀ a : L.comap T.π, ∀ ha : (a : H) ∈ T.C,
    ωL a = T.ω ⟨(a : H), ha⟩

theorem inducedSpace_stable {H : Type*} [Group H] [TopologicalSpace H]
    (A : Subgroup H) (χ : A →* ℂˣ) (g : H) :
    inducedSpace A χ ≤ Submodule.comap
      (rightTranslationRepresentation (G := H) g) (inducedSpace A χ) := by
  intro f hf a x
  change f (((a : H) * x) * g) = (χ a : ℂ) * f (x * g)
  rw [mul_assoc, hf a (x * g)]

def inducedRepresentation {H : Type*} [Group H] [TopologicalSpace H]
    (A : Subgroup H) (χ : A →* ℂˣ) :
    Representation ℂ H (inducedSpace A χ) :=
  (rightTranslationRepresentation (G := H)).subrepresentation
    (inducedSpace A χ) (inducedSpace_stable A χ)

abbrev InducedModule {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    {T : LocalHeisenbergData H D} (P : Polarization T) :=
  inducedSpace (P.L.comap T.π) P.ωL.toMonoidHom

def tau {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    {T : LocalHeisenbergData H D} (P : Polarization T) :
    Representation ℂ H (InducedModule P) :=
  inducedRepresentation (P.L.comap T.π) P.ωL.toMonoidHom

def HasCentralCharacter {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    (C : Subgroup H) (ω : C →* ℂˣ) (ρ : Representation ℂ H V) : Prop :=
  ∀ (c : C) (v : V), ρ (c : H) v = (ω c : ℂ) • v

theorem tau_hasCentralCharacter {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) :
    HasCentralCharacter T.C T.ω.toMonoidHom (tau P) := by
  intro c f
  have hc : T.π (c : H) = 1 := by
    have hker : (c : H) ∈ T.π.ker := by rw [T.quotient_kernel]; exact c.property
    exact hker
  let a : P.L.comap T.π := ⟨c, by change T.π (c : H) ∈ P.L; rw [hc]; exact P.L.one_mem⟩
  apply Subtype.ext
  funext x
  change f.val (x * (c : H)) = (T.ω c : ℂ) * f.val x
  rw [Subgroup.mem_center_iff.mp (T.central c.property) x, f.property a x]
  change (P.ωL a : ℂ) * f.val x = (T.ω c : ℂ) * f.val x
  rw [P.extends_center a c.property]

theorem tau_smooth {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) : SmoothRepresentation (tau P) := by
  let J : Subgroup H := T.ω.toMonoidHom.ker.map T.C.subtype
  have hJ : IsOpen (J : Set H) :=
    T.center_open.isOpenMap_subtype_val _ T.character_kernel_open
  intro v
  refine ⟨⟨J, hJ⟩, ?_⟩
  intro j hj
  obtain ⟨c, hc, rfl⟩ := hj
  change tau P (c : H) v = v
  rw [tau_hasCentralCharacter T P c v]
  change T.ω.toMonoidHom c = 1 at hc
  change (T.ω c : ℂ) • v = v
  rw [show T.ω c = 1 from hc]
  simp

theorem tau_moduleFinite {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) : Module.Finite ℂ (InducedModule P) := by
  classical
  let r : D → H := Function.surjInv T.quotient_surjective
  have hr : ∀ d, T.π (r d) = d := Function.surjInv_eq T.quotient_surjective
  let ev : InducedModule P →ₗ[ℂ] (D → ℂ) :=
    { toFun := fun f d => f.val (r d)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Finite.of_injective ev
  intro f g hfg
  apply Subtype.ext
  funext x
  let y := r (T.π x)
  have ha : x * y⁻¹ ∈ P.L.comap T.π := by
    change T.π (x * y⁻¹) ∈ P.L
    rw [map_mul, map_inv, hr]
    simp
  let a : P.L.comap T.π := ⟨x * y⁻¹, ha⟩
  have hxy : (a : H) * y = x := by dsimp [a]; simp
  rw [← hxy, f.property a y, g.property a y]
  congr 1
  exact congrFun hfg (T.π x)

 noncomputable def inducedCosetEquiv {H : Type*} [Group H]
    (A : Subgroup H) [A.Normal] (χ : A →* ℂˣ) : inducedSpace A χ ≃ₗ[ℂ] (H ⧸ A → ℂ) := by
  classical
  let q : H →* H ⧸ A := QuotientGroup.mk' A
  let r := Function.surjInv (QuotientGroup.mk'_surjective A)
  have hr : ∀ d, q (r d) = d := Function.surjInv_eq (QuotientGroup.mk'_surjective A)
  let a (x : H) : A := ⟨x * (r (q x))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (x * (r (q x))⁻¹) = 1
    rw [map_mul, map_inv, hr, mul_inv_cancel]⟩
  have ha (b : A) (x : H) : a ((b : H) * x) = b * a x := by
    apply Subtype.ext
    have hb : q (b : H) = 1 := (QuotientGroup.eq_one_iff _).mpr b.property
    simp [a, map_mul, hb, mul_assoc]
  have har (d : H ⧸ A) : a (r d) = 1 := by
    apply Subtype.ext
    simp [a, hr]
  refine
    { toFun := fun f d => f.val (r d)
      invFun := fun f => ⟨fun x => (χ (a x) : ℂ) * f (q x), ?_⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro b x
    have hb : q (b : H) = 1 := (QuotientGroup.eq_one_iff _).mpr b.property
    simp [ha, map_mul, hb, mul_assoc]
  · intro f
    apply Subtype.ext
    funext x
    have hax : (a x : H) * r (q x) = x := by dsimp [a]; simp
    exact (f.property (a x) (r (q x))).symm.trans (by rw [hax])
  · intro f
    funext d
    simp [har, hr]

theorem tau_finrank_eq_index {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) :
    Module.finrank ℂ (InducedModule P) = (P.L.comap T.π).index := by
  classical
  let A := P.L.comap T.π
  letI : A.Normal := inferInstance
  letI : A.FiniteIndex := inferInstance
  letI : Fintype (H ⧸ A) := Fintype.ofFinite _
  rw [(inducedCosetEquiv A P.ωL.toMonoidHom).finrank_eq, Module.finrank_pi]
  exact (Nat.card_eq_fintype_card).symm

theorem diagonal_isolation {ι k : Type*} [Finite ι] [DecidableEq ι] [Field k]
    (S : Submodule k (ι → k))
    (hsep : ∀ i j : ι, i ≠ j → ∃ m : ι → k,
      m i ≠ m j ∧ ∀ f ∈ S, (fun a => m a * f a) ∈ S)
    (f : ι → k) (hf : f ∈ S) (i : ι) : Pi.single i (f i) ∈ S := by
  classical
  letI := Fintype.ofFinite ι
  have aux : ∀ s : Finset ι, ∃ g ∈ S, g i = f i ∧ ∀ j ∈ s, j ≠ i → g j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨f, hf, rfl, by simp⟩
    | @insert j s hjs ih =>
      obtain ⟨g, hg, hgi, hgz⟩ := ih
      by_cases hji : j = i
      · exact ⟨g, hg, hgi, by simpa [hji] using hgz⟩
      obtain ⟨m, hm, hSm⟩ := hsep i j (Ne.symm hji)
      let g' : ι → k := (m i - m j)⁻¹ • ((fun a => m a * g a) - m j • g)
      refine ⟨g', S.smul_mem _ (S.sub_mem (hSm g hg) (S.smul_mem _ hg)), ?_, ?_⟩
      · change (m i - m j)⁻¹ * (m i * g i - m j * g i) = f i
        rw [← sub_mul, inv_mul_cancel_left₀ (sub_ne_zero.mpr hm), hgi]
      · intro a ha hai
        rcases Finset.mem_insert.mp ha with rfl | ha
        · simp [g']
        · simp [g', hgz a ha hai]
  obtain ⟨g, hg, hgi, hgz⟩ := aux Finset.univ
  have he : g = Pi.single i (f i) := by
    funext j
    by_cases hji : j = i
    · subst j; simpa using hgi
    · simp [Pi.single_apply, hji, hgz j (Finset.mem_univ _) hji]
  exact he ▸ hg

theorem tau_diagonal_formula {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T)
    (a : P.L.comap T.π) (f : InducedModule P) (x : H) :
    (tau P (a : H) f).val x =
      (T.pairing (T.π x) (T.π a) : ℂˣ) * (P.ωL a : ℂ) * f.val x := by
  let c : T.C := ⟨⁅x, (a : H)⁆, T.commutator_mem x a⟩
  have hc : (c : H) ∈ P.L.comap T.π := by
    change T.π (c : H) ∈ P.L
    have hker : (c : H) ∈ T.π.ker := by rw [T.quotient_kernel]; exact c.property
    rw [show T.π (c : H) = 1 from hker]
    exact P.L.one_mem
  let b : P.L.comap T.π := ⟨c, hc⟩
  have hmul : x * (a : H) = (b : H) * ((a : H) * x) := by
    simp [b, c, commutatorElement_def, mul_assoc]
  change f.val (x * (a : H)) = _
  rw [hmul, f.property b, f.property a, ← mul_assoc]
  congr 2
  have hω := P.extends_center b c.property
  change (P.ωL b : ℂ) = _
  rw [hω]
  exact congrArg (fun u : ℂˣ => (u : ℂ)) (T.commutator_pairing x a)

theorem polarization_separates {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) (x y : H)
    (hxy : (x : H ⧸ P.L.comap T.π) ≠ y) :
    ∃ a : P.L.comap T.π,
      (T.pairing (T.π x) (T.π a) : ℂˣ) ≠ (T.pairing (T.π y) (T.π a) : ℂˣ) := by
  classical
  by_contra! h
  apply hxy
  apply QuotientGroup.eq_iff_div_mem.mpr
  change T.π (x / y) ∈ P.L
  rw [← orthogonal_eq_of_isMaximalIsotropic T.pairing T.alternating P.maximal,
    mem_orthogonal]
  intro l
  obtain ⟨a, ha⟩ := T.quotient_surjective l
  have haL : a ∈ P.L.comap T.π := by change T.π a ∈ P.L; rw [ha]; exact l.property
  have hh := h ⟨a, haL⟩
  have hh' : T.pairing (T.π x) (T.π a) = T.pairing (T.π y) (T.π a) :=
    Subtype.ext hh
  have hh'' : T.pairing (T.π a) (T.π x) = T.pairing (T.π a) (T.π y) := by
    rw [pairing_swap_inv T.pairing T.alternating (T.π x) (T.π a),
      pairing_swap_inv T.pairing T.alternating (T.π y) (T.π a), hh']
  change T.pairing (l : D) (T.π (x / y)) = 1
  rw [← ha, map_div, map_div, hh'']
  simp

theorem tau_irreducible {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) : (tau P).IsIrreducible := by
  classical
  let A := P.L.comap T.π
  letI : A.Normal := inferInstance
  letI : A.FiniteIndex := inferInstance
  letI : Fintype (H ⧸ A) := Fintype.ofFinite _
  let q : H →* H ⧸ A := QuotientGroup.mk' A
  let r := Function.surjInv (QuotientGroup.mk'_surjective A)
  have hr : ∀ d, q (r d) = d := Function.surjInv_eq (QuotientGroup.mk'_surjective A)
  let e := inducedCosetEquiv A P.ωL.toMonoidHom
  have he (f : InducedModule P) (d : H ⧸ A) : e f d = f.val (r d) := rfl
  have hn : Nontrivial (InducedModule P) := e.toEquiv.nontrivial
  letI := hn
  have hbt : (⊥ : Subrepresentation (tau P)) ≠ ⊤ := by
    intro h
    have hall : ∀ f : InducedModule P, f = 0 := by
      intro f
      have hf : f ∈ (⊥ : Subrepresentation (tau P)) := h ▸ (show f ∈ (⊤ : Subrepresentation (tau P)) from trivial)
      change f ∈ (⊥ : Submodule ℂ (InducedModule P)) at hf
      simpa using hf
    obtain ⟨f, hf⟩ := exists_ne (0 : InducedModule P)
    exact hf (hall f)
  letI : Nontrivial (Subrepresentation (tau P)) := ⟨⟨⊥, ⊤, hbt⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  let F := S.toSubmodule.map e.toLinearMap
  have hstable : ∀ a : A, ∀ f ∈ F,
      (fun d => ((T.pairing (T.π (r d)) (T.π a) : ℂˣ) : ℂ) *
        (P.ωL a : ℂ) * f d) ∈ F := by
    intro a f hf
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hf
    refine Submodule.mem_map.mpr ⟨tau P (a : H) v, S.apply_mem_toSubmodule a hv, ?_⟩
    funext d
    exact tau_diagonal_formula T P a v (r d)
  have hsep : ∀ i j : H ⧸ A, i ≠ j → ∃ m : H ⧸ A → ℂ,
      m i ≠ m j ∧ ∀ f ∈ F, (fun d => m d * f d) ∈ F := by
    intro i j hij
    have hrij : (r i : H ⧸ A) ≠ r j := by
      intro heq
      apply hij
      calc i = q (r i) := (hr i).symm
        _ = q (r j) := heq
        _ = j := hr j
    obtain ⟨a, ha⟩ := polarization_separates T P (r i) (r j) hrij
    refine ⟨fun d => ((T.pairing (T.π (r d)) (T.π a) : ℂˣ) : ℂ) * (P.ωL a : ℂ), ?_, ?_⟩
    · intro h
      apply ha
      apply Units.ext
      exact (mul_right_cancel₀ (Units.ne_zero (P.ωL a)) h)
    · intro f hf
      simpa [mul_assoc] using hstable a f hf
  have hF : F ≠ ⊥ := by
    intro h
    apply hS
    ext v
    change v ∈ S.toSubmodule ↔ v = 0
    constructor
    · intro hv
      apply e.injective
      have hv' : e v ∈ F := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      simpa [h] using hv'
    · rintro rfl; exact S.toSubmodule.zero_mem
  obtain ⟨f, hf, hf0⟩ := F.ne_bot_iff.mp hF
  have hfi : ∃ i, f i ≠ 0 := by
    by_contra! h
    exact hf0 (funext h)
  obtain ⟨i, hfi⟩ := hfi
  have hi : Pi.single i (f i) ∈ F := diagonal_isolation F hsep f hf i
  obtain ⟨v, hv, hvf⟩ := Submodule.mem_map.mp hi
  have hvfi : e v i = f i := by simpa using congrFun hvf i
  have hj : ∀ j : H ⧸ A, Pi.single j (1 : ℂ) ∈ F := by
    intro j
    let g := (r j)⁻¹ * r i
    have hg : e (tau P g v) ∈ F := Submodule.mem_map.mpr ⟨tau P g v, S.apply_mem_toSubmodule g hv, rfl⟩
    have hgj : e (tau P g v) j = f i := by
      change v.val (r j * g) = f i
      simpa [g] using (he v i).symm.trans hvfi
    have hsingle := diagonal_isolation F hsep _ hg j
    have hscaled := F.smul_mem (f i)⁻¹ hsingle
    convert hscaled using 1
    ext k
    by_cases hkj : k = j
    · subst k; simp [hgj, hfi]
    · simp [Pi.single_apply, hkj]
  apply top_unique
  intro v hv
  have heF : e v ∈ F := by
    rw [← Finset.univ_sum_single (e v)]
    apply F.sum_mem
    intro j hj'
    have := F.smul_mem (e v j) (hj j)
    convert this using 1
    ext k
    by_cases hkj : k = j
    · subst k; simp
    · simp [Pi.single_apply, hkj]
  obtain ⟨u, hu, heuv⟩ := Submodule.mem_map.mp heF
  have : u = v := e.injective heuv
  exact this ▸ hu

theorem finite_heisenberg_induction {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T) :
    Module.Finite ℂ (InducedModule P) ∧ SmoothRepresentation (tau P) ∧
      (tau P).IsIrreducible ∧ HasCentralCharacter T.C T.ω.toMonoidHom (tau P) ∧
      Module.finrank ℂ (InducedModule P) = (P.L.comap T.π).index ∧
      Module.finrank ℂ (InducedModule P) = Nat.sqrt (Nat.card D) := by
  refine ⟨tau_moduleFinite T P, tau_smooth T P, tau_irreducible T P,
    tau_hasCentralCharacter T P, tau_finrank_eq_index T P, ?_⟩
  rw [tau_finrank_eq_index T P,
    P.L.index_comap_of_surjective T.quotient_surjective]
  exact KPLocalHeisenbergPolarization.maximal_isotropic_index T.pairing
    T.alternating T.perfect P.L P.maximal

theorem stone_von_neumann_uniqueness {H D V : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D] [AddCommGroup V] [Module ℂ V]
    (T : LocalHeisenbergData H D) (P : Polarization T) (ρ : Representation ℂ H V)
    (hρ : ρ.IsIrreducible) (hsmooth : SmoothRepresentation ρ)
    (hcentral : HasCentralCharacter T.C T.ω.toMonoidHom ρ) :
    Nonempty (ρ.Equiv (tau P)) := by
  have hCindex : T.C.FiniteIndex := by
    rw [← T.quotient_kernel]
    infer_instance
  letI : T.C.FiniteIndex := hCindex
  letI : Module.Finite ℂ V :=
    KPLocalHeisenbergPolarization.finite_of_scalar_finite_index
      ρ hρ T.C T.ω.toMonoidHom hcentral
  obtain ⟨ℓ, hℓ, hcov⟩ :=
    KPLocalHeisenbergPolarization.exists_polarization_eigenfunctional
      T.C T.central T.π T.quotient_surjective T.quotient_kernel
      T.ω.toMonoidHom T.pairing T.alternating T.perfect
      T.commutator_mem T.commutator_pairing P.L P.maximal
      P.ωL.toMonoidHom P.extends_center ρ hρ hcentral
  obtain ⟨F, hF, _⟩ := KPLocalHeisenbergPolarization.coefficient_intertwiner
    (P.L.comap T.π) P.ωL.toMonoidHom ρ (tau P)
    (by intro g f x; rfl) ℓ hℓ hcov
  letI : ρ.IsIrreducible := hρ
  letI : (tau P).IsIrreducible := tau_irreducible T P
  exact ⟨F.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero F).resolve_right hF)⟩

theorem independence_of_polarization {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P Q : Polarization T) :
    Nonempty ((tau P).Equiv (tau Q)) := by
  obtain ⟨_, hsmooth, hirr, hcentral, _⟩ := finite_heisenberg_induction T P
  exact stone_von_neumann_uniqueness T Q (tau P) hirr hsmooth hcentral

def weylConjugate {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    {T : LocalHeisenbergData H D} (P : Polarization T) (w : H ≃ₜ* H) :
    Representation ℂ H (InducedModule P) := (tau P).comp w.toMulEquiv.toMonoidHom

private theorem smooth_comp {H V : Type*} [Group H] [TopologicalSpace H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (w : H ≃ₜ* H) (h : SmoothRepresentation ρ) :
    SmoothRepresentation (ρ.comp w.toMulEquiv.toMonoidHom) := by
  intro v
  obtain ⟨J, hJ⟩ := h v
  refine ⟨J.comap w.toMulEquiv.toMonoidHom w.continuous, ?_⟩
  intro j hj
  exact hJ (w j) hj

 def compSubrepresentationOrderIso {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (w : H ≃* H) :
    Subrepresentation (ρ.comp w.toMonoidHom) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    simpa using S.apply_mem_toSubmodule (w.symm g) hv⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (w g) hv⟩
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

private theorem irreducible_comp {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (w : H ≃* H)
    (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp w.toMonoidHom) :=
  (compSubrepresentationOrderIso ρ w).isSimpleOrder_iff.mpr h

theorem weyl_conjugate_properties {H D : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CommGroup D] [Finite D]
    (T : LocalHeisenbergData H D) (P : Polarization T)
    (w : H ≃ₜ* H) (wC : T.C ≃* T.C)
    (hwC : ∀ c : T.C, (wC c : H) = w (c : H)) :
    Module.Finite ℂ (InducedModule P) ∧ SmoothRepresentation (weylConjugate P w) ∧
      (weylConjugate P w).IsIrreducible ∧
      HasCentralCharacter T.C (T.ω.toMonoidHom.comp wC.toMonoidHom)
        (weylConjugate P w) ∧
      Module.finrank ℂ (InducedModule P) = Nat.sqrt (Nat.card D) := by
  obtain ⟨hfin, hsmooth, hirr, hcentral, _, hdim⟩ := finite_heisenberg_induction T P
  refine ⟨hfin, smooth_comp (tau P) w hsmooth,
    irreducible_comp (tau P) w.toMulEquiv hirr, ?_, hdim⟩
  intro c v
  change tau P (w (c : H)) v = _
  rw [← hwC c]
  exact hcentral (wC c) v

end DedekindZetaZeroFree.KPLocalStoneVonNeumann

end
