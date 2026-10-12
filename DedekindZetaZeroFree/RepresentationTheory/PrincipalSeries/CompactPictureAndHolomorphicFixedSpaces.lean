module

public import DedekindZetaZeroFree.RepresentationTheory.Heisenberg.LocalStoneVonNeumann

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalPrincipalSeriesRaw
noncomputable section
universe u v
variable {G : Type u} {V : Type v} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V]

def rightTranslation : Representation ℂ G (G → V) where
  toFun g :=
    { toFun := fun f x => f (x * g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_assoc]

def Covariant (B : Subgroup G) (σ : Representation ℂ B V) (f : G → V) : Prop :=
  (∀ (b : B) (g : G), f ((b : G) * g) = σ b (f g)) ∧
  SmoothVector rightTranslation f

def CompactCovariant (B : Subgroup G) (L : OpenSubgroup G)
    (σ : Representation ℂ B V) (φ : L → V) : Prop :=
  (∀ (b : B) (k k' : L), (k' : G) = (b : G) * (k : G) → φ k' = σ b (φ k)) ∧
  SmoothVector rightTranslation φ

def compactExtension (B : Subgroup G) (L : OpenSubgroup G)
    (σ : Representation ℂ B V) (r : G → B) (k : G → L) (φ : L → V) : G → V :=
  fun g => σ (r g) (φ (k g))

def CompactFixed (L : OpenSubgroup G) (J : OpenSubgroup G) (φ : L → V) : Prop :=
  ∀ (j : J) (k k' : L), (k' : G) = (k : G) * (j : G) → φ k' = φ k

private theorem extension_restrict (B : Subgroup G) (L : OpenSubgroup G)
    (σ : Representation ℂ B V) (r : G → B) (k : G → L)
    (hr : ∀ l : L, r (l : G) = 1) (hk : ∀ l : L, k (l : G) = l)
    (φ : L → V) (l : L) : compactExtension B L σ r k φ l = φ l := by
  simp [compactExtension, hr, hk]

private theorem extension_covariance (B : Subgroup G) (L : OpenSubgroup G)
    (σ₀ σ : Representation ℂ B V) (r : G → B) (k : G → L)
    (hdec : ∀ g : G, g = (r g : G) * (k g : G))
    (hagree : ∀ b : B, (b : G) ∈ L → σ b = σ₀ b)
    (φ : L → V) (hφ : CompactCovariant B L σ₀ φ) :
    ∀ (b : B) (g : G), compactExtension B L σ r k φ ((b : G) * g) =
      σ b (compactExtension B L σ r k φ g) := by
  intro b g
  let a : B := (r ((b : G) * g))⁻¹ * b * r g
  have heq : (k ((b : G) * g) : G) = (a : G) * (k g : G) := by
    have h := hdec ((b : G) * g)
    conv at h => lhs; rhs; rw [hdec g]
    dsimp [a]
    apply (mul_left_cancel (a := (r ((b : G) * g) : G)))
    simpa [mul_assoc] using h.symm
  have ha : (a : G) ∈ L := by
    have hh : (a : G) = (k ((b : G) * g) : G) * (k g : G)⁻¹ := by
      rw [heq]; group
    rw [hh]
    exact L.mul_mem (k _).property (L.inv_mem (k _).property)
  have hv := hφ.1 a (k g) (k ((b : G) * g)) heq
  unfold compactExtension
  rw [hv, ← hagree a ha]
  change (σ (r ((b : G) * g)) * σ a) (φ (k g)) =
    (σ b * σ (r g)) (φ (k g))
  rw [← map_mul, ← map_mul]
  congr 2
  dsimp [a]
  group

private theorem extension_fixed (B : Subgroup G) (L : OpenSubgroup G)
    (σ : Representation ℂ B V) (r : G → B) (k : G → L)
    (hdec : ∀ g : G, g = (r g : G) * (k g : G))
    (hr : ∀ l : L, r (l : G) = 1) (hk : ∀ l : L, k (l : G) = l)
    (φ : L → V)
    (hcov : ∀ (b : B) (g : G), compactExtension B L σ r k φ ((b : G) * g) =
      σ b (compactExtension B L σ r k φ g))
    (J : OpenSubgroup G) (hJ : (J : Subgroup G) ≤ L) :
    CompactFixed L J φ ↔ ∀ j : J, rightTranslation (j : G)
      (compactExtension B L σ r k φ) = compactExtension B L σ r k φ := by
  constructor
  · intro hφ j
    funext g
    change compactExtension B L σ r k φ (g * (j : G)) = _
    let l' : L := ⟨(k g : G) * (j : G), L.mul_mem (k g).property (hJ j.property)⟩
    have hg : g * (j : G) = (r g : G) * (l' : G) := by
      dsimp [l']; rw [← mul_assoc, ← hdec g]
    rw [hg, hcov, extension_restrict B L σ r k hr hk φ l',
      hφ j (k g) l' rfl]
    rfl
  · intro hφ j l l' heq
    have hh := congrFun (hφ j) (l : G)
    change compactExtension B L σ r k φ ((l : G) * (j : G)) =
      compactExtension B L σ r k φ (l : G) at hh
    rw [← heq, extension_restrict B L σ r k hr hk φ l',
      extension_restrict B L σ r k hr hk φ l] at hh
    exact hh

theorem fixed_iwasawa_laws (B : Subgroup G) (L : OpenSubgroup G)
    (σ₀ σ : Representation ℂ B V) (r : G → B) (k : G → L)
    (hdec : ∀ g : G, g = (r g : G) * (k g : G))
    (hr : ∀ l : L, r (l : G) = 1) (hk : ∀ l : L, k (l : G) = l)
    (hagree : ∀ b : B, (b : G) ∈ L → σ b = σ₀ b) :
    CompactCovariant B L σ₀ 0 ∧
    (∀ φ ψ, CompactCovariant B L σ₀ φ → CompactCovariant B L σ₀ ψ →
      CompactCovariant B L σ₀ (φ + ψ)) ∧
    (∀ (c : ℂ) φ, CompactCovariant B L σ₀ φ → CompactCovariant B L σ₀ (c • φ)) ∧
    (∀ φ, CompactCovariant B L σ₀ φ → Covariant B σ (compactExtension B L σ r k φ)) ∧
    (∀ f, Covariant B σ f → CompactCovariant B L σ₀ (fun l => f (l : G))) ∧
    (∀ φ, (fun l : L => compactExtension B L σ r k φ (l : G)) = φ) ∧
    (∀ f, Covariant B σ f → compactExtension B L σ r k (fun l => f (l : G)) = f) ∧
    (∀ (J : OpenSubgroup G), (J : Subgroup G) ≤ L →
      ∀ φ, CompactCovariant B L σ₀ φ →
      (CompactFixed L J φ ↔
        ∀ j : J, rightTranslation (j : G) (compactExtension B L σ r k φ) =
          compactExtension B L σ r k φ)) := by
  have hres : ∀ φ, (fun l : L => compactExtension B L σ r k φ (l : G)) = φ := by
    intro φ; funext l
    exact extension_restrict B L σ r k hr hk φ l
  have hext : ∀ φ, CompactCovariant B L σ₀ φ → Covariant B σ
      (compactExtension B L σ r k φ) := by
    intro φ hφ
    have hc := extension_covariance B L σ₀ σ r k hdec hagree φ hφ
    refine ⟨hc, ?_⟩
    obtain ⟨K, hK⟩ := hφ.2
    let J : OpenSubgroup G :=
      ⟨(K : Subgroup L).map (L : Subgroup G).subtype, by
        change IsOpen (Subtype.val '' (K : Set L))
        exact K.isOpen.trans L.isOpen⟩
    have hJL : (J : Subgroup G) ≤ L := by
      rintro j ⟨l, hl, rfl⟩; exact l.property
    refine ⟨J, ?_⟩
    intro j hj
    apply (extension_fixed B L σ r k hdec hr hk φ hc J hJL).mp ?_ ⟨j, hj⟩
    intro j l l' heq
    obtain ⟨a, ha, he⟩ := j.property
    have hh := congrFun (hK a ha) l
    change φ (l * a) = φ l at hh
    have he' : l' = l * a := by
      apply Subtype.ext
      change (l' : G) = (l : G) * (a : G)
      change (a : G) = (j : G) at he
      rw [he]
      exact heq
    rw [he']; exact hh
  have hrest : ∀ f, Covariant B σ f → CompactCovariant B L σ₀ (fun l => f (l : G)) := by
    intro f hf
    constructor
    · intro b l l' heq
      have hb : (b : G) ∈ L := by
        have he : (b : G) = (l' : G) * (l : G)⁻¹ := by rw [heq]; group
        rw [he]; exact L.mul_mem l'.property (L.inv_mem l.property)
      change f (l' : G) = σ₀ b (f (l : G))
      rw [heq, hf.1, hagree b hb]
    · obtain ⟨J, hj⟩ := hf.2
      refine ⟨J.comap (L : Subgroup G).subtype continuous_subtype_val, ?_⟩
      intro j hmem
      funext l
      exact congrFun (hj (j : G) hmem) (l : G)
  refine ⟨?_, ?_, ?_, hext, hrest, hres, ?_, ?_⟩
  · exact ⟨by intros; simp, ⟨⊤, by intros; simp⟩⟩
  · intro φ ψ hφ hψ
    constructor
    · intro b l l' heq
      simp only [Pi.add_apply, hφ.1 b l l' heq, hψ.1 b l l' heq, map_add]
    · obtain ⟨Jφ, hjφ⟩ := hφ.2
      obtain ⟨Jψ, hjψ⟩ := hψ.2
      refine ⟨Jφ ⊓ Jψ, ?_⟩
      intro j hj
      change rightTranslation j (φ + ψ) = φ + ψ
      rw [map_add, hjφ j hj.1, hjψ j hj.2]
  · intro c φ hφ
    constructor
    · intro b l l' heq
      simp only [Pi.smul_apply, hφ.1 b l l' heq, map_smul]
    · obtain ⟨Jφ, hjφ⟩ := hφ.2
      refine ⟨Jφ, ?_⟩
      intro j hj
      change rightTranslation j (c • φ) = c • φ
      rw [map_smul, hjφ j hj]
  · intro f hf
    funext g
    change σ (r g) (f (k g : G)) = f g
    rw [← hf.1, ← hdec g]
  · intro J hJ φ hφ
    exact extension_fixed B L σ r k hdec hr hk φ (hext φ hφ).1 J hJ

def compactFixedSpace (B : Subgroup G) (L J : OpenSubgroup G)
    (σ₀ : Representation ℂ B V) : Submodule ℂ (L → V) where
  carrier := {φ | CompactCovariant B L σ₀ φ ∧ CompactFixed L J φ}
  zero_mem' := by
    constructor
    · exact ⟨by intros; simp, by
        exact ⟨⊤, by intros; simp⟩⟩
    · intro j l l' hh; rfl
  add_mem' := by
    rintro φ ψ ⟨hφ, fφ⟩ ⟨hψ, fψ⟩
    constructor
    · constructor
      · intro b l l' hh
        simp only [Pi.add_apply, hφ.1 b l l' hh, hψ.1 b l l' hh, map_add]
      · obtain ⟨Jφ, hjφ⟩ := hφ.2
        obtain ⟨Jψ, hjψ⟩ := hψ.2
        refine ⟨Jφ ⊓ Jψ, ?_⟩
        intro j hj
        change rightTranslation j (φ + ψ) = φ + ψ
        rw [map_add, hjφ j hj.1, hjψ j hj.2]
    · intro j l l' hh
      simp only [Pi.add_apply, fφ j l l' hh, fψ j l l' hh]
  smul_mem' := by
    rintro c φ ⟨hφ, fφ⟩
    constructor
    · constructor
      · intro b l l' hh
        simp only [Pi.smul_apply, hφ.1 b l l' hh, map_smul]
      · obtain ⟨Jφ, hjφ⟩ := hφ.2
        refine ⟨Jφ, ?_⟩
        intro j hj
        change rightTranslation j (c • φ) = c • φ
        rw [map_smul, hjφ j hj]
    · intro j l l' hh
      simp only [Pi.smul_apply, fφ j l l' hh]

theorem finite_level_and_holomorphic [IsTopologicalGroup G]
    (B : Subgroup G) (L J : OpenSubgroup G)
    (σ₀ : Representation ℂ B V) (hL : IsCompact (L : Set G))
    (hJ : (J : Subgroup G) ≤ L) [Module.Finite ℂ V]
    (σ : ℂ → Representation ℂ B V) (r : G → B) (k : G → L)
    (eval : V →ₗ[ℂ] ℂ)
    (hentire : ∀ (b : B) (v : V), Differentiable ℂ (fun s => eval (σ s b v))) :
    (∀ {U : Type (max u v)} [AddCommMonoid U] [Module ℂ U]
      (ev : U →ₗ[ℂ] compactFixedSpace B L J σ₀),
      Function.Injective ev → Module.Finite ℂ U) ∧
    (∀ (φ : compactFixedSpace B L J σ₀) (g x : G),
      Differentiable ℂ (fun s => eval (compactExtension B L (σ s) r k φ.val (x * g)))) := by
  constructor
  · intro U _ _ ev hev
    let K : Subgroup L := (J : Subgroup G).subgroupOf (L : Subgroup G)
    have hK : IsOpen (K : Set L) :=
      (J.isOpen).preimage continuous_subtype_val
    haveI : IsTopologicalGroup L :=
      Topology.IsInducing.subtypeVal.isTopologicalGroup (L : Subgroup G).subtype
    haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
    haveI : Finite (L ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
    let E : compactFixedSpace B L J σ₀ →ₗ[ℂ] ((L ⧸ K) → V) :=
      { toFun := fun φ q => φ.val (Quotient.out q)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hE : Function.Injective E := by
      intro φ ψ he
      apply Subtype.ext
      funext l
      let q : L ⧸ K := QuotientGroup.mk l
      have hj : ((l : G)⁻¹ * (Quotient.out q : L)) ∈ J := by
        have hmem : l⁻¹ * Quotient.out q ∈ K :=
          QuotientGroup.eq.mp (Quotient.out_eq q).symm
        exact hmem
      have hprod : (Quotient.out q : L) = (l : G) *
          ((⟨_, hj⟩ : J) : G) := by simp
      have hφ := φ.property.2 ⟨_, hj⟩ l (Quotient.out q) hprod
      have hψ := ψ.property.2 ⟨_, hj⟩ l (Quotient.out q) hprod
      exact hφ.symm.trans ((congrFun he q).trans hψ)
    haveI : Module.Finite ℂ ((L ⧸ K) → V) := inferInstance
    haveI : Module.Finite ℂ (compactFixedSpace B L J σ₀) :=
      Module.Finite.of_injective E hE
    exact Module.Finite.of_injective ev hev
  · intro φ g x
    exact hentire (r (x * g)) (φ.val (k (x * g)))
end
end DedekindZetaZeroFree.KPLocalPrincipalSeriesRaw
