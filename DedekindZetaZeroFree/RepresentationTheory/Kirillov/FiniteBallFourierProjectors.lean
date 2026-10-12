module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalFields.BallAnnihilators
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

namespace DedekindZetaZeroFree.KPKirillovFiniteBallProjectors

open scoped NumberField Classical
open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (𝓞 F))

def rootRepresentation {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) V) :
    Representation ℂ (Multiplicative (w.adicCompletion F)) V :=
  ρ.comp (KPLocalSmoothRepresentation.upperRoot F ζ hζ w)

abbrev IsSmooth {V : Type*} [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) V) :=
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  SmoothRepresentation ρ

def FixedByBall {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) V)
    (l : ℤ) (v : V) : Prop :=
  ∀ x ∈ finiteCompletionBall F w l,
    rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v = v

abbrev DualQuotient (u l : ℤ) :=
  KPRootAverage.LevelQuotient
    (localFiniteAnnihilator F w (finiteCompletionBall F w l))
    (localFiniteAnnihilator F w (finiteCompletionBall F w u))

 theorem phase_eq_of_mk_eq (u l : ℤ) (t : w.adicCompletion F)
    (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l))
    {a b : finiteCompletionBall F w u}
    (h : (QuotientAddGroup.mk a : finiteCompletionBallQuotient F w u l) =
      QuotientAddGroup.mk b) :
    localFiniteCharacter F w (t * (a : w.adicCompletion F)) =
      localFiniteCharacter F w (t * (b : w.adicCompletion F)) := by
  have hab' : a - b ∈ finiteCompletionBallSubgroup F w u l :=
    QuotientAddGroup.eq_iff_sub_mem.mp h
  have hab : (a : w.adicCompletion F) - (b : w.adicCompletion F) ∈
      finiteCompletionBall F w l := hab'
  have hp := ht _ hab
  rw [mul_comm, mul_sub, AddChar.map_sub_eq_div, div_eq_one] at hp
  exact hp

def quotientCharacter (u l : ℤ) (t : w.adicCompletion F)
    (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l)) :
    AddChar (finiteCompletionBallQuotient F w u l) Circle where
  toFun q := localFiniteCharacter F w
    (t * ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F))
  map_zero_eq_one' := by
    have h : (QuotientAddGroup.mk (Quotient.out (0 : finiteCompletionBallQuotient F w u l)) :
        finiteCompletionBallQuotient F w u l) = QuotientAddGroup.mk 0 := by
      simpa using (Quotient.out_eq (0 : finiteCompletionBallQuotient F w u l))
    simpa using phase_eq_of_mk_eq F w u l t ht h
  map_add_eq_mul' := by
    intro a b
    have h : (QuotientAddGroup.mk (Quotient.out (a + b)) :
        finiteCompletionBallQuotient F w u l) =
        QuotientAddGroup.mk (Quotient.out a + Quotient.out b) := by
      change (QuotientAddGroup.mk' (finiteCompletionBallSubgroup F w u l)) _ =
        (QuotientAddGroup.mk' (finiteCompletionBallSubgroup F w u l)) _
      rw [map_add]
      simp only [QuotientAddGroup.mk'_apply, Quotient.out_eq]
    simpa only [AddSubgroup.coe_add, mul_add, AddChar.map_add_eq_mul] using
      phase_eq_of_mk_eq F w u l t ht h

theorem quotientCharacter_mk (u l : ℤ) (t : w.adicCompletion F)
    (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l))
    (x : finiteCompletionBall F w u) :
    quotientCharacter F w u l t ht (QuotientAddGroup.mk x) =
      localFiniteCharacter F w (t * (x : w.adicCompletion F)) := by
  exact phase_eq_of_mk_eq F w u l t ht (Quotient.out_eq _)

theorem quotientCharacter_eq_iff (u l : ℤ) (hul : u ≤ l)
    (t s : w.adicCompletion F)
    (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l))
    (hs : s ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l)) :
    quotientCharacter F w u l t ht = quotientCharacter F w u l s hs ↔
      t - s ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u) := by
  constructor
  · intro h x hx
    have he := DFunLike.congr_fun h (QuotientAddGroup.mk ⟨x, hx⟩)
    simp only [quotientCharacter_mk] at he
    rw [mul_sub, AddChar.map_sub_eq_div, mul_comm x t, mul_comm x s, he]
    exact div_eq_one.mpr rfl
  · intro h
    apply AddChar.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [quotientCharacter_mk, quotientCharacter_mk]
    have he := h _ x.property
    rw [mul_sub, AddChar.map_sub_eq_div, div_eq_one] at he
    simpa only [mul_comm] using he

def dualCharacter (u l : ℤ) (q : DualQuotient F w u l) :
    AddChar (finiteCompletionBallQuotient F w u l) Circle :=
  quotientCharacter F w u l
    ((Quotient.out q : localFiniteAnnihilator F w (finiteCompletionBall F w l)) :
      w.adicCompletion F) (Quotient.out q).property

private theorem finiteBallDual_injective (u l : ℤ) (hul : u ≤ l) : Function.Injective (dualCharacter F w u l) := by
  intro a b h
  rw [← Quotient.out_eq a, ← Quotient.out_eq b]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact (quotientCharacter_eq_iff F w u l hul _ _ (Quotient.out a).property
    (Quotient.out b).property).mp h
private theorem finiteBallDual_character_card (u l : ℤ) (hul : u ≤ l) :
    Nat.card (AddChar (finiteCompletionBallQuotient F w u l) Circle) =
    Nat.card (finiteCompletionBallQuotient F w u l) := by
  letI := finite_finiteCompletionBallQuotient F w u l hul
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  rw [Nat.card_congr AddChar.circleEquivComplex.toEquiv, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, AddChar.card_eq]
private theorem finiteBallDual_card_le (u l : ℤ) (hul : u ≤ l) :
    Nat.card (DualQuotient F w u l) ≤ Nat.card (finiteCompletionBallQuotient F w u l) := by
  letI := finite_finiteCompletionBallQuotient F w u l hul
  letI : Finite (AddChar (finiteCompletionBallQuotient F w u l) Circle) :=
    Finite.of_equiv (AddChar (finiteCompletionBallQuotient F w u l) ℂ)
      AddChar.circleEquivComplex.symm.toEquiv
  exact (Nat.card_le_card_of_injective (dualCharacter F w u l) (finiteBallDual_injective F w u l hul)).trans_eq
    (finiteBallDual_character_card F w u l hul)
private theorem finiteBallDual_card_eq (u l : ℤ) (hul : u ≤ l) :
    Nat.card (DualQuotient F w u l) = Nat.card (finiteCompletionBallQuotient F w u l) := by
  apply le_antisymm (finiteBallDual_card_le F w u l hul)
  have h := finiteBallDual_card_le F w (-l - (localDifferentExponent F w : ℤ))
    (-u - (localDifferentExponent F w : ℤ)) (by omega)
  simp only [DualQuotient, localFiniteAnnihilator_finiteCompletionBall] at h ⊢
  have h1 : -(-u - (localDifferentExponent F w : ℤ)) - (localDifferentExponent F w : ℤ) = u := by omega
  have h2 : -(-l - (localDifferentExponent F w : ℤ)) - (localDifferentExponent F w : ℤ) = l := by omega
  rw [h1, h2] at h
  exact h

theorem dualCharacter_bijective (u l : ℤ) (hul : u ≤ l) :
    Function.Bijective (dualCharacter F w u l) := by
  letI := finite_finiteCompletionBallQuotient F w u l hul
  letI : Finite (AddChar (finiteCompletionBallQuotient F w u l) Circle) :=
    Finite.of_equiv (AddChar (finiteCompletionBallQuotient F w u l) ℂ)
      AddChar.circleEquivComplex.symm.toEquiv
  letI : Finite (DualQuotient F w u l) :=
    Finite.of_injective (dualCharacter F w u l) (finiteBallDual_injective F w u l hul)
  letI := Fintype.ofFinite (DualQuotient F w u l)
  letI := Fintype.ofFinite (AddChar (finiteCompletionBallQuotient F w u l) Circle)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨finiteBallDual_injective F w u l hul, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    finiteBallDual_character_card F w u l hul, finiteBallDual_card_eq F w u l hul]

theorem finite_dualQuotient (u l : ℤ) (hul : u ≤ l) :
    Finite (DualQuotient F w u l) := by
  refine KPRootAverage.finite_levelQuotient _ _ ?_ ?_ ?_
  · rw [localFiniteAnnihilator_finiteCompletionBall F w u,
      localFiniteAnnihilator_finiteCompletionBall F w l, finiteCompletionBall_le_iff]
    omega
  · rw [localFiniteAnnihilator_finiteCompletionBall F w l]
    exact isCompact_finiteCompletionBall F w _
  · rw [localFiniteAnnihilator_finiteCompletionBall F w u]
    exact isOpen_finiteCompletionBall F w _

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) V)

def levelAverageWithRepresentatives (u l : ℤ) (hul : u ≤ l)
    (t : w.adicCompletion F)
    (r : finiteCompletionBallQuotient F w u l → finiteCompletionBall F w u) :
    V →ₗ[ℂ] V := by
  letI := finite_finiteCompletionBallQuotient F w u l hul
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  exact (Nat.card (finiteCompletionBallQuotient F w u l) : ℂ)⁻¹ •
    ∑ q : finiteCompletionBallQuotient F w u l,
      (localFiniteCharacter F w (-t * (r q : w.adicCompletion F)) : ℂ) •
        rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd (r q : w.adicCompletion F))

def levelAverage (u l : ℤ) (hul : u ≤ l) (t : w.adicCompletion F) :
    V →ₗ[ℂ] V :=
  levelAverageWithRepresentatives F ζ hζ w ρ u l hul t Quotient.out

 def phaseUnit (t : w.adicCompletion F) : Multiplicative (w.adicCompletion F) →* ℂˣ where
  toFun x := Units.mk0 (localFiniteCharacter F w (t * Multiplicative.toAdd x) : ℂ) (Circle.coe_ne_zero _)
  map_one' := by apply Units.ext; simp
  map_mul' x y := by apply Units.ext; simp [mul_add, AddChar.map_add_eq_mul]
private theorem fixed_iff (l : ℤ) (v : V) :
    FixedByBall F ζ hζ w ρ l v ↔ v ∈ fixedSubmodule (rootRepresentation F ζ hζ w ρ)
      (finiteCompletionBall F w l).toSubgroup := by
  constructor
  · intro h x; exact h _ x.property
  · intro h x hx; exact h ⟨Multiplicative.ofAdd x, hx⟩
private theorem bridge (u l : ℤ) (hul : u ≤ l) (t : w.adicCompletion F)
    (v : V) (hv : FixedByBall F ζ hζ w ρ l v) :
    levelAverage F ζ hζ w ρ u l hul t v =
    (KPRootAverage.characterAverage (rootRepresentation F ζ hζ w ρ) (phaseUnit F w t)
      (finiteCompletionBall F w u) (finiteCompletionBall F w l)
      ((finiteCompletionBall_le_iff F w u l).mpr hul)
      (isCompact_finiteCompletionBall F w u) (isOpen_finiteCompletionBall F w l)
      ⟨v, (fixed_iff F ζ hζ w ρ l v).mp hv⟩ : V) := by
  letI := finite_finiteCompletionBallQuotient F w u l hul
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply, KPRootAverage.characterAverage, KPRootAverage.averageWithRepresentatives,
    Submodule.coe_smul, Submodule.coe_sum]
  rw [Nat.card_eq_fintype_card]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  simp [phaseUnit, KPRootAverage.representative, KPRootAverage.fixedRepresentation,
    Representation.subrepresentation_apply, LinearMap.restrict_apply,
    neg_mul, AddChar.map_neg_eq_inv]
  rfl
private theorem psi_trivial (l : ℤ) (t : w.adicCompletion F)
    (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l)) :
    ∀ x ∈ finiteCompletionBall F w l, phaseUnit F w t (Multiplicative.ofAdd x) = 1 := by
  intro x hx
  apply Units.ext
  simpa [phaseUnit, mul_comm] using congrArg (fun z : Circle => (z : ℂ)) (ht x hx)

theorem levelAverage_independent_level
    (u l k : ℤ) (hul : u ≤ l) (huk : u ≤ k) (t : w.adicCompletion F)
    (htl : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l))
    (htk : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w k))
    (v : V) (hvl : FixedByBall F ζ hζ w ρ l v)
    (hvk : FixedByBall F ζ hζ w ρ k v) :
    levelAverage F ζ hζ w ρ u l hul t v =
      levelAverage F ζ hζ w ρ u k huk t v := by
  rw [bridge F ζ hζ w ρ u l hul t v hvl, bridge F ζ hζ w ρ u k huk t v hvk]
  rcases le_total l k with hlk | hkl
  · exact KPRootAverage.characterAverage_refinement _ _ _ _ _
      ((finiteCompletionBall_le_iff F w u l).mpr hul)
      ((finiteCompletionBall_le_iff F w u k).mpr huk)
      ((finiteCompletionBall_le_iff F w l k).mpr hlk)
      (isCompact_finiteCompletionBall F w u) (isOpen_finiteCompletionBall F w l)
      (isOpen_finiteCompletionBall F w k) (psi_trivial F w l t htl) v
      ((fixed_iff F ζ hζ w ρ l v).mp hvl) ((fixed_iff F ζ hζ w ρ k v).mp hvk)
  · exact (KPRootAverage.characterAverage_refinement _ _ _ _ _
      ((finiteCompletionBall_le_iff F w u k).mpr huk)
      ((finiteCompletionBall_le_iff F w u l).mpr hul)
      ((finiteCompletionBall_le_iff F w k l).mpr hkl)
      (isCompact_finiteCompletionBall F w u) (isOpen_finiteCompletionBall F w k)
      (isOpen_finiteCompletionBall F w l) (psi_trivial F w k t htk) v
      ((fixed_iff F ζ hζ w ρ k v).mp hvk) ((fixed_iff F ζ hζ w ρ l v).mp hvl)).symm

theorem exists_averagingDepth (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ) (u : ℤ) (t : w.adicCompletion F) (v : V) :
    ∃ l : ℤ, u ≤ l ∧ FixedByBall F ζ hζ w ρ l v ∧
      t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  obtain ⟨J, hJ⟩ := hρ v
  let r := KPLocalSmoothRepresentation.continuousUpperRoot F ζ hζ w m hm
  have hopen : IsOpen {x : w.adicCompletion F | r (Multiplicative.ofAdd x) ∈ J} :=
    J.isOpen.preimage (r.continuous.comp continuous_ofAdd)
  have hzero : (0 : w.adicCompletion F) ∈
      {x | r (Multiplicative.ofAdd x) ∈ J} := by simp
  obtain ⟨k, _, hk⟩ := (finiteCompletionBall_hasBasis_nhds F w 0).mem_iff.mp
    (hopen.mem_nhds hzero)
  have hphase : IsLocallyConstant (fun x : w.adicCompletion F =>
      localFiniteCharacter F w (t * x)) :=
    (isLocallyConstant_localFiniteCharacter F w).comp_continuous (by fun_prop)
  obtain ⟨a, _, ha⟩ := (finiteCompletionBall_hasBasis_nhds F w 0).mem_iff.mp
    ((hphase.isOpen_fiber 1).mem_nhds (by simp))
  refine ⟨max u (max k a), le_max_left _ _, ?_, ?_⟩
  · intro x hx
    apply hJ
    apply hk
    simp only [sub_zero, Set.mem_setOf_eq]
    exact (finiteCompletionBall_le_iff F w _ _).mpr
      (le_trans (le_max_left k a) (le_max_right u _)) hx
  · intro x hx
    rw [mul_comm]
    apply ha
    simp only [sub_zero, Set.mem_setOf_eq]
    exact (finiteCompletionBall_le_iff F w _ _).mpr
      (le_trans (le_max_right k a) (le_max_right u _)) hx

def averagingDepth (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ) (u : ℤ) (t : w.adicCompletion F) (v : V) : ℤ :=
  Classical.choose (exists_averagingDepth F ζ hζ w ρ m hm hρ u t v)

theorem averagingDepth_spec (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ) (u : ℤ) (t : w.adicCompletion F) (v : V) :
    let l := averagingDepth F ζ hζ w ρ m hm hρ u t v
    u ≤ l ∧ FixedByBall F ζ hζ w ρ l v ∧
      t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l) :=
  Classical.choose_spec (exists_averagingDepth F ζ hζ w ρ m hm hρ u t v)

def projectorValue (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ) (u : ℤ) (t : w.adicCompletion F) (v : V) : V :=
  levelAverage F ζ hζ w ρ u (averagingDepth F ζ hζ w ρ m hm hρ u t v)
    (averagingDepth_spec F ζ hζ w ρ m hm hρ u t v).1 t v

theorem projectorValue_eq_levelAverage (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ) (u l : ℤ) (hul : u ≤ l)
    (t : w.adicCompletion F)
    (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l))
    (v : V) (hv : FixedByBall F ζ hζ w ρ l v) :
    projectorValue F ζ hζ w ρ m hm hρ u t v =
      levelAverage F ζ hζ w ρ u l hul t v := by
  exact levelAverage_independent_level F ζ hζ w ρ u
    (averagingDepth F ζ hζ w ρ m hm hρ u t v) l
    (averagingDepth_spec F ζ hζ w ρ m hm hρ u t v).1 hul t
    (averagingDepth_spec F ζ hζ w ρ m hm hρ u t v).2.2 ht v
    (averagingDepth_spec F ζ hζ w ρ m hm hρ u t v).2.1 hv

 theorem fixedByBall_mono (l k : ℤ) (h : k ≤ l) (v : V)
    (hv : FixedByBall F ζ hζ w ρ k v) : FixedByBall F ζ hζ w ρ l v := by
  intro x hx
  exact hv x ((finiteCompletionBall_le_iff F w k l).mpr h hx)

 theorem mem_annihilator_mono (l k : ℤ) (h : k ≤ l) (t : w.adicCompletion F)
    (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w k)) :
    t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l) := by
  rw [localFiniteAnnihilator_finiteCompletionBall F w k,
    localFiniteAnnihilator_finiteCompletionBall F w l, mem_finiteCompletionBall] at *
  exact ht.trans (WithZero.exp_le_exp.mpr (by omega))

def projector (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ) (u : ℤ) (t : w.adicCompletion F) : V →ₗ[ℂ] V where
  toFun := projectorValue F ζ hζ w ρ m hm hρ u t
  map_add' v1 v2 := by
    set L := max (averagingDepth F ζ hζ w ρ m hm hρ u t v1)
      (max (averagingDepth F ζ hζ w ρ m hm hρ u t v2)
        (averagingDepth F ζ hζ w ρ m hm hρ u t (v1 + v2)))
    have h1 := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v1
    have h2 := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v2
    have h12 := averagingDepth_spec F ζ hζ w ρ m hm hρ u t (v1 + v2)
    have hL1 : averagingDepth F ζ hζ w ρ m hm hρ u t v1 ≤ L := le_max_left _ _
    have hL2 : averagingDepth F ζ hζ w ρ m hm hρ u t v2 ≤ L :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hL12 : averagingDepth F ζ hζ w ρ m hm hρ u t (v1 + v2) ≤ L :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hulL : u ≤ L := le_trans h1.1 hL1
    rw [projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u L hulL t
          (mem_annihilator_mono F w L
            (averagingDepth F ζ hζ w ρ m hm hρ u t (v1 + v2)) hL12 t h12.2.2)
          (v1 + v2) (fixedByBall_mono F ζ hζ w ρ L
            (averagingDepth F ζ hζ w ρ m hm hρ u t (v1 + v2)) hL12 (v1 + v2) h12.2.1),
        projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u L hulL t
          (mem_annihilator_mono F w L
            (averagingDepth F ζ hζ w ρ m hm hρ u t v1) hL1 t h1.2.2)
          v1 (fixedByBall_mono F ζ hζ w ρ L
            (averagingDepth F ζ hζ w ρ m hm hρ u t v1) hL1 v1 h1.2.1),
        projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u L hulL t
          (mem_annihilator_mono F w L
            (averagingDepth F ζ hζ w ρ m hm hρ u t v2) hL2 t h2.2.2)
          v2 (fixedByBall_mono F ζ hζ w ρ L
            (averagingDepth F ζ hζ w ρ m hm hρ u t v2) hL2 v2 h2.2.1)]
    exact map_add (levelAverage F ζ hζ w ρ u L hulL t) v1 v2
  map_smul' c v := by
    set L := max (averagingDepth F ζ hζ w ρ m hm hρ u t (c • v))
      (averagingDepth F ζ hζ w ρ m hm hρ u t v)
    have h1 := averagingDepth_spec F ζ hζ w ρ m hm hρ u t (c • v)
    have h2 := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v
    have hL1 : averagingDepth F ζ hζ w ρ m hm hρ u t (c • v) ≤ L := le_max_left _ _
    have hL2 : averagingDepth F ζ hζ w ρ m hm hρ u t v ≤ L := le_max_right _ _
    have hulL : u ≤ L := le_trans h1.1 hL1
    rw [projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u L hulL t
          (mem_annihilator_mono F w L
            (averagingDepth F ζ hζ w ρ m hm hρ u t (c • v)) hL1 t h1.2.2)
          (c • v) (fixedByBall_mono F ζ hζ w ρ L
            (averagingDepth F ζ hζ w ρ m hm hρ u t (c • v)) hL1 (c • v) h1.2.1),
        projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u L hulL t
          (mem_annihilator_mono F w L
            (averagingDepth F ζ hζ w ρ m hm hρ u t v) hL2 t h2.2.2)
          v (fixedByBall_mono F ζ hζ w ρ L
            (averagingDepth F ζ hζ w ρ m hm hρ u t v) hL2 v h2.2.1)]
    simpa using map_smul (levelAverage F ζ hζ w ρ u L hulL t) c v

@[simp] theorem projector_apply (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ) (u : ℤ) (t : w.adicCompletion F) (v : V) :
    projector F ζ hζ w ρ m hm hρ u t v =
      projectorValue F ζ hζ w ρ m hm hρ u t v := rfl

variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (hρ : IsSmooth F ζ hζ w m ρ)

theorem projector_eigen (u : ℤ) (t x : w.adicCompletion F)
    (hx : x ∈ finiteCompletionBall F w u) (v : V) :
    rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x)
        (projector F ζ hζ w ρ m hm hρ u t v) =
      (localFiniteCharacter F w (t * x) : ℂ) •
        projector F ζ hζ w ρ m hm hρ u t v := by
  let l := averagingDepth F ζ hζ w ρ m hm hρ u t v
  have h := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v
  rw [projector_apply, projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u l h.1 t h.2.2 v h.2.1,
    bridge F ζ hζ w ρ u l h.1 t v h.2.1]
  have hr := KPRootAverage.characterAverage_range (rootRepresentation F ζ hζ w ρ)
    (phaseUnit F w t) (finiteCompletionBall F w u) (finiteCompletionBall F w l)
    ((finiteCompletionBall_le_iff F w u l).mpr h.1)
    (isCompact_finiteCompletionBall F w u) (isOpen_finiteCompletionBall F w l)
    (psi_trivial F w l t h.2.2)
  have he : (KPRootAverage.characterAverage (rootRepresentation F ζ hζ w ρ)
      (phaseUnit F w t) (finiteCompletionBall F w u) (finiteCompletionBall F w l)
      ((finiteCompletionBall_le_iff F w u l).mpr h.1)
      (isCompact_finiteCompletionBall F w u) (isOpen_finiteCompletionBall F w l)
      ⟨v, (fixed_iff F ζ hζ w ρ l v).mp h.2.1⟩ : V) ∈
      KPRootAverage.eigenspace (rootRepresentation F ζ hζ w ρ) (phaseUnit F w t)
        (finiteCompletionBall F w u) := by
    rw [← hr]
    exact ⟨⟨v, (fixed_iff F ζ hζ w ρ l v).mp h.2.1⟩, rfl⟩
  exact he x hx

theorem projector_eq_self (u : ℤ) (t : w.adicCompletion F) (v : V)
    (hv : ∀ x ∈ finiteCompletionBall F w u,
      rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v =
        (localFiniteCharacter F w (t * x) : ℂ) • v) :
    projector F ζ hζ w ρ m hm hρ u t v = v := by
  let l := averagingDepth F ζ hζ w ρ m hm hρ u t v
  have h := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v
  rw [projector_apply, projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u l h.1 t h.2.2 v h.2.1]
  letI := finite_finiteCompletionBallQuotient F w u l h.1
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  have ht : ∀ q : finiteCompletionBallQuotient F w u l,
      (localFiniteCharacter F w (-t * ((Quotient.out q : finiteCompletionBall F w u) :
        w.adicCompletion F)) : ℂ) •
      rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd
        ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F)) v = v := by
    intro q
    rw [hv _ (Quotient.out q).property, smul_smul, neg_mul, AddChar.map_neg_eq_inv]
    simp
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply, ht, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.card_pos.ne'

private theorem commute (u : ℤ) (t x : w.adicCompletion F) (v : V) :
    projector F ζ hζ w ρ m hm hρ u t
      (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v) =
    rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x)
      (projector F ζ hζ w ρ m hm hρ u t v) := by
  let l := averagingDepth F ζ hζ w ρ m hm hρ u t v
  have h := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v
  have hc (y : w.adicCompletion F) :
      (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd y)).comp
        (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x)) =
      (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x)).comp
        (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd y)) := by
    change rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd y) *
      rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) =
      rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) *
      rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd y)
    rw [← (rootRepresentation F ζ hζ w ρ).map_mul,
      ← (rootRepresentation F ζ hζ w ρ).map_mul, mul_comm]
  have hf : FixedByBall F ζ hζ w ρ l
      (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v) := by
    intro y hy
    have he := LinearMap.congr_fun (hc y) v
    simpa [h.2.1 y hy] using he
  rw [projector_apply, projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u l h.1 t h.2.2 _ hf,
    projector_apply, projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u l h.1 t h.2.2 v h.2.1]
  letI := finite_finiteCompletionBallQuotient F w u l h.1
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (fun z : V => _ • z) (LinearMap.congr_fun (hc _) v)
private theorem kill (u : ℤ) (t s : w.adicCompletion F)
    (hst : s - t ∉ localFiniteAnnihilator F w (finiteCompletionBall F w u))
    (v : V) (hv : ∀ x ∈ finiteCompletionBall F w u,
      rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v =
        (localFiniteCharacter F w (s * x) : ℂ) • v) :
    projector F ζ hζ w ρ m hm hρ u t v = 0 := by
  have hex : ∃ x ∈ finiteCompletionBall F w u,
      localFiniteCharacter F w (s * x) ≠ localFiniteCharacter F w (t * x) := by
    by_contra! h
    apply hst
    intro x hx
    rw [mul_sub, AddChar.map_sub_eq_div, mul_comm x s, mul_comm x t, h x hx]
    exact div_eq_one.mpr rfl
  obtain ⟨x, hx, hne⟩ := hex
  have he := projector_eigen F ζ hζ w ρ m hm hρ u t x hx v
  rw [← commute F ζ hζ w ρ m hm hρ u t x v, hv x hx, map_smul] at he
  have hz : ((localFiniteCharacter F w (s * x) : ℂ) -
      (localFiniteCharacter F w (t * x) : ℂ)) •
      projector F ζ hζ w ρ m hm hρ u t v = 0 := by
    rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Circle.coe_injective.ne hne))

theorem projector_eq_of_sub_mem_annihilator (u : ℤ) (t s : w.adicCompletion F)
    (hts : t - s ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u)) :
    projector F ζ hζ w ρ m hm hρ u t =
      projector F ζ hζ w ρ m hm hρ u s := by
  ext v
  rw [projector_apply, projector_apply]
  let L := averagingDepth F ζ hζ w ρ m hm hρ u t v
  have h := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v
  have hs : s ∈ localFiniteAnnihilator F w (finiteCompletionBall F w L) := by
    rw [mem_localFiniteAnnihilator]
    intro y hy
    have hty := (mem_localFiniteAnnihilator F w (finiteCompletionBall F w L) t).mp
      h.2.2 y hy
    have hyu : y ∈ finiteCompletionBall F w u :=
      (finiteCompletionBall_le_iff F w u L).mpr h.1 hy
    have htsy := (mem_localFiniteAnnihilator F w (finiteCompletionBall F w u)
      (t - s)).mp hts y hyu
    rw [show y * s = y * t - y * (t - s) from by ring, AddChar.map_sub_eq_div,
      hty, htsy, div_one]
  rw [projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u L h.1 t h.2.2 v h.2.1,
      projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u L h.1 s hs v h.2.1]
  letI := finite_finiteCompletionBallQuotient F w u L h.1
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u L)
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply]
  refine congrArg (fun Z : V => (Nat.card (finiteCompletionBallQuotient F w u L) : ℂ)⁻¹ • Z) ?_
  apply Finset.sum_congr rfl
  intro q _
  have hyu : ((Quotient.out q : finiteCompletionBall F w u) :
      w.adicCompletion F) ∈ finiteCompletionBall F w u := (Quotient.out q).property
  have hq := (mem_localFiniteAnnihilator F w (finiteCompletionBall F w u)
    (t - s)).mp hts _ hyu
  have hpsi : localFiniteCharacter F w (-t *
        ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F)) =
      localFiniteCharacter F w (-s *
        ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F)) := by
    rw [show -t * ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F) =
        -s * ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F) -
          (t - s) * ((Quotient.out q : finiteCompletionBall F w u) :
            w.adicCompletion F) from by ring,
      AddChar.map_sub_eq_div, mul_comm (t - s), hq, div_one]
  rw [hpsi]

theorem projector_orthogonal (u : ℤ) (t s : w.adicCompletion F)
    (hts : t - s ∉ localFiniteAnnihilator F w (finiteCompletionBall F w u)) :
    (projector F ζ hζ w ρ m hm hρ u t).comp
      (projector F ζ hζ w ρ m hm hρ u s) = 0 := by
  apply LinearMap.ext
  intro v
  change projector F ζ hζ w ρ m hm hρ u t (projector F ζ hζ w ρ m hm hρ u s v) = 0
  exact kill F ζ hζ w ρ m hm hρ u t s
    (by
      intro h
      apply hts
      simpa only [neg_sub] using (localFiniteAnnihilator F w (finiteCompletionBall F w u)).neg_mem h)
    _ (fun x hx => projector_eigen F ζ hζ w ρ m hm hρ u s x hx v)

private theorem phaseSum (u l : ℤ) (hul : u ≤ l) (x : finiteCompletionBallQuotient F w u l) :
    letI := finite_dualQuotient F w u l hul
    letI := Fintype.ofFinite (DualQuotient F w u l)
    ∑ q : DualQuotient F w u l,
      (localFiniteCharacter F w (-((Quotient.out q : localFiniteAnnihilator F w
        (finiteCompletionBall F w l)) : w.adicCompletion F) *
        ((Quotient.out x : finiteCompletionBall F w u) : w.adicCompletion F)) : ℂ) =
      if x = 0 then (Nat.card (finiteCompletionBallQuotient F w u l) : ℂ) else 0 := by
  letI := finite_dualQuotient F w u l hul
  letI := Fintype.ofFinite (DualQuotient F w u l)
  letI := finite_finiteCompletionBallQuotient F w u l hul
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  let e : DualQuotient F w u l ≃ AddChar (finiteCompletionBallQuotient F w u l) ℂ :=
    (Equiv.ofBijective (dualCharacter F w u l) (dualCharacter_bijective F w u l hul)).trans
      AddChar.circleEquivComplex.toEquiv
  have hterm (q : DualQuotient F w u l) :
      (localFiniteCharacter F w (-((Quotient.out q : localFiniteAnnihilator F w
        (finiteCompletionBall F w l)) : w.adicCompletion F) *
        ((Quotient.out x : finiteCompletionBall F w u) : w.adicCompletion F)) : ℂ) =
        e q (-x) := by
    change _ = (quotientCharacter F w u l _ (Quotient.out q).property (-x) : ℂ)
    rw [← Quotient.out_eq x, ← QuotientAddGroup.mk_neg, quotientCharacter_mk]
    simp [neg_mul, mul_neg]
  simp only [hterm]
  rw [e.sum_comp (fun c => c (-x)), AddChar.sum_apply_eq_ite]
  simp only [neg_eq_zero, Nat.card_eq_fintype_card]

theorem finite_fourier_decomposition (u l : ℤ) (hul : u ≤ l)
    (v : V) (hv : FixedByBall F ζ hζ w ρ l v) :
    letI := finite_dualQuotient F w u l hul
    letI := Fintype.ofFinite (DualQuotient F w u l)
    v = ∑ q : DualQuotient F w u l,
      projector F ζ hζ w ρ m hm hρ u
        ((Quotient.out q : localFiniteAnnihilator F w (finiteCompletionBall F w l)) :
          w.adicCompletion F) v := by
  letI := finite_dualQuotient F w u l hul
  letI := Fintype.ofFinite (DualQuotient F w u l)
  letI := finite_finiteCompletionBallQuotient F w u l hul
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  simp only [projector_apply]
  have hp (q : DualQuotient F w u l) := projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ
    u l hul ((Quotient.out q : localFiniteAnnihilator F w (finiteCompletionBall F w l)) :
      w.adicCompletion F) (Quotient.out q).property v hv
  simp only [hp]
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, phaseSum F w u l hul]
  simp_rw [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have hfix : rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd
      ((Quotient.out (0 : finiteCompletionBallQuotient F w u l) :
        finiteCompletionBall F w u) : w.adicCompletion F)) v = v := by
    apply hv
    have he : QuotientAddGroup.mk (Quotient.out (0 : finiteCompletionBallQuotient F w u l)) =
        (QuotientAddGroup.mk (0 : finiteCompletionBall F w u) :
          finiteCompletionBallQuotient F w u l) := by simp [Quotient.out_eq]
    have h := QuotientAddGroup.eq_iff_sub_mem.mp he
    have h' : Quotient.out (0 : finiteCompletionBallQuotient F w u l) - 0 ∈
        finiteCompletionBallSubgroup F w u l := h
    rw [sub_zero] at h'
    exact h'
  rw [hfix, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.card_pos.ne'

theorem projector_refinement_eq (u u' : ℤ) (huu' : u' ≤ u)
    (t s : w.adicCompletion F)
    (hst : s - t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u)) :
    (projector F ζ hζ w ρ m hm hρ u t).comp
        (projector F ζ hζ w ρ m hm hρ u' s) =
      projector F ζ hζ w ρ m hm hρ u' s := by
  apply LinearMap.ext
  intro v
  change projector F ζ hζ w ρ m hm hρ u t (projector F ζ hζ w ρ m hm hρ u' s v) = _
  apply projector_eq_self F ζ hζ w ρ m hm hρ u t
  intro x hx
  have he := projector_eigen F ζ hζ w ρ m hm hρ u' s x
    ((finiteCompletionBall_le_iff F w u' u).mpr huu' hx) v
  have hp := hst x hx
  rw [mul_sub, AddChar.map_sub_eq_div, div_eq_one] at hp
  have hp' : localFiniteCharacter F w (s * x) = localFiniteCharacter F w (t * x) := by
    simpa only [mul_comm] using hp
  rw [hp'] at he
  exact he

end DedekindZetaZeroFree.KPKirillovFiniteBallProjectors

end
