module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.GenuineSectionTensorCharts
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.ProjectorGermsAndFrequencySupport
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OpenCellKernelAndActions

@[expose] public section

noncomputable section

set_option maxHeartbeats 4000000

namespace DedekindZetaZeroFree.KPKirillovOrbitMapFaithful

open scoped NumberField Classical

open NumberField IsDedekindDomain

open KPKirillovGenuineSectionCharts KPKirillovProjectorGerms

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (𝓞 F))

abbrev ψ := frequencyCharacter F w 1

end DedekindZetaZeroFree.KPKirillovOrbitMapFaithful

end

section

noncomputable section

set_option maxHeartbeats 4000000

namespace DedekindZetaZeroFree.KPKirillovOrbitMapFaithful

open scoped NumberField Classical
open NumberField IsDedekindDomain
open KPKirillovGenuineSectionCharts KPKirillovProjectorGerms
open KPKirillovFiniteBallProjectors

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (𝓞 F))

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) V)

abbrev J := Fiber F ζ hζ w ρ 1

def rawOrbitMap : V →ₗ[ℂ] (P F ζ hζ w → J F ζ hζ w ρ) where
  toFun v p := quotientMap F ζ hζ w ρ 1 (ρ p.val v)
  map_add' := by intros; ext p; simp
  map_smul' := by intros; ext p; simp

@[simp] theorem rawOrbitMap_apply (v : V) (p : P F ζ hζ w) :
    rawOrbitMap F ζ hζ w ρ v p = quotientMap F ζ hζ w ρ 1 (ρ p.val v) := rfl

def ordinaryKernelRepresentation :
    Representation ℂ (P F ζ hζ w) (ordinaryKernel F ζ hζ w ρ) :=
  Representation.subrepresentation (ρ.comp (P F ζ hζ w).subtype)
    (ordinaryKernel F ζ hζ w ρ) (by
      intro p v hv
      exact ordinaryKernel_borel_stable F ζ hζ w ρ p v hv)

variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (hρ : IsSmooth F ζ hζ w m ρ)
  (hgen : KPLocalSmoothRepresentation.genuine F ζ hζ w ρ)

private theorem borel_conjugates_root (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) (p : P F ζ hζ w) (x : K F w) :
    p.val * KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd x) *
      p.val⁻¹ = KPLocalSmoothRepresentation.upperRoot F ζ hζ w
        (Multiplicative.ofAdd ((slope F ζ hζ w p : K F w) * x)) := by
  obtain ⟨⟨a, b⟩, hp, _⟩ := KPLocalInductionJacquetReciprocity.borel_factorization F ζ hζ w p
  let aa : P F ζ hζ w := KPJacquetClosedCellBump.torusInBorel F ζ hζ w m hm a
  have hps : p = aa * n F ζ hζ w b.toAdd := Subtype.ext hp
  have hs : slope F ζ hζ w p = KPJacquetOpenCell.r F ζ hζ w m hm a := by
    rw [hps, map_mul]
    have hn := n_mem_H F ζ hζ w b.toAdd
    change slope F ζ hζ w (n F ζ hζ w b.toAdd) = 1 at hn
    rw [hn, mul_one]
    rfl
  rw [hs, hp]
  have hc := (KPLocalSmoothRepresentation.upperRoot F ζ hζ w).map_mul b
    (Multiplicative.ofAdd x)
  have hc' := (KPLocalSmoothRepresentation.upperRoot F ζ hζ w).map_mul
    (Multiplicative.ofAdd x) b
  have hcomm : KPLocalSmoothRepresentation.upperRoot F ζ hζ w b *
      KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd x) =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd x) *
        KPLocalSmoothRepresentation.upperRoot F ζ hζ w b := by
    rw [← hc, ← hc', mul_comm]
  calc
    _ = a.val * KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd x) *
        a.val⁻¹ := by
      dsimp only [Prod.fst, Prod.snd]
      rw [mul_inv_rev, ← mul_assoc, mul_assoc a.val
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ w b), hcomm]
      group
    _ = _ := KPJacquetOpenCell.torus_conjugates_root F ζ hζ w m hm a x

private def quotientTransport (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) (p : P F ζ hζ w)
    (t s : K F w) (h : t * (slope F ζ hζ w p : K F w) = s) :
    Fiber F ζ hζ w ρ s →ₗ[ℂ] Fiber F ζ hζ w ρ t :=
  rootCoinvariantsLift ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w)
    (frequencyCharacter F w s) ⟨(quotientMap F ζ hζ w ρ t).comp (ρ p.val), by
      intro x v
      change quotientMap F ζ hζ w ρ t (ρ p.val
        (ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w x) v)) = _
      have hc := borel_conjugates_root F ζ hζ w m hm p x.toAdd
      have hc' : p.val * KPLocalSmoothRepresentation.upperRoot F ζ hζ w x =
          KPLocalSmoothRepresentation.upperRoot F ζ hζ w
            (Multiplicative.ofAdd ((slope F ζ hζ w p : K F w) * x.toAdd)) * p.val := by
        rw [← hc, mul_assoc, inv_mul_cancel, mul_one]
        rfl
      rw [← Module.End.mul_apply, ← map_mul, hc', map_mul, Module.End.mul_apply]
      change rootCoinvariantsMk ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w)
        (frequencyCharacter F w t) (ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w
          (Multiplicative.ofAdd ((slope F ζ hζ w p : K F w) * x.toAdd))) (ρ p.val v)) = _
      rw [rootCoinvariantsMk_equivariant]
      have he : frequencyCharacter F w t
          (Multiplicative.ofAdd ((slope F ζ hζ w p : K F w) * x.toAdd)) =
          frequencyCharacter F w s x := by
        change Circle.toUnits (localFiniteCharacter F w
          (t * ((slope F ζ hζ w p : K F w) * x.toAdd))) =
          Circle.toUnits (localFiniteCharacter F w (s * x.toAdd))
        rw [← mul_assoc, h]
      rw [he]
      rfl⟩

private theorem quotient_orbit_zero_iff (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) (p : P F ζ hζ w) (v : V) :
    quotientMap F ζ hζ w ρ 1 (ρ p.val v) = 0 ↔
      quotientMap F ζ hζ w ρ (slope F ζ hζ w p : K F w) v = 0 := by
  constructor
  · intro hv
    have h : (slope F ζ hζ w p : K F w) *
        (slope F ζ hζ w p⁻¹ : K F w) = 1 := by
      rw [map_inv]
      have hh := congrArg (fun a : (K F w)ˣ => (a : K F w))
        (mul_inv_cancel (slope F ζ hζ w p))
      exact hh
    let L := quotientTransport F ζ hζ w ρ m hm p⁻¹
      (slope F ζ hζ w p : K F w) 1 h
    have hh := congrArg L hv
    change quotientMap F ζ hζ w ρ (slope F ζ hζ w p : K F w)
      (ρ p⁻¹.val (ρ p.val v)) = L 0 at hh
    simpa only [Subgroup.coe_inv, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply, map_zero] using hh
  · intro hv
    let L := quotientTransport F ζ hζ w ρ m hm p 1
      (slope F ζ hζ w p : K F w) (one_mul _)
    have hh := congrArg L hv
    change quotientMap F ζ hζ w ρ 1 (ρ p.val v) = L 0 at hh
    simpa only [map_zero] using hh

include hgen in

theorem rawOrbitMap_covariance (v : V) (b : K F w) (e : rootsOfUnity 3 F)
    (p : P F ζ hζ w) :
    rawOrbitMap F ζ hζ w ρ v ((n F ζ hζ w b * z F ζ hζ w e) * p) =
      (((ψ F w (Multiplicative.ofAdd b) * iota F ζ hζ e : ℂˣ) : ℂ)) •
        rawOrbitMap F ζ hζ w ρ v p := by
  have hn : (n F ζ hζ w b).val =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd b) := rfl
  have hz : (z F ζ hζ w e).val =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e := rfl
  simp only [rawOrbitMap_apply, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  rw [hz, hgen e, map_smul, hn]
  change (iota F ζ hζ e : ℂ) •
      rootCoinvariantsMk ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w) (ψ F w)
        (ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd b))
          (ρ p.val v)) = _
  rw [rootCoinvariantsMk_equivariant]
  simp only [Units.val_mul, mul_smul]
  exact smul_comm _ _ _

def orbitSectionMap (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : IsSmooth F ζ hζ w m ρ)
    (hgen : KPLocalSmoothRepresentation.genuine F ζ hζ w ρ) :
    (ordinaryKernel F ζ hζ w ρ) →ₗ[ℂ]
    Sections F ζ hζ w m (ψ F w) (J F ζ hζ w ρ) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  exact {
    toFun := fun v => ⟨⟨⟨rawOrbitMap F ζ hζ w ρ v.val, by
      intro h p
      obtain ⟨⟨b, e⟩, he, _⟩ := H_decomposition F ζ hζ w h
      change rawOrbitMap F ζ hζ w ρ v.val (h.val * p) = _
      have hc := rawOrbitMap_covariance F ζ hζ w ρ hgen v.val b e p
      rw [← he] at hc
      rw [hc]
      have hf := inducingCharacter_formula F ζ hζ w (ψ F w) b e h he
      change _ = (((1 : H F ζ hζ w →* (NNReal)ˣ) h : NNReal) : ℂ) •
        ((inducingCharacter F ζ hζ w (ψ F w) h : ℂ) •
          rawOrbitMap F ζ hζ w ρ v.val p)
      rw [hf]
      change _ = (1 : ℂ) • _
      rw [one_smul]⟩, by
      apply (mem_smoothSubmodule _ _).mpr
      obtain ⟨U, hU⟩ := hρ v.val
      refine ⟨U.comap (P F ζ hζ w).subtype continuous_subtype_val, ?_⟩
      intro j hj
      apply Subtype.ext
      funext p
      change rawOrbitMap F ζ hζ w ρ v.val (p * j) = rawOrbitMap F ζ hζ w ρ v.val p
      simp only [rawOrbitMap_apply, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hU j.val hj]⟩, by
      obtain ⟨C, hC, hs⟩ := ordinaryKernel_support_compact_away_zero
        F ζ hζ w ρ m hm hρ v.val v.property
      let e := quotientHomeomorph F ζ hζ w m hm
      change IsCompact (closure ((Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w))) ''
        Function.support (rawOrbitMap F ζ hζ w ρ v.val)))
      apply (e.isCompact_preimage.mpr hC).of_isClosed_subset isClosed_closure
      apply closure_minimal _ (hC.isClosed.preimage e.continuous)
      rintro q ⟨p, hp, rfl⟩
      change e (Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w)) p) ∈ C
      rw [quotientHomeomorph_mk]
      have hp' : quotientMap F ζ hζ w ρ 1 (ρ p.val v.val) ≠ 0 := hp
      have ht : quotientMap F ζ hζ w ρ (slope F ζ hζ w p : K F w) v.val ≠ 0 := by
        intro hz
        exact hp' ((quotient_orbit_zero_iff F ζ hζ w ρ m hm p v.val).mpr hz)
      obtain ⟨a, ha, he⟩ := hs
        ((mem_characterProjectorSupport_iff F ζ hζ w ρ m hm hρ _ v.val).mpr ht)
      have hea : a = slope F ζ hζ w p := Units.ext he
      exact hea ▸ ha⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext p
      change rawOrbitMap F ζ hζ w ρ (a.val + b.val) p = _
      exact congrFun ((rawOrbitMap F ζ hζ w ρ).map_add a.val b.val) p
    map_smul' := by
      intro c a
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext p
      change rawOrbitMap F ζ hζ w ρ (c • a.val) p = _
      exact congrFun ((rawOrbitMap F ζ hζ w ρ).map_smul c a.val) p }

@[simp] theorem orbitSectionMap_value (v : ordinaryKernel F ζ hζ w ρ)
    (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m (ψ F w)
        (orbitSectionMap F ζ hζ w ρ m hm hρ hgen v) p =
      quotientMap F ζ hζ w ρ 1 (ρ p.val v.val) := rfl

theorem orbitSectionMap_intertwines (p : P F ζ hζ w)
    (v : ordinaryKernel F ζ hζ w ρ) :
    orbitSectionMap F ζ hζ w ρ m hm hρ hgen
        (ordinaryKernelRepresentation F ζ hζ w ρ p v) =
      rightAction F ζ hζ w m hm (ψ F w) (J F ζ hζ w ρ) p
        (orbitSectionMap F ζ hζ w ρ m hm hρ hgen v) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext a
  change quotientMap F ζ hζ w ρ 1 (ρ a.val (ρ p.val v.val)) =
    sectionValue F ζ hζ w m (ψ F w)
      (rightAction F ζ hζ w m hm (ψ F w) (J F ζ hζ w ρ) p
        (orbitSectionMap F ζ hζ w ρ m hm hρ hgen v)) a
  rw [rightAction_apply, orbitSectionMap_value]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

set_option maxHeartbeats 1500000 in

theorem orbitSectionMap_injective :
    Function.Injective (orbitSectionMap F ζ hζ w ρ m hm hρ hgen) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  intro a b hab
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_all_quotientMap_eq_zero F ζ hζ w ρ m hm hρ
  intro t
  by_cases ht : t = 0
  · subst t
    rw [map_sub, (quotientMap_zero_eq_zero_iff F ζ hζ w ρ a.val).mpr a.property,
      (quotientMap_zero_eq_zero_iff F ζ hζ w ρ b.val).mpr b.property, sub_self]
  · let c : (K F w)ˣ := Units.mk0 t ht
    obtain ⟨q, hq⟩ := (quotientHomeomorph F ζ hζ w m hm).surjective c
    obtain ⟨p, rfl⟩ := Quotient.exists_rep q
    have hp : slope F ζ hζ w p = c := by
      rw [← quotientHomeomorph_mk F ζ hζ w m hm p]
      exact hq
    have hh := congrArg (fun f => sectionValue F ζ hζ w m (ψ F w) f p) hab
    simp only [orbitSectionMap_value] at hh
    have hz : quotientMap F ζ hζ w ρ 1 (ρ p.val (a.val - b.val)) = 0 := by
      rw [map_sub, map_sub, hh]
      exact sub_self _
    have hz := (quotient_orbit_zero_iff F ζ hζ w ρ m hm p (a.val - b.val)).mp hz
    rw [hp] at hz
    exact hz

@[simp] theorem orbitSectionMap_at_one (v : ordinaryKernel F ζ hζ w ρ) :
    sectionValue F ζ hζ w m (ψ F w)
        (orbitSectionMap F ζ hζ w ρ m hm hρ hgen v) 1 =
      quotientMap F ζ hζ w ρ 1 v.val := by
  rw [orbitSectionMap_value]
  simp only [Subgroup.coe_one, map_one, Module.End.one_apply]

def frequencyCoset (u : ℤ) (t₀ : (K F w)ˣ) : Set (K F w) :=
  {t | t - (t₀ : K F w) ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u)}

private theorem quotientMap_projector_indicator (u : ℤ) (t s : K F w) (v : V) :
    quotientMap F ζ hζ w ρ t (projector F ζ hζ w ρ m hm hρ u s v) =
      if t - s ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u) then
        quotientMap F ζ hζ w ρ t v else 0 := by
  classical
  by_cases h : t - s ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u)
  · rw [if_pos h, ← projector_eq_of_sub_mem_annihilator F ζ hζ w ρ m hm hρ u t s h]
    exact quotientMap_projector F ζ hζ w ρ m hm hρ u t v
  · rw [if_neg h, ← quotientMap_projector F ζ hζ w ρ m hm hρ u t]
    have hh := LinearMap.congr_fun
      (projector_orthogonal F ζ hζ w ρ m hm hρ u t s h) v
    change projector F ζ hζ w ρ m hm hρ u t
      (projector F ζ hζ w ρ m hm hρ u s v) = 0 at hh
    rw [hh, map_zero]

theorem rawOrbitMap_projector_chart (u : ℤ) (t₀ : (K F w)ˣ)
    (v : V) (c : LocalChart F ζ hζ w m) (t : c.ball.domain) :
    rawOrbitMap F ζ hζ w ρ (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v)
        (c.lift t) =
      if (t.val : K F w) ∈ frequencyCoset F w u t₀ then
        rawOrbitMap F ζ hζ w ρ v (c.lift t) else 0 := by
  classical
  let p := c.lift t
  have hp : (slope F ζ hζ w p : K F w) = (t.val : K F w) :=
    congrArg (fun a : (K F w)ˣ => (a : K F w)) (c.slope_lift t)
  let L := quotientTransport F ζ hζ w ρ m hm p 1 (t.val : K F w)
    (by rw [one_mul, hp])
  have hh := congrArg L
    (quotientMap_projector_indicator F ζ hζ w ρ m hm hρ u
      (t.val : K F w) (t₀ : K F w) v)
  change rawOrbitMap F ζ hζ w ρ
    (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v) p = _ at hh
  change _ = if (t.val : K F w) - (t₀ : K F w) ∈
      localFiniteAnnihilator F w (finiteCompletionBall F w u) then _ else _
  split_ifs with h
  · rw [if_pos h] at hh
    exact hh
  · rw [if_neg h, map_zero] at hh
    exact hh

theorem projector_mem_ordinaryKernel (u : ℤ) (t₀ : (K F w)ˣ)
    (hzero : (0 : K F w) ∉ frequencyCoset F w u t₀) (v : V) :
    projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v ∈
      ordinaryKernel F ζ hζ w ρ := by
  apply (quotientMap_zero_eq_zero_iff F ζ hζ w ρ _).mp
  have ht : -(t₀ : K F w) ∉
      localFiniteAnnihilator F w (finiteCompletionBall F w u) := by
    simpa only [frequencyCoset, Set.mem_setOf_eq, zero_sub] using hzero
  have hx : ∃ x ∈ finiteCompletionBall F w u,
      localFiniteCharacter F w (x * -(t₀ : K F w)) ≠ 1 := by
    classical
    simpa only [mem_localFiniteAnnihilator, not_forall, exists_prop] using ht
  obtain ⟨x, hx, hχ⟩ := hx
  have hχ' : (localFiniteCharacter F w ((t₀ : K F w) * x) : ℂ) ≠ 1 := by
    intro he
    apply hχ
    have he' : localFiniteCharacter F w ((t₀ : K F w) * x) = 1 := Subtype.ext he
    rw [mul_neg, mul_comm x, AddChar.map_neg_eq_inv, he', inv_one]
  have he := congrArg (quotientMap F ζ hζ w ρ 0)
    (projector_eigen F ζ hζ w ρ m hm hρ u (t₀ : K F w) x hx v)
  change quotientMap F ζ hζ w ρ 0
      (ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd x))
        (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v)) = _ at he
  have hq := rootCoinvariantsMk_equivariant ρ
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ w) (frequencyCharacter F w 0)
    (Multiplicative.ofAdd x) (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v)
  change quotientMap F ζ hζ w ρ 0 _ = _ at hq
  rw [hq, map_smul] at he
  have hphase : (frequencyCharacter F w 0 (Multiplicative.ofAdd x) : ℂ) = 1 := by
    change (localFiniteCharacter F w (0 * x) : ℂ) = 1
    rw [zero_mul, AddChar.map_zero_eq_one]
    rfl
  rw [hphase, one_smul] at he
  have hz : ((localFiniteCharacter F w ((t₀ : K F w) * x) : ℂ) - 1) •
      quotientMap F ζ hζ w ρ 0
        (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v) = 0 := by
    rw [sub_smul, one_smul, ← he]
    exact sub_self _
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχ')

theorem projector_preserves_ordinaryKernel (u : ℤ) (t₀ : (K F w)ˣ)
    (v : ordinaryKernel F ζ hζ w ρ) :
    projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v.val ∈
      ordinaryKernel F ζ hζ w ρ := by
  apply (quotientMap_zero_eq_zero_iff F ζ hζ w ρ _).mp
  rw [quotientMap_projector_indicator F ζ hζ w ρ m hm hρ]
  have hv := (quotientMap_zero_eq_zero_iff F ζ hζ w ρ v.val).mpr v.property
  rw [hv]
  split_ifs <;> rfl

theorem orbitSectionMap_projector_chart (u : ℤ) (t₀ : (K F w)ˣ)
    (v : ordinaryKernel F ζ hζ w ρ) (c : LocalChart F ζ hζ w m)
    (t : c.ball.domain) :
    chartValue F ζ hζ w m (ψ F w) c
        (orbitSectionMap F ζ hζ w ρ m hm hρ hgen
          ⟨projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v.val,
            projector_preserves_ordinaryKernel F ζ hζ w ρ m hm hρ u t₀ v⟩) t =
      if (t.val : K F w) ∈ frequencyCoset F w u t₀ then
        chartValue F ζ hζ w m (ψ F w) c
          (orbitSectionMap F ζ hζ w ρ m hm hρ hgen v) t else 0 := by
  change rawOrbitMap F ζ hζ w ρ
    (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v.val) (c.lift t) =
    if (t.val : K F w) ∈ frequencyCoset F w u t₀ then
      rawOrbitMap F ζ hζ w ρ v.val (c.lift t) else 0
  exact rawOrbitMap_projector_chart F ζ hζ w ρ m hm hρ u t₀ v.val c t

end DedekindZetaZeroFree.KPKirillovOrbitMapFaithful

end
end
