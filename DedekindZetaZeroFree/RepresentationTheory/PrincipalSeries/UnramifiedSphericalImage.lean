module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalGoodSphericalImage

open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open scoped commutatorElement Valued
open ValuativeRel

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

def compactTorus (A : LocalBorelData (K := K) (G := G) T) (I : IwasawaData A) :
    Subgroup H :=
  (I.compact.toOpenSubgroup : Subgroup G).comap
    ((Subgroup.subtype A.B).comp A.torus)

structure UnramifiedCompactInducingData
    (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) : Prop where
  tame : (3 : 𝒪[K]) ∉ 𝓂[K]
  polarization_image : (compactTorus A I).map T.π = P.L
  character_trivial : ∀ u : compactTorus A I,
    ∀ hu : T.π (u : H) ∈ P.L, P.ωL ⟨(u : H), hu⟩ = 1
  compact_borel_retract : ∀ b : A.B,
    (b : G) ∈ I.compact.toOpenSubgroup → A.retract b ∈ compactTorus A I

private lemma orth_mem (P : Polarization T) (d : D)
    (hd : ∀ l ∈ P.L, T.pairing d l = 1) : d ∈ P.L := by
  have hsym (l : D) (hl : l ∈ P.L) : T.pairing l d = 1 := by
    have hh := T.alternating (d * l)
    simpa [map_mul, T.alternating, hd l hl] using hh
  let S : Set D := insert d (P.L : Set D)
  have hs (x : D) (hx : x ∈ S) (y : D) (hy : y ∈ S) : T.pairing x y = 1 := by
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact T.alternating _
    · exact hd y hy
    · exact hsym x hx
    · exact P.maximal.1 x hx y hy
  have hc : FinitePolarization.IsIsotropic T.pairing (Subgroup.closure S) := by
    intro x hx y hy
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      induction hy using Subgroup.closure_induction with
      | mem y hy => exact hs x hx y hy
      | one => simp
      | mul y z hy hz ihy ihz => simp [map_mul, ihy, ihz]
      | inv y hy ih => simp [map_inv, ih]
    | one => simp
    | mul x z hx hz ihx ihz => simp [map_mul, ihx, ihz]
    | inv x hx ih => simp [map_inv, ih]
  have he : Subgroup.closure S = P.L := P.maximal.2 _
    (fun l hl => Subgroup.subset_closure (Set.mem_insert_of_mem d hl)) hc
  rw [← he]
  exact Subgroup.subset_closure (Set.mem_insert d _)
private lemma fixed_support (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (h : UnramifiedCompactInducingData A P I)
    (v : InducedModule P) (hv : v ∈ fixedSubmodule (tau P) (compactTorus A I))
    (x : H) (hx : v.val x ≠ 0) : T.π x ∈ P.L := by
  apply orth_mem P
  intro l hl
  rw [← h.polarization_image] at hl
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hl
  have hjL : T.π j ∈ P.L := by
    rw [← h.polarization_image]
    exact Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
  have hr : v.val (x * j) = v.val x := congrArg (fun w : InducedModule P => w.val x) (hv ⟨j, hj⟩)
  have hl' : v.val (j * x) = v.val x := by
    rw [v.property ⟨j, hjL⟩ x]
    simp [h.character_trivial ⟨j, hj⟩ hjL]
  have hc := T.commutator_mem x j
  have hcL : T.π ⁅x, j⁆ ∈ P.L := by
    have : T.π ⁅x, j⁆ = 1 := by
      change ⁅x, j⁆ ∈ T.π.ker
      rw [T.quotient_kernel]
      exact hc
    rw [this]; exact P.L.one_mem
  have he : ⁅x, j⁆ * (j * x) = x * j := by
    simp [commutatorElement_def, mul_assoc]
  have heq := v.property ⟨⁅x, j⁆, hcL⟩ (j * x)
  rw [he, hr, hl'] at heq
  change v.val x = (P.ωL ⟨⁅x, j⁆, hcL⟩ : ℂ) * v.val x at heq
  rw [P.extends_center _ hc, T.commutator_pairing] at heq
  have hp : ((T.pairing (T.π x) (T.π j) : ℂˣ) : ℂ) = 1 := by
    apply (mul_right_cancel₀ hx)
    simpa using heq.symm
  apply Subtype.ext
  apply Units.ext
  exact hp

 def baseVector (P : Polarization T) : InducedModule P := by
  classical
  exact ⟨fun x => if hx : T.π x ∈ P.L then (P.ωL ⟨x, hx⟩ : ℂ) else 0, by
    classical
    intro a x
    by_cases hx : T.π x ∈ P.L
    · have hax : T.π ((a : H) * x) ∈ P.L := by
        rw [map_mul]; exact P.L.mul_mem a.property hx
      simp only [dif_pos hx, dif_pos hax]
      exact congrArg (fun u : ℂˣ => (u : ℂ)) (P.ωL.map_mul a ⟨x, hx⟩)
    · have hax : T.π ((a : H) * x) ∉ P.L := by
        rw [map_mul, P.L.mul_mem_cancel_left a.property]; exact hx
      simp only [dif_neg hx, dif_neg hax, mul_zero]⟩

 lemma baseVector_fixed (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (h : UnramifiedCompactInducingData A P I) :
    baseVector P ∈ fixedSubmodule (tau P) (compactTorus A I) := by
  classical
  intro j
  apply Subtype.ext
  funext x
  change (baseVector P).val (x * (j : H)) = (baseVector P).val x
  have hj : T.π (j : H) ∈ P.L := by
    rw [← h.polarization_image]
    exact Subgroup.mem_map.mpr ⟨j, j.property, rfl⟩
  by_cases hx : T.π x ∈ P.L
  · have hxj : T.π (x * (j : H)) ∈ P.L := by
      rw [map_mul]; exact P.L.mul_mem hx hj
    simp only [baseVector, dif_pos hx, dif_pos hxj]
    have hh := P.ωL.map_mul ⟨x, hx⟩ ⟨j, hj⟩
    change P.ωL ⟨x * (j : H), hxj⟩ = P.ωL ⟨x, hx⟩ * P.ωL ⟨j, hj⟩ at hh
    rw [hh, h.character_trivial j hj, mul_one]
  · have hxj : T.π (x * (j : H)) ∉ P.L := by
      rw [map_mul, P.L.mul_mem_cancel_right hj]; exact hx
    simp only [baseVector, dif_neg hx, dif_neg hxj]

 lemma fixed_vector_formula (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (h : UnramifiedCompactInducingData A P I)
    (v : InducedModule P) (hv : v ∈ fixedSubmodule (tau P) (compactTorus A I)) :
    v = v.val 1 • baseVector P := by
  classical
  apply Subtype.ext
  funext x
  by_cases hx : T.π x ∈ P.L
  · have hh := v.property ⟨x, hx⟩ 1
    simpa [baseVector, hx, mul_comm] using hh
  · have hz : v.val x = 0 := by
      by_contra hh
      exact hx (fixed_support A P I h v hv x hh)
    simp [baseVector, hx, hz]
 lemma baseVector_one (P : Polarization T) : (baseVector P).val 1 = 1 := by
  classical
  change (if hx : T.π 1 ∈ P.L then (P.ωL ⟨1, hx⟩ : ℂ) else 0) = 1
  rw [dif_pos (by simp)]
  change (P.ωL 1 : ℂ) = 1
  simp

theorem normalized_inducing_vector
    (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (_h : UnramifiedCompactInducingData A P I) :
    ∃! v : InducedModule P,
      v ∈ fixedSubmodule (tau P) (compactTorus A I) ∧ v.val 1 = 1 := by
  refine ⟨baseVector P, ⟨baseVector_fixed A P I _h, baseVector_one P⟩, ?_⟩
  intro v hv
  rw [fixed_vector_formula A P I _h v hv.1, hv.2, one_smul]

 lemma action_compact (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (b : A.B) (hb : (b : G) ∈ I.compact.toOpenSubgroup) (v : InducedModule P) :
    inducingAction A P .plus 0 b v = tau P (A.retract b) v := by
  change (inducingScalar A 0 b • borelAction A P .plus b) v = _
  have hs : inducingScalar A 0 b = 1 := by
    simp [inducingScalar, deltaHalf, normPower, I.intersection_norm b hb]
  rw [hs, one_smul]
  rfl

 def constantPicture (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (h : UnramifiedCompactInducingData A P I)
    (v : InducedModule P) (hv : v ∈ fixedSubmodule (tau P) (compactTorus A I)) :
    compactPicture A P I .plus :=
  ⟨fun _ => v, by
    constructor
    · intro b k k' he
      have hb : (b : G) ∈ I.compact.toOpenSubgroup := by
        have hb' : (b : G) = (k' : G) * (k : G)⁻¹ := by rw [he]; simp [mul_assoc]
        rw [hb']; exact I.compact.toOpenSubgroup.mul_mem k'.property
          (I.compact.toOpenSubgroup.inv_mem k.property)
      rw [action_compact A P I b hb v]
      exact (hv ⟨A.retract b, h.compact_borel_retract b hb⟩).symm
    · refine ⟨⊤, ?_⟩
      intro j hj
      apply funext
      intro k
      rfl⟩

 lemma constantPicture_level (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (h : UnramifiedCompactInducingData A P I)
    (v : InducedModule P) (hv : v ∈ fixedSubmodule (tau P) (compactTorus A I)) :
    constantPicture A P I h v hv ∈ compactLevel A P I .plus I.compact := by
  intro j k k' he; rfl

 lemma picture_constant (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (φ : compactPicture A P I .plus)
    (hφ : φ ∈ compactLevel A P I .plus I.compact)
    (k : I.compact.toOpenSubgroup) : φ.val k = φ.val 1 := by
  exact hφ k 1 k (by simp)

 lemma picture_fiber_fixed (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (φ : compactPicture A P I .plus)
    (hφ : φ ∈ compactLevel A P I .plus I.compact) :
    φ.val 1 ∈ fixedSubmodule (tau P) (compactTorus A I) := by
  intro j
  have hj : (A.torus (j : H) : G) ∈ I.compact.toOpenSubgroup := j.property
  let k : I.compact.toOpenSubgroup := ⟨A.torus (j : H), hj⟩
  have hc := φ.property.1 (A.torus (j : H)) 1 k (by simp [k])
  rw [picture_constant A P I φ hφ k, action_compact A P I _ hj,
    A.retract_torus] at hc
  exact hc.symm

 def compactSectionEquiv (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) :
    compactLevel A P I .plus I.compact ≃ₗ[ℂ]
      fixedSubmodule (V := sectionSpace A P .plus 0) (IPlus A P)
        (I.compact.toOpenSubgroup : Subgroup G) where
  toFun φ := ⟨compactTrivialization A P I .plus 0 φ.val,
    (compact_level_identification A P I .plus I.compact le_rfl 0 φ.val).mp φ.property⟩
  invFun f := ⟨(compactTrivialization A P I .plus 0).symm f.val,
    (compact_level_identification A P I .plus I.compact le_rfl 0 _).mpr
      (by simpa using f.property)⟩
  left_inv φ := by
    apply Subtype.ext
    exact (compactTrivialization A P I .plus 0).symm_apply_apply φ.val
  right_inv f := by
    apply Subtype.ext
    exact (compactTrivialization A P I .plus 0).apply_symm_apply f.val
  map_add' := by intros; apply Subtype.ext; simp
  map_smul' := by intros; apply Subtype.ext; simp

private lemma section_equiv_one (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (φ : compactLevel A P I .plus I.compact) :
    ((compactSectionEquiv A P I φ).val.val 1) = φ.val.val 1 := by
  change inducingAction A P .plus 0 (I.borelPart 1)
    (φ.val.val (I.compactPart 1)) = φ.val.val 1
  have hb : I.borelPart 1 = 1 := by simpa using I.borelPart_compact 1
  have hk : I.compactPart 1 = 1 := by simpa using I.compactPart_compact 1
  rw [hb, hk]
  simp

theorem normalized_plus_spherical_vector
    (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (_h : UnramifiedCompactInducingData A P I) :
    ∃! f : sectionSpace A P .plus 0,
      f ∈ fixedSubmodule (IPlus A P) I.compact.toOpenSubgroup ∧
        (f.val 1).val 1 = 1 := by
  obtain ⟨v, hv, hu⟩ := normalized_inducing_vector A P I _h
  let c : compactLevel A P I .plus I.compact :=
    ⟨constantPicture A P I _h v hv.1, constantPicture_level A P I _h v hv.1⟩
  let f := compactSectionEquiv A P I c
  refine ⟨f.val, ⟨f.property, ?_⟩, ?_⟩
  · rw [show (f.val.val 1) = c.val.val 1 from section_equiv_one A P I c]
    exact hv.2
  · intro g hg
    let cg := (compactSectionEquiv A P I).symm ⟨g, hg.1⟩
    have hev : cg.val.val 1 = g.val 1 := by
      have he := section_equiv_one A P I cg
      rw [(compactSectionEquiv A P I).apply_symm_apply] at he
      exact he.symm
    have hvg : cg.val.val 1 = v := hu _ ⟨picture_fiber_fixed A P I cg.val cg.property,
      by rw [hev]; exact hg.2⟩
    have hc : cg = c := by
      apply Subtype.ext
      apply Subtype.ext
      funext k
      rw [picture_constant A P I cg.val cg.property k, hvg]
      rfl
    have he := congrArg (compactSectionEquiv A P I) hc
    rw [(compactSectionEquiv A P I).apply_symm_apply] at he
    exact congrArg Subtype.val he

end

end DedekindZetaZeroFree.KPLocalGoodSphericalImage

section

namespace DedekindZetaZeroFree.KPLocalGoodSphericalImage

open KPLocalStoneVonNeumann KPLocalPrincipalSeries
open scoped commutatorElement Valued
open ValuativeRel

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

private def inducingEvaluation (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (h : UnramifiedCompactInducingData A P I) :
    fixedSubmodule (tau P) (compactTorus A I) ≃ₗ[ℂ] ℂ where
  toFun v := v.val.val 1
  invFun c := ⟨c • baseVector P, (fixedSubmodule _ _).smul_mem c (baseVector_fixed A P I h)⟩
  left_inv v := by
    apply Subtype.ext
    exact (fixed_vector_formula A P I h v.val v.property).symm
  right_inv c := by simp [baseVector_one]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem inducing_fixed_line
    (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (_h : UnramifiedCompactInducingData A P I) :
    Module.Finite ℂ (fixedSubmodule (tau P) (compactTorus A I)) ∧
      Module.finrank ℂ (fixedSubmodule (tau P) (compactTorus A I)) = 1 := by
  let e := inducingEvaluation A P I _h
  exact ⟨Module.Finite.of_injective e.toLinearMap e.injective, by rw [e.finrank_eq]; simp⟩

private def compactFiberEquiv (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (h : UnramifiedCompactInducingData A P I) :
    compactLevel A P I .plus I.compact ≃ₗ[ℂ]
      fixedSubmodule (tau P) (compactTorus A I) where
  toFun φ := ⟨φ.val.val 1, picture_fiber_fixed A P I φ.val φ.property⟩
  invFun v := ⟨constantPicture A P I h v.val v.property,
    constantPicture_level A P I h v.val v.property⟩
  left_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    exact (picture_constant A P I φ.val φ.property k).symm
  right_inv v := rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem plus_compact_fixed_line
    (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A)
    (_h : UnramifiedCompactInducingData A P I) :
    Module.Finite ℂ (fixedSubmodule (V := sectionSpace A P .plus 0)
        (IPlus A P) (I.compact.toOpenSubgroup : Subgroup G)) ∧
      Module.finrank ℂ (fixedSubmodule (V := sectionSpace A P .plus 0)
        (IPlus A P) (I.compact.toOpenSubgroup : Subgroup G)) = 1 := by
  let e := (compactSectionEquiv A P I).symm.trans (compactFiberEquiv A P I _h)
  have hi := inducing_fixed_line A P I _h
  letI : Module.Finite ℂ (fixedSubmodule (tau P) (compactTorus A I)) := hi.1
  exact ⟨(Module.Finite.equiv_iff e).mpr hi.1, by rw [e.finrank_eq]; exact hi.2⟩

end

end DedekindZetaZeroFree.KPLocalGoodSphericalImage

end
