module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.MeromorphicContinuation

@[expose] public section

section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped Valued Classical
open ValuativeRel KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPLocalGoodSphericalImage KPRankOneTameSphericalFactor

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
  {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
  {T : LocalHeisenbergData H D}

private theorem compact_action
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (b : A.B)
    (hb : (b : G) ∈ I.compact.toOpenSubgroup) (v : InducedModule P) :
    inducingAction A P ε 0 b v = borelAction A P ε b v := by
  have hs : inducingScalar A 0 b = 1 := by
    simp [inducingScalar, deltaHalf, normPower, I.intersection_norm b hb]
  change (inducingScalar A 0 b • borelAction A P ε b) v = _
  rw [hs, one_smul]

theorem compact_level_constant
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (φ : compactPicture A P I ε)
    (hφ : φ ∈ compactLevel A P I ε I.compact)
    (k : I.compact.toOpenSubgroup) : φ.val k = φ.val 1 :=
  hφ k 1 k (by simp)

theorem fixed_inducing_vector_formula
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (hu : UnramifiedCompactInducingData A P I)
    (v0 v : InducedModule P)
    (h0 : v0 ∈ fixedSubmodule (tau P) (compactTorus A I) ∧ v0.val 1 = 1)
    (hv : v ∈ fixedSubmodule (tau P) (compactTorus A I)) :
    v = v.val 1 • v0 := by
  obtain ⟨u, hu', huniq⟩ := normalized_inducing_vector A P I hu
  have hnorm : v + (1 - v.val 1) • v0 ∈ fixedSubmodule (tau P) (compactTorus A I) ∧
      (v + (1 - v.val 1) • v0).val 1 = 1 := by
    refine ⟨(fixedSubmodule _ _).add_mem hv ((fixedSubmodule _ _).smul_mem _ h0.1), ?_⟩
    change v.val 1 + (1 - v.val 1) * v0.val 1 = 1
    rw [h0.2]; ring
  have he : v + (1 - v.val 1) • v0 = v0 := (huniq _ hnorm).trans (huniq _ h0).symm
  apply Subtype.ext
  funext x
  change v.val x = v.val 1 * v0.val x
  have hx := congrArg (fun w : InducedModule P => w.val x) he
  change v.val x + (1 - v.val 1) * v0.val x = v0.val x at hx
  linear_combination hx

 theorem minus_fiber_fixed
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A)
    (hW : (compactTorus A I).map A.weyl.toMulEquiv.toMonoidHom = compactTorus A I)
    (φ : compactPicture A P I .minus)
    (hφ : φ ∈ compactLevel A P I .minus I.compact) :
    φ.val 1 ∈ fixedSubmodule (tau P) (compactTorus A I) := by
  intro j
  have hj : (j : H) ∈ (compactTorus A I).map A.weyl.toMulEquiv.toMonoidHom := by
    rw [hW]; exact j.property
  obtain ⟨a, ha, he⟩ := hj
  have ht : (A.torus a : G) ∈ I.compact.toOpenSubgroup := ha
  let k : I.compact.toOpenSubgroup := ⟨A.torus a, ht⟩
  have hc := φ.property.1 (A.torus a) 1 k (by simp [k])
  rw [compact_level_constant K A P I .minus φ hφ k,
    compact_action K A P I .minus _ ht] at hc
  change φ.val 1 = tau P (A.weyl (A.retract (A.torus a))) (φ.val 1) at hc
  change A.weyl a = (j : H) at he
  rw [A.retract_torus, he] at hc
  exact hc.symm

theorem exists_minus_spherical_vector
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (hu : UnramifiedCompactInducingData A P I)
    (hW : (compactTorus A I).map A.weyl.toMulEquiv.toMonoidHom = compactTorus A I) :
    ∃ φ : compactPicture A P I .minus, IsSphericalVector K A P I .minus φ := by
  obtain ⟨v, hv, _⟩ := normalized_inducing_vector A P I hu
  let φ : compactPicture A P I .minus := ⟨fun _ => v, by
    constructor
    · intro b k k' he
      have hb : (b : G) ∈ I.compact.toOpenSubgroup := by
        have hb' : (b : G) = (k' : G) * (k : G)⁻¹ := by rw [he]; simp [mul_assoc]
        rw [hb']; exact I.compact.toOpenSubgroup.mul_mem k'.property
          (I.compact.toOpenSubgroup.inv_mem k.property)
      rw [compact_action K A P I .minus b hb]
      have hw : A.weyl (A.retract b) ∈ compactTorus A I := by
        rw [← hW]
        exact ⟨A.retract b, hu.compact_borel_retract b hb, rfl⟩
      exact (hv.1 ⟨A.weyl (A.retract b), hw⟩).symm
    · refine ⟨⊤, ?_⟩
      intro j hj
      rfl⟩
  refine ⟨φ, (is_spherical_vector_iff K A P I .minus φ).mpr ⟨?_, hv.2⟩⟩
  intro j k k' he
  rfl

theorem minus_compact_level_formula
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (hu : UnramifiedCompactInducingData A P I)
    (hW : (compactTorus A I).map A.weyl.toMulEquiv.toMonoidHom = compactTorus A I)
    (φ0 φ : compactPicture A P I .minus)
    (h0 : IsSphericalVector K A P I .minus φ0)
    (hφ : φ ∈ compactLevel A P I .minus I.compact) :
    φ = (φ.val 1).val 1 • φ0 := by
  have h0' := (is_spherical_vector_iff K A P I .minus φ0).mp h0
  have hf := fixed_inducing_vector_formula K A P I hu (φ0.val 1) (φ.val 1)
    ⟨minus_fiber_fixed K A P I hW φ0 h0'.1, h0'.2⟩
    (minus_fiber_fixed K A P I hW φ hφ)
  apply Subtype.ext
  funext k
  change φ.val k = (φ.val 1).val 1 • φ0.val k
  rw [compact_level_constant K A P I .minus φ hφ k,
    compact_level_constant K A P I .minus φ0 h0'.1 k]
  exact hf

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end

end

section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped Valued Classical
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPLocalGoodSphericalImage KPRankOneTameSphericalFactor
open KPRankOneRootParameter KPRankOneShellContinuation

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
  {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
  {T : LocalHeisenbergData H D}

 theorem compact_extension_one
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (s : ℂ) (φ : compactPicture A P I ε) :
    (compactTrivialization A P I ε s φ).val 1 = φ.val 1 := by
  change inducingAction A P ε s (I.borelPart (1 : I.compact.toOpenSubgroup))
    (φ.val (I.compactPart (1 : I.compact.toOpenSubgroup))) = _
  rw [I.borelPart_compact, I.compactPart_compact]
  simp

theorem compact_torus_weyl_stable
    (A : LocalBorelData (K := K) (G := G) T) (I : IwasawaData A)
    (hw : A.liftedW ∈ I.compact.toOpenSubgroup) :
    (compactTorus A I).map A.weyl.toMulEquiv.toMonoidHom = compactTorus A I := by
  ext h
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (A.torus (A.weyl a) : G) ∈ I.compact.toOpenSubgroup
    rw [A.weyl_from_lift]
    exact I.compact.toOpenSubgroup.mul_mem
      (I.compact.toOpenSubgroup.mul_mem (I.compact.toOpenSubgroup.inv_mem hw) ha) hw
  · intro hh
    refine ⟨A.weyl.symm h, ?_, ?_⟩
    swap
    · change A.weyl (A.weyl.symm h) = h
      exact A.weyl.apply_symm_apply h
    change (A.torus (A.weyl.symm h) : G) ∈ I.compact.toOpenSubgroup
    have he : (A.torus (A.weyl.symm h) : G) =
        A.liftedW * (A.torus h : G) * A.liftedW⁻¹ := by
      have he' := A.weyl_from_lift (A.weyl.symm h)
      simp only [A.weyl.apply_symm_apply] at he'
      rw [he']; simp [mul_assoc]
    rw [he]
    exact I.compact.toOpenSubgroup.mul_mem
      (I.compact.toOpenSubgroup.mul_mem hw hh) (I.compact.toOpenSubgroup.inv_mem hw)

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end

end
