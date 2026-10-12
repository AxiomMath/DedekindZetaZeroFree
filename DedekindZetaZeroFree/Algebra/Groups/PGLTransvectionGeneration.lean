module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.FlowAction

@[expose] public section

noncomputable section
open scoped Classical MatrixGroups
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open Matrix

theorem projective_transvection_induction (P : PGL(Fin 2, ℂ) → Prop)
    (ht : ∀(i j : Fin 2) (h : i≠j) c,
      P (SpecialLinearGroup.toPGL (SpecialLinearGroup.transvection h c)))
    (hm : ∀a b,P a→P b→P (a*b)) (g : PGL(Fin 2,ℂ)) : P g := by
  have hs : Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n:=Fin 2) (R:=ℂ)) := by
    apply ProjectiveSpecialLinearGroup.toPGL_surj_of_roots
    intro r
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (r:ℂ) (n:=2) (by decide)
    have hn : z≠0 := by intro h;rw [h,zero_pow (by decide)] at hz;exact r.ne_zero hz.symm
    refine ⟨Units.mk0 z hn,?_⟩
    apply Units.ext
    simpa using hz
  obtain ⟨a,ha⟩ := hs g
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [←ha]
    change P (SpecialLinearGroup.toPGL a)
    apply SL2.transvection_induction (fun a=>P (SpecialLinearGroup.toPGL a)) ht
    intro a b h₁ h₂
    simpa only [map_mul] using hm (SpecialLinearGroup.toPGL a) (SpecialLinearGroup.toPGL b) h₁ h₂
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
