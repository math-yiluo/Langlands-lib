/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicUniverseLift

@[expose] public section

universe u u' v

namespace Algebra

/-- Source: Stacks Project, More on Algebra, Remark 07NS and Lemma 07NR
(blueprint: lem-weil-pbc-formally-smooth-adic-ring-equiv)

Give each R′-test algebra D the R-action obtained by composing its structure
map with e.symm. The R′-linear map g : S → D/J is R-linear because
e(e.symm(r)) = r, with the same positive-power vanishing witness. Apply
`formallySmoothAdic_lift_universe` to obtain an R-linear lift f at the test
universe. It is R′-linear because e.symm(e(r′)) = r′. Its underlying ring map
and quotient equality are unchanged, so it solves the original lifting problem. -/
theorem FormallySmoothAdic.of_ringEquiv
    {R : Type u} {R' : Type u'} {S : Type v}
    [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R S] (e : R' ≃+* R) (n : Ideal S)
    (h : FormallySmoothAdic R S n) :
    letI : Algebra R' S := ((algebraMap R S).comp e.toRingHom).toAlgebra
    FormallySmoothAdic R' S n := by
  let : Algebra R' S := ((algebraMap R S).comp e.toRingHom).toAlgebra
  intro D _ _ J hJ g hg
  let : Algebra R D := ((algebraMap R' D).comp e.symm.toRingHom).toAlgebra
  let gR : S →ₐ[R] D ⧸ J :=
    { toRingHom := g.toRingHom
      commutes' := by
        intro r
        have hr := g.commutes (e.symm r)
        change g ((algebraMap R S) (e (e.symm r))) =
          Ideal.Quotient.mk J ((algebraMap R' D) (e.symm r)) at hr
        change g ((algebraMap R S) r) =
          Ideal.Quotient.mk J ((algebraMap R' D) (e.symm r))
        simpa only [RingEquiv.apply_symm_apply] using hr }
  obtain ⟨f, hf⟩ := formallySmoothAdic_lift_universe R S n h D J hJ gR hg
  let f' : S →ₐ[R'] D :=
    { toRingHom := f.toRingHom
      commutes' := by
        intro r'
        have hr := f.commutes (e r')
        change f ((algebraMap R S) (e r')) =
          (algebraMap R' D) (e.symm (e r')) at hr
        change f ((algebraMap R S) (e r')) = (algebraMap R' D) r'
        simpa only [RingEquiv.symm_apply_apply] using hr }
  refine ⟨f', ?_⟩
  ext x
  exact DFunLike.congr_fun hf x

end Algebra
