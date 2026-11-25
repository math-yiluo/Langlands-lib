/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.EtaleSectionNeighbourhoodRefinement

/-! # Lifting a section at one pair neighbourhood

Source: Stacks Project, More on Algebra, Tag 0A02, verification of condition (2)
of Tag 09XI (blueprint: lem-weil-pbc-pair-henselization-stage-sections).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace RingTheory

private theorem quotient_map_unique
    {B C Q : Type u} [CommRing B] [CommRing C] [CommRing Q]
    (J : Ideal B) (f : B →+* C)
    (hq : Function.Surjective (Ideal.quotientMap (J.map f) f Ideal.le_comap_map))
    (r t : C →+* Q) (h : r.comp f = t.comp f)
    (hr : J.map f ≤ RingHom.ker r) (ht : J.map f ≤ RingHom.ker t) : r = t := by
  let r' := Ideal.Quotient.lift (J.map f) r hr
  let t' := Ideal.Quotient.lift (J.map f) t ht
  have he : r' = t' := by
    apply RingHom.ext
    intro x
    obtain ⟨b, hb⟩ := hq x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← hb]
    simp only [Ideal.quotientMap_mk, r', t', Ideal.Quotient.lift_mk]
    exact DFunLike.congr_fun h a
  ext x
  exact congrArg (fun z : C ⧸ J.map f →+* Q ↦ z (Ideal.Quotient.mk _ x)) he

/-- A section of an étale algebra over one neighbourhood extends to the vertex of
any cocone of pair neighbourhoods with unchanged quotient.
Source: Stacks Project, Tag 0A02, verification of condition (2) of Tag 09XI
(blueprint: lem-weil-pbc-pair-henselization-stage-sections).

Proof: Identify the quotient of the stage and the quotient of the vertex with B/J
using their canonical quotient isomorphisms. The section kills the extension of J
to D, hence factors through D/JD, an étale algebra over B/J by base change. Split
this section by an idempotent e with image 1, and lift e to g in D. Localize D at g.
Its quotient by J is B/J, since quotient commutes with localization and localization
at e is B/J by the splitting theorem. Composition and localization show that D_g
is étale over B, so it is another object of the neighbourhood category. The map
from the original stage to D_g is a morphism in that category. Compose D to D_g
with its cocone map to obtain t. Cocone naturality makes t an algebra map over
the original stage. Since s(g)=1, the original section extends to D_g. Every map
from D_g to B/J over B equals the inverse of its quotient isomorphism: it kills J,
and a map from B/J to itself fixing B is the identity by quotient surjectivity.
Apply this uniqueness both to the extended section and the reduced cocone map,
then restrict to D. No filteredness or colimit universality is used. -/
theorem pair_henselization_stage_sections (B : Type u) [CommRing B] (J : Ideal B)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hq : Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
      Ideal.le_comap_map))
    (i : ObjectProperty.FullSubcategory (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            Ideal.le_comap_map)))
    (D : Type u) [CommRing D] (g : i.obj.right →+* D)
    (hd : letI : Algebra i.obj.right D := g.toAlgebra
      Algebra.Etale i.obj.right D)
    (s : letI : Algebra i.obj.right c.pt.right := (c.ι.app i).right.hom.toAlgebra
      letI : Algebra i.obj.right D := g.toAlgebra
      D →ₐ[i.obj.right] c.pt.right ⧸ J.map c.pt.hom.hom) :
    letI : Algebra i.obj.right c.pt.right := (c.ι.app i).right.hom.toAlgebra
    letI : Algebra i.obj.right D := g.toAlgebra
    ∃ t : D →ₐ[i.obj.right] c.pt.right,
      ((Ideal.Quotient.mkₐ c.pt.right (J.map c.pt.hom.hom)).restrictScalars
        i.obj.right).comp t = s := by
  classical
  let : Algebra i.obj.right c.pt.right := (c.ι.app i).right.hom.toAlgebra
  let : Algebra i.obj.right D := g.toAlgebra
  let q := Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom Ideal.le_comap_map
  let e := RingEquiv.ofBijective q hq
  let s₀ : D →+* B ⧸ J := e.symm.toRingHom.comp s.toRingHom
  have hs₀ : (s₀.comp g).comp i.obj.hom.hom = Ideal.Quotient.mk J := by
    ext b
    apply e.injective
    change e (e.symm (s (g (i.obj.hom.hom b)))) = q (Ideal.Quotient.mk J b)
    rw [e.apply_symm_apply, Ideal.quotientMap_mk]
    have hw := congrArg CommRingCat.Hom.hom (c.ι.app i).w
    change s (algebraMap i.obj.right D (i.obj.hom.hom b)) = _
    rw [s.commutes]
    change Ideal.Quotient.mk _ ((c.ι.app i).right.hom (i.obj.hom.hom b)) = _
    exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun hw b)
  obtain ⟨N, j, k, r, hkg, hr, hrk⟩ :=
    etale_section_neighbourhood_refinement B J i D g hd s₀ hs₀
  let p : N.obj.right →+* c.pt.right := (c.ι.app N).right.hom
  let t : D →ₐ[i.obj.right] c.pt.right :=
    { toRingHom := p.comp k
      commutes' := by
        intro x
        change p (k (g x)) = (c.ι.app i).right.hom x
        have hn := congrArg (fun z ↦ z.right.hom) (c.w j)
        have hx := DFunLike.congr_fun hkg x
        change k (g x) = j.hom.right.hom x at hx
        rw [hx]
        exact DFunLike.congr_fun hn x }
  refine ⟨t, ?_⟩
  let red : N.obj.right →+* c.pt.right ⧸ J.map c.pt.hom.hom :=
    (Ideal.Quotient.mk _).comp p
  have hn : red.comp N.obj.hom.hom = q.comp (Ideal.Quotient.mk J) := by
    ext b
    have hw := congrArg CommRingCat.Hom.hom (c.ι.app N).w
    change Ideal.Quotient.mk _ (p (N.obj.hom.hom b)) = _
    change Ideal.Quotient.mk _ (p (N.obj.hom.hom b)) = q (Ideal.Quotient.mk J b)
    rw [Ideal.quotientMap_mk]
    exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun hw b)
  have hkill (a : N.obj.right →+* c.pt.right ⧸ J.map c.pt.hom.hom)
      (ha : a.comp N.obj.hom.hom = q.comp (Ideal.Quotient.mk J)) :
      J.map N.obj.hom.hom ≤ RingHom.ker a := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change a (N.obj.hom.hom b) = 0
    have h := DFunLike.congr_fun ha b
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hb] using h
  have hqr : (q.comp r).comp N.obj.hom.hom = q.comp (Ideal.Quotient.mk J) := by
    rw [RingHom.comp_assoc, hr]
  have heq : red = q.comp r :=
    quotient_map_unique J N.obj.hom.hom N.property.2.2 red (q.comp r)
      (hn.trans hqr.symm) (hkill red hn) (hkill (q.comp r) hqr)
  ext x
  change red (k x) = s x
  rw [heq]
  change q (r (k x)) = s x
  rw [show r (k x) = s₀ x from DFunLike.congr_fun hrk x]
  exact e.apply_symm_apply (s x)

end RingTheory
