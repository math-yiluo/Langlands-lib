/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.SmoothOverProductRing
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Filtered colimits of smooth algebras and products

Source: literature/stacks-project/smoothing.tex, Lemma Tag 07F3 (lemma-product)
(blueprint: lem-weil-pbc-popescu-product).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

-- The base ring may live in a smaller universe than the algebra objects.
-- Adapted from the ringColimit helper of FilteredColimitAlgebrasUnderlyingModule.
private noncomputable def forgetRingIsColimit
    (A : Type u) [CommRing A] {I : Type v} [SmallCategory I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{v} A) (c : Limits.Cocone B) (hc : Limits.IsColimit c) :
    Limits.IsColimit ((forget₂ (CommAlgCat A) CommRingCat).mapCocone c) := by
  classical
  let U := forget₂ (CommAlgCat.{v} A) CommRingCat.{v}
  let i : I := Classical.choice IsFiltered.nonempty
  have comm (s : Limits.Cocone (B ⋙ U)) (j : I) (a : A) :
      (s.ι.app j).hom (algebraMap A (B.obj j) a) =
        (s.ι.app i).hom (algebraMap A (B.obj i) a) := by
    let k := IsFiltered.max i j
    have hi := ConcreteCategory.congr_hom (s.w (IsFiltered.leftToMax i j))
      (algebraMap A (B.obj i) a)
    have hj := ConcreteCategory.congr_hom (s.w (IsFiltered.rightToMax i j))
      (algebraMap A (B.obj j) a)
    change (s.ι.app k).hom ((B.map _).hom (algebraMap A (B.obj i) a)) = _ at hi
    change (s.ι.app k).hom ((B.map _).hom (algebraMap A (B.obj j) a)) = _ at hj
    simp only [AlgHom.commutes] at hi hj
    exact hj.symm.trans hi
  let liftCocone (s : Limits.Cocone (B ⋙ U)) : Limits.Cocone B :=
    let : Algebra A s.pt :=
      ((s.ι.app i).hom.comp (algebraMap A (B.obj i))).toAlgebra
    { pt := CommAlgCat.of A s.pt
      ι :=
        { app := fun j ↦ CommAlgCat.ofHom
            { __ := (s.ι.app j).hom
              commutes' := comm s j }
          naturality := by
            intro j k f
            ext x
            exact ConcreteCategory.congr_hom (s.w f) x } }
  let desc (s : Limits.Cocone (B ⋙ U)) := U.map (hc.desc (liftCocone s))
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    exact congrArg (fun f ↦ U.map f) (hc.fac (liftCocone s) j)
  · intro s m hm
    let : Algebra A s.pt :=
      ((s.ι.app i).hom.comp (algebraMap A (B.obj i))).toAlgebra
    let ma : c.pt ⟶ (liftCocone s).pt := CommAlgCat.ofHom
      { __ := m.hom
        commutes' := by
          intro a
          have h := ConcreteCategory.congr_hom (hm i) (algebraMap A (B.obj i) a)
          change m.hom ((c.ι.app i).hom (algebraMap A (B.obj i) a)) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a) at h
          simp only [AlgHom.commutes] at h
          change m.hom (algebraMap A ↥(c.pt) a) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a)
          exact h }
    have he : ma = hc.desc (liftCocone s) := by
      apply hc.hom_ext
      intro j
      rw [hc.fac]
      ext x
      exact ConcreteCategory.congr_hom (hm j) x
    exact congrArg (fun f ↦ U.map f) he


-- Reflect the underlying ring colimit, then check the algebra-map law at one stage.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def algebraIsColimitOfForget
    {R : Type u} [CommRing R] {I : Type v} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{v} R} {c : Limits.Cocone F}
    (ht : Limits.IsColimit ((forget (CommAlgCat.{v} R)).mapCocone c)) : Limits.IsColimit c := by
  classical
  let U := forget₂ (CommAlgCat.{v} R) CommRingCat.{v}
  letI : Limits.ReflectsColimitsOfShape I (forget CommRingCat.{v}) :=
    Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hc : Limits.IsColimit (U.mapCocone c) :=
    Limits.isColimitOfReflects (forget CommRingCat.{v}) ht
  let i : I := Classical.choice IsFiltered.nonempty
  refine
    { desc := fun s ↦ CommAlgCat.ofHom
        { __ := (hc.desc (U.mapCocone s)).hom
          commutes' := ?_ }
      fac := ?_
      uniq := ?_ }
  · intro r
    have h := ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) i)
      (algebraMap R (F.obj i) r)
    change (hc.desc (U.mapCocone s)).hom
      ((c.ι.app i).hom (algebraMap R (F.obj i) r)) =
      (s.ι.app i).hom (algebraMap R (F.obj i) r) at h
    simp only [AlgHom.commutes] at h
    exact h
  · intro s j
    ext x
    exact ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) j) x
  · intro s m hm
    have h : U.map m = hc.desc (U.mapCocone s) := by
      apply hc.hom_ext
      intro j
      exact (congrArg (fun f ↦ U.map f) (hm j)).trans (hc.fac (U.mapCocone s) j).symm
    ext x
    exact ConcreteCategory.congr_hom h x

private def productObj {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    (A : CommAlgCat.{max u v} R₁) (B : CommAlgCat.{max u v} R₂) :
    CommAlgCat.{max u v} (R₁ × R₂) :=
  letI := (RingHom.prodMap (algebraMap R₁ A) (algebraMap R₂ B)).toAlgebra
  CommAlgCat.of (R₁ × R₂) (A × B)

private def productMap {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    {A A' : CommAlgCat.{max u v} R₁} {B B' : CommAlgCat.{max u v} R₂}
    (f : A ⟶ A') (g : B ⟶ B') : productObj A B ⟶ productObj A' B' := by
  letI := (RingHom.prodMap (algebraMap R₁ A) (algebraMap R₂ B)).toAlgebra
  letI := (RingHom.prodMap (algebraMap R₁ A') (algebraMap R₂ B')).toAlgebra
  exact CommAlgCat.ofHom
    { __ := RingHom.prodMap f.hom.toRingHom g.hom.toRingHom
      commutes' := by
        rintro ⟨r₁, r₂⟩
        exact Prod.ext (f.hom.commutes r₁) (g.hom.commutes r₂) }

set_option backward.isDefEq.respectTransparency false in
/-- The product of two filtered colimits of smooth algebras is such a colimit over the
product base ring.

Source: literature/stacks-project/smoothing.tex, Lemma Tag 07F3 (lemma-product).
(blueprint: lem-weil-pbc-popescu-product).

Proof:
1. By def-weil-pbc-filtered-colimit-smooth-algebras, choose small filtered diagrams
   `A : I ⥤ CommAlgCat R₁` and `B : J ⥤ CommAlgCat R₂`, with smooth terms and colimit
   cocones `ιᵢ : Aᵢ → Λ₁` and `κⱼ : Bⱼ → Λ₂` (def-weil-pbc-category-colimit).
   The category `I × J` is nonempty. Common upper objects and equalizers of parallel
   arrows are obtained componentwise, so it is small and filtered.
2. Define `D(i,j) = Aᵢ × Bⱼ` over `R₁ × R₂`, with transition maps the products of the
   component transition maps. Identities and composition hold componentwise. Each term
   is smooth by lem-weil-pbc-smooth-over-product-ring and def-weil-pbc-smooth-ring-map.
3. The maps `θ(i,j) = ιᵢ × κⱼ` are algebra maps to `Λ₁ × Λ₂` for the product structure
   map. Componentwise cocone compatibility makes them a cocone on `D`, in the sense of
   def-weil-pbc-category-colimit.
4. Forget each coordinate algebra colimit to rings: give any ring cocone apex its
   algebra structure using a leg at one index; common upper objects make all legs
   compatible with it. The algebra universal property then gives the ring universal
   property. Mathlib preserves these filtered ring colimits on underlying types.
   Every pair in `Λ₁ × Λ₂` is represented at `(i,j)` by representing its coordinates
   separately. If two pairs at `(i,j)` have equal images, the filtered type-colimit
   equality criterion gives arrows `i → k` and `j → l` making their respective
   coordinates equal. Their product arrow makes the pairs equal. Mathlib's
   `Types.FilteredColimit.isColimitOf'` therefore proves the type cocone colimiting.
   Reflect this colimit to rings, then lift each universal ring map to an algebra
   map: its compatibility with the structure map follows by evaluating the
   factorization identity on a base-ring element at one index. Factorization and
   uniqueness follow from the ring universal property, proving the algebra colimit
   in def-weil-pbc-category-colimit.
5. The small filtered product diagram has smooth terms and the required colimit cocone,
   so def-weil-pbc-filtered-colimit-smooth-algebras gives the conclusion.

Algebras and index categories live in universe `max u v`, as in the Popescu siblings
(lem-weil-pbc-colimit-standard-smooth-algebras, lem-weil-pbc-popescu-lift-once). -/
theorem ind_smooth_prod
    (R₁ R₂ : Type u) (Λ₁ Λ₂ : Type (max u v))
    [CommRing R₁] [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂]
    [Algebra R₁ Λ₁] [Algebra R₂ Λ₂]
    (h₁ : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R₁ ↦ Algebra.Smooth R₁ B) (CommAlgCat.of R₁ Λ₁))
    (h₂ : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R₂ ↦ Algebra.Smooth R₂ B) (CommAlgCat.of R₂ Λ₂)) :
    letI : Algebra (R₁ × R₂) (Λ₁ × Λ₂) :=
      RingHom.toAlgebra (RingHom.prodMap (algebraMap R₁ Λ₁) (algebraMap R₂ Λ₂))
    ObjectProperty.ind.{max u v} (fun B : CommAlgCat.{max u v} (R₁ × R₂) ↦
      Algebra.Smooth (R₁ × R₂) B) (CommAlgCat.of (R₁ × R₂) (Λ₁ × Λ₂)) := by
  classical
  let : Algebra (R₁ × R₂) (Λ₁ × Λ₂) :=
    (RingHom.prodMap (algebraMap R₁ Λ₁) (algebraMap R₂ Λ₂)).toAlgebra
  obtain ⟨I, _, _, p, hp⟩ := h₁
  obtain ⟨J, _, _, q, hq⟩ := h₂
  let D : I × J ⥤ CommAlgCat.{max u v} (R₁ × R₂) :=
    { obj := fun i ↦ productObj (p.diag.obj i.1) (q.diag.obj i.2)
      map := fun f ↦ productMap (p.diag.map f.1) (q.diag.map f.2)
      map_id := by
        intro i
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        change ((p.diag.map (𝟙 i.1)) x.1, (q.diag.map (𝟙 i.2)) x.2) = x
        simp
      map_comp := by
        intro i j k f g
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        change ((p.diag.map (f.1 ≫ g.1)) x.1, (q.diag.map (f.2 ≫ g.2)) x.2) =
          ((p.diag.map g.1) ((p.diag.map f.1) x.1),
            (q.diag.map g.2) ((q.diag.map f.2) x.2))
        simp }
  let c : Limits.Cocone D :=
    { pt := CommAlgCat.of (R₁ × R₂) (Λ₁ × Λ₂)
      ι :=
        { app := fun i ↦ productMap (p.ι.app i.1) (q.ι.app i.2)
          naturality := by
            intro i j f
            ext x
            exact Prod.ext
              (ConcreteCategory.congr_hom (p.w f.1) x.1)
              (ConcreteCategory.congr_hom (q.w f.2) x.2) } }
  have hc : Limits.IsColimit c := by
    apply algebraIsColimitOfForget
    have ht₁ := Limits.isColimitOfPreserves (forget CommRingCat.{max u v})
      (forgetRingIsColimit R₁ p.diag p.cocone p.isColimit)
    have ht₂ := Limits.isColimitOfPreserves (forget CommRingCat.{max u v})
      (forgetRingIsColimit R₂ q.diag q.cocone q.isColimit)
    apply Limits.Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨i, a, ha⟩ := Limits.Types.jointly_surjective_of_isColimit ht₁ x.1
      obtain ⟨j, b, hb⟩ := Limits.Types.jointly_surjective_of_isColimit ht₂ x.2
      exact ⟨(i, j), (a, b), Prod.ext ha.symm hb.symm⟩
    · intro i x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      change (p.ι.app i.1) x.1 = (p.ι.app i.1) y.1 at h₁
      change (q.ι.app i.2) x.2 = (q.ι.app i.2) y.2 at h₂
      obtain ⟨k, f, hf⟩ :=
        (Limits.Types.FilteredColimit.isColimit_eq_iff' ht₁ x.1 y.1).mp h₁
      obtain ⟨l, g, hg⟩ :=
        (Limits.Types.FilteredColimit.isColimit_eq_iff' ht₂ x.2 y.2).mp h₂
      exact ⟨(k, l), (f, g), Prod.ext hf hg⟩
  refine ⟨I × J, inferInstance, inferInstance, ⟨D, c.ι, hc⟩, ?_⟩
  intro i
  change @Smooth (R₁ × R₂) _
    (p.diag.obj i.1 × q.diag.obj i.2) _
    ((RingHom.prodMap (algebraMap R₁ _) (algebraMap R₂ _)).toAlgebra)
  apply smooth_over_product_ring
  · rw [toAlgebra_algebraMap]
    exact hp i.1
  · rw [toAlgebra_algebraMap]
    exact hq i.2

end Algebra
