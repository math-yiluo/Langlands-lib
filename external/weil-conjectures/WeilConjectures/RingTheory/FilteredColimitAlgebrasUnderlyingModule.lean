/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Underlying modules of filtered colimits of commutative algebras

Source: Stacks Project, Algebra, Tag 00D6 (lemma-directed-colimit); the algebra version is
used implicitly in Tag 07RI (lemma-colimit-etale).
(blueprint: theorem-finite-etale-covers-proper-henselian--2)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

-- This proves clause (1) of the elementwise node. The argument is reused from
-- the private helper in Sheaf.RingTheory.EtaleColimitNormalLocalDomain.
-- Forgetting the algebra structure preserves this filtered colimit, even when
-- the base ring and the diagram rings live in different universes.
private noncomputable def ringColimit
    (A : Type u) [CommRing A] {I : Type v} [SmallCategory I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{v} A) [HasColimit B] :
    IsColimit ((forget₂ (CommAlgCat A) CommRingCat).mapCocone (colimit.cocone B)) := by
  classical
  let U := forget₂ (CommAlgCat.{v} A) CommRingCat.{v}
  let i : I := Classical.choice IsFiltered.nonempty
  have comm (s : Cocone (B ⋙ U)) (j : I) (a : A) :
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
  let liftCocone (s : Cocone (B ⋙ U)) : Cocone B :=
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
  let desc (s : Cocone (B ⋙ U)) := U.map (colimit.desc B (liftCocone s))
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    exact congrArg (fun f ↦ U.map f) (colimit.ι_desc (liftCocone s) j)
  · intro s m hm
    let : Algebra A s.pt :=
      ((s.ι.app i).hom.comp (algebraMap A (B.obj i))).toAlgebra
    let ma : colimit B ⟶ (liftCocone s).pt := CommAlgCat.ofHom
      { __ := m.hom
        commutes' := by
          intro a
          have h := ConcreteCategory.congr_hom (hm i) (algebraMap A (B.obj i) a)
          change m.hom ((colimit.ι B i).hom (algebraMap A (B.obj i) a)) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a) at h
          simp only [AlgHom.commutes] at h
          change m.hom (algebraMap A ↥(colimit B) a) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a)
          exact h }
    have he : ma = colimit.desc B (liftCocone s) := by
      apply colimit.hom_ext
      intro j
      rw [colimit.ι_desc]
      ext x
      exact ConcreteCategory.congr_hom (hm j) x
    exact congrArg (fun f ↦ U.map f) he

/-- The underlying module of the filtered colimit `colimit F` of commutative `R`-algebras,
with the coprojections `colimit.ι F i`, satisfies the module colimit universal property.
Source: Stacks Project, Algebra, Tag 00D6 (lemma-directed-colimit), transcribed to algebras,
as used implicitly in Tag 07RI (lemma-colimit-etale).
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof, following the node's five steps:
1. By `lem-weil-pbc-filtered-colimit-algebras-elementwise`, the colimit cocone is also a ring
   colimit and every element is represented at a stage. Apply
   `lem-weil-pbc-filtered-colimit-rings-zero` to this ring colimit: two representatives
   agree exactly when their images agree at a common later object.
2. Algebra maps are additive and commute with the structure maps from `R`, hence are
   `R`-linear. The algebra cocone identities therefore give a module cocone, using
   `def-weil-pbc-category-colimit`.
3. Define the descended map on an element represented by `a` at stage `i` to be `f i a`.
   The equality criterion and compatibility of the family make this independent of
   the representative, and give the required identities on all coprojections.
4. Represent two elements at a common later object, using filteredness. Addition and
   scalar multiplication are computed there, so linearity follows from linearity of
   the stage map.
5. Every element comes from a stage. Thus any map with the required identities agrees
   with the descended map on every element, proving uniqueness and the universal property.
-/
theorem filtered_colimit_algebras_underlying_module
    {R : Type u} [CommRing R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{v} R) [HasColimit F]
    (P : Type w) [AddCommGroup P] [Module R P]
    (f : ∀ i : I, F.obj i →ₗ[R] P)
    (hf : ∀ (i j : I) (a : i ⟶ j), (f j).comp (F.map a).hom.toLinearMap = f i) :
    ∃! g : (colimit F : CommAlgCat.{v} R) →ₗ[R] P,
      ∀ i : I, g.comp (colimit.ι F i).hom.toLinearMap = f i := by
  classical
  let U := F ⋙ forget (CommAlgCat.{v} R)
  let d := (forget (CommAlgCat.{v} R)).mapCocone (colimit.cocone F)
  have hd : IsColimit d := isColimitOfPreserves (forget CommRingCat.{v}) (ringColimit R F)
  -- CoconeTypes allows the destination module to live in the independent universe w.
  let dt : U.CoconeTypes := U.coconeTypesEquiv.symm d
  have hdt : dt.IsColimit := (Types.isColimit_iff_coconeTypesIsColimit d).mp ⟨hd⟩
  let s : U.CoconeTypes :=
    { pt := P
      ι := fun i ↦ f i
      ι_naturality := by
        intro i j a
        exact congrArg DFunLike.coe (hf i j a) }
  let g : ↑(colimit F : CommAlgCat.{v} R) → P := hdt.desc s
  have hg (i : I) (x : F.obj i) : g ((colimit.ι F i).hom x) = f i x :=
    hdt.fac_apply s i x
  let l : (colimit F : CommAlgCat.{v} R) →ₗ[R] P :=
    { toFun := g
      map_add' := by
        intro x y
        obtain ⟨i, a, b, rfl, rfl⟩ :=
          Types.FilteredColimit.jointly_surjective_of_isColimit₂ hd x y
        change g ((colimit.ι F i).hom a + (colimit.ι F i).hom b) =
          g ((colimit.ι F i).hom a) + g ((colimit.ι F i).hom b)
        rw [← map_add, hg, hg, hg, map_add]
      map_smul' := by
        intro r x
        obtain ⟨i, a, rfl⟩ := Types.jointly_surjective_of_isColimit hd x
        change g (r • (colimit.ι F i).hom a) = r • g ((colimit.ι F i).hom a)
        rw [← map_smul, hg, hg, map_smul] }
  refine ⟨l, ?_, ?_⟩
  · intro i
    apply LinearMap.ext
    exact hg i
  · intro l' hl'
    apply LinearMap.ext
    intro x
    obtain ⟨i, a, rfl⟩ := Types.jointly_surjective_of_isColimit hd x
    exact (DFunLike.congr_fun (hl' i) a).trans (hg i a).symm

end CommAlgCat
