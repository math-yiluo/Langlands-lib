/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.RingTheory.ElementwiseFpModuleEquivDescent
import WeilConjectures.RingTheory.TensorTailColimitElementwise

/-! # Descending a module comparison along compatible coefficient maps

Source: Stacks Project, Algebra, Tag 05N7 (2), (3), used in Tag 02JO (3).
(blueprint: lem-pc-compatible-module-model-descent)
-/

@[expose] public section

universe v w x
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem cancel_comparison
    {R S Q B L M : Type*} [CommRing R] [CommRing S] [CommRing Q] [CommRing B]
    [AddCommMonoid L] [AddCommMonoid M] [Module Q L] [Module B M]
    [Algebra Q R] [Algebra B R] [Algebra Q S] [Algebra B S]
    (t : R →+* S)
    (hQ : t.comp (algebraMap Q R) = algebraMap Q S)
    (hB : t.comp (algebraMap B R) = algebraMap B S)
    (e : letI : Algebra R S := t.toAlgebra
      Nonempty (S ⊗[R] (R ⊗[Q] L) ≃ₗ[S] S ⊗[R] (R ⊗[B] M))) :
    Nonempty (S ⊗[Q] L ≃ₗ[S] S ⊗[B] M) := by
  let : Algebra R S := t.toAlgebra
  let : IsScalarTower Q R S := IsScalarTower.of_algebraMap_eq' hQ.symm
  let : IsScalarTower B R S := IsScalarTower.of_algebraMap_eq' hB.symm
  obtain ⟨e⟩ := e
  exact ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange Q R S S L).symm.trans
    (e.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange B R S S M))⟩

set_option linter.unusedVariables false in
/-- An equivalence between two finitely presented module base changes descends
along a compatible family of coefficient maps. No algebra model or flatness
hypothesis is needed.

Source: Stacks Project, Algebra, Tag 05N7 (2), (3); Tag 02JO (3), final paragraph.
(blueprint: lem-pc-compatible-module-model-descent)

Proof:
1. On the cofinal tail above k, the algebras B_j = F(j) tensor B have colimit
   c.pt tensor B. The compatibility assumptions make them Q-algebras and make
   their coprojections Q-linear. This colimit assertion follows by tensor
   representatives and eventual equality. If the index is only a preorder,
   take its poset reflection: mutually comparable indices give inverse ring
   maps, so both the diagram and its colimit descend up to canonical isomorphism.
2. At k the modules B_k tensor_Q L and B_k tensor_B M are finitely presented
   over B_k, by finite presentation under base change. Their base changes to
   the colimit are the two modules in eM, by tensor cancellation.
3. Apply Tag 05N7 (2) to eM and its inverse, take a common later stage, and apply
   part (3) to their two composites and the identity maps. At a common upper
   bound the descended maps are inverse, hence define a linear equivalence.
4. Base change this equivalence to every later stage. Compatibility of q
   and tensor cancellation identify those modules with the displayed ones.
   Transport from the poset reflection to original indices if necessary.
   Empty presentations and zero modules need no separate argument, and no
   flatness is used to descend maps, equalities, or inverse identities.
-/
theorem exists_eventually_compatible_module_equiv
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {B M : Type w} [CommRing B] [AddCommMonoid M]
    [Algebra (F.obj i : Type v) B] [Module B M] [Module.FinitePresentation B M]
    (Q L : Type x) [CommRing Q] [AddCommMonoid L] [Module Q L]
    [Module.FinitePresentation Q L]
    (qC : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      Q →+* (c.pt : Type v) ⊗[F.obj i] B)
    (eM : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI : Algebra Q ((c.pt : Type v) ⊗[F.obj i] B) := qC.toAlgebra
      letI : Algebra B ((c.pt : Type v) ⊗[F.obj i] B) :=
        Algebra.TensorProduct.rightAlgebra
      Nonempty (((c.pt : Type v) ⊗[F.obj i] B) ⊗[Q] L ≃ₗ[
        (c.pt : Type v) ⊗[F.obj i] B] ((c.pt : Type v) ⊗[F.obj i] B) ⊗[B] M))
    (k : I) (hik : i ≤ k)
    (q : ∀ (j : I) (hkj : k ≤ j),
      letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      Q →+* (F.obj j : Type v) ⊗[F.obj i] B)
    (hqC : ∀ (j : I) (hkj : k ≤ j),
      letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      let t : F.obj j →ₐ[F.obj i] c.pt :=
        { (c.ι.app j).hom with
          commutes' := fun s ↦ ConcreteCategory.congr_hom
            (c.w (homOfLE (hik.trans hkj))) s }
      (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
        (q j hkj) = qC)
    (hq : ∀ (j l : I) (hkj : k ≤ j) (hkl : k ≤ l) (hjl : j ≤ l),
      letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      letI := (F.map (homOfLE (hik.trans hkl))).hom.toAlgebra
      let t : F.obj j →ₐ[F.obj i] F.obj l :=
        { (F.map (homOfLE hjl)).hom with
          commutes' := fun s ↦ (ConcreteCategory.congr_hom
            (F.map_comp (homOfLE (hik.trans hkj)) (homOfLE hjl)) s).symm }
      (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
        (q j hkj) = q l hkl) :
    ∃ (j₀ : I) (hkj₀ : k ≤ j₀), ∀ (j : I) (h₀ : k ≤ j₀) (h₁ : j₀ ≤ j),
      letI := (F.map (homOfLE (hik.trans (h₀.trans h₁)))).hom.toAlgebra
      let E := (F.obj j : Type v) ⊗[F.obj i] B
      letI : Algebra Q E := (q j (h₀.trans h₁)).toAlgebra
      letI : Algebra B E := Algebra.TensorProduct.rightAlgebra
      Nonempty (E ⊗[Q] L ≃ₗ[E] E ⊗[B] M) := by
  classical
  let : AddCommGroup L := Module.addCommMonoidToAddCommGroup Q
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup B
  let J := {j : I // k ≤ j}
  let : IsDirectedOrder J := ⟨fun j l ↦ by
    obtain ⟨m, hjm, hlm⟩ := exists_ge_ge j.val l.val
    exact ⟨⟨m, j.property.trans hjm⟩, hjm, hlm⟩⟩
  let : ∀ j : J, Algebra (F.obj i : Type v) (F.obj j.val : Type v) :=
    fun j ↦ (F.map (homOfLE (hik.trans j.property))).hom.toAlgebra
  let : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
  let E (j : J) := (F.obj j.val : Type v) ⊗[F.obj i] B
  let Y := (c.pt : Type v) ⊗[F.obj i] B
  let f (j l : J) (h : j ≤ l) : E j →+* E l :=
    (Algebra.TensorProduct.map
      ({ (F.map (homOfLE h)).hom with
        commutes' := fun s ↦ (ConcreteCategory.congr_hom
          (F.map_comp (homOfLE (hik.trans j.property)) (homOfLE h)) s).symm } :
          F.obj j.val →ₐ[F.obj i] F.obj l.val)
      (AlgHom.id (F.obj i) B)).toRingHom
  let g (j : J) : E j →+* Y :=
    (Algebra.TensorProduct.map
      ({ (c.ι.app j.val).hom with
        commutes' := fun s ↦ ConcreteCategory.congr_hom
          (c.w (homOfLE (hik.trans j.property))) s } :
          F.obj j.val →ₐ[F.obj i] c.pt)
      (AlgHom.id (F.obj i) B)).toRingHom
  have hself : ∀ j, f j j le_rfl = RingHom.id (E j) := by
    intro j
    apply RingHom.ext
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a b
      change F.map (homOfLE (le_refl j.val)) a ⊗ₜ[F.obj i] b = a ⊗ₜ[F.obj i] b
      simp
    · intro z z' hz hz'
      simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  have hcomp : ∀ j l m (hjl : j ≤ l) (hlm : l ≤ m),
      (f l m hlm).comp (f j l hjl) = f j m (hjl.trans hlm) := by
    intro j l m hjl hlm
    apply RingHom.ext
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a b
      change F.map (homOfLE hlm) (F.map (homOfLE hjl) a) ⊗ₜ[F.obj i] b =
        F.map (homOfLE (hjl.trans hlm)) a ⊗ₜ[F.obj i] b
      exact congrArg (fun x ↦ x ⊗ₜ[F.obj i] b)
        (ConcreteCategory.congr_hom (F.map_comp (homOfLE hjl) (homOfLE hlm)) a).symm
    · intro z z' hz hz'
      simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  have hg : ∀ j l (hjl : j ≤ l), (g l).comp (f j l hjl) = g j := by
    intro j l hjl
    apply RingHom.ext
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a b
      simp only [f, g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
      exact congrArg (fun x : c.pt ↦ x ⊗ₜ[F.obj i] b)
        (ConcreteCategory.congr_hom (c.w (homOfLE hjl)) a)
    · intro z z' hz hz'
      simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  obtain ⟨hs, hz⟩ := TensorProduct.tensorTailColimitElementwise F c hc i B k hik
  have hsurj : ∀ y : Y, ∃ j a, g j a = y := by
    intro y
    obtain ⟨j, hkj, a, ha⟩ := hs y
    exact ⟨⟨j, hkj⟩, a, ha⟩
  have hzero : ∀ j a, g j a = 0 → ∃ (l : J) (hjl : j ≤ l), f j l hjl a = 0 := by
    intro j a ha
    obtain ⟨l, hjl, hl⟩ := hz j.val j.property a ha
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hl⟩
  let jbase : J := ⟨k, le_rfl⟩
  let : ∀ j : J, Algebra Q (E j) := fun j ↦ (q j.val j.property).toAlgebra
  let : ∀ j : J, Algebra B (E j) := fun _ ↦ Algebra.TensorProduct.rightAlgebra
  let : Algebra Q Y := qC.toAlgebra
  let : Algebra B Y := Algebra.TensorProduct.rightAlgebra
  let : Algebra (E jbase) Y := (g jbase).toAlgebra
  let : IsScalarTower Q (E jbase) Y :=
    IsScalarTower.of_algebraMap_eq' (hqC k le_rfl).symm
  have hgB (j : J) : (g j).comp (algebraMap B (E j)) = algebraMap B Y := by
    ext b
    let t : F.obj j.val →ₐ[F.obj i] c.pt :=
      { (c.ι.app j.val).hom with
        commutes' := fun s ↦ ConcreteCategory.congr_hom
          (c.w (homOfLE (hik.trans j.property))) s }
    change t.toLinearMap.rTensor B ((1 : F.obj j.val) ⊗ₜ[F.obj i] b) =
      (1 : c.pt) ⊗ₜ[F.obj i] b
    rw [LinearMap.rTensor_tmul]
    exact congrArg (fun x : c.pt ↦ x ⊗ₜ[F.obj i] b) t.map_one
  let : IsScalarTower B (E jbase) Y :=
    IsScalarTower.of_algebraMap_eq' (hgB jbase).symm
  obtain ⟨eM⟩ := eM
  let e : Y ⊗[E jbase] (E jbase ⊗[Q] L) ≃ₗ[Y]
      Y ⊗[E jbase] (E jbase ⊗[B] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange Q (E jbase) Y Y L).trans
      (eM.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange
        B (E jbase) Y Y M).symm)
  obtain ⟨j₀, hj₀, ej₀⟩ := exists_stage_equiv_of_elementwise_colimit
    E f hself hcomp Y g hg hsurj hzero jbase
    (E jbase ⊗[Q] L) (E jbase ⊗[B] M) ⟨e⟩
  have hfB (j l : J) (hjl : j ≤ l) :
      (f j l hjl).comp (algebraMap B (E j)) = algebraMap B (E l) := by
    ext b
    change F.map (homOfLE hjl) 1 ⊗ₜ[F.obj i] b = 1 ⊗ₜ[F.obj i] b
    rw [map_one]
  have ej : Nonempty (E j₀ ⊗[Q] L ≃ₗ[E j₀] E j₀ ⊗[B] M) :=
    cancel_comparison (f jbase j₀ hj₀)
      (hq k j₀.val le_rfl j₀.property hj₀) (hfB jbase j₀ hj₀) ej₀
  refine ⟨j₀.val, j₀.property, ?_⟩
  intro j h₀ h₁
  let j' : J := ⟨j, h₀.trans h₁⟩
  let : Algebra Q (E j') := (q j j'.property).toAlgebra
  let : Algebra B (E j') := Algebra.TensorProduct.rightAlgebra
  change Nonempty (E j' ⊗[Q] L ≃ₗ[E j'] E j' ⊗[B] M)
  obtain ⟨ej⟩ := ej
  let : Algebra (E j₀) (E j') := (f j₀ j' h₁).toAlgebra
  exact cancel_comparison (f j₀ j' h₁)
    (hq j₀.val j j₀.property j'.property h₁) (hfB j₀ j' h₁) ⟨ej.baseChange (E j₀) (E j') _ _⟩

end AlgebraicGeometry
