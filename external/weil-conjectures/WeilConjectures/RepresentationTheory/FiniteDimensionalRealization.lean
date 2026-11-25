/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Basic

/-!
# Small models of finite-dimensional realizations

Suppose a category `A` is realized by finite-dimensional representations of a group `G` on
vector spaces living in a large universe `Type (u + 1)`, via a fully faithful and essentially
surjective (onto representations that are continuous along a homomorphism `ι : H →* G`)
realization. Then `A` is equivalent to the full subcategory of `Rep.{u} k G` on the
finite-dimensional representations that are continuous along `ι`.

The point is the universe bookkeeping: each vector space `V X : Type (u + 1)` is replaced by the
small coordinate model `ULift.{u} (Fin (finrank k (V X)) → k)`, and conversely every small
representation is lifted to `Type (u + 1)` with `ULift.{u + 1}`.

## Main definitions and statements

* `Representation.IsContinuousOn ι ρ`: all matrix coefficients `h ↦ φ (ρ (ι h) v)` are
  continuous on `H`.
* `Representation.IsContinuousOn.of_linearEquiv`: this is invariant under intertwining linear
  equivalences (across universes).
* `Representation.transport`: transport of a representation along a linear equivalence.
* `Representation.exists_equivalence_of_realization`: the small model equivalence.
-/

@[expose] public section

universe u

open CategoryTheory Module

namespace Representation

section IsContinuousOn

variable {k G H : Type*} [CommRing k] [TopologicalSpace k] [Monoid G] [Monoid H]
  [TopologicalSpace H]

/-- A representation `ρ` of `G` is continuous along `ι : H →* G` if all its matrix coefficients
`h ↦ φ (ρ (ι h) v)`, for `φ` a linear form and `v` a vector, are continuous functions on `H`. -/
def IsContinuousOn {V : Type*} [AddCommGroup V] [Module k V] (ι : H →* G)
    (ρ : Representation k G V) : Prop :=
  ∀ (φ : Module.Dual k V) (v : V), Continuous fun h : H ↦ φ (ρ (ι h) v)

/-- Continuity along `ι` is transported along intertwining linear equivalences, between vector
spaces in possibly different universes. -/
theorem IsContinuousOn.of_linearEquiv {V V' : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] {ι : H →* G} {ρ : Representation k G V}
    {ρ' : Representation k G V'} (e : V ≃ₗ[k] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (h : ρ.IsContinuousOn ι) : ρ'.IsContinuousOn ι := by
  intro φ v
  have : (fun x : H ↦ φ (ρ' (ι x) v)) =
      fun x : H ↦ (φ ∘ₗ e.toLinearMap) (ρ (ι x) (e.symm v)) := by
    funext x
    simp [he]
  rw [this]
  exact h _ _

/-- Continuity along `ι` is invariant under intertwining linear equivalences, between vector
spaces in possibly different universes. -/
theorem isContinuousOn_iff_of_linearEquiv {V V' : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] {ι : H →* G} {ρ : Representation k G V}
    {ρ' : Representation k G V'} (e : V ≃ₗ[k] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    ρ.IsContinuousOn ι ↔ ρ'.IsContinuousOn ι :=
  ⟨IsContinuousOn.of_linearEquiv e he, IsContinuousOn.of_linearEquiv e.symm fun g v ↦ by
    apply e.injective
    simp [he]⟩


end IsContinuousOn

section transport

variable {k G V W : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The transport of a representation `ρ` on `V` along a linear equivalence `e : V ≃ₗ[k] W`:
`g` acts on `W` by `e ∘ ρ g ∘ e⁻¹`. -/
def transport (ρ : Representation k G V) (e : V ≃ₗ[k] W) : Representation k G W where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := LinearMap.ext fun w ↦ by simp
  map_mul' g g' := LinearMap.ext fun w ↦ by simp

/-- The transported representation on elements. -/
@[simp]
lemma transport_apply (ρ : Representation k G V) (e : V ≃ₗ[k] W) (g : G) (w : W) :
    ρ.transport e g w = e (ρ g (e.symm w)) := rfl

/-- The linear equivalence `e` intertwines `ρ` with its transport along `e`. -/
lemma apply_transport (ρ : Representation k G V) (e : V ≃ₗ[k] W) (g : G) (v : V) :
    e (ρ g v) = ρ.transport e g (e v) := by
  simp

end transport

namespace Realization

variable (k : Type) [Field k] {A : Type*} (V : A → Type (u + 1)) [∀ X, AddCommGroup (V X)]
  [∀ X, Module k (V X)] [∀ X, FiniteDimensional k (V X)]

/-- The small coordinate model `ULift.{u} (Fin n → k)` of `V X`, where `n` is its dimension. -/
abbrev Model (X : A) : Type u := ULift.{u} (Fin (finrank k (V X)) → k)

/-- A chosen linear equivalence of `V X` with its small coordinate model. -/
noncomputable def basisEquiv (X : A) : V X ≃ₗ[k] Model k V X :=
  (Module.finBasis k (V X)).equivFun ≪≫ₗ ULift.moduleEquiv.symm

end Realization

open Realization in
/-- **Natural small model of a realization.** Let `A` be a category, realized by
finite-dimensional representations `ρ X` of `G` on vector spaces `V X : Type (u + 1)`, continuous
along `ι : H →* G`. Suppose the realization is faithful, full (on intertwining maps) and
essentially surjective onto finite-dimensional representations in `Type (u + 1)` that are
continuous along `ι`. Then `A` is equivalent to the full subcategory `Q` of `Rep.{u} k G` on
finite-dimensional representations continuous along `ι`, and the equivalence comes with
identifications `f X` of the underlying spaces with `V X` which intertwine the representations
and are natural in `X`. -/
theorem exists_equivalence_of_realization_natural
    {k : Type} [Field k] [TopologicalSpace k] {G : Type u} [Group G] {H : Type*} [Group H]
    [TopologicalSpace H] (ι : H →* G) {A : Type*} [Category A]
    (V : A → Type (u + 1)) [∀ X, AddCommGroup (V X)] [∀ X, Module k (V X)]
    [∀ X, FiniteDimensional k (V X)]
    (ρ : ∀ X, Representation k G (V X)) (hρ : ∀ X, (ρ X).IsContinuousOn ι)
    (map : ∀ {X Y : A}, (X ⟶ Y) → (V X →ₗ[k] V Y))
    (map_id : ∀ X, map (𝟙 X) = LinearMap.id)
    (map_comp : ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map g ∘ₗ map f)
    (map_comm : ∀ {X Y : A} (f : X ⟶ Y) (g : G) (v : V X), map f (ρ X g v) = ρ Y g (map f v))
    (faithful : ∀ {X Y : A} (f f' : X ⟶ Y), map f = map f' → f = f')
    (full : ∀ {X Y : A} (φ : V X →ₗ[k] V Y), (∀ g v, φ (ρ X g v) = ρ Y g (φ v)) →
      ∃ f : X ⟶ Y, map f = φ)
    (essSurj : ∀ (V' : Type (u + 1)) [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      (ρ' : Representation k G V'), ρ'.IsContinuousOn ι →
        ∃ (X : A) (e : V X ≃ₗ[k] V'), ∀ g v, e (ρ X g v) = ρ' g (e v))
    (Q : ObjectProperty (Rep.{u} k G))
    (hQ : ∀ X : Rep.{u} k G, Q X ↔ FiniteDimensional k X.V ∧ X.ρ.IsContinuousOn ι) :
    ∃ (e : A ≌ Q.FullSubcategory) (f : ∀ X : A, (e.functor.obj X).obj.V ≃ₗ[k] V X),
      (∀ X g v, f X ((e.functor.obj X).obj.ρ g v) = ρ X g (f X v)) ∧
      ∀ {X Y : A} (φ : X ⟶ Y) v, f Y ((e.functor.map φ).hom.hom v) = map φ (f X v) := by
  let b := basisEquiv k V
  let F : A ⥤ Q.FullSubcategory :=
    { obj X := ⟨Rep.of ((ρ X).transport (b X)),
        (hQ _).2 ⟨LinearEquiv.finiteDimensional (b X),
          (hρ X).of_linearEquiv (b X) fun g v ↦ apply_transport _ _ _ _⟩⟩
      map {X Y} f := ObjectProperty.homMk <| Rep.ofHom
        ⟨(b Y).toLinearMap ∘ₗ map f ∘ₗ (b X).symm.toLinearMap, fun g ↦
          LinearMap.ext fun w ↦ by simp [map_comm]⟩
      map_id X := ObjectProperty.hom_ext _ <| Rep.hom_ext <|
        IntertwiningMap.ext <| LinearMap.ext fun w ↦ by simp [map_id]
      map_comp f g := ObjectProperty.hom_ext _ <| Rep.hom_ext <|
        IntertwiningMap.ext <| LinearMap.ext fun w ↦ by simp [map_comp] }
  have hF : F.IsEquivalence :=
    { faithful := ⟨fun {X Y} f f' hff' ↦ faithful f f' <| LinearMap.ext fun v ↦ by
        have := congr($(hff').hom.hom (b X v))
        simpa [F] using this⟩
      full := ⟨fun {X Y} φ ↦ by
        obtain ⟨f, hf⟩ := full ((b Y).symm.toLinearMap ∘ₗ φ.hom.hom.toLinearMap ∘ₗ
          (b X).toLinearMap) fun g v ↦ by
            have := Rep.hom_comm_apply φ.hom g (b X v)
            change φ.hom.hom ((ρ X).transport (b X) g (b X v)) =
              (ρ Y).transport (b Y) g (φ.hom.hom (b X v)) at this
            simp only [transport_apply, LinearEquiv.symm_apply_apply] at this
            exact (congrArg (b Y).symm this).trans ((b Y).symm_apply_apply _)
        refine ⟨f, ObjectProperty.hom_ext _ <| Rep.hom_ext <|
          IntertwiningMap.ext <| LinearMap.ext fun w ↦ ?_⟩
        simp [F, hf]⟩
      essSurj := ⟨fun Y ↦ by
        have := ((hQ _).1 Y.property).1
        let ρ' : Representation k G (ULift.{u + 1} Y.obj.V) :=
          Y.obj.ρ.transport ULift.moduleEquiv.symm
        have : FiniteDimensional k (ULift.{u + 1} Y.obj.V) :=
          LinearEquiv.finiteDimensional ULift.moduleEquiv.symm
        obtain ⟨X, e, he⟩ := essSurj (ULift.{u + 1} Y.obj.V) ρ'
          (((hQ _).1 Y.property).2.of_linearEquiv _ fun g v ↦ apply_transport _ _ _ _)
        let e' : ((ρ X).transport (b X)).Equiv Y.obj.ρ :=
          .mk ((b X).symm ≪≫ₗ e ≪≫ₗ ULift.moduleEquiv) fun g ↦ LinearMap.ext fun w ↦ by
            have := he g ((b X).symm w)
            simp only [ρ', transport_apply] at this
            simp [this]
        exact ⟨X, ⟨ObjectProperty.isoMk _ (Rep.mkIso e')⟩⟩⟩ }
  refine ⟨F.asEquivalence, fun X ↦ (b X).symm, fun X g v ↦ (b X).symm_apply_apply _,
    fun {X Y} φ v ↦ ?_⟩
  exact (b Y).symm_apply_apply _

/-- **Small model of a realization.** Let `A` be a category, realized by finite-dimensional
representations `ρ X` of `G` on vector spaces `V X : Type (u + 1)`, continuous along
`ι : H →* G`. Suppose the realization is faithful, full (on intertwining maps) and essentially
surjective onto finite-dimensional representations in `Type (u + 1)` that are continuous along
`ι`. Then `A` is equivalent to the full subcategory `Q` of `Rep.{u} k G` on finite-dimensional
representations continuous along `ι`, and the equivalence is compatible with the realization up
to intertwining linear equivalences (forgetting the naturality in
`Representation.exists_equivalence_of_realization_natural`). -/
theorem exists_equivalence_of_realization
    {k : Type} [Field k] [TopologicalSpace k] {G : Type u} [Group G] {H : Type*} [Group H]
    [TopologicalSpace H] (ι : H →* G) {A : Type*} [Category A]
    (V : A → Type (u + 1)) [∀ X, AddCommGroup (V X)] [∀ X, Module k (V X)]
    [∀ X, FiniteDimensional k (V X)]
    (ρ : ∀ X, Representation k G (V X)) (hρ : ∀ X, (ρ X).IsContinuousOn ι)
    (map : ∀ {X Y : A}, (X ⟶ Y) → (V X →ₗ[k] V Y))
    (map_id : ∀ X, map (𝟙 X) = LinearMap.id)
    (map_comp : ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map g ∘ₗ map f)
    (map_comm : ∀ {X Y : A} (f : X ⟶ Y) (g : G) (v : V X), map f (ρ X g v) = ρ Y g (map f v))
    (faithful : ∀ {X Y : A} (f f' : X ⟶ Y), map f = map f' → f = f')
    (full : ∀ {X Y : A} (φ : V X →ₗ[k] V Y), (∀ g v, φ (ρ X g v) = ρ Y g (φ v)) →
      ∃ f : X ⟶ Y, map f = φ)
    (essSurj : ∀ (V' : Type (u + 1)) [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
      (ρ' : Representation k G V'), ρ'.IsContinuousOn ι →
        ∃ (X : A) (e : V X ≃ₗ[k] V'), ∀ g v, e (ρ X g v) = ρ' g (e v))
    (Q : ObjectProperty (Rep.{u} k G))
    (hQ : ∀ X : Rep.{u} k G, Q X ↔ FiniteDimensional k X.V ∧ X.ρ.IsContinuousOn ι) :
    ∃ e : A ≌ Q.FullSubcategory, ∀ X : A, ∃ f : (e.functor.obj X).obj.V ≃ₗ[k] V X,
      ∀ g v, f ((e.functor.obj X).obj.ρ g v) = ρ X g (f v) := by
  obtain ⟨e, f, hf, -⟩ := exists_equivalence_of_realization_natural ι V ρ hρ map map_id map_comp
    map_comm faithful full essSurj Q hQ
  exact ⟨e, fun X ↦ ⟨f X, hf X⟩⟩

end Representation
