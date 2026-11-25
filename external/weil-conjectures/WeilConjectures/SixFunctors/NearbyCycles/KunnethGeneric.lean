/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!

# The Künneth map of nearby cycles on the geometric generic fibre

A nearby-cycles model `M` of `X` carries an identification `ε : 𝒳_η̄ ⟶ X`, and its nearby cycles
`Ψ_M = Li^* Rj_* Lε^*` are the nearby cycles of the model `M.toGeneric` of the geometric generic
fibre `𝒳_η̄` itself (the same total space, with `ε = 𝟙`,
`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.toGeneric`), precomposed with `Lε^*`.
This file shows that the Künneth map `Π_{A,B}` of three models is, up to isomorphisms of arrows,
the Künneth map `Π_{Lε_M^* A, Lε_N^* B}` of the models of the geometric generic fibres
(`NearbyCyclesModel.kunnethMapArrowIsoToGeneric`); in particular one is an isomorphism if and
only if the other is (`NearbyCyclesModel.isIso_kunnethMap_iff_toGeneric`).

The point is that a morphism of models of the geometric generic fibres exists in more situations:
the morphism from a model of finite type over the trait to the trait itself exists on the
geometric generic fibres, while there need not be a morphism `X ⟶ Spec Ω` from the scheme `X`
that `ε` identifies the geometric generic fibre with.

## Implementation notes

All exchange maps and lax tensor maps factor through the *reduced* versions `ᾱ` and `μ̄`, which
do not involve `ε`; the comparison is proved for abstract functors
(`NearbyCyclesModel.kunnethMap_eq_aux`, `NearbyCyclesModel.isIso_reducedKunneth_iff_aux`) and
then instantiated.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### Abstract computations -/

section Abstract

variable {CM CN CP GM GN GP SM SN SP : Type*} [Category CM] [Category CN] [Category CP]
  [Category GM] [Category GN] [Category GP] [Category SM] [Category SN] [Category SP]
  [MonoidalCategory CP] [MonoidalCategory GP] [MonoidalCategory SP]
  {EM : CM ⥤ GM} {EN : CN ⥤ GN} {EP : CP ⥤ GP} {ΨM : GM ⥤ SM} {ΨN : GN ⥤ SN} {ΨP : GP ⥤ SP}
  {f₁ : CM ⥤ CP} {f₂ : CN ⥤ CP} {g₁ : GM ⥤ GP} {g₂ : GN ⥤ GP} {s₁ : SM ⥤ SP} {s₂ : SN ⥤ SP}

/-- The Künneth map, written with the reduced exchanges `ᾱ` and the reduced lax tensor map `μ̄`,
is the reduced Künneth map `(ᾱ₁ ⊗ ᾱ₂) ≫ μ̄` at `(Lε_M^* A, Lε_N^* B)` followed by `Ψ_P` of the
identifications of the pullbacks. -/
lemma kunnethMap_eq_aux (α₁ : ΨM ⋙ s₁ ⟶ g₁ ⋙ ΨP) (α₂ : ΨN ⋙ s₂ ⟶ g₂ ⋙ ΨP)
    (c₁ : EM ⋙ g₁ ⟶ f₁ ⋙ EP) (c₂ : EN ⋙ g₂ ⟶ f₂ ⋙ EP)
    (μ : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : GP} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨP.map x ⊗ₘ ΨP.map y) ≫ μ U' V' = μ U V ≫ ΨP.map (x ⊗ₘ y))
    (μE : ∀ A B, EP.obj A ⊗ EP.obj B ⟶ EP.obj (A ⊗ B)) (A : CM) (B : CN) :
    ((α₁.app (EM.obj A) ≫ ΨP.map (c₁.app A)) ⊗ₘ (α₂.app (EN.obj B) ≫ ΨP.map (c₂.app B))) ≫
        μ (EP.obj (f₁.obj A)) (EP.obj (f₂.obj B)) ≫ ΨP.map (μE _ _) =
      ((α₁.app (EM.obj A) ⊗ₘ α₂.app (EN.obj B)) ≫ μ _ _) ≫
        ΨP.map ((c₁.app A ⊗ₘ c₂.app B) ≫ μE _ _) := by
  have h := hμ (c₁.app A) (c₂.app B)
  dsimp only [Functor.comp_obj] at h ⊢
  rw [← tensorHom_comp_tensorHom, Category.assoc, reassoc_of% h, Category.assoc, ← ΨP.map_comp]

/-- The reduced Künneth map `(ᾱ₁ ⊗ ᾱ₂) ≫ μ̄` is natural in its two arguments. -/
lemma reducedKunneth_natural_aux (α₁ : ΨM ⋙ s₁ ⟶ g₁ ⋙ ΨP) (α₂ : ΨN ⋙ s₂ ⟶ g₂ ⋙ ΨP)
    (μ : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : GP} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨP.map x ⊗ₘ ΨP.map y) ≫ μ U' V' = μ U V ≫ ΨP.map (x ⊗ₘ y))
    {U U' : GM} {V V' : GN} (x : U ⟶ U') (y : V ⟶ V') :
    (s₁.map (ΨM.map x) ⊗ₘ s₂.map (ΨN.map y)) ≫ (α₁.app U' ⊗ₘ α₂.app V') ≫ μ _ _ =
      ((α₁.app U ⊗ₘ α₂.app V) ≫ μ _ _) ≫ ΨP.map (g₁.map x ⊗ₘ g₂.map y) := by
  have n₁ := α₁.naturality x
  have n₂ := α₂.naturality y
  simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
  rw [tensorHom_comp_tensorHom_assoc, n₁, n₂, ← tensorHom_comp_tensorHom_assoc, hμ,
    Category.assoc]

/-- The reduced Künneth map at `(U, V)` is an isomorphism if and only if it is one at isomorphic
arguments `(U', V')`. -/
lemma isIso_reducedKunneth_iff_aux (α₁ : ΨM ⋙ s₁ ⟶ g₁ ⋙ ΨP) (α₂ : ΨN ⋙ s₂ ⟶ g₂ ⋙ ΨP)
    (μ : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : GP} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨP.map x ⊗ₘ ΨP.map y) ≫ μ U' V' = μ U V ≫ ΨP.map (x ⊗ₘ y))
    {U U' : GM} {V V' : GN} (x : U ≅ U') (y : V ≅ V') {T : Type*} [Category T] (F : SP ⥤ T) :
    IsIso (F.map ((α₁.app U ⊗ₘ α₂.app V) ≫ μ _ _)) ↔
      IsIso (F.map ((α₁.app U' ⊗ₘ α₂.app V') ≫ μ _ _)) := by
  have h : F.map (s₁.map (ΨM.map x.hom) ⊗ₘ s₂.map (ΨN.map y.hom)) ≫
      F.map ((α₁.app U' ⊗ₘ α₂.app V') ≫ μ _ _) =
      F.map ((α₁.app U ⊗ₘ α₂.app V) ≫ μ _ _) ≫ F.map (ΨP.map (g₁.map x.hom ⊗ₘ g₂.map y.hom)) := by
    rw [← F.map_comp, ← F.map_comp, reducedKunneth_natural_aux α₁ α₂ μ hμ x.hom y.hom]
  constructor
  · intro _
    have : IsIso (F.map (s₁.map (ΨM.map x.hom) ⊗ₘ s₂.map (ΨN.map y.hom)) ≫
        F.map ((α₁.app U' ⊗ₘ α₂.app V') ≫ μ _ _)) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left (F.map (s₁.map (ΨM.map x.hom) ⊗ₘ s₂.map (ΨN.map y.hom))) _
  · intro _
    have : IsIso (F.map ((α₁.app U ⊗ₘ α₂.app V) ≫ μ _ _) ≫
        F.map (ΨP.map (g₁.map x.hom ⊗ₘ g₂.map y.hom))) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map (ΨP.map (g₁.map x.hom ⊗ₘ g₂.map y.hom)))

/-- **The Künneth map and the models of the geometric generic fibres, abstractly.** The Künneth
map `(α₁ ⊗ α₂) ≫ μ_Ψ` of models with nearby cycles `Ψ = E ⋙ R ⋙ I` and pullback exchanges
`α = c ≫ I(m ≫ R(d))` is, after any functor `F`, an isomorphism at `(A, B)` if and only if the
Künneth map of the models with `E = E°` (and the comparisons `d°`) is one at `(EM A, EN B)`,
provided `E° ≅ 𝟭` and the comparisons `d`, `d°` and the lax structures of `EP`, `EP°` are
invertible. -/
lemma isIso_map_kunneth_iff_aux {TM TN TP : Type*} [Category TM] [Category TN] [Category TP]
    [MonoidalCategory TP] {RM : GM ⥤ TM} {RN : GN ⥤ TN} {RP : GP ⥤ TP} {IM : TM ⥤ SM}
    {IN : TN ⥤ SN} {IP : TP ⥤ SP} [IP.LaxMonoidal] {t₁ : TM ⥤ TP} {t₂ : TN ⥤ TP}
    {EM' : GM ⥤ GM} {EN' : GN ⥤ GN} {EP' : GP ⥤ GP}
    (c₁ : IM ⋙ s₁ ⟶ t₁ ⋙ IP) (c₂ : IN ⋙ s₂ ⟶ t₂ ⋙ IP) (m₁ : RM ⋙ t₁ ⟶ g₁ ⋙ RP)
    (m₂ : RN ⋙ t₂ ⟶ g₂ ⋙ RP) (d₁ : EM ⋙ g₁ ⟶ f₁ ⋙ EP) (d₂ : EN ⋙ g₂ ⟶ f₂ ⋙ EP)
    (d₁' : EM' ⋙ g₁ ⟶ g₁ ⋙ EP') (d₂' : EN' ⋙ g₂ ⟶ g₂ ⋙ EP') [IsIso d₁] [IsIso d₂] [IsIso d₁']
    [IsIso d₂'] (μR : ∀ U V, RP.obj U ⊗ RP.obj V ⟶ RP.obj (U ⊗ V))
    (hμR : ∀ {U U' V V' : GP} (x : U ⟶ U') (y : V ⟶ V'),
      (RP.map x ⊗ₘ RP.map y) ≫ μR U' V' = μR U V ≫ RP.map (x ⊗ₘ y))
    (μE : ∀ A B, EP.obj A ⊗ EP.obj B ⟶ EP.obj (A ⊗ B)) [∀ A B, IsIso (μE A B)]
    (μE' : ∀ U V, EP'.obj U ⊗ EP'.obj V ⟶ EP'.obj (U ⊗ V)) [∀ U V, IsIso (μE' U V)]
    (eM : EM' ≅ 𝟭 GM) (eN : EN' ≅ 𝟭 GN)
    (α₁ : (EM ⋙ RM ⋙ IM) ⋙ s₁ ⟶ f₁ ⋙ EP ⋙ RP ⋙ IP)
    (hα₁ : α₁ = Functor.whiskerLeft (EM ⋙ RM) c₁ ≫
      Functor.whiskerRight (Functor.whiskerLeft EM m₁ ≫ Functor.whiskerRight d₁ RP) IP)
    (α₂ : (EN ⋙ RN ⋙ IN) ⋙ s₂ ⟶ f₂ ⋙ EP ⋙ RP ⋙ IP)
    (hα₂ : α₂ = Functor.whiskerLeft (EN ⋙ RN) c₂ ≫
      Functor.whiskerRight (Functor.whiskerLeft EN m₂ ≫ Functor.whiskerRight d₂ RP) IP)
    (α₁' : (EM' ⋙ RM ⋙ IM) ⋙ s₁ ⟶ g₁ ⋙ EP' ⋙ RP ⋙ IP)
    (hα₁' : α₁' = Functor.whiskerLeft (EM' ⋙ RM) c₁ ≫
      Functor.whiskerRight (Functor.whiskerLeft EM' m₁ ≫ Functor.whiskerRight d₁' RP) IP)
    (α₂' : (EN' ⋙ RN ⋙ IN) ⋙ s₂ ⟶ g₂ ⋙ EP' ⋙ RP ⋙ IP)
    (hα₂' : α₂' = Functor.whiskerLeft (EN' ⋙ RN) c₂ ≫
      Functor.whiskerRight (Functor.whiskerLeft EN' m₂ ≫ Functor.whiskerRight d₂' RP) IP)
    (μP : ∀ A B, (EP ⋙ RP ⋙ IP).obj A ⊗ (EP ⋙ RP ⋙ IP).obj B ⟶ (EP ⋙ RP ⋙ IP).obj (A ⊗ B))
    (hμP : μP = fun A B ↦ Functor.LaxMonoidal.μ IP _ _ ≫ IP.map (μR _ _ ≫ RP.map (μE A B)))
    (μP' : ∀ U V, (EP' ⋙ RP ⋙ IP).obj U ⊗ (EP' ⋙ RP ⋙ IP).obj V ⟶
      (EP' ⋙ RP ⋙ IP).obj (U ⊗ V))
    (hμP' : μP' = fun U V ↦ Functor.LaxMonoidal.μ IP _ _ ≫ IP.map (μR _ _ ≫ RP.map (μE' U V)))
    {T : Type*} [Category T] (F : SP ⥤ T) (A : CM) (B : CN) :
    IsIso (F.map ((α₁.app A ⊗ₘ α₂.app B) ≫ μP _ _)) ↔
      IsIso (F.map ((α₁'.app (EM.obj A) ⊗ₘ α₂'.app (EN.obj B)) ≫ μP' _ _)) := by
  subst hα₁ hα₂ hα₁' hα₂' hμP hμP'
  let α₁ : (RM ⋙ IM) ⋙ s₁ ⟶ g₁ ⋙ RP ⋙ IP :=
    Functor.whiskerLeft RM c₁ ≫ Functor.whiskerRight m₁ IP
  let α₂ : (RN ⋙ IN) ⋙ s₂ ⟶ g₂ ⋙ RP ⋙ IP :=
    Functor.whiskerLeft RN c₂ ≫ Functor.whiskerRight m₂ IP
  let μ : ∀ U V, (RP ⋙ IP).obj U ⊗ (RP ⋙ IP).obj V ⟶ (RP ⋙ IP).obj (U ⊗ V) :=
    fun U V ↦ Functor.LaxMonoidal.μ IP _ _ ≫ IP.map (μR U V)
  have hμ : ∀ {U U' V V' : GP} (x : U ⟶ U') (y : V ⟶ V'),
      ((RP ⋙ IP).map x ⊗ₘ (RP ⋙ IP).map y) ≫ μ U' V' = μ U V ≫ (RP ⋙ IP).map (x ⊗ₘ y) := by
    intro U U' V V' x y
    simp only [μ, Functor.comp_map, Functor.LaxMonoidal.μ_natural_assoc, ← IP.map_comp, hμR,
      Category.assoc]
  have e₁ : ∀ A,
      (Functor.whiskerLeft (EM ⋙ RM) c₁ ≫ Functor.whiskerRight
        (Functor.whiskerLeft EM m₁ ≫ Functor.whiskerRight d₁ RP) IP).app A =
        α₁.app (EM.obj A) ≫ (RP ⋙ IP).map (d₁.app A) := by
    intros; simp [α₁]
  have e₂ : ∀ B,
      (Functor.whiskerLeft (EN ⋙ RN) c₂ ≫ Functor.whiskerRight
        (Functor.whiskerLeft EN m₂ ≫ Functor.whiskerRight d₂ RP) IP).app B =
        α₂.app (EN.obj B) ≫ (RP ⋙ IP).map (d₂.app B) := by
    intros; simp [α₂]
  have e₁' : ∀ U,
      (Functor.whiskerLeft (EM' ⋙ RM) c₁ ≫ Functor.whiskerRight
        (Functor.whiskerLeft EM' m₁ ≫ Functor.whiskerRight d₁' RP) IP).app U =
        α₁.app (EM'.obj U) ≫ (RP ⋙ IP).map (d₁'.app U) := by
    intros; simp [α₁]
  have e₂' : ∀ V,
      (Functor.whiskerLeft (EN' ⋙ RN) c₂ ≫ Functor.whiskerRight
        (Functor.whiskerLeft EN' m₂ ≫ Functor.whiskerRight d₂' RP) IP).app V =
        α₂.app (EN'.obj V) ≫ (RP ⋙ IP).map (d₂'.app V) := by
    intros; simp [α₂]
  have r : ∀ {U V : GP} {W : GP} (h : U ⊗ V ⟶ W),
      Functor.LaxMonoidal.μ IP (RP.obj U) (RP.obj V) ≫ IP.map (μR U V ≫ RP.map h) =
        μ U V ≫ (RP ⋙ IP).map h := by
    intros; simp [μ]
  dsimp only
  rw [e₁, e₂, e₁', e₂']
  simp only [Functor.comp_obj]
  rw [r, r,
    kunnethMap_eq_aux α₁ α₂ d₁ d₂ μ hμ μE A B,
    kunnethMap_eq_aux α₁ α₂ d₁' d₂' μ hμ μE' (EM.obj A) (EN.obj B),
    F.map_comp _ ((RP ⋙ IP).map ((d₁.app A ⊗ₘ d₂.app B) ≫ μE _ _)),
    F.map_comp _ ((RP ⋙ IP).map ((d₁'.app _ ⊗ₘ d₂'.app _) ≫ μE' _ _)),
    isIso_comp_right_iff, isIso_comp_right_iff]
  exact isIso_reducedKunneth_iff_aux α₁ α₂ μ hμ (eM.app _).symm (eN.app _).symm F

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' : Scheme.{u}}

/-! ### The model of the geometric generic fibre -/

/-- The *model of the geometric generic fibre* of a model `M`: the same total space, geometric
generic fibre and inclusions, with the identification `ε = 𝟙`. Its nearby cycles are
`Li^* Rj_* L(𝟙)^*`, and `Ψ_M = Lε^* ⋙ Ψ_{M.toGeneric}` up to `L(𝟙)^* ≅ 𝟭`. -/
abbrev toGeneric (M : NearbyCyclesModel X X') : NearbyCyclesModel M.generic X' where
  total := M.total
  generic := M.generic
  j := M.j
  i := M.i
  ε := 𝟙 _

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}

/-- A morphism of models induces a morphism of the models of the geometric generic fibres, over
the morphism of geometric generic fibres. -/
abbrev Hom.toGeneric {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f') :
    M.toGeneric.Hom N.toGeneric φ.generic f' where
  total := φ.total
  generic := φ.generic
  comm_j := φ.comm_j
  comm_i := φ.comm_i
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

variable {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

-- the instantiation unfolds the pullback exchanges and nearby cycles of the four models
/-- **Reduction to the geometric generic fibres**: after any functor `F`, the Künneth map
`Π_{A,B}` of the models `M`, `N`, `P` is an isomorphism if and only if the Künneth map
`Π_{Lε_M^* A, Lε_N^* B}` of the models of their geometric generic fibres is. -/
lemma isIso_map_kunnethMap_iff_toGeneric (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) {T : Type*} [Category T]
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (condensedRingObj Λ Z')) ⥤ T) :
    IsIso (F.map (kunnethMap Λ φ₁ φ₂ A B)) ↔
      IsIso (F.map (kunnethMap Λ φ₁.toGeneric φ₂.toGeneric (L((M.ε)^*⟦Λ⟧).obj A)
        (L((N.ε)^*⟦Λ⟧).obj B))) := by
  have key := isIso_map_kunneth_iff_aux
    (pullbackSquareComparison Λ φ₁.commSq_i).hom (pullbackSquareComparison Λ φ₂.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedUpperStarLowerStarAdjunction Λ P.j)
      (pullbackSquareComparison Λ φ₁.commSq_j).hom)
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ P.j)
      (pullbackSquareComparison Λ φ₂.commSq_j).hom)
    (pullbackSquareComparison Λ φ₁.commSq_ε).hom (pullbackSquareComparison Λ φ₂.commSq_ε).hom
    (pullbackSquareComparison Λ φ₁.toGeneric.commSq_ε).hom
    (pullbackSquareComparison Λ φ₂.toGeneric.commSq_ε).hom
    (lowerStarTensorMap' Λ P.j) (fun x y ↦ lowerStarTensorMap'_natural Λ P.j x y)
    (Functor.LaxMonoidal.μ L((P.ε)^*⟦Λ⟧)) (Functor.LaxMonoidal.μ L((𝟙 P.generic)^*⟦Λ⟧))
    (leftDerivedUpperStarId Λ M.generic) (leftDerivedUpperStarId Λ N.generic)
    (φ₁.pullbackExchange Λ) rfl (φ₂.pullbackExchange Λ) rfl
    (φ₁.toGeneric.pullbackExchange Λ) rfl (φ₂.toGeneric.pullbackExchange Λ) rfl
    (P.tensorMap Λ) rfl (P.toGeneric.tensorMap Λ) rfl F A B
  exact key

/-- **Reduction to the geometric generic fibres**: the Künneth map `Π_{A,B}` of the models `M`,
`N`, `P` is an isomorphism if and only if the Künneth map `Π_{Lε_M^* A, Lε_N^* B}` of the models
of their geometric generic fibres is. -/
lemma isIso_kunnethMap_iff_toGeneric (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) ↔
      IsIso (kunnethMap Λ φ₁.toGeneric φ₂.toGeneric (L((M.ε)^*⟦Λ⟧).obj A)
        (L((N.ε)^*⟦Λ⟧).obj B)) :=
  by simpa only [Functor.id_map] using isIso_map_kunnethMap_iff_toGeneric Λ φ₁ φ₂ A B (𝟭 _)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
