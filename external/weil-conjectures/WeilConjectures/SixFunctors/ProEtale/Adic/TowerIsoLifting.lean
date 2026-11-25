/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Lifting local isomorphisms of towers over weakly contractible objects

Let `R` and `G` be towers `ℕᵒᵖ ⥤ Sheaf J A` of sheaves on a site. Suppose that `R₀` and `G₀`
are locally isomorphic, and that every local isomorphism `Rₙ ≅ Gₙ` lifts locally to an
isomorphism `Rₙ₊₁ ≅ Gₙ₊₁` compatible with the transition maps. Then over every weakly
contractible object `W` the towers are isomorphic: `R|_W ≅ G|_W`
(`CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isWeaklyContractible`).

This is the sheaf-theoretic step of the passage from a tower `(Gₙ)` of locally constant
`ℤ/ℓⁿ`-sheaves to the lattice `lim Gₙ`: local trivialisations `Gₙ ≅ (ℤ/ℓⁿ)ʳ` at each finite
level, which a priori are not compatible, become compatible over weakly contractible objects,
where every locally surjective map of sheaves of sets is surjective on sections. The proof
applies this to the sheaves of isomorphisms `Iso(Rₙ, Gₙ)` (`CategoryTheory.isoSheaf`) and to
the sheaves of compatible pairs of isomorphisms at consecutive levels
(`CategoryTheory.isoPairSheaf`), and chooses the lifts recursively.

## Main definitions

- `CategoryTheory.isoSheaf`: the sheaf of types `X ↦ (F|_X ≅ G|_X)`.
- `CategoryTheory.isoPairSheaf`: the sheaf of pairs of isomorphisms `(ψ, φ)`, with
  `ψ : F'|_X ≅ G'|_X` and `φ : F|_X ≅ G|_X` compatible with given maps `F' ⟶ F`, `G' ⟶ G`.

## Main results

- `CategoryTheory.isSheaf_isoPresheaf`: isomorphisms between sheaves glue.
- `CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isWeaklyContractible`: towers
  with locally liftable local isomorphisms are isomorphic over weakly contractible objects; and
  `CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_limit_of_isWeaklyContractible`
  for their limits.
- `CategoryTheory.GrothendieckTopology.exists_lift_iso_of_descent`: local lifting of
  isomorphisms follows from local triviality, descent of isomorphisms, and local lifting of
  automorphisms of one of the two towers.
- `CategoryTheory.Limits.exists_iso_comp_eq_of_isColimit_cokernelCofork`: descent of
  isomorphisms along cokernels (reduction modulo `ℓⁿ`).
- `CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isColimit_cokernelCofork`:
  the case of `ℓ`-adic towers, `Xₙ₊₁/ℓⁿ ≅ Xₙ`.
- `AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_overPullback_limit` and
  `ProEtale.exists_cover_nonempty_iso_overPullback_limit_of_isColimit_cokernelCofork`:
  on the pro-étale site, the limits of such towers are locally isomorphic.
-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf of types `X ↦ (F|_X ≅ G|_X)` of isomorphisms between the restrictions of two
sheaves to the slices `Over X`. -/
@[simps obj]
def isoPresheaf (F G : Sheaf J A) : Cᵒᵖ ⥤ Type _ where
  obj X := (J.overPullback A X.unop).obj F ≅ (J.overPullback A X.unop).obj G
  map f := ↾fun e ↦ (J.overMapPullback A f.unop).mapIso e
  map_id X := by
    ext e : 3
    refine Iso.ext ?_
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_id X) e.hom
  map_comp f g := by
    ext e : 3
    refine Iso.ext ?_
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_comp f g) e.hom

/-- The isomorphisms underlying sections of `isoPresheaf`, as a morphism to `sheafHom'`. -/
@[simps app]
def isoPresheafToSheafHom' (F G : Sheaf J A) : isoPresheaf F G ⟶ sheafHom' F G where
  app _ := ↾fun e ↦ e.hom

/-- The restriction of an isomorphism has the restricted underlying morphism. -/
lemma isoPresheaf_map_hom (F G : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : (isoPresheaf F G).obj X) :
    ((isoPresheaf F G).map f e).hom = (sheafHom' F G).map f e.hom := rfl

/-- The restriction of an isomorphism has the restricted inverse. -/
lemma isoPresheaf_map_inv (F G : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : (isoPresheaf F G).obj X) :
    ((isoPresheaf F G).map f e).inv = (sheafHom' G F).map f e.inv := rfl

/-- Restriction of morphisms between restricted sheaves commutes with composition. -/
lemma sheafHom'_map_comp (F G H : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : (sheafHom' F G).obj X) (b : (sheafHom' G H).obj X) :
    (sheafHom' F H).map f (a ≫ b) = (sheafHom' F G).map f a ≫ (sheafHom' G H).map f b :=
  (J.overMapPullback A f.unop).map_comp a b

/-- Restriction of morphisms between restricted sheaves preserves identities. -/
lemma sheafHom'_map_id (F : Sheaf J A) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (sheafHom' F F).map f (𝟙 _) = 𝟙 _ :=
  (J.overMapPullback A f.unop).map_id _

/-- The sheaf of types `sheafHom' F G` satisfies the sheaf condition for types. -/
lemma isSheaf_sheafHom' (F G : Sheaf J A) : Presieve.IsSheaf J (sheafHom' F G) :=
  (isSheaf_iff_isSheaf_of_type J _).1 (sheafHom F G).property

/-- Isomorphisms between sheaves glue: `isoPresheaf F G` is a sheaf. -/
lemma isSheaf_isoPresheaf (F G : Sheaf J A) : Presieve.IsSheaf J (isoPresheaf F G) := by
  intro X S hS x hx
  have hFG := isSheaf_sheafHom' F G S hS
  have hGF := isSheaf_sheafHom' G F S hS
  have hFF := isSheaf_sheafHom' F F S hS
  have hGG := isSheaf_sheafHom' G G S hS
  let xh : Presieve.FamilyOfElements (sheafHom' F G) S := fun Y f hf ↦ (x f hf).hom
  let xi : Presieve.FamilyOfElements (sheafHom' G F) S := fun Y f hf ↦ (x f hf).inv
  have hxh : xh.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congrArg Iso.hom (hx g₁ g₂ h₁ h₂ w)
  have hxi : xi.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congrArg Iso.inv (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨a, ha, -⟩ := hFG xh hxh
  obtain ⟨b, hb, -⟩ := hGF xi hxi
  have hab : a ≫ b = 𝟙 _ := hFF.isSeparatedFor.ext fun Y f hf ↦ by
    rw [sheafHom'_map_comp, sheafHom'_map_id, ha f hf, hb f hf]
    exact (x f hf).hom_inv_id
  have hba : b ≫ a = 𝟙 _ := hGG.isSeparatedFor.ext fun Y f hf ↦ by
    rw [sheafHom'_map_comp, sheafHom'_map_id, ha f hf, hb f hf]
    exact (x f hf).inv_hom_id
  refine ⟨⟨a, b, hab, hba⟩, fun Y f hf ↦ Iso.ext (ha f hf), fun e he ↦ Iso.ext ?_⟩
  exact hFG.isSeparatedFor.ext fun Y f hf ↦ (congrArg Iso.hom (he f hf)).trans (ha f hf).symm

/-- The sheaf of types `X ↦ (F|_X ≅ G|_X)` of isomorphisms between the restrictions of two
sheaves to the slices `Over X`. -/
def isoSheaf (F G : Sheaf J A) : Sheaf J (Type _) :=
  ⟨isoPresheaf F G, (isSheaf_iff_isSheaf_of_type J _).2 (isSheaf_isoPresheaf F G)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The binary product of two presheaves of types satisfying the sheaf condition satisfies the
sheaf condition. -/
lemma Presieve.isSheaf_prod {P Q : Cᵒᵖ ⥤ Type w} (hP : Presieve.IsSheaf J P)
    (hQ : Presieve.IsSheaf J Q) : Presieve.IsSheaf J (FunctorToTypes.prod P Q) := by
  intro X S hS x hx
  let x₁ : Presieve.FamilyOfElements P S := fun Y f hf ↦ (x f hf).1
  let x₂ : Presieve.FamilyOfElements Q S := fun Y f hf ↦ (x f hf).2
  have hx₁ : x₁.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    (Prod.ext_iff.1 (hx g₁ g₂ h₁ h₂ w)).1
  have hx₂ : x₂.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    (Prod.ext_iff.1 (hx g₁ g₂ h₁ h₂ w)).2
  obtain ⟨a, ha, -⟩ := hP S hS x₁ hx₁
  obtain ⟨b, hb, -⟩ := hQ S hS x₂ hx₂
  refine ⟨(a, b), fun Y f hf ↦ Prod.ext (ha f hf) (hb f hf), fun c hc ↦ Prod.ext ?_ ?_⟩
  · exact (hP S hS).isSeparatedFor.ext fun Y f hf ↦
      (Prod.ext_iff.1 (hc f hf)).1.trans (ha f hf).symm
  · exact (hQ S hS).isSeparatedFor.ext fun Y f hf ↦
      (Prod.ext_iff.1 (hc f hf)).2.trans (hb f hf).symm

variable {F' F G' G : Sheaf J A}

/-- Given morphisms `r : F' ⟶ F` and `g : G' ⟶ G`, the subpresheaf of pairs of isomorphisms
`(ψ, φ)`, with `ψ : F'|_X ≅ G'|_X` and `φ : F|_X ≅ G|_X`, such that `ψ ≫ g = r ≫ φ`. -/
def isoPairSubfunctor (r : F' ⟶ F) (g : G' ⟶ G) :
    Subfunctor (FunctorToTypes.prod (isoPresheaf F' G') (isoPresheaf F G)) where
  obj X := {p | p.1.hom ≫ (J.overPullback A X.unop).map g =
    (J.overPullback A X.unop).map r ≫ p.2.hom}
  map {X Y} f p hp := by
    have := congrArg ((J.overMapPullback A f.unop).map) hp
    simp only [Functor.map_comp] at this
    exact this

/-- Membership in `isoPairSubfunctor` is the compatibility of the two isomorphisms. -/
lemma mem_isoPairSubfunctor_iff (r : F' ⟶ F) (g : G' ⟶ G) {X : Cᵒᵖ}
    (p : (FunctorToTypes.prod (isoPresheaf F' G') (isoPresheaf F G)).obj X) :
    p ∈ (isoPairSubfunctor r g).obj X ↔ p.1.hom ≫ (J.overPullback A X.unop).map g =
      (J.overPullback A X.unop).map r ≫ p.2.hom := Iff.rfl

/-- The compatible pairs of isomorphisms form a sheaf. -/
lemma isSheaf_isoPairSubfunctor (r : F' ⟶ F) (g : G' ⟶ G) :
    Presieve.IsSheaf J (isoPairSubfunctor r g).toFunctor := by
  rw [Subfunctor.isSheaf_iff _
    (Presieve.isSheaf_prod (isSheaf_isoPresheaf F' G') (isSheaf_isoPresheaf F G))]
  intro X p hp
  refine (isSheaf_sheafHom' F' G _ hp).isSeparatedFor.ext fun Y f hf ↦ ?_
  have hf' : (sheafHom' F' G').map f.op p.1.hom ≫ (J.overPullback A Y).map g =
      (J.overPullback A Y).map r ≫ (sheafHom' F G).map f.op p.2.hom := hf
  exact ((sheafHom'_map_comp F' G' G f.op _ _).trans hf').trans
    (sheafHom'_map_comp F' F G f.op _ _).symm

/-- The sheaf of compatible pairs of isomorphisms `(ψ, φ)`, with `ψ : F'|_X ≅ G'|_X` and
`φ : F|_X ≅ G|_X` such that `ψ ≫ g = r ≫ φ`. -/
def isoPairSheaf (r : F' ⟶ F) (g : G' ⟶ G) : Sheaf J (Type _) :=
  ⟨(isoPairSubfunctor r g).toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).2 (isSheaf_isoPairSubfunctor r g)⟩

/-- The projection from compatible pairs of isomorphisms to the second isomorphism. -/
def isoPairSheafSnd (r : F' ⟶ F) (g : G' ⟶ G) : isoPairSheaf r g ⟶ isoSheaf F G :=
  ObjectProperty.homMk ((isoPairSubfunctor r g).ι ≫ FunctorToTypes.prod.snd)

namespace GrothendieckTopology.IsWeaklyContractible

variable {W : C}

/-- Over a weakly contractible object `W`, a morphism of sheaves of types which is locally
surjective, in the explicit sense that every section is locally in the image, is surjective on
sections over `W`. -/
lemma exists_app_eq {E P : Sheaf J (Type w)} (hW : J.IsWeaklyContractible.{w} W) (φ : E ⟶ P)
    (h : ∀ (X : C) (s : P.obj.obj (op X)), ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
      ∃ t : E.obj.obj (op Y), φ.hom.app (op Y) t = P.obj.map f.op s)
    (s : P.obj.obj (op W)) : ∃ t : E.obj.obj (op W), φ.hom.app (op W) t = s := by
  have : Sheaf.IsLocallySurjective φ := ⟨fun {X} s ↦ by
    obtain ⟨S, hS, hs⟩ := h X s
    exact J.superset_covering (fun Y f hf ↦ hs f hf) hS⟩
  exact hW φ this s

/-- Over a weakly contractible object `W`, a locally nonempty sheaf of types has a section. -/
lemma nonempty {P : Sheaf J (Type w)} (hW : J.IsWeaklyContractible.{w} W)
    (h : ∀ X : C, ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → Nonempty (P.obj.obj (op Y))) :
    Nonempty (P.obj.obj (op W)) := by
  obtain ⟨t, -⟩ := hW.exists_app_eq ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from P)
    (fun X _ ↦ by
      obtain ⟨S, hS, hne⟩ := h X
      exact ⟨S, hS, fun Y f hf ↦ ⟨(hne f hf).some, rfl⟩⟩) PUnit.unit
  exact ⟨t⟩

end GrothendieckTopology.IsWeaklyContractible

namespace GrothendieckTopology

/-- **Lifting local isomorphisms of towers over a weakly contractible object.** Let `R` and `G`
be towers of sheaves such that `R₀` and `G₀` are locally isomorphic, and such that every local
isomorphism `φ : Rₙ|_X ≅ Gₙ|_X` locally lifts to an isomorphism `ψ : Rₙ₊₁ ≅ Gₙ₊₁` compatible
with `φ` and the transition maps. Then over every weakly contractible object `W` the towers are
isomorphic: choose `φ₀` over `W`, and recursively lift `φₙ` to `φₙ₊₁` over `W`, using that the
locally surjective projection from compatible pairs to `Iso(Rₙ, Gₙ)` is surjective over `W`. -/
theorem nonempty_iso_overPullback_of_isWeaklyContractible (R G : ℕᵒᵖ ⥤ Sheaf J A) {W : C}
    (hW : J.IsWeaklyContractible.{max u v v'} W)
    (h₀ : ∀ X : C, ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
      Nonempty ((isoPresheaf (R.obj (op 0)) (G.obj (op 0))).obj (op Y)))
    (hlift : ∀ (n : ℕ) (X : C) (φ : (isoPresheaf (R.obj (op n)) (G.obj (op n))).obj (op X)),
      ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
        ∃ ψ : (isoPresheaf (R.obj (op (n + 1))) (G.obj (op (n + 1)))).obj (op Y),
          ψ.hom ≫ (J.overPullback A Y).map (G.map (homOfLE n.le_succ).op) =
            (J.overPullback A Y).map (R.map (homOfLE n.le_succ).op) ≫
              ((isoPresheaf _ _).map f.op φ).hom) :
    Nonempty (R ⋙ J.overPullback A W ≅ G ⋙ J.overPullback A W) := by
  have step (n : ℕ) (φ : (isoPresheaf (R.obj (op n)) (G.obj (op n))).obj (op W)) :
      ∃ ψ : (isoPresheaf (R.obj (op (n + 1))) (G.obj (op (n + 1)))).obj (op W),
        ψ.hom ≫ (J.overPullback A W).map (G.map (homOfLE n.le_succ).op) =
          (J.overPullback A W).map (R.map (homOfLE n.le_succ).op) ≫ φ.hom := by
    obtain ⟨⟨⟨ψ, φ'⟩, hψ⟩, hφ'⟩ := hW.exists_app_eq
      (isoPairSheafSnd (R.map (homOfLE n.le_succ).op) (G.map (homOfLE n.le_succ).op))
      (fun X φ ↦ by
        obtain ⟨S, hS, hlS⟩ := hlift n X φ
        refine ⟨S, hS, fun Y f hf ↦ ?_⟩
        obtain ⟨ψ, hψ⟩ := hlS f hf
        exact ⟨⟨⟨ψ, (isoPresheaf _ _).map f.op φ⟩, hψ⟩, rfl⟩) φ
    obtain rfl : φ' = φ := hφ'
    exact ⟨ψ, hψ⟩
  choose next hnext using step
  let φ₀ := (hW.nonempty (P := isoSheaf (R.obj (op 0)) (G.obj (op 0))) h₀).some
  let seq : ∀ n : ℕ, (isoPresheaf (R.obj (op n)) (G.obj (op n))).obj (op W) :=
    fun n ↦ Nat.rec φ₀ (fun n φ ↦ next n φ) n
  let α : R ⋙ J.overPullback A W ⟶ G ⋙ J.overPullback A W :=
    NatTrans.ofOpSequence (fun n ↦ (seq n).hom) (fun n ↦ (hnext n (seq n)).symm)
  have (n : ℕᵒᵖ) : IsIso (α.app n) := by
    simp only [α, NatTrans.ofOpSequence_app]
    exact (seq n.unop).isIso_hom
  have : IsIso α := NatIso.isIso_of_isIso_app _
  exact ⟨asIso α⟩

end GrothendieckTopology

namespace GrothendieckTopology

variable (J) in
/-- Restriction to a slice preserves the limits which exist in the coefficient category: limits
of sheaves are computed on sections. -/
instance preservesLimitsOfShape_overPullback {K : Type*} [Category* K] [HasLimitsOfShape K A]
    (X : C) : PreservesLimitsOfShape K (J.overPullback A X) := by
  have : PreservesLimitsOfShape K (J.overPullback A X ⋙ sheafToPresheaf (J.over X) A) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft _ _ A).obj (Over.forget X).op))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf (J.over X) A)

/-- **Limits of towers with locally liftable local isomorphisms are isomorphic over weakly
contractible objects**: under the hypotheses of
`GrothendieckTopology.nonempty_iso_overPullback_of_isWeaklyContractible`,
`(lim R)|_W ≅ (lim G)|_W`. -/
theorem nonempty_iso_overPullback_limit_of_isWeaklyContractible [HasLimitsOfShape ℕᵒᵖ A]
    (R G : ℕᵒᵖ ⥤ Sheaf J A) {W : C} (hW : J.IsWeaklyContractible.{max u v v'} W)
    (h₀ : ∀ X : C, ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
      Nonempty ((isoPresheaf (R.obj (op 0)) (G.obj (op 0))).obj (op Y)))
    (hlift : ∀ (n : ℕ) (X : C) (φ : (isoPresheaf (R.obj (op n)) (G.obj (op n))).obj (op X)),
      ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
        ∃ ψ : (isoPresheaf (R.obj (op (n + 1))) (G.obj (op (n + 1)))).obj (op Y),
          ψ.hom ≫ (J.overPullback A Y).map (G.map (homOfLE n.le_succ).op) =
            (J.overPullback A Y).map (R.map (homOfLE n.le_succ).op) ≫
              ((isoPresheaf _ _).map f.op φ).hom) :
    Nonempty ((J.overPullback A W).obj (limit R) ≅ (J.overPullback A W).obj (limit G)) := by
  obtain ⟨e⟩ := nonempty_iso_overPullback_of_isWeaklyContractible R G hW h₀ hlift
  exact ⟨preservesLimitIso _ R ≪≫ lim.mapIso e ≪≫ (preservesLimitIso _ G).symm⟩

end GrothendieckTopology

namespace GrothendieckTopology

/-- **Criterion for lifting local isomorphisms of towers.** Let `r : R' ⟶ R` and `g : G' ⟶ G`.
Suppose that `R'` and `G'` are locally isomorphic, that every isomorphism `ψ : R'|_Y ≅ G'|_Y`
descends to an isomorphism `φ : R|_Y ≅ G|_Y` with `ψ ≫ g = r ≫ φ`, and that every
automorphism of `R|_Y` locally lifts along `r` to an automorphism of `R'`. Then every
isomorphism `φ : R|_X ≅ G|_X` locally lifts along `r` and `g` to an isomorphism `R' ≅ G'`:
locally choose `ψ₀ : R' ≅ G'`, descend it to `φ₀`, and correct `ψ₀` by a local lift of the
automorphism `φ ≫ φ₀⁻¹` of `R`. -/
lemma exists_lift_iso_of_descent {R' R G' G : Sheaf J A} (r : R' ⟶ R) (g : G' ⟶ G)
    (hloc : ∀ X : C, ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
      Nonempty ((isoPresheaf R' G').obj (op Y)))
    (hdesc : ∀ (Y : C) (ψ : (isoPresheaf R' G').obj (op Y)),
      ∃ φ : (isoPresheaf R G).obj (op Y),
        ψ.hom ≫ (J.overPullback A Y).map g = (J.overPullback A Y).map r ≫ φ.hom)
    (haut : ∀ (Y : C) (α : (isoPresheaf R R).obj (op Y)), ∃ S ∈ J Y, ∀ ⦃Z : C⦄ (h : Z ⟶ Y),
      S h → ∃ β : (isoPresheaf R' R').obj (op Z),
        β.hom ≫ (J.overPullback A Z).map r =
          (J.overPullback A Z).map r ≫ ((isoPresheaf R R).map h.op α).hom)
    (X : C) (φ : (isoPresheaf R G).obj (op X)) :
    ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → ∃ ψ : (isoPresheaf R' G').obj (op Y),
      ψ.hom ≫ (J.overPullback A Y).map g =
        (J.overPullback A Y).map r ≫ ((isoPresheaf R G).map f.op φ).hom := by
  obtain ⟨S₁, hS₁, h₁⟩ := hloc X
  have key (Y : C) (f : Y ⟶ X) (hf : S₁ f) : ∃ S ∈ J Y, ∀ ⦃Z : C⦄ (h : Z ⟶ Y), S h →
      ∃ ψ : (isoPresheaf R' G').obj (op Z), ψ.hom ≫ (J.overPullback A Z).map g =
        (J.overPullback A Z).map r ≫ ((isoPresheaf R G).map (h ≫ f).op φ).hom := by
    let ψ₀ := (h₁ f hf).some
    obtain ⟨φ₀, hφ₀⟩ := hdesc Y ψ₀
    obtain ⟨S, hS, hSlift⟩ := haut Y ((isoPresheaf R G).map f.op φ ≪≫ φ₀.symm)
    refine ⟨S, hS, fun Z h hh ↦ ?_⟩
    obtain ⟨β, hβ⟩ := hSlift h hh
    refine ⟨β ≪≫ (isoPresheaf R' G').map h.op ψ₀, ?_⟩
    have hφ₀' := congrArg (J.overMapPullback A h).map hφ₀
    rw [Functor.map_comp, Functor.map_comp] at hφ₀'
    have hβ' : β.hom ≫ (J.overPullback A Z).map r = (J.overPullback A Z).map r ≫
        (J.overMapPullback A h).map ((isoPresheaf R G).map f.op φ).hom ≫
          (J.overMapPullback A h).map φ₀.inv :=
      hβ.trans (congrArg _ ((J.overMapPullback A h).map_comp _ _))
    rw [op_comp, Functor.map_comp_apply]
    calc (β ≪≫ (isoPresheaf R' G').map h.op ψ₀).hom ≫ (J.overPullback A Z).map g
        = β.hom ≫ (J.overPullback A Z).map r ≫ (J.overMapPullback A h).map φ₀.hom := by
          rw [Iso.trans_hom, Category.assoc]
          exact congrArg _ hφ₀'
      _ = (J.overPullback A Z).map r ≫
          (J.overMapPullback A h).map ((isoPresheaf R G).map f.op φ).hom := by
          rw [← Category.assoc, hβ', Category.assoc, Category.assoc, ← Functor.map_comp,
            Iso.inv_hom_id, Functor.map_id, Category.comp_id]
  choose S₂ hS₂ h₂ using key
  refine ⟨Sieve.bind S₁ S₂, J.bind_covering hS₁ hS₂, ?_⟩
  rintro Z _ ⟨Y, h, f, hf, hh, rfl⟩
  exact h₂ Y f hf h hh

end GrothendieckTopology


namespace Limits

/-- **Descent of isomorphisms along cokernels.** Let `r : R' ⟶ R` be a cokernel of `a : R' ⟶ R'`
and `g : G' ⟶ G` a cokernel of `b : G' ⟶ G'`. An isomorphism `ψ : R' ≅ G'` intertwining `a`
and `b` descends to an isomorphism `φ : R ≅ G` with `r ≫ φ = ψ ≫ g`. For `a` and `b`
multiplication by `ℓⁿ`, this is the reduction modulo `ℓⁿ` of an isomorphism. -/
lemma exists_iso_comp_eq_of_isColimit_cokernelCofork {D : Type*} [Category* D]
    [HasZeroMorphisms D] {R' R G' G : D} {a : R' ⟶ R'} {b : G' ⟶ G'} {r : R' ⟶ R}
    {g : G' ⟶ G} {wr : a ≫ r = 0} {wg : b ≫ g = 0} (hr : IsColimit (CokernelCofork.ofπ r wr))
    (hg : IsColimit (CokernelCofork.ofπ g wg)) (ψ : R' ≅ G') (hψ : a ≫ ψ.hom = ψ.hom ≫ b) :
    ∃ φ : R ≅ G, r ≫ φ.hom = ψ.hom ≫ g := by
  have hψ' : b ≫ ψ.inv = ψ.inv ≫ a := by
    rw [← cancel_epi ψ.hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← hψ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  obtain ⟨f, hf⟩ := CokernelCofork.IsColimit.desc' hr (ψ.hom ≫ g)
    (by rw [← Category.assoc, hψ, Category.assoc, wg, comp_zero])
  obtain ⟨f', hf'⟩ := CokernelCofork.IsColimit.desc' hg (ψ.inv ≫ r)
    (by rw [← Category.assoc, hψ', Category.assoc, wr, comp_zero])
  have hf₁ : r ≫ f = ψ.hom ≫ g := hf
  have hf₂ : g ≫ f' = ψ.inv ≫ r := hf'
  refine ⟨⟨f, f', ?_, ?_⟩, hf₁⟩
  · refine Cofork.IsColimit.hom_ext hr ?_
    rw [Cofork.π_ofπ, ← Category.assoc, hf₁, Category.assoc, hf₂, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · refine Cofork.IsColimit.hom_ext hg ?_
    rw [Cofork.π_ofπ, ← Category.assoc, hf₂, Category.assoc, hf₁, Iso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

end Limits

namespace GrothendieckTopology

variable [Preadditive A]

/-- **Lifting local trivialisations of `ℓ`-adic towers over weakly contractible objects.** Let
`R` and `G` be towers of sheaves of abelian groups (or of objects of a preadditive category)
such that, restricted to every `Y`, each transition map `Xₙ₊₁ ⟶ Xₙ` is a cokernel of
multiplication by an integer `N n` (for instance `N n = ℓⁿ` and `Xₙ₊₁/ℓⁿ ≅ Xₙ`). Suppose that
`Rₙ` and `Gₙ` are locally isomorphic for every `n`, and that every automorphism of `Rₙ|_Y`
locally lifts to an automorphism of `Rₙ₊₁`. Then over every weakly contractible `W` the towers
`R` and `G` are isomorphic. -/
theorem nonempty_iso_overPullback_of_isColimit_cokernelCofork (R G : ℕᵒᵖ ⥤ Sheaf J A)
    (N : ℕ → ℤ) {W : C} (hW : J.IsWeaklyContractible.{max u v v'} W)
    (hR : ∀ (n : ℕ) (Y : C), ∃ w : (N n • 𝟙 _) ≫
        (J.overPullback A Y).map (R.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hG : ∀ (n : ℕ) (Y : C), ∃ w : (N n • 𝟙 _) ≫
        (J.overPullback A Y).map (G.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (X : C), ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
      Nonempty ((isoPresheaf (R.obj (op n)) (G.obj (op n))).obj (op Y)))
    (haut : ∀ (n : ℕ) (Y : C) (α : (isoPresheaf (R.obj (op n)) (R.obj (op n))).obj (op Y)),
      ∃ S ∈ J Y, ∀ ⦃Z : C⦄ (h : Z ⟶ Y), S h →
        ∃ β : (isoPresheaf (R.obj (op (n + 1))) (R.obj (op (n + 1)))).obj (op Z),
          β.hom ≫ (J.overPullback A Z).map (R.map (homOfLE n.le_succ).op) =
            (J.overPullback A Z).map (R.map (homOfLE n.le_succ).op) ≫
              ((isoPresheaf _ _).map h.op α).hom) :
    Nonempty (R ⋙ J.overPullback A W ≅ G ⋙ J.overPullback A W) := by
  refine nonempty_iso_overPullback_of_isWeaklyContractible R G hW (hloc 0)
    fun n ↦ exists_lift_iso_of_descent _ _ (hloc (n + 1)) (fun Y ψ ↦ ?_) (haut n)
  obtain ⟨wr, ⟨hr⟩⟩ := hR n Y
  obtain ⟨wg, ⟨hg⟩⟩ := hG n Y
  obtain ⟨φ, hφ⟩ := exists_iso_comp_eq_of_isColimit_cokernelCofork hr hg ψ
    (by rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, Category.comp_id])
  exact ⟨φ, hφ.symm⟩

end GrothendieckTopology

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.GrothendieckTopology

variable {T : Scheme.{u}} {A : Type u'} [Category.{v'} A]

/-- **Towers with locally liftable local isomorphisms have locally isomorphic limits** on the
small pro-étale site: every object is covered by weakly contractible objects (Stacks 0990),
over which the towers themselves become isomorphic. -/
theorem exists_cover_nonempty_iso_overPullback_limit [HasLimitsOfShape ℕᵒᵖ A]
    (R G : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) A)
    (h₀ : ∀ X : T.ProEt, ∃ S ∈ Scheme.ProEt.topology T X, ∀ ⦃Y : T.ProEt⦄ (f : Y ⟶ X), S f →
      Nonempty ((isoPresheaf (R.obj (op 0)) (G.obj (op 0))).obj (op Y)))
    (hlift : ∀ (n : ℕ) (X : T.ProEt)
      (φ : (isoPresheaf (R.obj (op n)) (G.obj (op n))).obj (op X)),
      ∃ S ∈ Scheme.ProEt.topology T X, ∀ ⦃Y : T.ProEt⦄ (f : Y ⟶ X), S f →
        ∃ ψ : (isoPresheaf (R.obj (op (n + 1))) (G.obj (op (n + 1)))).obj (op Y),
          ψ.hom ≫ ((Scheme.ProEt.topology T).overPullback A Y).map
              (G.map (homOfLE n.le_succ).op) =
            ((Scheme.ProEt.topology T).overPullback A Y).map (R.map (homOfLE n.le_succ).op) ≫
              ((isoPresheaf _ _).map f.op φ).hom)
    (V : T.ProEt) :
    ∃ (ι : Type u) (W : ι → T.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ Scheme.ProEt.topology T V ∧
      ∀ i, Nonempty (((Scheme.ProEt.topology T).overPullback A (W i)).obj (limit R) ≅
        ((Scheme.ProEt.topology T).overPullback A (W i)).obj (limit G)) := by
  obtain ⟨ι, W, f, hW, hcov⟩ := Scheme.ProEt.exists_isWeaklyContractible_cover.{max (u + 1) v'} V
  exact ⟨ι, W, f, hcov, fun i ↦
    nonempty_iso_overPullback_limit_of_isWeaklyContractible R G (hW i).2 h₀ hlift⟩

/-- **Lattices of `ℓ`-adic towers are pro-étale locally isomorphic.** Let `R` and `G` be towers
of pro-étale sheaves (valued in a preadditive category with sequential limits) whose
transitions are, locally, cokernels of multiplication by integers `N n` (e.g.
`Xₙ₊₁/ℓⁿ ≅ Xₙ`), such that `Rₙ` and `Gₙ` are locally isomorphic for every `n` and automorphisms
of `Rₙ` locally lift to `Rₙ₊₁`. Then `lim R` and `lim G` are isomorphic over the members of a
pro-étale cover of any object: the weakly contractible covers of Stacks 0990. -/
theorem exists_cover_nonempty_iso_overPullback_limit_of_isColimit_cokernelCofork
    [Preadditive A] [HasLimitsOfShape ℕᵒᵖ A] (R G : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) A)
    (N : ℕ → ℤ)
    (hR : ∀ (n : ℕ) (Y : T.ProEt), ∃ w : (N n • 𝟙 _) ≫
        ((Scheme.ProEt.topology T).overPullback A Y).map (R.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hG : ∀ (n : ℕ) (Y : T.ProEt), ∃ w : (N n • 𝟙 _) ≫
        ((Scheme.ProEt.topology T).overPullback A Y).map (G.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (X : T.ProEt), ∃ S ∈ Scheme.ProEt.topology T X,
      ∀ ⦃Y : T.ProEt⦄ (f : Y ⟶ X), S f →
        Nonempty ((isoPresheaf (R.obj (op n)) (G.obj (op n))).obj (op Y)))
    (haut : ∀ (n : ℕ) (Y : T.ProEt)
      (α : (isoPresheaf (R.obj (op n)) (R.obj (op n))).obj (op Y)),
      ∃ S ∈ Scheme.ProEt.topology T Y, ∀ ⦃Z : T.ProEt⦄ (h : Z ⟶ Y), S h →
        ∃ β : (isoPresheaf (R.obj (op (n + 1))) (R.obj (op (n + 1)))).obj (op Z),
          β.hom ≫ ((Scheme.ProEt.topology T).overPullback A Z).map
              (R.map (homOfLE n.le_succ).op) =
            ((Scheme.ProEt.topology T).overPullback A Z).map (R.map (homOfLE n.le_succ).op) ≫
              ((isoPresheaf _ _).map h.op α).hom)
    (V : T.ProEt) :
    ∃ (ι : Type u) (W : ι → T.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ Scheme.ProEt.topology T V ∧
      ∀ i, Nonempty (((Scheme.ProEt.topology T).overPullback A (W i)).obj (limit R) ≅
        ((Scheme.ProEt.topology T).overPullback A (W i)).obj (limit G)) := by
  obtain ⟨ι, W, f, hW, hcov⟩ := Scheme.ProEt.exists_isWeaklyContractible_cover.{max (u + 1) v'} V
  refine ⟨ι, W, f, hcov, fun i ↦ ?_⟩
  obtain ⟨e⟩ := nonempty_iso_overPullback_of_isColimit_cokernelCofork R G N (hW i).2 hR hG hloc
    haut
  exact ⟨preservesLimitIso _ R ≪≫ lim.mapIso e ≪≫ (preservesLimitIso _ G).symm⟩

end AlgebraicGeometry.ProEtale
